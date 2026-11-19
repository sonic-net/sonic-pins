#!/usr/bin/env python3
"""Build production TARs and run all P4RT tests through the existing Common SDK."""

import argparse
import importlib.util
import json
import os
from pathlib import Path
import shutil
import shlex
import sys
import subprocess
import tempfile
import xml.etree.ElementTree as ET

from runtime_contract import PROFILES, seal_contracts
from production_handoff import sdk_inventory, verify_build, runtime_environment, verify_installed, verify_runtime_unchanged


def private_directory(output_base):
    """Create audit scratch space owned by one invocation, beside its output base.

    Graph and test-event files must not be shared by invocations whose output
    bases have the same parent, or one run could truncate or read another's.
    """
    parent = Path(output_base).resolve().parent
    parent.mkdir(parents=True, exist_ok=True)
    return Path(tempfile.mkdtemp(prefix="p4rt-runtime-private-", dir=parent))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--buildimage", required=True, type=Path)
    parser.add_argument("--sdk", required=True, type=Path)
    parser.add_argument("--output-base", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--jobs", type=int, default=2)
    parser.add_argument("--phase", choices=("build", "test", "all"), default="all")
    parser.add_argument("--bazel", default="bazel", help="Bazelisk or the Bazel 6.4.0 executable")
    parser.add_argument("--runtime-receipt", type=Path,
                        help="Required prepared matching runtime for the separate test phase")
    args = parser.parse_args()
    source = Path(__file__).resolve().parents[1]

    def identity():
        if subprocess.check_output(["git", "status", "--porcelain"], cwd=source, text=True).strip():
            raise ValueError("Production acceptance requires a clean source checkout")
        return subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=source, text=True).strip()

    source_commit = identity()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    sdk = args.sdk.resolve()
    initial_sdk = sdk_inventory(sdk)
    # Reuse the established SDK/no-DEB auditor; the workflow pins this checkout.
    spec = importlib.util.spec_from_file_location(
        "sdk_acceptance", args.buildimage.resolve() / "tools/bazel/ci/p4rt_common_sdk.py")
    acceptance = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(acceptance)
    env = dict(os.environ, USE_BAZEL_VERSION="6.4.0")
    bazel = [args.bazel, "--output_base=" + str(args.output_base.resolve())]
    override = "--override_repository=sonic_swss_common=" + str(sdk)
    options = ["--config=p4rt-runtime", override, "--jobs=" + str(args.jobs)]
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    runtime_proof = None
    if args.phase == "test" and not args.runtime_receipt:
        parser.error("--phase=test requires --runtime-receipt")
    if args.runtime_receipt:
        runtime_env, runtime_proof = runtime_environment(args.runtime_receipt, sdk)
        for key in ("LD_PRELOAD", "LD_AUDIT", "LD_LIBRARY_PATH"):
            env.pop(key, None)
        options.extend("--test_env=" + key + "=" + value for key, value in runtime_env.items())
        options.append('--run_under=' + shlex.join([
            sys.executable, '-B', str(source / 'ci/runtime_run_under.py'), '--sdk', str(sdk),
            '--receipt', str(args.runtime_receipt.resolve()),
            '--receipt-sha256', runtime_proof['receipt_sha256'], '--']))
    packages = ["//p4rt_app:" + name for name in PROFILES]
    templates = [target + "_contract_template" for target in packages]
    private = private_directory(args.output_base)

    def run(arguments, **kwargs):
        return subprocess.run([*bazel, *arguments], cwd=source, env=env,
                              check=True, **kwargs)

    def capture(arguments):
        return run(arguments, text=True, stdout=subprocess.PIPE).stdout.strip()

    def record(name, value):
        (output / name).write_text(json.dumps(value, indent=2) + "\n")

    try:
        version = capture(["version", "--gnu_format"])
        if [line for line in version.splitlines() if line.startswith("bazel ")] != ["bazel 6.4.0"]:
            raise ValueError("The production profile requires Bazel 6.4.0")
        tests = sorted(capture(["query", override, "tests(//p4rt_app/...)",
                                "--output=label"]).splitlines())
        if ("//p4rt_app:runtime_package_test" not in tests or
                any(not label.startswith(("//p4rt_app/", "//p4rt_app:")) for label in tests)):
            raise ValueError("Expected all original P4RT tests and the installed-package test")
        built = verify_build(output, sdk, source_commit) if args.phase == "test" else None
        if built is not None and built.get("test_targets") != tests:
            raise ValueError("Original test selection changed after build")
        (output / "test-targets.txt").write_text("\n".join(tests) + "\n")
        selection = (tests if args.phase == "test" else packages + templates +
                     (tests if args.phase == "all" else []))
        graph_path = private / "actions.json"
        with graph_path.open("w") as stream:
            run(["aquery", *options, "--output=jsonproto", "--include_artifacts",
                 "--include_commandline=false", "deps(set(" + " ".join(selection) + "))"],
                stdout=stream)
        audit_name = "test-action-audit.json" if args.phase == "test" else "action-audit.json"
        record(audit_name, acceptance.audit_graph(json.loads(graph_path.read_text())))
        graph_path.unlink()
        if args.phase != "test":
            run(["build", *options, *packages, *templates])
            execution_root = Path(capture(["info", *options, "execution_root"]))
            for target in packages + templates:
                files = capture(["cquery", *options, target, "--output=files"]).splitlines()
                suffix = ".tar" if target in packages else ".json"
                if len(files) != 1 or not files[0].endswith(suffix):
                    raise ValueError("Unexpected production artifact: " + target)
                shutil.copyfile(execution_root / files[0], output / Path(files[0]).name)
            shutil.copyfile(sdk / "sdk-build.json", output / "sdk-build.json")
            if identity() != source_commit:
                raise ValueError("Source changed during production build")
            if sdk_inventory(sdk) != initial_sdk:
                raise ValueError("SDK inputs changed during production build")
            contracts = seal_contracts(output, source, source_commit)
            record("source.json", {"commit": source_commit,
                "bazel": "6.4.0", "options": options, "architecture": "amd64",
                "test_targets": tests, "sdk_inventory": sdk_inventory(sdk),
                "tar_sha256": {name + ".tar": acceptance.digest(output / (name + ".tar")) for name in PROFILES},
                "contract_sha256": {item.name: acceptance.digest(item) for item in contracts.values()}})
            built = verify_build(output, sdk, source_commit)
        if args.phase == "build":
            print("PASS: two production TARs and sealed source/SDK handoff; tests are separate")
            return
        events = private / "test-events.json"
        result = subprocess.run([*bazel, "test", *options, "--nocache_test_results",
                                 "--test_output=errors", "--nozip_undeclared_test_outputs",
                                 "--build_event_json_file=" + str(events),
                                 *tests], cwd=source, env=env)
        statuses = {}
        if events.exists():
            for line in events.read_text().splitlines():
                event = json.loads(line)
                if "testSummary" in event:
                    statuses[event["id"]["testSummary"]["label"]] = event["testSummary"]["overallStatus"]
        record("test-results.json", statuses)
        result.check_returncode()
        if set(statuses) != set(tests) or any(status != "PASSED" for status in statuses.values()):
            raise ValueError("Every original and installed P4RT test must execute and pass")
        testlogs = Path(capture(["info", *options, "bazel-testlogs"]))
        installed = testlogs / "p4rt_app/runtime_package_test/test.outputs/installed-packages.json"
        shutil.copyfile(installed, output / "installed-packages.json")
        for label in tests:
            relative = label.removeprefix("//").replace(":", "/")
            destination = output / "test-results" / relative / "test.xml"
            destination.parent.mkdir(parents=True, exist_ok=True)
            xml = testlogs / relative / "test.xml"
            document = ET.parse(xml).getroot()
            if not document.findall(".//testcase") or any(
                    document.findall(".//" + tag) for tag in ("failure", "error", "skipped")):
                raise ValueError("Expected executed, passing original test cases: " + label)
            shutil.copyfile(xml, destination)
        if identity() != source_commit:
            raise ValueError("Source changed during production acceptance")
        verify_build(output, sdk, source_commit)
        verify_installed(json.loads((output / "installed-packages.json").read_text()), built, sdk)
        if args.runtime_receipt:
            verify_runtime_unchanged(args.runtime_receipt, sdk, runtime_proof)
            record("prepared-runtime.json", runtime_proof)
        print(f"PASS: two production TARs and all {len(tests)} P4RT tests")
    finally:
        subprocess.run([*bazel, "shutdown"], cwd=source, env=env, check=False)
        shutil.rmtree(private, ignore_errors=True)


if __name__ == "__main__":
    main()
