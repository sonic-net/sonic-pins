"""Bind source-owned package contracts to the selected checkout and TAR bytes."""

import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import subprocess


PROFILES = {
    "p4rt_runtime": "sonic-p4rt",
    "p4rt_runtime_debug": "sonic-p4rt-dbgsym",
}


def require(value, message):
    if not value:
        raise ValueError(message)


def seal_contracts(directory, source, revision):
    """Use contracts built by the owner; never infer controls in the image."""
    directory, source = Path(directory), Path(source)
    require(re.fullmatch(r"[0-9a-f]{40}", revision), "Expected the full source commit")
    actual = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=source, text=True).strip()
    require(actual == revision, "Source checkout changed after the build")
    require(not subprocess.check_output(["git", "status", "--porcelain"], cwd=source, text=True).strip(),
            "Package contracts require a clean source checkout")
    outputs = {}
    for target, package in PROFILES.items():
        template = directory / (target + "_contract_template.json")
        payload = directory / (target + ".tar")
        contract = json.loads(template.read_text())
        require(contract.get("schema") == 1 and contract.get("owner") == "sonic-pins" and
                set(contract.get("packages", {})) == {package}, "Unexpected source-owned contract")
        entry = contract["packages"][package]
        require(entry.get("target") == "//p4rt_app:" + target, "Contract names a different producer")
        fields = entry.get("control_fields", {})
        require(fields.get("Package") == package and fields.get("Architecture") == "amd64" and
                fields.get("Version"), "Contract package identity differs")
        paths = entry.get("required_paths", [])
        require(len(paths) == 5 and len(set(paths)) == 5 and all(
            isinstance(path, str) and not PurePosixPath(path).is_absolute() and
            ".." not in PurePosixPath(path).parts and path.startswith("usr/local/bin/")
            for path in paths), "Expected five safe production paths")
        require(payload.is_file() and not payload.is_symlink(), "Missing owner TAR")
        with payload.open("rb") as stream:
            payload_hash = hashlib.file_digest(stream, "sha256").hexdigest()
        entry.update(source_revision=revision, payload_sha256=payload_hash)
        contract["source"] = {"kind": "workspace", "name": "com_github_sonic_net_sonic_pins",
                              "revision": revision}
        output = directory / (target + "_contract.json")
        output.write_text(json.dumps(contract, indent=2, sort_keys=True) + "\n")
        outputs[target] = output
    return outputs
