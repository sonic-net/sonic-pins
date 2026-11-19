"""Check the installed production programs and their matching split DWARF."""

import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import subprocess
import tarfile
import tempfile


PROGRAMS = {
    "p4rt": ("p4rt_app/p4rt.cc", "p4rt_grpc_port"),
    "p4rt_program_table": ("p4rt_app/scripts/p4rt_program_table.cc", "push_config"),
    "p4rt_read": ("p4rt_app/scripts/p4rt_read.cc", "table_ids"),
    "p4rt_set_forwarding_pipeline": (
        "p4rt_app/scripts/p4rt_set_forwarding_pipeline.cc", "default_middleblock_p4info"),
    "p4rt_write": ("p4rt_app/scripts/p4rt_write.cc", "ir_write_request_file"),
}


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def digest(filename):
    with Path(filename).open("rb") as source:
        return hashlib.file_digest(source, "sha256").hexdigest()


def run(argv, **kwargs):
    result = subprocess.run(argv, text=True, capture_output=True, timeout=180, **kwargs)
    require(result.returncode == 0, repr(argv) + "\n" + result.stdout + result.stderr)
    return result.stdout


def unpack(archive, destination, suffix, mode):
    expected = {"usr/local/bin/" + name + suffix for name in PROGRAMS}
    found = set()
    with tarfile.open(archive) as source:
        for member in source:
            path = PurePosixPath(member.name)
            require(not path.is_absolute() and ".." not in path.parts,
                    "unsafe installed path: " + member.name)
            name = str(path)
            require((member.uid, member.gid, member.mtime) == (0, 0, 0),
                    "noncanonical ownership/timestamp: " + name)
            if member.isdir():
                require(name in (".", "usr", "usr/local", "usr/local/bin") and
                        member.mode == 0o755, "unexpected installed directory: " + name)
                continue
            require(member.isfile() and name in expected and name not in found and
                    member.mode == mode and member.size > 0,
                    "unexpected, duplicate, empty or wrongly permissioned payload: " + name)
            output = destination / path.name
            with source.extractfile(member) as incoming, output.open("wb") as outgoing:
                shutil.copyfileobj(incoming, outgoing)
            output.chmod(mode)
            found.add(name)
    require(found == expected, "incomplete production payload: " + repr(expected - found))


def debug_lookup(binary, work):
    script = work / "lookup.gdb"
    script.write_text('''python
import gdb, json
try:
    location = gdb.decode_line("main")[1][0]
    block = gdb.block_for_pc(location.pc)
    while block is not None and block.function is None:
        block = block.superblock
    symbol = block.function if block is not None else None
    if symbol is None or symbol.symtab is None or symbol.name.split("(", 1)[0] != "main":
        raise ValueError("main has no debug function")
    parameters = [str(field.type) for field in symbol.type.fields()]
    if len(parameters) != 2 or parameters[0] != "int":
        raise ValueError("main lacks parameter type information")
    result = {"found": True, "file": location.symtab.filename,
              "line": location.line, "parameters": parameters}
except Exception as error:
    result = {"found": False, "error": str(error)}
print("P4RT_INSTALLED_DEBUG=" + json.dumps(result))
end
''')
    output = run([
        "gdb", "-nx", "-nh", "--batch", "-iex", "set auto-load off",
        "-iex", "set debuginfod enabled off", "-iex", "set pagination off",
        "-iex", "set debug-file-directory " + json.dumps(str(work / "empty")),
        "-ex", "file " + json.dumps(str(binary)), "-x", str(script),
    ], cwd=work, env=dict(os.environ, LC_ALL="C", DEBUGINFOD_URLS=""))
    prefix = "P4RT_INSTALLED_DEBUG="
    records = [json.loads(line[len(prefix):]) for line in output.splitlines()
               if line.startswith(prefix)]
    require(len(records) == 1, "no unique installed GDB result")
    return records[0]


def installed_command(binary, arguments, common, *, listing=False):
    loader = os.environ.get('P4RT_TEST_RUNTIME_LOADER')
    libraries = os.environ.get('P4RT_TEST_LIBRARY_PATH')
    require(bool(loader) == bool(libraries), 'Incomplete declared test runtime')
    if loader:
        require(Path(loader).is_absolute() and Path(loader).is_file(), 'Missing declared runtime interpreter')
        search = os.pathsep.join((str(common.parent), libraries))
        return [loader, '--library-path', search, *(['--list'] if listing else []), str(binary), *arguments]
    return (['ldd', str(binary)] if listing else [str(binary), *arguments])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--runtime", required=True, type=Path)
    parser.add_argument("--debug", required=True, type=Path)
    parser.add_argument("--common-library", required=True, type=Path)
    parser.add_argument("--runtime-contract", required=True, type=Path)
    parser.add_argument("--debug-contract", required=True, type=Path)
    args = parser.parse_args()
    for path, package, target, suffix in (
            (args.runtime_contract, "sonic-p4rt", "p4rt_runtime", ""),
            (args.debug_contract, "sonic-p4rt-dbgsym", "p4rt_runtime_debug", ".dwp")):
        contract = json.loads(path.read_text())
        require(contract.get("schema") == 1 and contract.get("owner") == "sonic-pins" and
                set(contract["packages"]) == {package}, "unexpected package owner contract")
        entry = contract["packages"][package]
        require(entry["target"] == "//p4rt_app:" + target and
                set(entry["required_paths"]) == {"usr/local/bin/" + name + suffix for name in PROGRAMS},
                "owner contract differs from installed production inventory")
        require(entry["control_fields"]["Package"] == package and
                entry["control_fields"]["Architecture"] == "amd64" and
                entry["control_fields"]["Version"], "invalid package identity")
    common = args.common_library.resolve()
    source_root = Path.cwd()
    results = {}
    with tempfile.TemporaryDirectory(prefix="p4rt-installed-") as temporary:
        work = Path(temporary)
        runtime, debug = work / "runtime", work / "debug"
        runtime.mkdir(); debug.mkdir()
        unpack(args.runtime, runtime, "", 0o755)
        unpack(args.debug, debug, ".dwp", 0o644)
        environment = {key: value for key, value in os.environ.items() if key not in ('LD_PRELOAD', 'LD_AUDIT')}
        environment['LC_ALL'] = 'C'
        if os.environ.get('P4RT_TEST_RUNTIME_LOADER'):
            environment.pop('LD_LIBRARY_PATH', None)
        else:
            environment['LD_LIBRARY_PATH'] = os.pathsep.join(filter(None,
                (str(common.parent), os.environ.get('LD_LIBRARY_PATH', ''))))
        for name, (source, flag) in PROGRAMS.items():
            binary, symbols = runtime / name, debug / (name + ".dwp")
            header = run(["readelf", "-h", str(binary)])
            require("Advanced Micro Devices X86-64" in header, name + " is not AMD64")
            sections = run(["readelf", "-SW", str(symbols)])
            for section in (".debug_info.dwo", ".debug_abbrev.dwo", ".debug_cu_index"):
                require(section in sections, name + " has incomplete DWP: " + section)
            dynamic = run(["readelf", "-d", str(binary)])
            needed = re.findall(r"\(NEEDED\).*?\[([^]]+)\]", dynamic)
            loaded = run(installed_command(binary, [], common, listing=True), env=environment)
            require("not found" not in loaded, "unresolved installed dependency: " + name)
            if name == "p4rt":
                require("libswsscommon.so.0" in needed, "P4RT no longer imports the Common library")
                match = re.search(r"libswsscommon\.so\.0 => (\S+)", loaded)
                require(match and digest(match[1]) == digest(common), "loaded Common differs from SDK")
                run(installed_command(binary, ["--only_check_args"], common), env=environment)
            help_result = subprocess.run(installed_command(binary, ["--helpshort"], common), env=environment,
                                         text=True, capture_output=True, timeout=30)
            require(help_result.returncode in (0, 1) and flag in help_result.stdout + help_result.stderr,
                    "installed production CLI did not expose its original flags: " + name)
            isolated = work / name
            isolated.mkdir(); (isolated / "empty").mkdir()
            copied = isolated / name
            shutil.copyfile(binary, copied)
            without = debug_lookup(copied, isolated)
            require(not without["found"], "loose DWO or embedded debug fallback for " + name)
            shutil.copyfile(symbols, isolated / (name + ".dwp"))
            with_symbols = debug_lookup(copied, isolated)
            require(with_symbols["found"], "matching DWP cannot resolve main: " + name)
            require(with_symbols["file"].replace("\\", "/").endswith(source),
                    "DWP main resolves to a different source: " + name)
            lines = (source_root / source).read_text().splitlines()
            definitions = [number for number, line in enumerate(lines, 1)
                           if re.match(r"\s*int\s+main\s*\(", line)]
            require(len(definitions) == 1 and definitions[0] <= with_symbols["line"] <= len(lines),
                    "DWP line lies outside the matching source main: " + name)
            build_ids = re.findall(r"Build ID: (\w+)", run(["readelf", "-n", str(binary)]))
            require(len(build_ids) == 1, "missing/ambiguous runtime build ID: " + name)
            results[name] = {"runtime_sha256": digest(binary), "dwp_sha256": digest(symbols),
                             "source_sha256": digest(source_root / source), "build_id": build_ids[0],
                             "needed": needed, "without_dwp": without, "with_dwp": with_symbols,
                             "installed_cli": "passed"}
    report = {"status": "passed", "architecture": "amd64", "programs": results,
              "runtime_tar_sha256": digest(args.runtime), "debug_tar_sha256": digest(args.debug),
              "common_library_sha256": digest(common),
              "limits": "Installed CLI/library and offline symbol checks; original P4RT tests run separately."}
    output = os.environ.get("TEST_UNDECLARED_OUTPUTS_DIR")
    if output:
        (Path(output) / "installed-packages.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
