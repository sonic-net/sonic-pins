"""Verify native Bazel 8 P4RT runtime TAR, .build-id debug symbols, and OCI metadata."""

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
        "p4rt_app/scripts/p4rt_set_forwarding_pipeline.cc",
        "default_middleblock_p4info",
    ),
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


def build_id_of(elf_path):
    notes = run(["readelf", "-n", str(elf_path)])
    build_ids = re.findall(r"Build ID:\s*([0-9a-fA-F]+)", notes)
    require(len(build_ids) == 1, f"expected unique GNU Build ID in {elf_path}, got {build_ids}")
    return build_ids[0].lower()


def unpack_runtime(archive, destination):
    expected = {"usr/local/bin/" + name for name in PROGRAMS}
    found = {}
    with tarfile.open(archive) as source:
        for member in source:
            path = PurePosixPath(member.name.removeprefix("./"))
            name = "." if not path.parts else str(path)
            require(not path.is_absolute() and ".." not in path.parts,
                    "unsafe installed path: " + member.name)
            require((member.uid, member.gid) == (0, 0),
                    "non-root ownership: " + member.name)
            if member.isdir():
                require(name in (".", "usr", "usr/local", "usr/local/bin") and
                        member.mode == 0o755,
                        "unexpected installed directory: " + member.name)
                continue
            require(member.mtime == 0, "noncanonical file timestamp: " + member.name)
            require(member.isfile() and name in expected and name not in found and
                    member.mode == 0o755 and member.size > 0,
                    "unexpected, duplicate, empty or wrongly permissioned payload: " + member.name)
            output = destination / path.name
            with source.extractfile(member) as incoming, output.open("wb") as outgoing:
                shutil.copyfileobj(incoming, outgoing)
            output.chmod(0o755)
            found[name] = output
    require(set(found) == expected, "incomplete production payload: " + repr(expected - set(found)))
    return {Path(p).name: p for p in found.values()}


def unpack_debug_symbols(archive, debug_root):
    entries = {}
    with tarfile.open(archive) as source:
        for member in source:
            path = PurePosixPath(member.name.removeprefix("./"))
            name = "." if not path.parts else str(path)
            require(not path.is_absolute() and ".." not in path.parts,
                    "unsafe debug symbol path: " + member.name)
            require((member.uid, member.gid) == (0, 0),
                    "non-root debug symbol ownership: " + member.name)
            if member.isdir():
                continue
            require(member.isfile() and member.mode == 0o644 and member.size > 0,
                    "unexpected debug symbol member: " + member.name)
            parts = path.parts
            require(
                len(parts) == 6 and parts[:4] == ("usr", "lib", "debug", ".build-id")
                and len(parts[4]) == 2 and parts[5].endswith(".debug"),
                "unexpected debug symbol layout path: " + member.name,
            )
            rel_id = parts[4] + parts[5].removesuffix(".debug")
            out = debug_root / ".build-id" / parts[4] / parts[5]
            out.parent.mkdir(parents=True, exist_ok=True)
            with source.extractfile(member) as incoming, out.open("wb") as outgoing:
                shutil.copyfileobj(incoming, outgoing)
            out.chmod(0o644)
            require(rel_id not in entries, "duplicate build-id debug symbol: " + rel_id)
            entries[rel_id] = out
    require(len(entries) == len(PROGRAMS),
            f"expected {len(PROGRAMS)} debug symbol files, got {len(entries)}")
    return entries


def check_elf_hardening(binary, name):
    header = run(["readelf", "-h", str(binary)])
    require(re.search(r"Type:\s+DYN\b", header), f"{name} is not PIE (ET_DYN):\n{header}")

    phdrs = run(["readelf", "-lW", str(binary)])
    require("GNU_RELRO" in phdrs, f"{name} lacks GNU_RELRO")
    stack_match = re.search(r"^\s*GNU_STACK\s+.*?\s([RWE]+)\s+0x", phdrs, re.M)
    require(stack_match and "E" not in stack_match.group(1),
            f"{name} has executable or missing GNU_STACK:\n{phdrs}")

    dynamic = run(["readelf", "-dW", str(binary)])
    require("BIND_NOW" in dynamic or "(FLAGS_1)" in dynamic and "NOW" in dynamic,
            f"{name} lacks BIND_NOW:\n{dynamic}")
    require("(RPATH)" not in dynamic and "(RUNPATH)" not in dynamic,
            f"{name} embeds RPATH/RUNPATH:\n{dynamic}")

    sections = run(["readelf", "-SW", str(binary)])
    require("SYMTAB" not in sections and ".debug_info" not in sections,
            f"{name} was not stripped of symbol/debug sections")

    return re.findall(r"\(NEEDED\).*?\[([^\]]+)\]", dynamic)


def debug_lookup(binary, debug_root, work):
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
    if len(parameters) < 2 or parameters[0] != "int":
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
        "-iex", "set debug-file-directory " + str(debug_root),
        "-ex", "file " + str(binary), "-x", str(script),
    ], cwd=work, env=dict(os.environ, LC_ALL="C", DEBUGINFOD_URLS=""))
    prefix = "P4RT_INSTALLED_DEBUG="
    records = [json.loads(line[len(prefix):]) for line in output.splitlines()
               if line.startswith(prefix)]
    require(len(records) == 1, "no unique installed GDB result")
    return records[0]


def stage_runtime_lib_dir(lib_root):
    candidates = []
    for env_key in ("RUNFILES_DIR", "TEST_SRCDIR"):
        val = os.environ.get(env_key)
        if val and Path(val).is_dir():
            candidates.append(Path(val))
    if not candidates and Path.cwd().is_dir():
        candidates.append(Path.cwd())

    search_roots = []
    seen_roots = set()
    for root in candidates:
        resolved = str(root.resolve())
        if resolved not in seen_roots:
            seen_roots.add(resolved)
            search_roots.append(root)

    skip_prefixes = (
        "libc.so",
        "libm.so",
        "libdl.so",
        "libpthread.so",
        "librt.so",
        "ld-linux",
        "libasan.",
        "libtsan.",
        "liblsan.",
        "libubsan.",
        "libhwasan.",
    )
    lib_root.mkdir(parents=True, exist_ok=True)
    staged_names = set()
    for root in search_roots:
        for match in sorted(root.rglob("*.so*")):
            if any(part.startswith("rules_python") for part in match.parts):
                continue
            in_runtime_tree = any(
                part.startswith(("_solib_", "rules_distroless++apt+"))
                for part in match.parts
            ) or match.name.startswith(("libswsscommon.so", "libnl-"))
            if not in_runtime_tree:
                continue
            if match.name.startswith(skip_prefixes) or not match.is_file():
                continue
            target = match.resolve()
            if any(
                any(directory.glob(blocked))
                for directory in (match.parent, target.parent)
                for blocked in ("libc.so*", "ld-linux*")
            ):
                continue
            if match.name not in staged_names:
                staged_names.add(match.name)
                (lib_root / match.name).symlink_to(target)
    return lib_root


def defined_netlink_symbols(elf_path):
    symbols = []
    for line in run(["nm", "-D", "--defined-only", str(elf_path)]).splitlines():
        parts = line.split()
        if not parts:
            continue
        name = parts[-1].split("@", 1)[0]
        if name.startswith(("nl_", "nla_", "genl_", "rtnl_")):
            symbols.append(name)
    return symbols


def verify_metadata(metadata_path, runtime_tar):
    meta = json.loads(metadata_path.read_text())
    require(meta.get("schema") == 1, f"unexpected schema: {meta.get('schema')}")
    require(meta.get("module") == "sonic-pins", f"unexpected module: {meta.get('module')}")
    packages = meta.get("packages", {})
    require(set(packages) == {"sonic-p4rt"}, f"unexpected packages: {set(packages)}")
    entry = packages["sonic-p4rt"]
    require(entry.get("runtime_target") == "//p4rt_app:p4rt_runtime",
            f"unexpected runtime_target: {entry.get('runtime_target')}")
    require(entry.get("payload_sha256") == digest(runtime_tar),
            "runtime_packages.json payload_sha256 differs from p4rt_runtime TAR")
    controls = entry.get("control_fields", {})
    require(controls.get("Package") == "sonic-p4rt" and controls.get("Architecture") and controls.get("Version"),
            f"incomplete control_fields: {controls}")
    depends = {
        dep.strip().split()[0]
        for dep in controls.get("Depends", "").split(",")
        if dep.strip()
    }
    for required_pkg in ("libswsscommon", "libnl-3-200", "libnl-genl-3-200", "libhiredis1.1.0"):
        require(required_pkg in depends,
                f"runtime_packages.json missing {required_pkg} in Depends: {controls.get('Depends')}")
    return meta


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--runtime", required=True, type=Path)
    parser.add_argument("--debug", required=True, type=Path)
    parser.add_argument("--metadata", required=True, type=Path)
    args = parser.parse_args()

    meta = verify_metadata(args.metadata, args.runtime)
    source_root = Path(__file__).resolve().parents[1]
    results = {}
    with tempfile.TemporaryDirectory(prefix="p4rt-installed-") as temporary:
        work = Path(temporary)
        runtime_dir = work / "runtime"
        debug_root = work / "debug"
        empty_debug_root = work / "empty"
        lib_root = stage_runtime_lib_dir(work / "libs")
        for required_lib in ("libswsscommon.so.0", "libnl-3.so.200", "libnl-genl-3.so.200"):
            require((lib_root / required_lib).exists(),
                    f"{required_lib} missing from staged test runtime library dir: {lib_root}")
        runtime_dir.mkdir()
        debug_root.mkdir()
        empty_debug_root.mkdir()

        binaries = unpack_runtime(args.runtime, runtime_dir)
        debug_entries = unpack_debug_symbols(args.debug, debug_root)

        env = {k: v for k, v in os.environ.items() if k not in ("LD_PRELOAD", "LD_AUDIT")}
        env["LC_ALL"] = "C"
        existing_ld = env.get("LD_LIBRARY_PATH", "")
        env["LD_LIBRARY_PATH"] = os.pathsep.join(filter(None, [str(lib_root), existing_ld]))

        for name, (source, flag) in PROGRAMS.items():
            binary = binaries[name]
            needed = check_elf_hardening(binary, name)
            nl_symbols = defined_netlink_symbols(binary)
            require(not nl_symbols,
                    f"{name} exports embedded libnl symbols: {nl_symbols[:10]}")
            ident = build_id_of(binary)
            require(ident in debug_entries, f"missing .build-id debug file {ident} for {name}")
            debug_elf = debug_entries[ident]
            require(build_id_of(debug_elf) == ident, f"build ID mismatch in debug symbol for {name}")
            debug_sections = run(["readelf", "-SW", str(debug_elf)])
            require(".debug_info" in debug_sections, f"missing .debug_info in {debug_elf}")

            ldd_out = run(["ldd", str(binary)], env=env)
            require("not found" not in ldd_out, f"unresolved shared dependency in {name}:\n{ldd_out}")
            if name == "p4rt":
                for required_soname in ("libswsscommon.so.0", "libnl-3.so.200", "libnl-genl-3.so.200"):
                    require(required_soname in needed,
                            f"p4rt missing DT_NEEDED {required_soname}: {needed}")
                require(all("libgmpxx" not in n for n in needed), f"unexpected libgmpxx in p4rt: {needed}")
                run([str(binary), "--only_check_args"], env=env)

            help_result = subprocess.run([str(binary), "--helpshort"], env=env,
                                         text=True, capture_output=True, timeout=30)
            require(help_result.returncode in (0, 1) and flag in help_result.stdout + help_result.stderr,
                    f"CLI flag {flag} missing for {name}")

            without = debug_lookup(binary, empty_debug_root, work)
            require(not without["found"], f"unexpected embedded/fallback debug info for {name}: {without}")
            with_symbols = debug_lookup(binary, debug_root, work)
            require(with_symbols["found"], f"detached .build-id debug lookup failed for {name}: {with_symbols}")
            require(with_symbols["file"].replace("\\", "/").endswith(source),
                    f"debug lookup source mismatch for {name}: {with_symbols}")
            lines = (source_root / source).read_text().splitlines()
            definitions = [num for num, line in enumerate(lines, 1)
                           if re.match(r"\s*int\s+main\s*\(", line)]
            require(len(definitions) == 1 and definitions[0] <= with_symbols["line"] <= len(lines),
                    f"debug main line mismatch for {name}: {with_symbols}")

            results[name] = {
                "runtime_sha256": digest(binary),
                "debug_sha256": digest(debug_elf),
                "build_id": ident,
                "needed": needed,
                "without_symbols": without,
                "with_symbols": with_symbols,
            }

    output = os.environ.get("TEST_UNDECLARED_OUTPUTS_DIR")
    report = {
        "status": "passed",
        "module": meta["module"],
        "programs": results,
    }
    if output:
        (Path(output) / "installed-packages.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
