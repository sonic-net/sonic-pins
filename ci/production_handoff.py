"""Verify the exact SDK and built owner outputs between separate CI phases."""

import hashlib
import json
from pathlib import Path
import re
import stat
import subprocess

from runtime_contract import PROFILES, require


def digest(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def sdk_inventory(directory):
    directory = Path(directory).resolve()
    result = {}
    for path in sorted(directory.rglob('*')):
        relative = path.relative_to(directory).as_posix()
        mode = stat.S_IMODE(path.lstat().st_mode)
        if path.is_symlink():
            require(path.resolve().is_relative_to(directory), 'SDK link escapes its repository: ' + relative)
            result[relative] = {'kind': 'symlink', 'target': path.readlink().as_posix(), 'mode': mode}
        elif path.is_file():
            result[relative] = {'kind': 'file', 'sha256': digest(path), 'mode': mode}
        else:
            require(path.is_dir(), 'Unsupported SDK input: ' + relative)
    require({'sdk-build.json', 'WORKSPACE.bazel', 'BUILD.bazel', 'lib/libswsscommon.so.0'} <= result.keys(),
            'Incomplete prepared Common SDK')
    require(any(name.startswith('include/swss/') for name in result), 'Missing SDK headers')
    return result


def verify_build(directory, sdk, revision):
    directory, sdk = Path(directory), Path(sdk)
    receipt = json.loads((directory / 'source.json').read_text())
    require(receipt.get('commit') == revision and receipt.get('bazel') == '6.4.0' and
            receipt.get('architecture') == 'amd64', 'Built source identity differs')
    require(receipt.get('sdk_inventory') == sdk_inventory(sdk), 'SDK inputs changed after build')
    for field, suffix in (('tar_sha256', '.tar'), ('contract_sha256', '_contract.json')):
        expected = {name + suffix for name in PROFILES}
        require(set(receipt.get(field, {})) == expected, 'Incomplete owner output inventory')
        for name, checksum in receipt[field].items():
            path = directory / name
            require(path.is_file() and not path.is_symlink() and digest(path) == checksum,
                    'Built owner output changed: ' + name)
    for target, package in PROFILES.items():
        contract = json.loads((directory / (target + '_contract.json')).read_text())
        require(contract.get('schema') == 1 and contract.get('owner') == 'sonic-pins' and
                contract.get('source') == {'kind': 'workspace',
                    'name': 'com_github_sonic_net_sonic_pins', 'revision': revision} and
                set(contract.get('packages', {})) == {package}, 'Owner contract identity differs')
        entry = contract['packages'][package]
        require(entry.get('target') == '//p4rt_app:' + target and
                entry.get('source_revision') == revision and
                entry.get('payload_sha256') == receipt['tar_sha256'][target + '.tar'],
                'Owner contract does not match its built TAR')
    return receipt


def runtime_environment(path, sdk):
    """Accept a prepared private runtime; never install or infer host libraries."""
    path, sdk = Path(path), Path(sdk)
    receipt = json.loads(path.read_text())
    require(receipt.get('schema') == 1 and receipt.get('architecture') == 'amd64' and
            receipt.get('sdk_inventory') == sdk_inventory(sdk), 'Prepared runtime uses a different SDK')
    directories, libraries = receipt.get('library_path', []), receipt.get('libraries', {})
    require(directories and len(directories) == len(set(directories)) and libraries,
            'Missing prepared runtime libraries')
    require(all(isinstance(name, str) and Path(name).is_absolute() and Path(name).is_dir()
                and ':' not in name and '\n' not in name for name in directories),
            'Invalid prepared runtime search path')
    for name, checksum in libraries.items():
        library = Path(name)
        require(library.is_absolute() and library.is_file() and digest(library) == checksum,
                'Prepared runtime library changed: ' + name)
    for key in ('loader', 'common_runner', 'patchelf', 'runtime_archive'):
        item = receipt.get(key, {})
        require(isinstance(item.get('path'), str) and Path(item['path']).is_absolute() and
                Path(item['path']).is_file() and digest(item['path']) == item.get('sha256'),
                'Declared runtime input changed: ' + key)
    require(receipt['loader']['path'] in libraries and
            receipt['loader']['sha256'] == libraries[receipt['loader']['path']],
            'Runtime interpreter is not a declared selected library')
    import os
    process_env = {key: value for key, value in os.environ.items()
                   if key not in ('LD_LIBRARY_PATH', 'LD_PRELOAD', 'LD_AUDIT')}
    process_env['LC_ALL'] = 'C'
    loaded = subprocess.check_output([receipt['loader']['path'], '--library-path', ':'.join(directories),
                                     '--list', str(sdk / 'lib/libswsscommon.so.0')],
                                     env=process_env, text=True, timeout=30)
    require('not found' not in loaded, 'Common SDK has an unresolved runtime dependency')
    resolved = {match.group(1): digest(match.group(2)) for match in
                re.finditer(r'^\s*(\S+) => (/\S+) \(', loaded, re.MULTILINE)}
    require(resolved and resolved == receipt.get('common_ldd'),
            'Common SDK runtime resolution differs from preparation')
    # Only test children consume the receipt. The Bazel/JVM/compiler and native
    # Python/GDB environment must never inherit the staged libc search path.
    return {'SONIC_P4RT_TEST_RUNTIME': str(path)}, {
        'receipt_sha256': digest(path), 'common_ldd': resolved,
        'library_path': directories, 'libraries': libraries,
        **{key: receipt[key] for key in ('loader', 'common_runner', 'patchelf', 'runtime_archive')}}


def verify_installed(report, built, sdk):
    require(report.get('status') == 'passed' and report.get('architecture') == 'amd64' and
            report.get('runtime_tar_sha256') == built['tar_sha256']['p4rt_runtime.tar'] and
            report.get('debug_tar_sha256') == built['tar_sha256']['p4rt_runtime_debug.tar'] and
            report.get('common_library_sha256') == digest(Path(sdk) / 'lib/libswsscommon.so.0'),
            'Installed test did not validate the exact built TARs and SDK')


def verify_runtime_unchanged(path, sdk, expected):
    _, actual = runtime_environment(path, sdk)
    require(actual == expected, 'Prepared runtime identity changed during tests')
    return actual
