#!/usr/bin/env python3
"""Reuse Common's declared ELF runner while keeping the Python verifier native."""

import argparse
import json
import os
from pathlib import Path
import sys

from production_handoff import digest
from runtime_contract import require


def invocation(command, sdk, receipt, environment):
    require(command, 'Missing original P4RT test command')
    clean = {name: value for name, value in environment.items()
             if name not in ('LD_LIBRARY_PATH', 'LD_PRELOAD', 'LD_AUDIT',
                             'P4RT_TEST_RUNTIME_LOADER', 'P4RT_TEST_LIBRARY_PATH')}
    with Path(command[0]).open('rb') as stream:
        native = stream.read(4) == b'\x7fELF'
    if native:
        runner, patchelf = receipt['common_runner'], receipt['patchelf']
        for item in (runner, patchelf):
            require(digest(item['path']) == item['sha256'], 'Declared Common test tool changed')
        return [sys.executable, '-B', runner['path'], patchelf['path'],
                receipt['runtime_archive']['path'], str(Path(sdk) / 'lib/libswsscommon.so.0'),
                'enabled', *command], clean
    if Path(command[0]).name == 'p4_constraints_test':
        # Upstream cmd_diff_test generates a Bash script without a shebang.
        # Keep its original pipeline and diff native; its declared child prefix
        # applies Common's ELF runner only to p4_constraints_test_runner.
        clean.update(SONIC_P4RT_TEST_SDK=str(sdk),
                     SONIC_P4RT_TEST_RUNTIME=str(receipt['_path']),
                     SONIC_P4RT_TEST_RUNTIME_SHA256=receipt['_sha256'])
        return ['/bin/bash', *command], clean
    require(Path(command[0]).name == 'runtime_package_test',
            'Only the original installed-package Python test may use the native interpreter')
    clean.update(P4RT_TEST_RUNTIME_LOADER=receipt['loader']['path'],
                 P4RT_TEST_LIBRARY_PATH=':'.join(receipt['library_path']))
    return command, clean


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--sdk', required=True, type=Path)
    parser.add_argument('--receipt', required=True, type=Path)
    parser.add_argument('--receipt-sha256', required=True)
    parser.add_argument('command', nargs=argparse.REMAINDER)
    args = parser.parse_args()
    require(digest(args.receipt) == args.receipt_sha256, 'Prepared runtime receipt changed during tests')
    receipt = json.loads(args.receipt.read_text())
    receipt.update(_path=str(args.receipt), _sha256=args.receipt_sha256)
    command = args.command[1:] if args.command[:1] == ['--'] else args.command
    command, environment = invocation(command, args.sdk, receipt, os.environ)
    # Preserve Bazel's runfiles, temporary directories, XML path and all original
    # test arguments. Common owns private ELF copies and their interpreter fix.
    os.execvpe(command[0], command, environment)


if __name__ == '__main__':
    sys.exit(main())
