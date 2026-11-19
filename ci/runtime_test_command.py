#!/usr/bin/env python3
"""Run the golden test's original ELF with its explicitly prepared runtime."""

import json
import os
from pathlib import Path
import sys

from production_handoff import digest
from runtime_contract import require
from runtime_run_under import invocation


def command_invocation(command, environment):
    require(command, 'Missing original golden-test command')
    receipt_path = environment.get('SONIC_P4RT_TEST_RUNTIME')
    if not receipt_path:
        return command, environment
    expected = environment.get('SONIC_P4RT_TEST_RUNTIME_SHA256')
    sdk = environment.get('SONIC_P4RT_TEST_SDK')
    require(expected and sdk and digest(receipt_path) == expected,
            'Prepared golden-test runtime identity changed')
    receipt = json.loads(Path(receipt_path).read_text())
    with Path(command[0]).open('rb') as stream:
        require(stream.read(4) == b'\x7fELF', 'Golden-test child must be the original ELF')
    return invocation(command, sdk, receipt, environment)


if __name__ == '__main__':
    command, environment = command_invocation(sys.argv[1:], os.environ)
    os.execvpe(command[0], command, environment)
