"""Preserve original test arguments while reusing the selected Common runner."""

import importlib.util
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from production_handoff import digest
from runtime_run_under import invocation
from runtime_test_command import command_invocation


class RunnerTest(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.tool = self.root / 'tool'
        self.tool.write_text('declared tool fixture')
        self.receipt = {key: {'path': str(self.tool), 'sha256': digest(self.tool)}
                        for key in ('common_runner', 'patchelf', 'runtime_archive', 'loader')}
        self.receipt['library_path'] = [str(self.root / 'lib')]
        self.environment = {'TEST_TMPDIR': '/private/test', 'TEST_SRCDIR': '/declared/runfiles',
                            'XML_OUTPUT_FILE': '/private/result.xml', 'LD_PRELOAD': 'ambient.so',
                            'LD_LIBRARY_PATH': '/ambient', 'LD_AUDIT': 'ambient-audit.so'}

    def test_native_test_delegates_to_exact_common_runner(self):
        binary = self.root / 'original_test'
        binary.write_bytes(b'\x7fELFnative fixture')
        original = [str(binary), '--gtest_filter=Original.*']
        command, environment = invocation(original, self.root / 'sdk', self.receipt, self.environment)
        self.assertEqual(command[-2:], original)
        self.assertEqual(command[2:5], [str(self.tool)] * 3)
        self.assertIn('enabled', command)
        self.assertEqual(environment, {key: value for key, value in self.environment.items() if not key.startswith('LD_')})
        self.tool.write_text('changed after preparation')
        with self.assertRaisesRegex(ValueError, 'test tool changed'):
            invocation(original, self.root / 'sdk', self.receipt, self.environment)

    def test_python_verifier_keeps_native_environment_and_original_arguments(self):
        binary = self.root / 'runtime_package_test'
        binary.write_text('#!/usr/bin/python3\n')
        original = [str(binary), '--runtime', 'unchanged.tar']
        command, environment = invocation(original, self.root / 'sdk', self.receipt, self.environment)
        self.assertEqual(command, original)
        self.assertFalse(any(key.startswith('LD_') for key in environment))
        self.assertEqual(environment['P4RT_TEST_RUNTIME_LOADER'], str(self.tool))
        self.assertEqual(environment['XML_OUTPUT_FILE'], '/private/result.xml')
        other = self.root / 'unrecognized_script'
        other.write_text('#!/bin/sh\n')
        with self.assertRaisesRegex(ValueError, 'Only the original'):
            invocation([str(other)], self.root / 'sdk', self.receipt, self.environment)

    def test_installed_cli_uses_declared_loader_without_changing_binary(self):
        path = Path(__file__).resolve().parents[1] / 'p4rt_app/runtime_package_test.py'
        spec = importlib.util.spec_from_file_location('installed_p4rt_test', path)
        installed = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(installed)
        binary, common = self.root / 'production', self.root / 'sdk/lib/common.so'
        with patch.dict(os.environ, {}, clear=True):
            self.assertEqual(installed.installed_command(binary, ['--helpshort'], common), [str(binary), '--helpshort'])
        with patch.dict(os.environ, {'P4RT_TEST_RUNTIME_LOADER': str(self.tool),
                                     'P4RT_TEST_LIBRARY_PATH': '/declared/lib'}, clear=True):
            self.assertEqual(installed.installed_command(binary, [], common, listing=True),
                             [str(self.tool), '--library-path', str(common.parent) + ':/declared/lib', '--list', str(binary)])

    def test_golden_pipeline_keeps_native_shell_and_wraps_only_elf_child(self):
        script = self.root / 'p4_constraints_test'
        script.write_text('echo original | sed original\ndiff expected actual\n')
        receipt_path = self.root / 'receipt.json'
        receipt_path.write_text(json.dumps(self.receipt))
        receipt = dict(self.receipt, _path=receipt_path, _sha256=digest(receipt_path))
        original = [str(script), '--original-argument']
        command, environment = invocation(original, self.root / 'sdk', receipt, self.environment)
        self.assertEqual(command, ['/bin/bash', *original])
        self.assertEqual(script.read_text(), 'echo original | sed original\ndiff expected actual\n')
        self.assertFalse(any(key.startswith('LD_') for key in environment))
        child = self.root / 'p4_constraints_test_runner'
        child.write_bytes(b'\x7fELForiginal test fixture')
        child_command = [str(child), '--unchanged']
        wrapped, _ = command_invocation(child_command, environment)
        self.assertEqual(wrapped[-2:], child_command)
        self.assertEqual(command_invocation(child_command, {}), (child_command, {}))
        receipt_path.write_text('{}')
        with self.assertRaisesRegex(ValueError, 'runtime identity changed'):
            command_invocation(child_command, environment)


if __name__ == '__main__':
    unittest.main()
