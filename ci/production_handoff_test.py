"""Negative controls for keeping owner build and test phases independent."""

import json
from pathlib import Path
import unittest
from unittest.mock import patch

from production_handoff import digest, sdk_inventory, verify_build, runtime_environment, verify_installed, verify_runtime_unchanged
from runtime_contract import seal_contracts
import runtime_contract_test as fixtures


class HandoffTest(unittest.TestCase):
    def setUp(self):
        fixtures.ContractTest.setUp(self)
        self.sdk = Path(self.temporary.name) / 'sdk'
        for name, content in {'WORKSPACE.bazel': 'workspace()', 'BUILD.bazel': 'exports_files([])',
                              'sdk-build.json': '{}', 'include/swss/dbconnector.h': 'header',
                              'lib/libswsscommon.so.0': 'library'}.items():
            path = self.sdk / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(content)
        contracts = seal_contracts(self.output, self.source, self.revision)
        self.receipt = {'commit': self.revision, 'bazel': '6.4.0', 'architecture': 'amd64',
                        'sdk_inventory': sdk_inventory(self.sdk),
                        'tar_sha256': {name + '.tar': digest(self.output / (name + '.tar')) for name in contracts},
                        'contract_sha256': {path.name: digest(path) for path in contracts.values()}}
        (self.output / 'source.json').write_text(json.dumps(self.receipt))

    def test_prior_output_is_accepted_without_rebuilding(self):
        self.assertEqual(verify_build(self.output, self.sdk, self.revision), self.receipt)

    def test_rejects_stale_source_changed_header_or_changed_library(self):
        with self.assertRaisesRegex(ValueError, 'source identity'):
            verify_build(self.output, self.sdk, '0' * 40)
        for name in ('include/swss/dbconnector.h', 'lib/libswsscommon.so.0'):
            path = self.sdk / name
            original = path.read_bytes()
            path.write_bytes(original + b' changed')
            with self.assertRaisesRegex(ValueError, 'SDK inputs changed'):
                verify_build(self.output, self.sdk, self.revision)
            path.write_bytes(original)

    def test_rejects_changed_tar_or_contract_without_resealing(self):
        for name in ('p4rt_runtime.tar', 'p4rt_runtime_debug_contract.json'):
            path = self.output / name
            original = path.read_bytes()
            path.write_bytes(original + b' changed')
            with self.assertRaisesRegex(ValueError, 'owner output changed'):
                verify_build(self.output, self.sdk, self.revision)
            path.write_bytes(original)

    def test_rejects_sdk_symlink_escape(self):
        (self.sdk / 'include/escape.h').symlink_to('/etc/passwd')
        with self.assertRaisesRegex(ValueError, 'SDK link escapes'):
            sdk_inventory(self.sdk)

    def test_rejects_installed_receipt_for_another_tar(self):
        report = {'status': 'passed', 'architecture': 'amd64',
                  'runtime_tar_sha256': self.receipt['tar_sha256']['p4rt_runtime.tar'],
                  'debug_tar_sha256': self.receipt['tar_sha256']['p4rt_runtime_debug.tar'],
                  'common_library_sha256': digest(self.sdk / 'lib/libswsscommon.so.0')}
        verify_installed(report, self.receipt, self.sdk)
        report['runtime_tar_sha256'] = '0' * 64
        with self.assertRaisesRegex(ValueError, 'exact built TARs'):
            verify_installed(report, self.receipt, self.sdk)

    def test_prepared_runtime_rechecks_bytes_and_actual_resolution(self):
        library = self.sdk / 'lib/libswsscommon.so.0'
        path = self.output / 'runtime.json'
        receipt = {'schema': 1, 'architecture': 'amd64', 'sdk_inventory': sdk_inventory(self.sdk),
                   'library_path': [str(library.parent)], 'libraries': {str(library): digest(library)},
                   'common_ldd': {'libfixture.so': digest(library)},
                   **{key: {'path': str(library), 'sha256': digest(library)}
                      for key in ('loader', 'common_runner', 'patchelf', 'runtime_archive')}}
        path.write_text(json.dumps(receipt))
        with patch('production_handoff.subprocess.check_output',
                   return_value='libfixture.so => ' + str(library) + ' (0x123)\n'):
            environment, _ = runtime_environment(path, self.sdk)
            self.assertEqual(environment, {'SONIC_P4RT_TEST_RUNTIME': str(path)})
            receipt['common_ldd']['libfixture.so'] = '0' * 64
            path.write_text(json.dumps(receipt))
            with self.assertRaisesRegex(ValueError, 'runtime resolution differs'):
                runtime_environment(path, self.sdk)

    def test_rejects_runtime_receipt_replaced_during_tests(self):
        before = {'receipt_sha256': 'a' * 64, 'common_ldd': {'fixture': 'b' * 64}}
        after = dict(before, receipt_sha256='c' * 64)
        with patch('production_handoff.runtime_environment', return_value=({}, after)):
            with self.assertRaisesRegex(ValueError, 'identity changed during tests'):
                verify_runtime_unchanged('unused.json', self.sdk, before)


if __name__ == '__main__':
    unittest.main()
