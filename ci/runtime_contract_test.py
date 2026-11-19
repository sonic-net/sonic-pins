"""Check provenance sealing without compiling or producing Debian packages."""

import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

from runtime_contract import PROFILES, seal_contracts


class ContractTest(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        root = Path(self.temporary.name)
        self.source, self.output = root / "source", root / "output"
        self.source.mkdir(); self.output.mkdir()
        subprocess.run(["git", "init", "-q", str(self.source)], check=True)
        (self.source / "tracked").write_text("source fixture\n")
        subprocess.run(["git", "add", "tracked"], cwd=self.source, check=True)
        subprocess.run(["git", "-c", "user.name=Guohan Lu", "-c", "user.email=securely1g@gmail.com",
                        "commit", "-qm", "Create provenance fixture"], cwd=self.source, check=True)
        self.revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=self.source, text=True).strip()
        for target, package in PROFILES.items():
            suffix = ".dwp" if target.endswith("debug") else ""
            template = {"schema": 1, "owner": "sonic-pins", "packages": {package: {
                "control_fields": {"Package": package, "Version": "0.0.1", "Architecture": "amd64"},
                "target": "//p4rt_app:" + target,
                "required_paths": ["usr/local/bin/" + name + suffix for name in
                                   ("p4rt", "p4rt_read", "p4rt_write", "p4rt_program_table", "p4rt_set_forwarding_pipeline")],
            }}}
            (self.output / (target + "_contract_template.json")).write_text(json.dumps(template))
            (self.output / (target + ".tar")).write_bytes(("payload identity fixture " + target).encode())

    def test_sealed_contract_binds_commit_and_actual_bytes(self):
        outputs = seal_contracts(self.output, self.source, self.revision)
        for target, path in outputs.items():
            document = json.loads(path.read_text())
            entry = document["packages"][PROFILES[target]]
            self.assertEqual(entry["source_revision"], self.revision)
            self.assertEqual(entry["payload_sha256"], hashlib.sha256((self.output / (target + ".tar")).read_bytes()).hexdigest())
            self.assertEqual(document["source"]["kind"], "workspace")
            self.assertNotIn("module", document)

    def test_stale_revision_and_dirty_checkout_are_rejected(self):
        with self.assertRaisesRegex(ValueError, "checkout changed"):
            seal_contracts(self.output, self.source, "0" * 40)
        (self.source / "tracked").write_text("changed after build\n")
        with self.assertRaisesRegex(ValueError, "clean source checkout"):
            seal_contracts(self.output, self.source, self.revision)

    def test_contract_cannot_name_a_different_producer(self):
        path = self.output / "p4rt_runtime_contract_template.json"
        document = json.loads(path.read_text())
        document["packages"]["sonic-p4rt"]["target"] = "//p4rt_app:p4rt_binaries"
        path.write_text(json.dumps(document))
        with self.assertRaisesRegex(ValueError, "different producer"):
            seal_contracts(self.output, self.source, self.revision)


if __name__ == "__main__":
    unittest.main()
