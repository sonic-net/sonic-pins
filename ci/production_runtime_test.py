"""Regression checks for per-invocation audit scratch space."""

from pathlib import Path
import tempfile
import unittest

from production_runtime import private_directory


class PrivateDirectoryTest(unittest.TestCase):
    def test_invocations_sharing_an_output_parent_keep_separate_files(self):
        with tempfile.TemporaryDirectory() as temporary:
            parent = Path(temporary).resolve()
            first = private_directory(parent / "out-a")
            second = private_directory(parent / "out-b")
            again = private_directory(parent / "out-a")
            self.assertEqual(len({first, second, again}), 3)
            self.assertEqual({first.parent, second.parent, again.parent}, {parent})
            (first / "actions.json").write_text("first graph")
            (first / "test-events.json").write_text("first events")
            (second / "actions.json").write_text("second graph")
            (second / "actions.json").unlink()
            self.assertEqual((first / "actions.json").read_text(), "first graph")
            self.assertEqual((first / "test-events.json").read_text(), "first events")
            self.assertFalse((second / "test-events.json").exists())
            self.assertFalse(any(again.iterdir()))

    def test_creates_a_missing_output_parent(self):
        with tempfile.TemporaryDirectory() as temporary:
            parent = Path(temporary) / "nested" / "work"
            directory = private_directory(parent / "out")
            self.assertTrue(directory.is_dir())
            self.assertEqual(directory.parent, parent.resolve())


if __name__ == "__main__":
    unittest.main()
