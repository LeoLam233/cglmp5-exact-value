#!/usr/bin/env python3
"""Isolated path-containment tests; never clean or mutate a real build cache."""
import sys
sys.dont_write_bytecode = True
from pathlib import Path
import shutil, subprocess, tempfile, unittest
from lean_replay_paths import validate_checkout_paths

class Paths(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='cglmp-path-test-')
        self.addCleanup(self.temp.cleanup)
        self.base = Path(self.temp.name)
        self.root = self.base / 'repo'
        (self.root / 'lean/CGLMP5').mkdir(parents=True)
        (self.root / 'lean/CGLMP5.lean').write_text('import CGLMP5.A\n')
        (self.root / 'lean/CGLMP5/A.lean').write_text('namespace CGLMP5\nend CGLMP5\n')
        self.outside = self.base / 'external'
        self.outside.mkdir()
        (self.outside / 'KEEP').write_text('must remain unchanged')
    def rejects(self):
        with self.assertRaises(RuntimeError):
            validate_checkout_paths(self.root)
        self.assertEqual((self.outside / 'KEEP').read_text(), 'must remain unchanged')
    def test_normal_sources_and_ignored_cache(self):
        (self.root / 'lean/.lake/build').mkdir(parents=True)
        (self.root / 'lean/.lake/build/output').write_text('generated')
        self.assertEqual(validate_checkout_paths(self.root)['production_lean_files'], 2)
    def test_external_lake_ancestor_rejected(self):
        (self.root / 'lean/.lake').symlink_to(self.outside, target_is_directory=True)
        self.rejects()
    def test_build_cli_rejects_ancestor_before_cleanup(self):
        scripts = self.root / 'scripts'
        scripts.mkdir()
        original = Path(__file__).resolve().parent
        for name in ('build_lean_clean.py', 'lean_replay_paths.py'):
            shutil.copy2(original / name, scripts / name)
        (self.root / 'lean/.lake').symlink_to(self.outside, target_is_directory=True)
        result = subprocess.run([sys.executable, '-B', str(scripts / 'build_lean_clean.py'),
                                 '--receipt-dir', str(self.base / 'receipts'), '--clean-project'],
                                text=True, capture_output=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('symlinked source/cache directory', result.stderr)
        self.assertEqual((self.outside / 'KEEP').read_text(), 'must remain unchanged')
    def test_linked_build_leaf_rejected(self):
        (self.root / 'lean/.lake').mkdir()
        (self.root / 'lean/.lake/build').symlink_to(self.outside, target_is_directory=True)
        self.rejects()
    def test_linked_proof_file_rejected(self):
        path = self.root / 'lean/CGLMP5/A.lean'
        path.unlink()
        path.symlink_to(self.outside / 'KEEP')
        self.rejects()
    def test_linked_proof_directory_rejected(self):
        (self.root / 'lean/CGLMP5/Hidden').symlink_to(self.outside, target_is_directory=True)
        self.rejects()
    def test_linked_dependency_root_rejected(self):
        (self.root / 'lean/.lake/packages').mkdir(parents=True)
        (self.root / 'lean/.lake/packages/mathlib').symlink_to(self.outside, target_is_directory=True)
        self.rejects()

if __name__ == '__main__':
    unittest.main()
