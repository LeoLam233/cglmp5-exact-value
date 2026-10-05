#!/usr/bin/env python3
"""Byte-manifest positive and destructive controls in isolated tiny Git fixtures."""
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]

class ManifestTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='cglmp5-manifest-')
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        (self.root / 'scripts').mkdir()
        shutil.copy2(ROOT / 'scripts/check_source_manifest.py', self.root / 'scripts/check_source_manifest.py')
        (self.root / 'source.txt').write_text('original\n')
        (self.root / '.gitignore').write_text('build/\n')
        subprocess.run(['git', 'init', '-q', str(self.root)], check=True)
        subprocess.run(['git', 'add', '.'], cwd=self.root, check=True)
        self.assertEqual(self.run_manifest('--write').returncode, 0)

    def run_manifest(self, *args):
        return subprocess.run([sys.executable, str(self.root / 'scripts/check_source_manifest.py'), *args],
                              text=True, capture_output=True)

    def test_original(self):
        result = self.run_manifest()
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_changed_byte(self):
        (self.root / 'source.txt').write_text('changed\n')
        self.assertNotEqual(self.run_manifest().returncode, 0)

    def test_missing_file(self):
        (self.root / 'source.txt').unlink()
        self.assertNotEqual(self.run_manifest().returncode, 0)

    def test_extra_candidate_file(self):
        (self.root / 'new-source.txt').write_text('extra\n')
        self.assertNotEqual(self.run_manifest().returncode, 0)

    def test_ignored_build_product(self):
        (self.root / 'build').mkdir()
        (self.root / 'build/compiled.bin').write_bytes(b'generated')
        result = self.run_manifest()
        self.assertEqual(result.returncode, 0, result.stderr)

if __name__ == '__main__':
    unittest.main()
