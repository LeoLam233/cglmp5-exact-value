#!/usr/bin/env python3
"""Destructive tests of independent source authentication (not Lean proof tests)."""
from pathlib import Path
import os
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]

class SourceReadbackTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='cglmp5-source-readback-')
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        paths = ['scripts/check_source_chunks.py', 'artifact_v0.1.1/SOS14.json',
                 'lean/CGLMP5/CertificateSource.lean', 'lean/CGLMP5/CertificateHeaderData.lean']
        paths += [f'lean/CGLMP5/CertificateChunkData{j:02}.lean' for j in range(14)]
        for relative in paths:
            destination = self.root / relative
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(ROOT / relative, destination)

    def run_reader(self, optimized=False, check_only=False):
        env = os.environ.copy()
        env.pop('PYTHONOPTIMIZE', None)
        command = [sys.executable] + (['-O'] if optimized else [])
        command += [str(self.root / 'scripts/check_source_chunks.py')]
        if check_only:
            command.append('--check-only')
        return subprocess.run(command, env=env, text=True, capture_output=True)

    def mutate(self, file, before, after):
        path = self.root / file
        text = path.read_text()
        self.assertIn(before, text)
        path.write_text(text.replace(before, after, 1))

    def assert_rejected(self):
        result = self.run_reader()
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn('AssertionError', result.stderr)
        self.assertFalse((self.root / 'lean/SOURCE_CHUNKS_READBACK.json').exists())

    def test_original(self):
        result = self.run_reader()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn('"status": "PASS"', result.stdout)

    def test_check_only_does_not_write(self):
        result = self.run_reader(check_only=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertFalse((self.root / 'lean/SOURCE_CHUNKS_READBACK.json').exists())

    def test_optimized_python_rejected(self):
        result = self.run_reader(optimized=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('Refusing optimized Python', result.stderr)

    def test_header_gamma(self):
        file = 'lean/CGLMP5/CertificateHeaderData.lean'
        text = (self.root / file).read_text()
        import re
        start = text.index('def sourceHeaderGamma')
        match = re.search(r'"[0-9]+"', text[start:])
        pos = start + match.start()
        replacement = '"' + str(int(match.group()[1:-1]) + 1) + '"'
        path = self.root / file
        path.write_text(text[:pos] + replacement + text[pos+len(match.group()):])
        self.assert_rejected()

    def test_canonical_bytes(self):
        path = self.root / 'artifact_v0.1.1/SOS14.json'
        path.write_bytes(path.read_bytes() + b'\n')
        self.assert_rejected()

    def test_header_alias(self):
        self.mutate('lean/CGLMP5/CertificateSource.lean',
                    'def canonicalPrefix : String := canonicalHeaderPrefix',
                    'def canonicalPrefix : String := "unbound"')
        self.assert_rejected()

    def test_term_label(self):
        file = 'lean/CGLMP5/CertificateChunkData00.lean'
        text = (self.root / file).read_text()
        import re
        label = re.search(r'def chunkTerm00 : ChunkTerm := ⟨("[^"]*")', text).group(1)
        self.mutate(file, 'def chunkTerm00 : ChunkTerm := ⟨' + label,
                    'def chunkTerm00 : ChunkTerm := ⟨"wrong-source-label"')
        self.assert_rejected()

if __name__ == '__main__':
    unittest.main()
