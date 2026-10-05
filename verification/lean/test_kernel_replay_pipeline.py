#!/usr/bin/env python3
"""Lightweight receipt/command tests. Never invokes Lean or leanchecker."""
import sys
sys.dont_write_bytecode = True
from pathlib import Path
import importlib.util, json, subprocess, tempfile, unittest
ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'scripts'))
spec = importlib.util.spec_from_file_location('kernel_pipeline', ROOT / 'scripts/recheck_lean_kernel.py')
pipeline = importlib.util.module_from_spec(spec)
spec.loader.exec_module(pipeline)

class KernelPipelineTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='cglmp-kernel-pipeline-')
        self.addCleanup(self.temp.cleanup)
        self.base = Path(self.temp.name)
        self.root = self.base / 'repo'
        self.runtime = self.base / 'runtime'
        self.objects = self.root / 'lean/.lake/build/lib/lean'
        self.objects.mkdir(parents=True)
        (self.runtime / 'lib/lean').mkdir(parents=True)
        (self.runtime / 'lib/lean/Init.olean').write_bytes(b'fixture runtime object, not a Lean proof')
        (self.objects / 'CGLMP5.olean').write_bytes(b'fixture project object, not a Lean proof')
        (self.root / 'lean/lake-manifest.json').write_text(json.dumps({'packages': [{'name': 'unused'}]}))
        old = pipeline.ROOT
        pipeline.ROOT = self.root
        self.addCleanup(setattr, pipeline, 'ROOT', old)
    def test_exact_fresh_root_command(self):
        self.assertEqual(pipeline.replay_command(self.runtime),
                         [str(self.runtime / 'bin/lake'), 'env', 'leanchecker', '--fresh', 'CGLMP5'])
    def test_unused_dependency_directory_recorded(self):
        snap = pipeline.object_snapshot(self.runtime)
        self.assertIsNone(snap['dependency:unused/@OBJECT_DIRECTORY_MISSING'])
        self.assertIn('project/CGLMP5.olean', snap)
    def test_private_object_part_changes_detected(self):
        private = self.objects / 'CGLMP5.olean.private'
        private.write_bytes(b'first')
        first = pipeline.object_snapshot(self.runtime)
        private.write_bytes(b'second')
        self.assertNotEqual(first, pipeline.object_snapshot(self.runtime))
    def test_missing_final_object_rejected(self):
        (self.objects / 'CGLMP5.olean').unlink()
        with self.assertRaisesRegex(RuntimeError, 'umbrella object is missing'):
            pipeline.object_snapshot(self.runtime)
    def test_optimized_replay_rejected(self):
        result = subprocess.run([sys.executable, '-O', '-B', str(ROOT / 'scripts/recheck_lean_kernel.py'), '--help'], text=True, capture_output=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('Optimized Python execution is forbidden', result.stderr)

if __name__ == '__main__':
    unittest.main()
