#!/usr/bin/env python3
"""Fast offline CI pin/readiness guard tests; no proof or full replay claim."""
import sys
sys.dont_write_bytecode = True
import copy, importlib.util, json, tempfile, unittest
from pathlib import Path
ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'scripts'))

def load(name, file):
    spec = importlib.util.spec_from_file_location(name, file)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

setup = load('setup_ci', ROOT / 'scripts/setup_lean_ci.py')
ready = load('readiness', ROOT / 'scripts/check_lean_completion_readiness.py')

class Guards(unittest.TestCase):
    def test_pins_match_current_sources(self):
        pins = json.loads((ROOT / 'verification/lean/ci/pins.json').read_text())
        data = setup.validate_pins(ROOT, pins)
        self.assertEqual(len(data['packages']), 9)
        self.assertGreater(len(setup.direct_mathlib_imports(ROOT)), 0)
    def test_changed_manifest_pin_rejected(self):
        pins = json.loads((ROOT / 'verification/lean/ci/pins.json').read_text())
        pins['lake_manifest_sha256'] = '0' * 64
        with self.assertRaisesRegex(RuntimeError, 'manifest'):
            setup.validate_pins(ROOT, pins)
    def test_missing_sos_hook_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            for name in ('verification/lean/inspect_dependencies.py', 'verification/lean/declaration_inventory.json', 'verification/lean/ci/completion_hooks.json'):
                target = root / name
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes((ROOT / name).read_bytes())
            hook = root / 'verification/lean/ci/completion_hooks.json'
            hook.write_text(json.dumps({'actual_sos_coefficient_corruption': {'status': 'ready', 'runner': 'scripts/run_lean_sos_corruption.py'}}))
            result = ready.check(root)
            self.assertEqual(result['status'], 'BLOCKED')
            self.assertIn('Required actual SOS coefficient corruption hook is pending or missing', result['errors'])
    def test_optimized_python_rejected(self):
        import subprocess
        for name in ('run_lean_verification.py', 'setup_lean_ci.py'):
            result = subprocess.run([sys.executable, '-O', str(ROOT / 'scripts' / name), '--help'], text=True, capture_output=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('Optimized Python execution is forbidden', result.stderr)
    def test_mapped_inventory_is_mandatory_before_build(self):
        import ast
        source = (ROOT / 'scripts/run_lean_verification.py').read_text()
        tree = ast.parse(source)
        lists = [n.value for n in ast.walk(tree) if isinstance(n, ast.Assign)
                 and any(isinstance(t, ast.Name) and t.id == 'stages' for t in n.targets)]
        self.assertEqual(len(lists), 1)
        stages = [item.elts[0].value for item in lists[0].elts]
        workflow = (ROOT / '.github/workflows/lean-verification.yml').read_text()
        for name in ('mapped_inventory', 'mapped_inventory_guard_tests',
                     'mapped_inventory_optimized_guard_tests'):
            self.assertEqual(stages.count(name), 1)
            self.assertLess(stages.index(name), stages.index('clean_build'))
        for script in ('check_mapped_inventory.py', 'test_mapped_inventory.py'):
            self.assertIn(script, source)
            self.assertIn(script, workflow)
        for name in ('axiom_report_guard_tests', 'axiom_report_optimized_guard_tests'):
            self.assertEqual(stages.count(name), 1)
            self.assertLess(stages.index(name), stages.index('clean_build'))
        self.assertEqual(stages.count('axiom_report_comparison'), 1)
        self.assertEqual(stages.index('axiom_report_comparison'), stages.index('types_axioms') + 1)
        self.assertIn('check_axiom_report.py', source)
        self.assertIn('test_axiom_report.py', source)
        self.assertIn('test_axiom_report.py', workflow)
    def test_actions_are_pinned_read_only(self):
        text = (ROOT / '.github/workflows/lean-verification.yml').read_text()
        self.assertIn('contents: read', text)
        self.assertIn('persist-credentials: false', text)
        self.assertNotIn('pull_request_target', text)
        import re
        for action in re.findall(r'(?:uses: )([^\s]+)', text):
            self.assertRegex(action, r'^[A-Za-z0-9_/-]+@[0-9a-f]{40}$')

if __name__ == '__main__':
    unittest.main()
