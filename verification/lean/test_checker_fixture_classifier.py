#!/usr/bin/env python3
"""Pure diagnostic guard tests; no Lean process is started."""
import importlib.util,pathlib,subprocess,sys,unittest
ROOT=pathlib.Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'scripts'))
spec=importlib.util.spec_from_file_location('checker_fixture',ROOT/'scripts/run_lean_checker_fixture.py')
runner=importlib.util.module_from_spec(spec);spec.loader.exec_module(runner)
GOOD="uncaught exception: while replaying declaration 'TrustFixture.claim':\n(kernel) declaration type mismatch, 'TrustFixture.claim' has type\n  True\nbut it is expected to have type\n  False\n"
class CheckerFixtureTests(unittest.TestCase):
 def test_kernel_mismatch(self):self.assertTrue(runner.is_kernel_mismatch(GOOD,1,False))
 def test_timeout(self):self.assertFalse(runner.is_kernel_mismatch(GOOD,1,True))
 def test_signal_exit(self):self.assertFalse(runner.is_kernel_mismatch(GOOD,-9,False))
 def test_import_error(self):self.assertFalse(runner.is_kernel_mismatch(GOOD+'failed to import',1,False))
 def test_memory_error(self):self.assertFalse(runner.is_kernel_mismatch(GOOD+'out of memory',1,False))
 def test_wrong_declaration(self):self.assertFalse(runner.is_kernel_mismatch(GOOD.replace('TrustFixture.claim','Other.claim'),1,False))
 def test_success(self):self.assertFalse(runner.is_kernel_mismatch('',0,False))
 def test_output_required_without_launching_lean(self):
  r=subprocess.run([sys.executable,'-B',str(ROOT/'scripts/run_lean_checker_fixture.py'),'--lake','/missing/lake'],text=True,capture_output=True)
  self.assertNotEqual(r.returncode,0)
  self.assertIn('--output-dir is required',r.stderr)
 def test_repository_output_rejected_without_launching_lean(self):
  r=subprocess.run([sys.executable,'-B',str(ROOT/'scripts/run_lean_checker_fixture.py'),'--lake','/missing/lake','--output-dir',str(ROOT/'verification/forbidden-fixture-output')],text=True,capture_output=True)
  self.assertNotEqual(r.returncode,0)
  self.assertIn('outputs must be outside the repository',r.stderr)
if __name__=='__main__':unittest.main()
