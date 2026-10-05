#!/usr/bin/env python3
"""Fail-closed diagnostic tests; no compiler invocation and no scientific oracle."""
import importlib.util,pathlib,sys,unittest
ROOT=pathlib.Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'scripts'))
spec=importlib.util.spec_from_file_location('sos_mutation',ROOT/'scripts/run_lean_sos_corruption.py')
runner=importlib.util.module_from_spec(spec);spec.loader.exec_module(runner)
GOOD='/tmp/shadow/CGLMP5/SOSIntegerResidual000.lean:140:2: error: Tactic `decide` proved that the proposition\n  2 = 3\nis false\n'
class ClassifierTests(unittest.TestCase):
 def test_expected_arithmetic_rejection(self):
  self.assertTrue(runner.classify_rejection(GOOD,1)['actual_arithmetic_false'])
 def test_resource_exit_rejected(self):
  self.assertFalse(runner.classify_rejection(GOOD,137)['actual_arithmetic_false'])
 def test_resource_diagnostic_rejected(self):
  self.assertFalse(runner.classify_rejection(GOOD+'out of memory\n',1)['actual_arithmetic_false'])
 def test_import_error_rejected(self):
  self.assertFalse(runner.classify_rejection(GOOD+'failed to import module\n',1)['actual_arithmetic_false'])
 def test_wrong_module_rejected(self):
  self.assertFalse(runner.classify_rejection(GOOD.replace('SOSIntegerResidual000','SOSIntegerLiterals'),1)['actual_arithmetic_false'])
 def test_multiple_errors_rejected(self):
  self.assertFalse(runner.classify_rejection(GOOD+GOOD,1)['actual_arithmetic_false'])
 def test_success_not_rejection(self):
  self.assertFalse(runner.classify_rejection('',0)['actual_arithmetic_false'])
if __name__=='__main__':unittest.main()
