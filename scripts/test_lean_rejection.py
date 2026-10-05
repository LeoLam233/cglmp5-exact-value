#!/usr/bin/env python3
"""Synthetic and historical-log classifier tests; no Lean compiler or audit runs."""
import sys
sys.dont_write_bytecode = True
from pathlib import Path
import unittest
from lean_rejection import BLOCKED_MARKERS, FIXTURE_KINDS, SOURCE_KINDS, classify_rejection
ROOT=Path(__file__).resolve().parents[1]
GOOD='Probe.lean:3:2: error: Tactic `decide` proved that the proposition\n  1 = 2\nis false\n'
class RejectionTests(unittest.TestCase):
 def classify(self,log=GOOD,code=1,**kw):
  return classify_rejection(log,code,'Probe.lean',('decide_false',),**kw)
 def test_expected_typed_rejection(self):
  self.assertTrue(self.classify()['accepted'])
 def test_old_resource_false_positive_rejected(self):
  log='Probe.lean:9:2: error: maximum recursion depth has been reached\n'
  self.assertFalse(self.classify(log)['accepted'])
 def test_all_blocked_markers_rejected_even_with_proof_error(self):
  for marker in BLOCKED_MARKERS:
   with self.subTest(marker=marker):self.assertFalse(self.classify(GOOD+'\n'+marker)['accepted'])
 def test_nonordinary_exit_rejected(self):
  for code in [0,None,-9,2,137]:
   with self.subTest(code=code):self.assertFalse(self.classify(code=code)['accepted'])
 def test_timeout_rejected(self):self.assertFalse(self.classify(timed_out=True)['accepted'])
 def test_parser_error_rejected(self):
  self.assertFalse(self.classify('Probe.lean:2:0: error: unexpected token\n')['accepted'])
 def test_typeclass_stuck_rejected(self):
  self.assertFalse(self.classify('Probe.lean:2:0: error: typeclass instance problem is stuck\nCompleteSpace ?m.2\n')['accepted'])
 def test_unknown_error_rejected(self):
  self.assertFalse(self.classify('Probe.lean:2:0: error: unrecognized failure\n')['accepted'])
 def test_wrong_file_rejected(self):
  self.assertFalse(self.classify(GOOD.replace('Probe.lean','Import.lean'))['accepted'])
 def test_wrong_proof_kind_rejected(self):
  r=classify_rejection(GOOD,1,'Probe.lean',('type_mismatch',));self.assertFalse(r['accepted'])
 def test_false_marker_required_for_decide(self):
  self.assertFalse(self.classify(GOOD.replace('is false',''))['accepted'])
 def test_extra_unparsed_error_rejected(self):
  self.assertFalse(self.classify(GOOD+'error: unstructured failure\n')['accepted'])
 def test_fixture_requires_one_expected_error(self):
  self.assertFalse(self.classify(GOOD+GOOD,expected_count=1)['accepted'])
 def test_diagnostic_and_hash_recorded(self):
  r=self.classify();self.assertEqual(r['diagnostics'][0]['kind'],'decide_false')
  self.assertEqual(r['diagnostics'][0]['line'],3);self.assertEqual(len(r['raw_log_sha256']),64)
 def test_known_historical_fixture_diagnostics(self):
  base=ROOT/'verification/lean_negative_controls/runs/20261004T120258Z'
  for name,kinds in FIXTURE_KINDS.items():
   with self.subTest(case=name):
    result=classify_rejection((base/(name+'.log')).read_text(),1,name+'.lean',kinds,expected_count=1)
    self.assertEqual(result['accepted'],name!='proper_isometry_surjective',result)
 def test_known_historical_source_mutation_diagnostics(self):
  base=ROOT/'verification/lean_negative_controls/source_runs/20261004T115907Z'
  names={'event_shift':'Events.lean','same_party_order':'Words.lean','root_embedding_sign':'Root.lean','weight_sign':'Positivity.lean','setting_dependent_J':'POVMDilation.lean'}
  for name,kinds in SOURCE_KINDS.items():
   with self.subTest(case=name):
    r=classify_rejection((base/(name+'_mutated.log')).read_text(),1,names[name],kinds)
    self.assertTrue(r['accepted'],r)
 def test_explicit_isometry_type_mismatch_is_expected_kind(self):
  log='proper_isometry_surjective.lean:5:2: error: Type mismatch\n  commonJ_isometry\nhas type\n  J.adjoint * J = 1\nbut is expected to have type\n  J * J.adjoint = 1\n'
  r=classify_rejection(log,1,'proper_isometry_surjective.lean',FIXTURE_KINDS['proper_isometry_surjective'],expected_count=1)
  self.assertTrue(r['accepted'])
if __name__=='__main__':unittest.main()
