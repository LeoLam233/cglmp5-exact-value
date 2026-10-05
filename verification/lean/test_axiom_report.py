#!/usr/bin/env python3
"""Synthetic fail-closed exact-table comparison tests; no Lean process."""
import sys
sys.dont_write_bytecode=True
import copy, unittest
from check_axiom_report import compare
class AxiomReportTests(unittest.TestCase):
 def setUp(self):
  self.inventory={'declarations':[{'name':'CGLMP5.test','module':'CGLMP5.Test','status':'ready'}]}
  self.receipt={'declarations':[{'name':'CGLMP5.test','module':'CGLMP5.Test','axioms':['propext'],'printed_type':'CGLMP5.test : True'}], 'lean_exit_code':0,'source_changed_during_run':False,'inspection_inputs_changed_during_run':False,'pending':[],'unparsed_declarations':[],'types_with_omissions':[],'missing_required_scalar_declarations':[],'unexpected_axioms':{},'mapped_reference_coverage':{'status':'CONSISTENT'}}
  self.report='| `CGLMP5.test` | `CGLMP5.Test` | `[propext]` |\n'
 def rejected(self,part):
  r=compare(self.receipt,self.inventory,self.report);self.assertEqual(r['status'],'INCONSISTENT');self.assertTrue(any(part in e for e in r['errors']),r)
 def test_matching_exact_set(self):self.assertEqual(compare(self.receipt,self.inventory,self.report)['status'],'CONSISTENT')
 def test_changed_axiom_set(self):self.report=self.report.replace('[propext]','[]');self.rejected('axiom set mismatch')
 def test_missing_report_row(self):self.report='';self.rejected('Report declaration set')
 def test_duplicate_report_row(self):self.report+=self.report;self.rejected('Duplicate report')
 def test_missing_capture(self):self.receipt['declarations']=[];self.rejected('Captured declaration set')
 def test_lean_failure(self):self.receipt['lean_exit_code']=1;self.rejected('did not succeed')
 def test_pending_capture(self):self.receipt['pending']=['CGLMP5.test'];self.rejected('pending')
 def test_changed_sources(self):self.receipt['source_changed_during_run']=True;self.rejected('not stable')
 def test_type_omission(self):self.receipt['declarations'][0]['printed_type']='CGLMP5.test : ⋯';self.rejected('omitted printed type')
 def test_unexpected_axiom(self):self.receipt['declarations'][0]['axioms']=['Lean.ofReduceBool'];self.rejected('Unexpected axiom')
 def test_missing_map_check(self):self.receipt.pop('mapped_reference_coverage');self.rejected('not checked')
 def test_module_mismatch(self):self.report=self.report.replace('CGLMP5.Test','CGLMP5.Other');self.rejected('module mismatch')
 def test_malformed_extra_report_row(self):
  self.report+='| `CGLMP5.Test.phantom` | `CGLMP5.Test` | propext |\n';self.rejected('Malformed declaration table row')
 def test_whitespace_type(self):
  self.receipt['declarations'][0]['printed_type']=' \n\t';self.rejected('omitted printed type')
 def test_null_capture(self):
  self.receipt['declarations']=None;self.rejected('Malformed captured declaration list')
 def test_null_inventory(self):
  self.inventory['declarations']=None;self.rejected('Malformed inventory declaration list')
 def test_exact_universe_instantiations(self):
  self.receipt['declarations'][0]['axioms']=['Classical.choice.{u}'];self.report=self.report.replace('propext','Classical.choice.{v}');self.rejected('axiom set mismatch')
if __name__=='__main__':unittest.main()
