#!/usr/bin/env python3
"""Fast fail-closed tests for the inspection harness; does not invoke Lean."""
import importlib.util,json,pathlib,subprocess,sys,tempfile,unittest
HERE=pathlib.Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('inspection_harness', HERE/'inspect_dependencies.py')
inspection=importlib.util.module_from_spec(spec);spec.loader.exec_module(inspection)
class InventoryGuardTests(unittest.TestCase):
 def check_rejected(self, inventory, expected):
  with tempfile.TemporaryDirectory(prefix='cglmp5-inventory-guard-') as d:
   root=pathlib.Path(d);p=root/'inventory.json';p.write_text(json.dumps(inventory))
   r=subprocess.run([sys.executable,str(HERE/'inspect_dependencies.py'),'--inventory',str(p),'--output',str(root/'receipt')],text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
   self.assertNotEqual(r.returncode,0,r.stdout);self.assertIn(expected,r.stdout)
 def test_empty_inventory_rejected(self):
  self.check_rejected({'declarations':[]},'Missing or empty declaration inventory')
 def test_optimized_empty_inventory_rejected(self):
  with tempfile.TemporaryDirectory(prefix='cglmp5-optimized-inventory-') as d:
   p=pathlib.Path(d)/'inventory.json';p.write_text('{"declarations":[]}')
   r=subprocess.run([sys.executable,'-O','-B',str(HERE/'inspect_dependencies.py'),'--inventory',str(p),'--output',str(pathlib.Path(d)/'receipt')],text=True,capture_output=True)
   self.assertNotEqual(r.returncode,0)
   self.assertIn('Missing or empty declaration inventory',r.stdout+r.stderr)
 def test_missing_final_roles_rejected(self):
  self.check_rejected({'declarations':[{'role':'unrelated','status':'pending'}]},'Missing required final-root roles')
 def test_invalid_ready_name_rejected(self):
  inv=json.loads((HERE/'declaration_inventory.json').read_text())
  inv['declarations'].append({'role':'invalid','module':None,'name':None,'status':'ready'})
  self.check_rejected(inv,'Invalid ready declaration entry')
class AxiomAllowlistTests(unittest.TestCase):
 def test_core_axioms_allowed(self):
  self.assertEqual(inspection.forbidden_axioms(['propext','Classical.choice.{u}','Quot.sound.{u}']),[])
 def test_unexpected_axioms_rejected(self):
  self.assertEqual(inspection.forbidden_axioms(['Lean.ofReduceBool','CGLMP5.fakeAxiom.{u, v}']),['Lean.ofReduceBool','CGLMP5.fakeAxiom.{u, v}'])
 def test_universe_comma_preserved(self):
  self.assertEqual(inspection.split_axiom_names('propext, Fake.{u, v}, Quot.sound.{u}'),['propext','Fake.{u, v}','Quot.sound.{u}'])
class TypeCompletenessTests(unittest.TestCase):
 def test_omitted_type_rejected(self):
  self.assertTrue(inspection.type_has_omissions('∀ {H : ⋯}, True'))
 def test_complete_type_accepted(self):
  self.assertFalse(inspection.type_has_omissions('∀ {H : Type u}, True'))
 def test_final_cannot_skip_freshness(self):
  with tempfile.TemporaryDirectory(prefix='cglmp5-final-freshness-') as d:
   r=subprocess.run([sys.executable,str(HERE/'inspect_dependencies.py'),'--fail-if-pending','--skip-freshness-check','--output',d],text=True,capture_output=True)
   self.assertNotEqual(r.returncode,0)
   self.assertIn('Final inspection cannot skip module freshness checks',r.stdout+r.stderr)
if __name__=='__main__':unittest.main()
