#!/usr/bin/env python3
"""Fast negative controls for map/inventory consistency. Does not invoke Lean."""
import sys
sys.dont_write_bytecode = True
import copy, importlib.util, json, pathlib, subprocess, tempfile, unittest
HERE=pathlib.Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('mapped',HERE/'check_mapped_inventory.py');mapped=importlib.util.module_from_spec(spec);spec.loader.exec_module(mapped)
class MappedInventoryTests(unittest.TestCase):
 def setUp(self):
  self.manifest=json.loads((HERE/'mapped_declarations.json').read_text())
  self.inventory=json.loads((HERE/'declaration_inventory.json').read_text())
 def result(self):return mapped.check(manifest=self.manifest,inventory=self.inventory)
 def rejected(self,text):
  r=self.result();self.assertEqual(r['status'],'INCONSISTENT');self.assertTrue(any(text in e for e in r['errors']),r)
 def test_current_coverage(self):self.assertEqual(self.result()['status'],'CONSISTENT')
 def test_missing_symbol(self):
  self.manifest['references'].pop();self.rejected('Unclassified mapped symbol')
 def test_duplicate_symbol(self):
  self.manifest['references'].append(copy.deepcopy(self.manifest['references'][0]));self.rejected('Duplicate mapped symbol')
 def test_stale_symbol(self):
  self.manifest['references'].append({'symbol':'missing_map_token','category':'module','reason':'test'});self.rejected('Stale mapped symbol')
 def test_missing_inventory_bridge(self):
  target=next(t for r in self.manifest['references'] for t in r.get('targets',[]));self.inventory['declarations']=[d for d in self.inventory['declarations'] if d['name']!=target['name']];self.rejected('Mapped declaration missing')
 def test_source_hash_changed(self):
  next(t for r in self.manifest['references'] for t in r.get('targets',[]))['source_sha256']='0'*64;self.rejected('Mapped source changed')
 def test_wrong_symbol_target(self):
  r=next(r for r in self.manifest['references'] if r['category']=='declaration');r['targets'][0]['name']='CGLMP5.sextic_mu';self.rejected('Symbol does not resolve')
 def test_incomplete_phase_family(self):
  r=next(r for r in self.manifest['references'] if r['symbol']=='phase_linear_e_k');r['targets'].pop();self.rejected('Incomplete or changed theorem family')
 def test_unknown_exemption(self):
  r=next(r for r in self.manifest['references'] if r['category']=='declaration');r.update(category='tactic',reason='pretend exempt');r.pop('targets');self.rejected('Unreviewed nondeclaration exemption')
 def test_final_inspection_rejects_missing_mapped_bridge(self):
  self.inventory['declarations']=[d for d in self.inventory['declarations'] if d['name']!='CGLMP5.Attainment.alice_fourier_formula']
  with tempfile.TemporaryDirectory(prefix='cglmp-map-negative-') as directory:
   root=pathlib.Path(directory);path=root/'inventory.json';path.write_text(json.dumps(self.inventory))
   run=subprocess.run([sys.executable,'-B',str(HERE/'inspect_dependencies.py'),'--fail-if-pending','--inventory',str(path),'--output',str(root/'capture')],text=True,capture_output=True)
   self.assertNotEqual(run.returncode,0);self.assertIn('Mapped declaration coverage failed',run.stdout+run.stderr)
 def test_duplicate_target(self):
  r=next(r for r in self.manifest['references'] if r['category']=='declaration');r['targets'].append(copy.deepcopy(r['targets'][0]));self.rejected('Duplicate resolved')
 def test_ambiguous_target_list(self):
  r=next(r for r in self.manifest['references'] if r['category']=='declaration');other=next(t for q in self.manifest['references'] for t in q.get('targets',[]) if t['name']!=r['targets'][0]['name']);r['targets'].append(copy.deepcopy(other));self.rejected('exactly one declaration')
 def test_null_reference_list(self):
  self.manifest['references']=None;self.rejected('Malformed mapped reference list')
 def test_null_inventory_list(self):
  self.inventory['declarations']=None;self.rejected('Malformed inventory declaration list')
 def test_changed_document_scope(self):
  self.manifest['documents'].pop();self.rejected('Changed source-map document scope')
 def test_duplicate_inventory(self):
  self.inventory['declarations'].append(copy.deepcopy(self.inventory['declarations'][0]));self.rejected('Duplicate inventory declaration')
if __name__=='__main__':unittest.main()
