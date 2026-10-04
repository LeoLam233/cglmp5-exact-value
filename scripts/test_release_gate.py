#!/usr/bin/env python3
"""Isolated synthetic negative controls for the release-evidence packaging guard.

These dummy files test guard behavior only, never certificate mathematics.
"""
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

CHECKER = Path(__file__).with_name('check_release_gate.py')
REQUIRED = ['artifact_v0.1.1/'+name for name in (
    'SOS14.json','EXACT_KERNELS.json','EXACT_SOS_CANDIDATE.json','POSITIVITY_CERTIFICATE.json',
    'verify_sos14.py','verify_independent.py','verify_statement.py','validate_integer_encoding.py',
    'strict_schema.py','verification_receipt.py','kill_tests.py','PROOF.md','ROOT_EMBEDDING.md',
    'POVM_BRIDGE.md','SCHEMA.md')]+['paper/main.tex','paper/references.bib','paper/main.pdf','paper/README.md']
class GuardTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix='cglmp5-gate-unit-')
        self.root = Path(self.tmp.name)
        self.gate = {'status':'PASS','gates':{},'source_binding':{}}
        for name in REQUIRED:
            self.write(name,b'SYNTHETIC GUARD UNIT TEST ONLY\n')
            self.gate['source_binding'][name] = self.sha(name)
        for i in range(1,15):
            name=f'verification/receipts/R{i:02d}.json'
            self.write(name,b'{"synthetic":true,"status":"PASS"}\n')
            self.gate['gates'][f'R{i:02d}']={'status':'PASS','receipts':[{'path':name,'sha256':self.sha(name)}]}
    def tearDown(self):
        self.tmp.cleanup()
    def write(self,name,data):
        p=self.root/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
    def sha(self,name):
        return hashlib.sha256((self.root/name).read_bytes()).hexdigest()
    def run_guard(self):
        self.write('verification/release_gate.json',(json.dumps(self.gate)+'\n').encode())
        return subprocess.run([sys.executable,str(CHECKER),'--root',str(self.root)],capture_output=True,text=True)
    def test_complete_synthetic_fixture(self):
        self.assertEqual(self.run_guard().returncode,0)
    def test_top_level_failure(self):
        self.gate['status']='FAIL';self.assertNotEqual(self.run_guard().returncode,0)
    def test_missing_gate(self):
        del self.gate['gates']['R14'];self.assertNotEqual(self.run_guard().returncode,0)
    def test_failed_gate(self):
        self.gate['gates']['R06']['status']='FAIL';self.assertNotEqual(self.run_guard().returncode,0)
    def test_missing_receipts(self):
        self.gate['gates']['R06']['receipts']=[];self.assertNotEqual(self.run_guard().returncode,0)
    def test_tampered_receipt(self):
        self.write('verification/receipts/R06.json',b'tampered');self.assertNotEqual(self.run_guard().returncode,0)
    def test_unrelated_binding(self):
        del self.gate['source_binding']['paper/main.pdf'];self.assertNotEqual(self.run_guard().returncode,0)
    def test_tampered_source(self):
        self.write('artifact_v0.1.1/SOS14.json',b'tampered');self.assertNotEqual(self.run_guard().returncode,0)
    def test_escape_receipt(self):
        self.gate['gates']['R01']['receipts'][0]['path']='../outside';self.assertNotEqual(self.run_guard().returncode,0)

if __name__=='__main__':
    unittest.main(verbosity=2)
