#!/usr/bin/env python3
"""Synthetic protocol tests only; these fixtures never constitute scientific audits."""
import sys
sys.dont_write_bytecode = True
import copy, datetime, hashlib, json, subprocess, tempfile, unittest
from pathlib import Path
import check_audit_receipts as checker

TREE = '1' * 40
NOW = datetime.datetime(2026, 1, 1, tzinfo=datetime.timezone.utc)
BASE = datetime.datetime(2020, 1, 1, tzinfo=datetime.timezone.utc)
def stamp(seconds): return (BASE + datetime.timedelta(seconds=seconds)).isoformat()

class ReceiptTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='audit-consistency-unit-')
        self.root = Path(self.temp.name)
        self.bundle = self.root / 'synthetic_bundle'
        self.bundle.mkdir()
        self.index = self.bundle / 'index.json'
        self.data = {'format_version': 1, 'git_tree': TREE, 'rounds': []}
        for r in range(1, 4):
            start = (r-1)*3600
            workers = []
            for w in range(5):
                workers.append({'worker_id': f'worker-{w}', 'coverage': f'Synthetic coverage {w}',
                    'status': 'PASS', 'started_utc': stamp(start+60+w),
                    'finished_utc': stamp(start+3500+w),
                    'report': self.artifact(f'r{r}-w{w}-report.md'),
                    'attacks': [self.artifact(f'r{r}-w{w}-attack.txt')], 'findings': []})
            round = {'round': r, 'status': 'PASS', 'git_tree': TREE,
                     'started_utc': stamp(start), 'finished_utc': stamp(start+3600),
                     'report': self.artifact(f'r{r}-report.md'), 'workers': workers, 'findings': []}
            if r == 3:
                round['fresh_route_pass'] = {'status': 'PASS',
                    'initial_attacks_finished_utc': stamp(start+2400),
                    'started_utc': stamp(start+2700), 'finished_utc': stamp(start+3300),
                    'report': self.artifact('r3-fresh-report.md'),
                    'attacks': [self.artifact('r3-fresh-attack.txt')], 'findings': []}
            self.data['rounds'].append(round)
    def tearDown(self): self.temp.cleanup()
    def artifact(self, name, text=None):
        content = (text or ('Synthetic protocol fixture, not a scientific audit: ' + name)).encode()
        (self.bundle / name).write_bytes(content)
        return {'path': name, 'sha256': hashlib.sha256(content).hexdigest()}
    def check(self):
        self.index.write_text(json.dumps(self.data, indent=2))
        return checker.validate_receipts(self.index, TREE, NOW)
    def reject(self, substring):
        result = self.check()
        self.assertEqual(result['status'], 'INCONSISTENT', result)
        self.assertFalse(result['scientific_pass_inferred'])
        self.assertIn(substring, '\n'.join(result['errors']))
    def test_consistent_does_not_infer_science(self):
        result = self.check()
        self.assertEqual(result['status'], 'CONSISTENT', result)
        self.assertFalse(result['scientific_pass_inferred'])
    def test_missing_round(self):
        self.data['rounds'].pop(); self.reject('exactly three rounds')
    def test_extra_round(self):
        self.data['rounds'].append(copy.deepcopy(self.data['rounds'][0])); self.reject('exactly three rounds')
    def test_mismatched_tree(self):
        self.data['rounds'][1]['git_tree'] = '2'*40; self.reject('Git tree differs')
    def test_missing_worker(self):
        self.data['rounds'][0]['workers'].pop(); self.reject('exactly five worker')
    def test_duplicate_worker(self):
        self.data['rounds'][0]['workers'][1]['worker_id'] = 'worker-0'; self.reject('duplicate worker')
    def test_empty_coverage(self):
        self.data['rounds'][0]['workers'][0]['coverage'] = ''; self.reject('nonempty text')
    def test_nonpass(self):
        self.data['rounds'][1]['status'] = 'RUNNING'; self.reject('round status')
    def test_unresolved_actionable(self):
        self.data['rounds'][0]['workers'][0]['findings'] = [dict(id='F1', actionable=True,
            resolved=False, resolution='', evidence=[])]; self.reject('unresolved actionable')
    def test_resolved_finding_with_bound_evidence(self):
        self.data['rounds'][0]['findings'] = [dict(id='F1', actionable=True,
            resolved=True, resolution='Synthetic tested resolution',
            evidence=[self.data['rounds'][0]['workers'][0]['attacks'][0]])]
        self.assertEqual(self.check()['status'], 'CONSISTENT')
    def test_round_overlap(self):
        self.data['rounds'][1]['started_utc'] = stamp(3599); self.reject('overlaps or precedes')
    def test_round_order(self):
        self.data['rounds'][0], self.data['rounds'][1] = self.data['rounds'][1], self.data['rounds'][0]
        self.reject('exactly in order')
    def test_worker_outside_round(self):
        self.data['rounds'][0]['workers'][0]['finished_utc'] = stamp(3601); self.reject('outside its round')
    def test_reversed_time(self):
        self.data['rounds'][0]['workers'][0]['finished_utc'] = stamp(20); self.reject('start must precede')
    def test_timezone_required(self):
        self.data['rounds'][0]['started_utc'] = '2020-01-01T00:00:00'; self.reject('explicit UTC timestamp')
    def test_altered_evidence(self):
        (self.bundle/'r1-w0-attack.txt').write_text('altered'); self.reject('SHA256 mismatch')
    def test_missing_evidence(self):
        (self.bundle/'r1-w0-report.md').unlink(); self.reject('artifact is missing')
    def test_path_traversal(self):
        self.data['rounds'][0]['report']['path'] = '../escape'; self.reject('path traversal')
    def test_symlink_evidence(self):
        p=self.bundle/'r1-w0-attack.txt';p.unlink();p.symlink_to(self.bundle/'r2-w0-attack.txt')
        self.reject('symlink or bundle escape')
    def test_fresh_route_required(self):
        self.data['rounds'][2].pop('fresh_route_pass'); self.reject('missing fields: fresh_route_pass')
    def test_fresh_after_initial(self):
        self.data['rounds'][2]['fresh_route_pass']['started_utc'] = stamp(7200+2000)
        self.reject('before initial attacks finish')
    def test_fresh_evidence_not_reused(self):
        self.data['rounds'][2]['fresh_route_pass']['attacks'] = self.data['rounds'][0]['workers'][0]['attacks']
        self.reject('must not reuse')
    def test_renamed_old_evidence_not_fresh(self):
        old=(self.bundle/'r1-w0-attack.txt').read_text()
        self.data['rounds'][2]['fresh_route_pass']['attacks']=[self.artifact('renamed-old.txt',old)]
        self.reject('must not reuse')
    def test_unknown_fields_rejected(self):
        self.data['unresolved_findings'] = ['hidden']; self.reject('unknown fields')
    def test_duplicate_json_keys(self):
        self.check();text=self.index.read_text().replace('"format_version": 1','"format_version": 1, "format_version": 1')
        self.index.write_text(text);r=checker.validate_receipts(self.index,TREE,NOW)
        self.assertEqual(r['status'],'INCONSISTENT');self.assertIn('Duplicate JSON key','\n'.join(r['errors']))
    def test_cli_external_result(self):
        self.check();output=self.root/'result.json'
        p=subprocess.run([sys.executable,'-B',checker.__file__,'--tree',TREE,'--receipts',str(self.index),'--output',str(output)],capture_output=True,text=True)
        self.assertEqual(p.returncode,0,p.stderr+p.stdout)
        self.assertFalse(json.loads(output.read_text())['scientific_pass_inferred'])
    def test_cli_refuses_candidate_write(self):
        self.check();output=checker.ROOT/'verification/forbidden-audit-receipt.json'
        p=subprocess.run([sys.executable,'-B',checker.__file__,'--tree',TREE,'--receipts',str(self.index),'--output',str(output)],capture_output=True,text=True)
        self.assertNotEqual(p.returncode,0);self.assertIn('outside the candidate',p.stderr)
        self.assertFalse(output.exists())
    def test_cli_preserves_prior_result(self):
        self.check();output=self.root/'existing.json';output.write_text('preserved failed attempt')
        p=subprocess.run([sys.executable,'-B',checker.__file__,'--tree',TREE,'--receipts',str(self.index),'--output',str(output)],capture_output=True,text=True)
        self.assertNotEqual(p.returncode,0);self.assertEqual(output.read_text(),'preserved failed attempt')

if __name__ == '__main__': unittest.main()
