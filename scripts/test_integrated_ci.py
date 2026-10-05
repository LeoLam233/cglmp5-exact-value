#!/usr/bin/env python3
import copy
import unittest
from verify_integrated_ci import REQUIRED, verify

class IntegratedCITests(unittest.TestCase):
    def setUp(self):
        self.sha = 'a' * 40
        self.runs = [dict(path=p, head_sha=self.sha, head_branch='main', event='push',
                          run_number=1, run_attempt=1, status='completed', conclusion='success', id=i)
                     for i, p in enumerate(sorted(REQUIRED))]

    def test_good(self):
        self.assertEqual(verify(self.runs, self.sha)['status'], 'PASS')

    def test_missing_workflow(self):
        with self.assertRaises(ValueError): verify(self.runs[:1], self.sha)

    def test_wrong_commit(self):
        with self.assertRaises(ValueError): verify(self.runs, 'b' * 40)

    def test_non_main(self):
        self.runs[0]['head_branch'] = 'candidate'
        with self.assertRaises(ValueError): verify(self.runs, self.sha)

    def test_not_complete(self):
        self.runs[0]['status'] = 'in_progress'
        with self.assertRaises(ValueError): verify(self.runs, self.sha)

    def test_newer_failure_overrides_old_success(self):
        failed = copy.deepcopy(self.runs[0]); failed.update(run_attempt=2, conclusion='failure')
        with self.assertRaises(ValueError): verify(self.runs + [failed], self.sha)

    def test_pull_request_is_not_integrated_push(self):
        self.runs[0]['event'] = 'pull_request'
        with self.assertRaises(ValueError): verify(self.runs, self.sha)

if __name__ == '__main__':
    unittest.main()
