#!/usr/bin/env python3
"""Synthetic Git integrity tests; none perform or imply a proof replay or audit."""
import sys
sys.dont_write_bytecode = True
import copy
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch
import check_release_payload as checker


class PayloadTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='payload-gate-test-')
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.git('init', '-q')
        initial = {
            'lean/CGLMP5.lean': 'theorem intact : True := True.intro\n',
            'lean/lakefile.toml': 'name = "fixture"\n',
            'lean/lake-manifest.json': '{"packages": []}\n',
            'lean/lean-toolchain': 'leanprover/lean4:v4.34.1\n',
            'artifact_v0.1.1/SOS14.json': '{"fixture": 14}\n',
            'verification/lean/declaration_inventory.json': '{"fixture": "root"}\n',
            'scripts/recheck_lean_kernel.py': '# frozen runner fixture\n',
            'README.md': 'Baseline release text.\n',
            'SOURCE_MANIFEST.sha256': 'baseline source manifest fixture\n',
        }
        for name, content in initial.items():
            self.write(name, content)
        self.commit()
        commit = self.git('rev-parse', 'HEAD').decode().strip()
        tree = self.git('rev-parse', 'HEAD^{tree}').decode().strip()
        self.constants = patch.multiple(checker, BASELINE_COMMIT=commit,
                                       VALIDATED_COMMIT=commit, BASELINE_TREE=tree)
        self.constants.start()
        self.addCleanup(self.constants.stop)
        entries = checker.tree_entries(self.root, 'HEAD')
        files = []
        excluded = {'README.md', 'SOURCE_MANIFEST.sha256'}
        for name, (mode, _, oid) in sorted(entries.items()):
            if name in excluded:
                continue
            content = (self.root / name).read_bytes()
            files.append(dict(path=name, mode=mode, git_blob_sha1=oid,
                              bytes=len(content), sha256=checker.digest(content), role='synthetic fixture'))
        self.data = dict(format_version=1, baseline_commit=commit, baseline_tree=tree,
                         validated_commit=commit, validated_tree=tree,
                         baseline_manifest_sha256=checker.digest(initial['SOURCE_MANIFEST.sha256'].encode()),
                         payload_sha256='', files=files,
                         excluded_baseline_files=[dict(path=p, reason='Release metadata fixture')
                                                  for p in sorted(excluded)])
        self.reseal()

    def git(self, *args):
        return subprocess.check_output(['git', *args], cwd=self.root, stderr=subprocess.PIPE)

    def commit(self):
        self.git('add', '--all')
        self.git('-c', 'user.name=Synthetic Test', '-c', 'user.email=fixture@example.invalid',
                 'commit', '-qm', 'Synthetic release-integrity fixture')

    def write(self, name, content):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content)

    def reseal(self):
        self.data['files'].sort(key=lambda item: item['path'])
        lines = ''.join(e['sha256'] + '  ' + e['path'] + '\n' for e in self.data['files'])
        self.data['payload_sha256'] = checker.digest(lines.encode())

    def check(self):
        self.write(checker.MANIFEST, json.dumps(self.data))
        return checker.check(self.root)

    def reject(self, message):
        result = self.check()
        self.assertEqual(result['status'], 'FAIL', result)
        self.assertFalse(result['scientific_pass_inferred'])
        self.assertIn(message, '\n'.join(result['errors']))

    def test_valid_preserves_narrow_scope(self):
        result = self.check()
        self.assertEqual(result['status'], 'PASS', result)
        self.assertFalse(result['scientific_pass_inferred'])

    def test_legitimate_release_only_change(self):
        self.write('README.md', 'Truthful final release scope.\n')
        self.write('SOURCE_MANIFEST.sha256', 'regenerated source manifest\n')
        self.write('scripts/check_release_payload.py', '# synthetic added release checker\n')
        self.check()
        self.commit()
        self.assertEqual(self.check()['status'], 'PASS')

    def test_changed_lean_worktree(self):
        self.write('lean/CGLMP5.lean', 'axiom unchecked : False\n')
        self.reject('Working-tree payload differs')

    def test_changed_configs_and_exact_data(self):
        for name in ('lean/lakefile.toml', 'lean/lake-manifest.json', 'lean/lean-toolchain',
                     'artifact_v0.1.1/SOS14.json', 'verification/lean/declaration_inventory.json',
                     'scripts/recheck_lean_kernel.py'):
            with self.subTest(path=name):
                original = (self.root / name).read_bytes()
                self.write(name, 'changed fixture\n')
                self.reject('Working-tree payload differs')
                (self.root / name).write_bytes(original)

    def test_changed_index_even_if_worktree_restored(self):
        name = 'lean/CGLMP5.lean'
        original = (self.root / name).read_bytes()
        self.write(name, 'changed staged proof\n')
        self.git('add', name)
        (self.root / name).write_bytes(original)
        self.reject('Index payload differs')

    def test_changed_final_commit(self):
        self.write('lean/CGLMP5.lean', 'changed committed proof\n')
        self.commit()
        self.reject('Final HEAD payload differs')

    def test_deleted_file(self):
        (self.root / 'lean/CGLMP5.lean').unlink()
        self.reject('Missing, escaped, or symlinked')

    def test_deleted_tracked_path(self):
        self.git('rm', 'lean/CGLMP5.lean')
        self.reject('Baseline tracked paths removed')

    def test_new_lean_untracked(self):
        self.write('lean/Backdoor.lean', 'axiom unchecked : False\n')
        self.reject('Unapproved new release path')

    def test_new_config_tracked(self):
        self.write('lean/lakefile.lean', '-- alternate project config\n')
        self.git('add', 'lean/lakefile.lean')
        self.reject('Unapproved new release path')

    def test_new_arbitrary_data_committed(self):
        self.write('replacement_data.json', '{"hidden": true}\n')
        self.commit()
        self.reject('Unapproved new release path')

    def test_payload_omission(self):
        self.data['files'].pop()
        self.reseal()
        self.reject('partition every baseline tracked path')

    def test_payload_omission_disguised_as_release_layer(self):
        entry = self.data['files'].pop()
        self.data['excluded_baseline_files'].append(dict(path=entry['path'], reason='Pretend editorial'))
        self.reseal()
        self.reject('Unauthorized or duplicate release-layer exclusion')

    def test_wrong_baseline_and_validated_provenance(self):
        for name in ('baseline_commit', 'baseline_tree', 'validated_commit', 'validated_tree'):
            with self.subTest(field=name):
                previous = self.data[name]
                self.data[name] = '0' * 40
                self.reject('Pinned provenance mismatch: ' + name)
                self.data[name] = previous

    def test_baseline_tree_object_is_checked(self):
        wrong = '0' * 40
        with patch.object(checker, 'BASELINE_TREE', wrong):
            self.data['baseline_tree'] = wrong
            self.data['validated_tree'] = wrong
            self.reject('Public baseline tree differs')

    def test_rewritten_manifest_cannot_authenticate_changed_proof(self):
        entry = self.data['files'][0]
        self.write(entry['path'], 'replacement bytes\n')
        content = (self.root / entry['path']).read_bytes()
        entry['bytes'], entry['sha256'] = len(content), checker.digest(content)
        entry['git_blob_sha1'] = self.git('hash-object', entry['path']).decode().strip()
        self.reseal()
        self.reject('Manifest entry differs from baseline Git object')

    def test_modified_historical_manifest_digest(self):
        self.data['baseline_manifest_sha256'] = '0' * 64
        self.reject('Historical SOURCE_MANIFEST baseline digest mismatch')

    def test_wrong_aggregate_digest(self):
        self.data['payload_sha256'] = '0' * 64
        self.reject('Payload aggregate SHA256 mismatch')

    def test_duplicate_path(self):
        self.data['files'].append(copy.deepcopy(self.data['files'][0]))
        self.reject('Invalid or duplicate payload path')

    def test_path_traversal(self):
        self.data['files'][0]['path'] = '../escaped'
        self.reject('Invalid or duplicate payload path')

    def test_symlinked_payload(self):
        path = self.root / 'lean/CGLMP5.lean'
        path.unlink()
        path.symlink_to(self.root / 'README.md')
        self.reject('Missing, escaped, or symlinked')

    def test_changed_executable_mode(self):
        path = self.root / 'lean/CGLMP5.lean'
        os.chmod(path, 0o755)
        self.reject('Working-tree payload differs')

    def test_unknown_schema_fields(self):
        self.data['skip_proof_check'] = True
        self.reject('fields do not match')

    def test_duplicate_json_keys(self):
        self.check()
        path = self.root / checker.MANIFEST
        path.write_text(path.read_text().replace('"format_version": 1', '"format_version": 1, "format_version": 1'))
        result = checker.check(self.root)
        self.assertEqual(result['status'], 'FAIL')
        self.assertIn('Duplicate JSON key', '\n'.join(result['errors']))


if __name__ == '__main__':
    unittest.main()
