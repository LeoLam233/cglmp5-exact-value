"""Output routing and immutable-candidate guards for negative-control replay."""
from pathlib import Path
import datetime, hashlib, json, subprocess

def add_replay_arguments(parser):
    parser.add_argument('--output-dir', type=Path, help='External directory receiving timestamped receipts and logs.')
    parser.add_argument('--require-clean-tree', action='store_true', help='Require a clean immutable Git HEAD/tree and tracked-file hashes before and after every check.')

def snapshot(repo):
    def git(*args):
        return subprocess.check_output(['git','-C',str(repo),*args])
    tracked = git('ls-files','-z').decode().split('\0')
    hashes = {}
    for name in tracked:
        if name:
            p=repo/name
            hashes[name]=hashlib.sha256(p.read_bytes()).hexdigest() if p.is_file() else None
    return dict(head=git('rev-parse','HEAD').decode().strip(),
                tree=git('rev-parse','HEAD^{tree}').decode().strip(),
                status=git('status','--porcelain=v1','--untracked-files=all').decode(),
                tracked_sha256=hashes)

class ReplayGuard:
    def __init__(self, repo, args, default_base):
        self.repo=repo.resolve();self.strict=args.require_clean_tree
        base=(args.output_dir or default_base).resolve()
        if self.strict and base.is_relative_to(self.repo):
            raise RuntimeError('--require-clean-tree requires --output-dir outside the audited repository')
        self.baseline=snapshot(self.repo)
        if self.strict and self.baseline['status']:
            raise RuntimeError('Frozen replay refused: Git tree is not clean')
        self.stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
        self.out=base/self.stamp;self.out.mkdir(parents=True,exist_ok=False)
        self.events=[];self.check('start')
    def check(self,label):
        now=snapshot(self.repo)
        equal=(now==self.baseline)
        clean=not now['status']
        self.events.append(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),label=label,
                                head=now['head'],tree=now['tree'],clean=clean,unchanged=equal,
                                source_hashes_unchanged=now['tracked_sha256']==self.baseline['tracked_sha256']))
        (self.out/'frozen_tree_checks.json').write_text(json.dumps(dict(strict=self.strict,baseline=self.baseline,events=self.events),indent=2)+'\n')
        if self.strict and (not equal or not clean):
            (self.out/'IMMUTABILITY_FAILURE.json').write_text(json.dumps(self.events[-1],indent=2)+'\n')
            receipt=self.out/'receipt.json'
            if receipt.exists():
                data=json.loads(receipt.read_text());data['status']='FAIL_FROZEN_TREE_CHANGED';receipt.write_text(json.dumps(data,indent=2)+'\n')
            raise RuntimeError('Frozen replay stopped: HEAD, tree, worktree, or tracked source hashes changed')
    def metadata(self):
        # A suite is never a complete gate by itself. Report the current declared
        # hook state without treating its presence as evidence that it passed.
        hook_path = self.repo/'verification/lean/ci/completion_hooks.json'
        hook = json.loads(hook_path.read_text()).get('actual_sos_coefficient_corruption', {}) if hook_path.exists() else {}
        hook_ready = hook.get('status') == 'ready' and hook.get('runner') == 'scripts/run_lean_sos_corruption.py' and (self.repo/'scripts/run_lean_sos_corruption.py').is_file()
        return dict(require_clean_tree=self.strict,external_output=not self.out.is_relative_to(self.repo),
                    head=self.baseline['head'],tree=self.baseline['tree'],
                    all_checkpoints_clean=all(e['clean'] for e in self.events),
                    all_checkpoints_unchanged=all(e['unchanged'] for e in self.events),
                    candidate_gate_eligible=False,
                    pending_hooks=[] if hook_ready else ['actual_SOS_coefficient_corruption_after_complete_identity'],
                    standalone_completion_gate=False)
