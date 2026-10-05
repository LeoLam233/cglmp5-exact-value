#!/usr/bin/env python3
"""Generate the split kernel phase checks, without computing any mathematical result."""
from pathlib import Path
import argparse
root=Path(__file__).resolve().parents[1]/'lean/CGLMP5'
p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');args=p.parse_args()
files={}
b='import CGLMP5.SOSCompressedData\n\nnamespace CGLMP5.SOSFinite\n\nset_option Elab.async false\nset_option maxHeartbeats 0\nset_option maxRecDepth 200000\n\n'
b+='theorem phase_zero : phase 0 = Scalar.ofRat 1 := by\n  apply funext\n  decide +kernel\n\n'
for e in range(19):b+=f'theorem phase_step_{e} : ∀ k : Fin 24, Scalar.mul (phase {e}) Scalar.zetaExact k = phase {e+1} k := by\n  decide +kernel\n\n'
files['SOSPhaseBaseChecks']=b+'end CGLMP5.SOSFinite\n'
for e in range(20):
 b='import CGLMP5.SOSCompressedData\nnamespace CGLMP5.SOSFinite\nset_option Elab.async false\nset_option maxHeartbeats 0\nset_option maxRecDepth 200000\n\n'
 b+=f'/-- Exact phase-pair identities for fixed first phase {e}, with all second phases and coordinates. -/\ntheorem phase_pair_row_{e} : ∀ (q : Fin 20) (k : Fin 24),\n    Scalar.mul (Scalar.conj (phase {e})) (phase q) k = phase (phaseDifference {e} q) k := by\n  decide +kernel\n\nend CGLMP5.SOSFinite\n'
 files[f'SOSPhasePair{e:02}']=b
b='import CGLMP5.SOSPhaseBaseChecks\n'+''.join(f'import CGLMP5.SOSPhasePair{e:02}\n' for e in range(20))+'\nnamespace CGLMP5.SOSFinite\nset_option Elab.async false\nset_option maxRecDepth 200000\n\n'
b+='/-- The full phase-pair table, assembled without reevaluating its checked numeric leaves. -/\ntheorem phase_pair_check : ∀ (p q : Fin 20) (k : Fin 24),\n    Scalar.mul (Scalar.conj (phase p)) (phase q) k = phase (phaseDifference p q) k :=\n  '
t='(fun p => Fin.elim0 p)'
for e in reversed(range(20)):t=f'Fin.cases phase_pair_row_{e} ({t})'
b+=t+'\nend CGLMP5.SOSFinite\n';files['SOSPhaseChecks']=b
for name,body in files.items():
 path=root/(name+'.lean')
 if args.check:assert path.read_text()==body, f'generated source mismatch: {name}'
 else:path.write_text(body)
print('Split phase-check sources match.' if args.check else 'Generated split phase-check sources.')
