#!/usr/bin/env python3
"""Propose sparse linear phase-multiplication formulas; Lean verifies every formula.
This generator only reads the current exact integer phase/table data and writes
its owned SOSPhaseLinear modules. No external arithmetic result is trusted.
"""
from pathlib import Path
import ast, hashlib, json, re
ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'lean/CGLMP5'
phase_source=OUT/'SOSIntegerData.lean'; table_source=OUT/'ScalarTableData.lean'
s=phase_source.read_text(); block=s.split('def phaseNumerator ',1)[1].split('\ndef ',1)[0]
phases=[ast.literal_eval(re.search(r'^  \| '+str(e)+r' => (.*)$',block,re.M).group(1).replace('![','[')) for e in range(20)]
ts=table_source.read_text(); tables=[ast.literal_eval(re.search(r'^  \| '+str(k)+r' => (.*)$',ts,re.M).group(1)) for k in range(24)]
def vector(v): return '!['+', '.join(str(x) for x in v)+']'
def terms(v):return '['+', '.join('('+', '.join(str(x) for x in t)+')' for t in v)+']'
def coeffs(e,k):
 d={}
 for i,j,c in tables[k]:d[i]=d.get(i,0)+phases[e][j]*c
 return [(i,c) for i,c in sorted(d.items()) if c]
def expr(e,k):
 q=coeffs(e,k)
 return ' + '.join(f'({c} : ℤ) * n {i}' for i,c in q) if q else '0'
head='''namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

'''
data='''import CGLMP5.SOSIntegerData
import CGLMP5.ScalarIntegerArithmetic
import Mathlib.Data.Fin.VecNotation

/-! Small opaque lookup equalities prevent repeated unfolding of entire data tables. -/
'''+head
for e in range(20): data+=f'theorem phaseLinear_phase_literal_{e} : phaseNumerator {e} = {vector(phases[e])} := rfl\n\n'
for k in range(24): data+=f'theorem phaseLinear_terms_literal_{k} : Scalar.mulTerms {k} = {terms(tables[k])} := rfl\n\n'
data+='end CGLMP5.SOSFinite\n';(OUT/'SOSPhaseLinearData.lean').write_text(data)
for e in range(20):
 o='''import CGLMP5.SOSPhaseLinearData
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

'''+head
 for k in range(24):
  o+=f'/-- Exact sparse phase {e}, coordinate {k}; valid for every integer numerator vector. -/\n'
  o+=f'theorem phase_linear_{e}_{k} (n : Fin 24 → ℤ) :\n    Scalar.mulNumerator n (phaseNumerator {e}) {k} = {expr(e,k)} := by\n'
  o+=f'  rw [phaseLinear_phase_literal_{e}, Scalar.mulNumerator, phaseLinear_terms_literal_{k}]\n  norm_num <;> ring\n\n'
 o+='end CGLMP5.SOSFinite\n';(OUT/f'SOSPhaseLinear{e:02}.lean').write_text(o)
(OUT/'SOSPhaseLinear.lean').write_text(''.join(f'import CGLMP5.SOSPhaseLinear{e:02}\n' for e in range(20)))
manifest={'kind':'kernel_checked_sparse_phase_formula_generation','source_files':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [phase_source,table_source]},'phase_count':20,'coordinate_count':24,'formula_count':480,'max_nonzero_terms':max(len(coeffs(e,k)) for e in range(20) for k in range(24)),'proof_method':'Opaque rfl lookup equalities, then Lean norm_num/ring for symbolic integer vectors. No external result is trusted.'}
path=ROOT/'verification/formalization_development/residual_pilot/phase_linear_generation.json';path.parent.mkdir(parents=True,exist_ok=True);path.write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps(manifest,indent=2))
