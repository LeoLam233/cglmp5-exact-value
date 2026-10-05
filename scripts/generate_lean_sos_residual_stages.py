#!/usr/bin/env python3
"""Generate opaque lookup/scale stages and sparse, kernel-checked integer residuals.
Python generates literals, never proof conclusions: every numerical statement is checked in Lean.
"""
from pathlib import Path
from collections import defaultdict
import json,math,hashlib,sys
from generate_lean_sos_arithmetic import ROOT,data,P,W,T,M
OUT=ROOT/'lean/CGLMP5'
CHECK = '--check' in sys.argv
meta=json.loads((ROOT/'lean/SOS_COMPRESSION_MANIFEST.json').read_text())
cores=[P[j][i] for j,i in meta['origins']]
gram=[W[j]*cores[p].conj()*cores[q] for j,p,q in meta['gram_origins']]
gindex={tuple(a):i for i,a in enumerate(meta['gram_origins'])}
z=[0]*24;z[6]=1;z[12]=-1;z[13]=1;phase=[T(1)]
for _ in range(19):phase.append(phase[-1]*T(z,4))
def canon(w):
 ps=[[],[]]
 for r,k in w:
  k%=5
  if not k:continue
  p=ps[r%2]
  if p and p[-1][0]==r:k=(p.pop()[1]+k)%5
  if k:p.append((r,k))
 return tuple(ps[0]+ps[1])
def adj(w):return canon([(r,5-k) for r,k in reversed(w)])
fibers=defaultdict(list)
for j,term in enumerate(data['terms']):
 for a,ta in enumerate(term['polynomial']):
  for b,tb in enumerate(term['polynomial']):
   w=tuple(map(tuple,ta['word']));v=tuple(map(tuple,tb['word']))
   p,pe=meta['phase_map'][j][a];q,qe=meta['phase_map'][j][b];f=(gindex[j,p,q],(qe-pe)%20)
   fibers[canon(adj(w)+v)].append(f);fibers[canon(v+adj(w))].append(f)
target={():T([0,0,1]+[0]*21,5)}
for r in range(4):
 for k in range(1,5):
  c=T()
  for q in range(5):c=c+phase[(-4*k*q)%20]*T(2-q,10)
  if r==3:c=c*phase[(-4*k)%20]
  w=canon(((r,k),((r+1)%4,5-k)));target[w]=target.get(w,T())+-c
words=sorted(set(fibers)|set(target));assert len(words)==273
vals=[target.get(w,T()) for w in words]
D=[math.lcm(vals[i].d,*[gram[g].d*phase[e].d for g,e in fibers[w]]) for i,w in enumerate(words)]
def vec(v):return '!['+', '.join(str(x) for x in v)+']'
def fl(fs):return '['+', '.join(f'({g}, {e})' for g,e in fs)+']'
def header(imps):return '\n'.join('import CGLMP5.'+x for x in imps)+'\n\nnamespace CGLMP5.SOSFinite\nset_option Elab.async false\nset_option linter.unusedSimpArgs false\nset_option maxHeartbeats 0\nset_option maxRecDepth 200000\n\n'
def save(name,s):
 text=s+'\nend CGLMP5.SOSFinite\n';p=OUT/(name+'.lean')
 if CHECK:
  assert p.read_text()==text, f'generated source mismatch: {name}'
 elif not p.exists() or p.read_text()!=text:p.write_text(text)
# Opaque literal lookup lemmas stop the simplifier traversing the large dispatch tables.
s=header(['SOSIntegerResidualDefinitions'])
for g,v in enumerate(gram):s+=f'theorem gram_numerator_literal_{g} : gramNumerator {g} = {vec(v.n)} := rfl\n\n'
for i,w in enumerate(words):
 s+=f'theorem fiber_literal_{i} : fiber {i} = {fl(fibers[w])} := rfl\n'
 s+=f'theorem denominator_literal_{i} : commonDenominator {i} = {D[i]} := rfl\n'
 s+=f'theorem target_denominator_literal_{i} : targetDenominator {i} = {vals[i].d} := rfl\n'
 s+=f'theorem target_numerator_literal_{i} : targetNumerator {i} = {vec(vals[i].n)} := rfl\n\n'
save('SOSIntegerLiterals',s)
for i,w in enumerate(words):
 fs=fibers[w];unique=list(dict.fromkeys(fs));es=sorted(set(e for _,e in fs));gs=sorted(set(g for g,_ in fs))
 s=header(['SOSIntegerLiterals']+[f'SOSPhaseLinear{e:02}' for e in es])
 for n,(g,e) in enumerate(unique):
  scale=D[i]//(gram[g].d*phase[e].d)
  assert scale*(gram[g].d*phase[e].d)==D[i]
  s+=f'private theorem scale_{i}_{n} : commonDenominator {i} / (gramDenominator {g} * phaseDenominator {e}) = {scale} := by\n  decide +kernel\n\n'
 s+=f'theorem denominator_divides_{i:03} : ∀ f ∈ fiber {i}, commonDenominator {i} % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by\n  decide +kernel\n\n'
 for k in range(24):
  lemmas=['List.map_cons','List.map_nil','List.sum_cons','List.sum_nil','Prod.fst','Prod.snd']
  lemmas += [f'scale_{i}_{n}' for n in range(len(unique))]
  lemmas += [f'phase_linear_{e}_{k}' for e in es]
  lemmas += [f'gram_numerator_literal_{g}' for g in gs]
  lemmas += [f'denominator_literal_{i}',f'target_denominator_literal_{i}',f'target_numerator_literal_{i}']
  s+=f'private theorem coordinate_{i}_{k} : integerCoordinateClaim {i} {k} := by\n  unfold integerCoordinateClaim\n  rw [integerNumerator, fiber_literal_{i}]\n  simp only ['+', '.join(lemmas)+']\n  decide +kernel\n\n'
 # Fin.cases is a checked eliminator; no tactic re-normalization of huge family goals.
 family='(fun i => Fin.elim0 i)'
 for k in reversed(range(24)):family=f'(Fin.cases coordinate_{i}_{k} {family})'
 s+=f'theorem integer_residual_{i:03} : integerResidualClaim {i} :=\n  {family}\n'
 save(f'SOSIntegerResidual{i:03}',s)
s=header([f'SOSIntegerResidual{i:03}' for i in range(273)])
s+='theorem denominator_divides (i : Fin 273) : ∀ f ∈ fiber i, commonDenominator i % (gramDenominator f.1 * phaseDenominator f.2) = 0 := by\n  have h : ∀ j : Fin 273, ∀ f ∈ fiber j, commonDenominator j % (gramDenominator f.1 * phaseDenominator f.2) = 0 :=\n    '
fam='(fun i => Fin.elim0 i)'
for i in reversed(range(273)):fam=f'(Fin.cases denominator_divides_{i:03} {fam})'
s+=fam+'\n  exact h i\n\n'
s+='theorem integer_residual : ∀ i : Fin 273, integerResidualClaim i :=\n  '
fam='(fun i => Fin.elim0 i)'
for i in reversed(range(273)):fam=f'(Fin.cases integer_residual_{i:03} {fam})'
s+=fam+'\n';save('SOSIntegerResidualChecks',s)
manifest={'canonical_sha256':hashlib.sha256((ROOT/'artifact_v0.1.1/SOS14.json').read_bytes()).hexdigest(),'word_count':273,'coordinate_count':6552,'method':'opaque literal lookup + exact scale certificates + universally proved sparse phase action + kernel integer residual','source_scales':sum(len(set(fibers[w])) for w in words),'phase_pair_count':len(set(f for fs in fibers.values() for f in fs))}
manifest_path=ROOT/'lean/SOS_STAGED_RESIDUAL_MANIFEST.json'
manifest_text=json.dumps(manifest,indent=2)+'\n'
if CHECK:assert manifest_path.read_text()==manifest_text, 'staged residual manifest mismatch'
elif not manifest_path.exists() or manifest_path.read_text()!=manifest_text:manifest_path.write_text(manifest_text)
print('Generated273sparse staged residual modules with6552kernel integer coordinate goals')
