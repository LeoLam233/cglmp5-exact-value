#!/usr/bin/env python3
"""Build-time exact tower computations; all generated identities require kernel checks."""
from pathlib import Path
from functools import lru_cache
import json,math,hashlib,sys
CHECK = __name__ == "__main__" and "--check" in sys.argv
def write_generated(path, text):
 if CHECK:
  if path.read_text() != text:
   import difflib
   print("".join(difflib.unified_diff(path.read_text().splitlines(True), text.splitlines(True), fromfile=str(path), tofile="regenerated")))
   raise AssertionError(f"generated source mismatch: {path.name}")
 elif not path.exists() or path.read_text() != text:path.write_text(text)
ROOT=Path(__file__).resolve().parents[1]
data=json.loads((ROOT/'artifact_v0.1.1/SOS14.json').read_text())
assert hashlib.sha256((ROOT/'artifact_v0.1.1/SOS14.json').read_bytes()).hexdigest()=='1c0708628ca5b89caef11a80d3a5e89f4074a14a26ea5c2d2d92087ffa5f22c2'
@lru_cache(None)
def red(a,b,c,e):
 if e>=2: ts=[((a,b,c,e-2),-1)]
 elif c>=2:ts=[((a,b,c-2,e),10),((a+1,b,c-2,e),2)]
 elif b>=3:ts=[((a+1,b-1,c,e),5),((a,b-2,c,e),100),((a+1,b-2,c,e),-20),((a,b-3,c,e),500),((a+1,b-3,c,e),-200)]
 elif a>=2:ts=[((a-2,b,c,e),5)]
 else:return {a+2*b+6*c+12*e:1}
 r={}
 for t,n in ts:
  for k,v in red(*t).items():r[k]=r.get(k,0)+n*v
 return {k:v for k,v in r.items() if v}
def idx(i):return i%2,(i//2)%3,(i//6)%2,i//12
M=[[red(*(x+y for x,y in zip(idx(i),idx(j)))) for j in range(24)] for i in range(24)]
class T:
 def __init__(self,n=0,d=1):
  if isinstance(n,int):n=[n]+[0]*23
  g=math.gcd(d,*n);self.n=tuple(x//g for x in n);self.d=d//g
 def __add__(a,b):return T([x*b.d+y*a.d for x,y in zip(a.n,b.n)],a.d*b.d)
 def __neg__(a):return T([-x for x in a.n],a.d)
 def __mul__(a,b):
  r=[0]*24
  for i,x in enumerate(a.n):
   if x:
    for j,y in enumerate(b.n):
     if y:
      for k,c in M[i][j].items():r[k]+=x*y*c
  return T(r,a.d*b.d)
 def conj(a):return T([x if i<12 else -x for i,x in enumerate(a.n)],a.d)
 def __eq__(a,b):return a.n==b.n and a.d==b.d
 def __hash__(a):return hash((a.n,a.d))
def load(v):return T(list(map(int,v['n'])),int(v['d']))
def lean(v):return 'Scalar.ofCanonical !['+', '.join(str(x) for x in v.n)+'] '+str(v.d)
P=[[load(t['coefficient']) for t in term['polynomial']] for term in data['terms']]
W=[load(term['weight']) for term in data['terms']]

# Phase-compressed certificate. Each generated numerical claim is kernel checked.
def gen_compressed():
 Z=T([0]*6+[1]+[0]*5+[-1,1]+[0]*10,4)
 PH=[T(1)]
 for _ in range(19):PH.append(PH[-1]*Z)
 cores=[];origins=[];maps=[];go=[];gp=[];gv=[];gdict={}
 for j,ps in enumerate(P):
  mp=[]
  for i,c in enumerate(ps):
   found=next(((h,e) for h,v in enumerate(cores) for e,z in enumerate(PH) if v*z==c),None)
   if found is None:cores.append(c);origins.append((j,i));found=(len(cores)-1,0)
   mp.append(found)
  maps.append(mp)
  ids=sorted(set(h for h,e in mp))
  for p in ids:
   for q in ids:
    gdict[j,p,q]=len(go);go.append((j,p,q));prod=cores[p].conj()*cores[q];gp.append(prod);gv.append(W[j]*prod)
 assert len(cores)==28 and len(go)==135
 out=ROOT/'lean/CGLMP5'
 def header(imps):return '\n'.join('import CGLMP5.'+p for p in imps)+'\n\nnamespace CGLMP5.SOSFinite\n\nset_option Elab.async false\nset_option maxHeartbeats 0\nset_option maxRecDepth 200000\n\n'
 def save(name,s):
  p=out/(name+'.lean'); text=s+'\nend CGLMP5.SOSFinite\n'
  write_generated(p,text)
 def matchdef(name,n,typ,vals):
  return f'def {name} (j : Fin {n}) : {typ} :=\n  match j.val with\n'+''.join(f'  | {i} => {v}\n' for i,v in enumerate(vals))+f'  | _ => {vals[0]}\n\n'
 body=header(['CanonicalData','ScalarPowerData'])
 body+='def canonicalCoefficient (j : Fin 14) (i : ℕ) : Scalar :=\n  (((CanonicalData.polynomial j)[i]?).getD (Word.one, Scalar.zero)).2\n\n'
 body+=matchdef('core',28,'Scalar',[f'canonicalCoefficient {j} {i}' for j,i in origins])
 body+=matchdef('phase',20,'Scalar',[lean(v) for v in PH])
 body+='def phaseDifference (p q : Fin 20) : Fin 20 := ⟨(q.val + 20 - p.val) % 20, Nat.mod_lt _ (by decide)⟩\n\n'
 body+=matchdef('gramOrigin',135,'Fin 14 × Fin 28 × Fin 28',[f'({j}, {p}, {q})' for j,p,q in go])
 body+=matchdef('gramPair',135,'Scalar',[lean(v) for v in gp])
 body+=matchdef('gram',135,'Scalar',[lean(v) for v in gv])
 body+='def gramIndex (j : Fin 14) (p q : Fin 28) : Fin 135 :=\n  match j.val, p.val, q.val with\n'+''.join(f'  | {j}, {p}, {q} => {h}\n' for (j,p,q),h in gdict.items())+'  | _, _, _ => 0\n\n'
 body+='structure PhaseTerm where\n  word : Word\n  core : Fin 28\n  phase : Fin 20\n  deriving DecidableEq, Repr\n\n'
 def word(a):
  left=[(r//2,k) for r,k in a if r%2==0];right=[(r//2,k) for r,k in a if r%2==1]
  return '⟨['+', '.join(f'({r}, {k})' for r,k in left)+'], ['+', '.join(f'({r}, {k})' for r,k in right)+']⟩'
 pts=[]
 for j,t in enumerate(data['terms']):pts.append('['+', '.join('⟨'+word(v['word'])+f', {h}, {e}⟩' for v,(h,e) in zip(t['polynomial'],maps[j]))+']')
 body+=matchdef('phaseTerms',14,'List PhaseTerm',pts)
 localids=[sorted(set(h for h,e in mp)) for mp in maps]
 body+='def localCore (j : Fin 14) (p : Fin 4) : Fin 28 :=\n  match j.val, p.val with\n'
 for j,ids in enumerate(localids):
  for p in range(4):body+=f'  | {j}, {p} => {ids[p] if p<len(ids) else ids[0]}\n'
 body+='  | _, _ => 0\n\n'
 locals=[]
 for j,t in enumerate(data['terms']):
  ids=localids[j]
  locals.append('['+', '.join('('+word(v['word'])+f', {ids.index(h)}, {e})' for v,(h,e) in zip(t['polynomial'],maps[j]))+']')
 body+=matchdef('localTerms',14,'List (Word × Fin 4 × Fin 20)',locals)
 body+='theorem gramIndex_origin : ∀ (j : Fin 14) (p q : Fin 4), gramOrigin (gramIndex j (localCore j p) (localCore j q)) = (j, localCore j p, localCore j q) := by\n  decide +kernel\n\n'
 save('SOSCompressedData',body)
 for j,mp in enumerate(maps):
  body=header(['SOSCompressedData'])
  for i,(h,e) in enumerate(mp):
   if e==0:
    body+=f'theorem source_phase_{j}_{i} : ∀ k : Fin 24, canonicalCoefficient {j} {i} k = core {h} k := by\n  decide +kernel\n\n'
   else:
    body+=f'theorem source_phase_{j}_{i} : ∀ k : Fin 24, canonicalCoefficient {j} {i} k = Scalar.mul (core {h}) (phase {e}) k := by\n  decide +kernel\n\n'
  for h,(jj,p,q) in enumerate(go):
   if jj==j:
    body+=f'theorem gram_pair_{h} : ∀ k : Fin 24, Scalar.mul (Scalar.conj (core {p})) (core {q}) k = gramPair {h} k := by\n  decide +kernel\n\n'
    body+=f'theorem gram_weight_{h} : ∀ k : Fin 24, Scalar.mul (CanonicalData.weight {j}) (gramPair {h}) k = gram {h} k := by\n  decide +kernel\n\n'
  save(f'SOSCompressedCheck{j:02}',body)
 # Split phase checks are maintained by the low-memory row generator.
 import subprocess, sys
 subprocess.run([sys.executable, str(ROOT/'scripts/generate_lean_sos_phase_checks.py')]+(['--check'] if CHECK else []), check=True)
 manifest={'core_count':len(cores),'gram_pair_count':len(go),'origins':origins,'phase_map':maps,'gram_origins':go,'canonical_sha256':hashlib.sha256((ROOT/'artifact_v0.1.1/SOS14.json').read_bytes()).hexdigest()}
 write_generated(ROOT/'lean/SOS_COMPRESSION_MANIFEST.json',json.dumps(manifest,indent=2)+'\n')
 print('Generated',len(cores),'phase cores and',len(go),'weighted corepair certificates')
 return PH,cores,go,gp,gv,gdict,maps,origins
if __name__=='__main__':COMPRESSION=gen_compressed()

def gen_features(ctx):
 from collections import defaultdict
 PH,cores,go,gp,gv,gdict,maps,origins=ctx
 def canon(w):
  ps=[[],[]]
  for r,k in w:
   k%=5
   if not k:continue
   a=ps[r%2]
   if a and a[-1][0]==r:k=(a.pop()[1]+k)%5
   if k:a.append((r,k))
  return tuple(ps[0]+ps[1])
 def adj(w):return canon([(r,5-k) for r,k in reversed(w)])
 def word(a):
  left=[(r//2,k) for r,k in a if r%2==0];right=[(r//2,k) for r,k in a if r%2==1]
  return '⟨['+', '.join(f'({r}, {k})' for r,k in left)+'], ['+', '.join(f'({r}, {k})' for r,k in right)+']⟩'
 fibers=defaultdict(list);termfeatures=[[] for _ in range(14)]
 for j,t in enumerate(data['terms']):
  for i,a in enumerate(t['polynomial']):
   for k,b in enumerate(t['polynomial']):
    w=tuple(map(tuple,a['word']));v=tuple(map(tuple,b['word']));p,pe=maps[j][i];q,qe=maps[j][k];feat=(gdict[j,p,q],(qe-pe)%20)
    for ww in [canon(adj(w)+v),canon(v+adj(w))]:
     fibers[ww].append(feat);termfeatures[j].append((ww,feat))
 target={():T([0,0,1]+[0]*21,5)}
 for r in range(4):
  for k in range(1,5):
   c=T()
   for z in range(5):c=c+PH[(-4*k*z)%20]*T(2-z,10)
   if r==3:c=c*PH[(-4*k)%20]
   w=canon(((r,k),((r+1)%4,5-k)))
   target[w]=target.get(w,T())+-c
 words=sorted(set(fibers)|set(target))
 assert len(words)==273
 for w in words:
  total=T()
  for g,e in fibers[w]:total=total+gv[g]*PH[e]
  assert total==target.get(w,T()),('nonzero residual',w)
 out=ROOT/'lean/CGLMP5'
 def header(imps):return '\n'.join('import CGLMP5.'+p for p in imps)+'\n\nnamespace CGLMP5.SOSFinite\n\nset_option Elab.async false\nset_option maxHeartbeats 0\nset_option maxRecDepth 200000\n\n'
 def save(name,s):
  p=out/(name+'.lean'); text=s+'\nend CGLMP5.SOSFinite\n'
  write_generated(p,text)
 body=header(['SOSCompressedData'])
 body+='abbrev Feature := Fin 135 × Fin 20\n\n'
 body+='def computedFeatures (j : Fin 14) : List (Word × Feature) :=\n  (localTerms j).flatMap fun t => (localTerms j).flatMap fun u =>\n      let f : Feature := (gramIndex j (localCore j t.2.1) (localCore j u.2.1), phaseDifference t.2.2 u.2.2)\n      [(Word.mul (Word.adjoint t.1) u.1, f), (Word.mul u.1 (Word.adjoint t.1), f)]\n\n'
 body+='def wordAt (j : Fin 273) : Word :=\n  match j.val with\n'+''.join(f'  | {i} => {word(w)}\n' for i,w in enumerate(words))+'  | _ => Word.one\n\n'
 windex={w:i for i,w in enumerate(words)}
 body+='def indexedFeatures (j : Fin 14) : List (Fin 273 × Feature) :=\n  match j.val with\n'+''.join(f'  | {j} => ['+', '.join(f'({windex[w]}, {g}, {e})' for w,(g,e) in fs)+']\n' for j,fs in enumerate(termfeatures))+'  | _ => []\n\n'
 body+='def allIndexedFeatures : List (Fin 273 × Feature) := (List.finRange 14).flatMap indexedFeatures\n\n'
 body+='def expandedFeatures : List (Word × Feature) := allIndexedFeatures.map fun t => (wordAt t.1, t.2)\n\n'
 body+='def fiber (j : Fin 273) : List Feature :=\n  match j.val with\n'+''.join(f'  | {i} => ['+', '.join(f'({g}, {e})' for g,e in fibers[w])+']\n' for i,w in enumerate(words))+'  | _ => []\n\n'
 body+='def targetAt (j : Fin 273) : Scalar :=\n  match j.val with\n'+''.join(f'  | {i} => {lean(target[w])}\n' for i,w in enumerate(words) if w in target)+'  | _ => Scalar.zero\n\n'
 body+='def featureValue (f : Feature) : Scalar := Scalar.mul (gram f.1) (phase f.2)\n\n'
 body+='def sumScalars (xs : List Scalar) : Scalar := xs.foldr Scalar.add Scalar.zero\n\n'
 body+='def fiberValue (w : Fin 273) : Scalar := sumScalars ((fiber w).map featureValue)\n\n'
 body+='def reflectedPolynomial : List (Word × Scalar) := expandedFeatures.map fun t => (t.1, featureValue t.2)\n\n'
 body+='def targetPolynomial : List (Word × Scalar) := ['+',\n  '.join('('+word(w)+', '+lean(v)+')' for w,v in target.items())+']\n\n'
 body+='def targetIndexedPolynomial : List (Fin 273 × Scalar) := ['+',\n  '.join(f'({windex[w]}, '+lean(v)+')' for w,v in target.items())+']\n\n'
 save('SOSFeatureData',body)
 for j in range(14):
  check=header(['SOSFeatureData'])+f'theorem feature_expansion_{j:02} : computedFeatures {j} = ((indexedFeatures {j}).map fun t => (wordAt t.1, t.2)) := by\n  decide +kernel\n'
  save(f'SOSExpansion{j:02}',check)
 write_generated(ROOT/'lean/SOS_FEATURE_MANIFEST.json',json.dumps({'canonical_sha256':hashlib.sha256((ROOT/'artifact_v0.1.1/SOS14.json').read_bytes()).hexdigest(),'word_count':len(words),'feature_count':sum(map(len,fibers.values())),'largest_fiber':max(map(len,fibers.values())),'nonzero_target_words':len(target),'words':words},indent=2)+'\n')
 print('Generated273word fibers; external generator residual zero (Lean checks mandatory)')
 return words,fibers,target,termfeatures
if __name__=='__main__':FEATURES=gen_features(COMPRESSION)

def gen_integer_residuals(ctx,features):
 PH,cores,go,gp,gv,gdict,maps,origins=ctx
 words,fibers,target,termfeatures=features
 out=ROOT/'lean/CGLMP5'
 def header(imps):return '\n'.join('import CGLMP5.'+p for p in imps)+'\n\nnamespace CGLMP5.SOSFinite\n\nset_option Elab.async false\nset_option maxHeartbeats 0\nset_option maxRecDepth 200000\n\n'
 def save(name,s):
  p=out/(name+'.lean'); text=s+'\nend CGLMP5.SOSFinite\n'
  write_generated(p,text)
 def vect(v):return '!['+', '.join(str(n) for n in v)+']'
 def mdef(name,n,typ,vals):return f'def {name} (j : Fin {n}) : {typ} :=\n  match j.val with\n'+''.join(f'  | {i} => {v}\n' for i,v in enumerate(vals))+f'  | _ => {vals[0]}\n\n'
 tv=[target.get(w,T()) for w in words]
 ds=[math.lcm(tv[i].d,*[gv[g].d*PH[e].d for g,e in fibers[w]]) for i,w in enumerate(words)]
 body=header(['SOSFeatureData'])
 body+=mdef('gramNumerator',135,'Fin 24 → ℤ',[vect(v.n) for v in gv])
 body+=mdef('gramDenominator',135,'ℕ',[str(v.d) for v in gv])
 body+=mdef('phaseNumerator',20,'Fin 24 → ℤ',[vect(v.n) for v in PH])
 body+=mdef('phaseDenominator',20,'ℕ',[str(v.d) for v in PH])
 body+=mdef('targetNumerator',273,'Fin 24 → ℤ',[vect(v.n) for v in tv])
 body+=mdef('targetDenominator',273,'ℕ',[str(v.d) for v in tv])
 body+=mdef('commonDenominator',273,'ℕ',[str(v) for v in ds])
 soundness='import Mathlib.Data.Fintype.Fin\n'+header(['SOSIntegerData']).replace('\n\nnamespace CGLMP5.SOSFinite\n\n','\nimport Mathlib.Tactic.FinCases\n\nnamespace CGLMP5.SOSFinite\n')
 for name,n in [('gram',135),('phase',20),('target',273)]:
  rhs='targetAt' if name=='target' else name
  proof='  funext k\n  revert i k\n  decide +kernel\n' if name=='target' else '  funext k\n  fin_cases i <;> first | rfl | (fin_cases k <;> simp [targetAt, targetNumerator, targetDenominator, Scalar.zero, Scalar.ofCanonical])\n'
  soundness+=f'theorem {name}_as_canonical (i : Fin {n}) : {rhs} i = Scalar.ofCanonical ({name}Numerator i) ({name}Denominator i) := by\n'+proof+'\n'
 save('SOSIntegerDataSoundness',soundness+'\n')
 body+='theorem all_denominators_positive : (∀i, 0 < gramDenominator i) ∧ (∀i, 0 < phaseDenominator i) ∧ (∀i, 0 < targetDenominator i) ∧ (∀i, 0 < commonDenominator i) := by\n  decide +kernel\n'
 save('SOSIntegerData',body)
 body=header(['SOSIntegerData','ScalarIntegerArithmetic'])
 body+='def integerNumerator (w : Fin 273) (k : Fin 24) : ℤ :=\n  ((fiber w).map fun f =>\n    ((commonDenominator w / (gramDenominator f.1 * phaseDenominator f.2) : ℕ) : ℤ) *\n      Scalar.mulNumerator (gramNumerator f.1) (phaseNumerator f.2) k).sum\n'
 body+='\n/-- The exact coordinate proposition, kept named during finite-family assembly. -/\ndef integerCoordinateClaim (w : Fin 273) (k : Fin 24) : Prop :=\n  integerNumerator w k * (targetDenominator w : Int) =\n    targetNumerator w k * (commonDenominator w : Int)\n\n/-- All24exact coordinates for one ordered normal word. -/\ndef integerResidualClaim (w : Fin 273) : Prop := ∀ k : Fin 24, integerCoordinateClaim w k\n'

 save('SOSIntegerResidualDefinitions',body)
 # Fiber proofs are separate, so no Rat residual normalization remains on this path.
 for i in range(273):
  body=header(['SOSFeatureData'])
  body+=f'theorem index_fiber_{i:03} : ((allIndexedFeatures.filter fun t => t.1 = {i}).map Prod.snd) = fiber {i} := by\n  decide +kernel\n'
  save(f'SOSIndexFiber{i:03}',body)
 body=header([f'SOSIndexFiber{i:03}' for i in range(273)])
 family='(fun k => Fin.elim0 k)'
 for i in reversed(range(273)):family=f'(Fin.cases index_fiber_{i:03} {family})'
 body+='theorem index_fiber_checked : ∀ (i : Fin 273), ((allIndexedFeatures.filter fun t => t.1 = i).map Prod.snd) = fiber i :=\n  '+family+'\n\n'
 save('SOSIndexFiberChecks',body)
 print('Generated denominator-cleared273integer residuals; maximumDbits',max(d.bit_length() for d in ds))
if __name__=='__main__':gen_integer_residuals(COMPRESSION,FEATURES)
