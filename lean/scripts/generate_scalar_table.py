#!/usr/bin/env python3
"""Generate the 24-coordinate multiplication table and kernel-checked witnesses.

This script is not a trusted oracle. ScalarTable.lean proves each of its 576
basis products by explicit combinations of the four actual embedding relations.
"""
from functools import lru_cache
from pathlib import Path
from collections import defaultdict

def write_if_changed(path, text):
 p=Path(path)
 if not p.exists() or p.read_text()!=text:p.write_text(text)

def add(p,q,f=1):
 r=p.copy()
 for k,v in q.items():
  r[k]=r.get(k,0)+f*v
  if not r[k]:del r[k]
 return r

def mon(a,b,c,e):return {(a,b,c,e):1}

def times(p,q):
 r={}
 for a,v in p.items():
  for b,w in q.items():
   k=tuple(x+y for x,y in zip(a,b));r[k]=r.get(k,0)+v*w
 return {k:v for k,v in r.items() if v}

@lru_cache(None)
def red(a,b,c,e):
 p=[{}, {}, {}, {}]
 if e>=2:
  terms=[((a,b,c,e-2),-1)];rel=3;rest=(a,b,c,e-2)
 elif c>=2:
  terms=[((a,b,c-2,e),10),((a+1,b,c-2,e),2)];rel=2;rest=(a,b,c-2,e)
 elif b>=3:
  terms=[((a+1,b-1,c,e),5),((a,b-2,c,e),100),((a+1,b-2,c,e),-20),((a,b-3,c,e),500),((a+1,b-3,c,e),-200)];rel=1;rest=(a,b-3,c,e)
 elif a>=2:
  terms=[((a-2,b,c,e),5)];rel=0;rest=(a-2,b,c,e)
 else:return ({(a,b,c,e):1},p)
 r={};p[rel]=mon(*rest)
 for power,v in terms:
  q,w=red(*power);r=add(r,q,v)
  p=[add(pp,ww,v) for pp,ww in zip(p,w)]
 return r,p

def idx(i):return(i%2,(i//2)%3,(i//6)%2,i//12)
def ix(k):a,b,c,e=k;return a+2*b+6*c+12*e

def pp(p):
 if not p:return '0'
 ts=[]
 for k,v in sorted(p.items()):
  fs=[]
  for n,e in zip(['(s : ℂ)','(x : ℂ)','(u : ℂ)','Complex.I'],k):
   if e:fs.append(n if e==1 else f'{n}^{e}')
  term='*'.join(fs) if fs else '1'
  if v!=1:term=f'({v})*{term}'
  ts.append(term)
 return '('+' + '.join(ts)+')'

table={};witness={}
for i in range(24):
 for j in range(24):
  r,w=red(*[a+b for a,b in zip(idx(i),idx(j))]);table[i,j]={ix(k):v for k,v in r.items()};witness[i,j]=w
out=['import CGLMP5.ScalarSyntax','','/-! Generated sparse integer table; its complete soundness is proved by ScalarTable. -/','','namespace CGLMP5.Scalar','','def mulTerms (k : Fin 24) : List (Fin 24 × Fin 24 × ℤ) :=','  match k.val with']
for k in range(24):
 terms=[f'({i}, {j}, {r[k]})' for (i,j),r in table.items() if k in r]
 out.append(f'  | {k} => ['+', '.join(terms)+']')
out+=['  | _ => []','','def mul (a b : Scalar) : Scalar := fun k =>','  ((mulTerms k).map fun t => a t.1 * b t.2.1 * (t.2.2 : ℚ)).sum','','def mulCoeff (i j k : Fin 24) : ℤ :=','  ((mulTerms k).map fun t => if t.1 = i ∧ t.2.1 = j then t.2.2 else 0).sum','','end CGLMP5.Scalar','']
write_if_changed('CGLMP5/ScalarTableData.lean','\n'.join(out))
# Generated reduction witness proofs are split by input row.
for i in range(24):
 out=['import CGLMP5.ScalarProductsBase','import Mathlib.Tactic.LinearCombination','','namespace CGLMP5.Scalar','','set_option Elab.async false','set_option maxRecDepth 20000','set_option maxHeartbeats 2000000','']
 for j in range(24):
  r=table[i,j];vec='!['+', '.join(str(r.get(k,0)) for k in range(24))+']'
  out += [f'private lemma coeff_{i}_{j} (k : Fin 24) : mulCoeff {i} {j} k = ({vec} : Fin 24 → ℤ) k := by', '  fin_cases k <;> decide +kernel','']
 out += [f'lemma mulCoeff_sound_row_{i} (j : Fin 24) :',f'    (∑ k : Fin 24, (mulCoeff {i} j k : ℂ)*basisEval k) = basisEval {i}*basisEval j := by','  fin_cases j']
 for j in range(24):
  w=witness[i,j];args=[]
  for p,h in zip(w,['sC_sq','xC_cubic','uC_sq','Complex.I_sq']):
   if p:args.append(f'-{pp(p)} * {h}')
  out.append(f'  · change (∑ k : Fin 24, (mulCoeff {i} {j} k : ℂ)*basisEval k) = basisEval {i}*basisEval {j}')
  out.append(f'    simp only [coeff_{i}_{j}]')
  out.append('    norm_num [basisEval, Fin.sum_univ_succ]')
  if not args:out.append('    <;> ring')
  else:out.append('    <;> linear_combination '+' + '.join(args))
 out+=['','end CGLMP5.Scalar','']
 write_if_changed(f'CGLMP5/ScalarTableRow{i:02d}.lean','\n'.join(out))
out=[f'import CGLMP5.ScalarTableRow{i:02d}' for i in range(24)]
out+=['','namespace CGLMP5.Scalar','','lemma mulCoeff_sound (i j : Fin 24) :','    (∑ k : Fin 24, (mulCoeff i j k : ℂ)*basisEval k) = basisEval i* basisEval j := by','  fin_cases i']
for i in range(24):out.append(f'  · exact mulCoeff_sound_row_{i} j')
out+=['','end CGLMP5.Scalar','']
write_if_changed('CGLMP5/ScalarTable.lean','\n'.join(out))
