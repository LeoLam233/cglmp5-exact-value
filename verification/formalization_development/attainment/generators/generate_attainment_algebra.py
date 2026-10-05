#!/usr/bin/env python3
"""Emit kernel-checkable ring certificates, never an external proof oracle.
Schmidt polynomial input transcribed from canonical artifact_v0.1.1/SOS14.json.
All generated identities are checked by Lean linear_combination.
"""
from pathlib import Path
import sympy as S
m,u,s=S.symbols('m u s')
gens=[m**3-s*m**2-(4-S.Rational(4,5)*s)*m-4+S.Rational(8,5)*s,u**2-10-2*s,s**2-5]
f1=u*(5-s)/20;f2=(s-1)/2;f3=u*s/10;f4=(s+1)/2
a=u*(5+s+13*m+6*s*m-5*m*m-2*s*m*m)/4
b=(-18-8*s-55*m-24*s*m+20*m*m+9*s*m*m)/2
def lean(p): return str(S.expand(p)).replace('**','^')
def cert(p):
 qs,r=S.reduced(S.expand(p),gens,m,u,s)
 assert r==0,r
 return ' + '.join(f'({lean(q)}) * {h}' for q,h in zip(qs,['hm','hu','hs']) if q!=0) or '0 * hs'
head='''import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-! Exact Schmidt algebra for the full CGLMP5 attaining strategy.
The polynomial coefficients are the canonical SOS14.json gamma records,
rewritten with x=5m. Every displayed certificate is kernel-visible. -/
namespace CGLMP5.Attainment
noncomputable section

def f1 (s u : ℝ) : ℝ := u * (5 - s) / 20
def f2 (s : ℝ) : ℝ := (s - 1) / 2
def f3 (s u : ℝ) : ℝ := u * s / 10
def f4 (s : ℝ) : ℝ := (s + 1) / 2

def coeffA (m s u : ℝ) : ℝ :=
  u * (5 + s + 13*m + 6*s*m - 5*m^2 - 2*s*m^2) / 4

def coeffB (m s : ℝ) : ℝ :=
  (-18 - 8*s - 55*m - 24*s*m + 20*m^2 + 9*s*m^2) / 2

def schmidtDenom (m s u : ℝ) : ℝ := m * (m - f2 s) - 2 * (f1 s u)^2

def schmidtNumer (m s u : ℝ) : ℝ := m * (f1 s u + f3 s u) + 2 * f1 s u * f2 s

variable (m s u : ℝ)
variable (hs : s^2 = 5) (hu : u^2 = 10 + 2*s)
variable (hm : m^3 = s*m^2 + (4 - 4*s/5)*m + 4 - 8*s/5)

'''
lemmas=[
 ('f1_mul_u','f1 s u * u = 2',f1*u-2,['f1']),
 ('two_s_mul_f3','2 * s * f3 s u = u',2*s*f3-u,['f3']),
 ('f1_sq','(f1 s u)^2 = (5-s)/10',f1*f1-(5-s)/10,['f1']),
 ('coeffA_mul_denom','coeffA m s u * schmidtDenom m s u = schmidtNumer m s u',a*(m*(m-f2)-2*f1*f1)-(m*(f1+f3)+2*f1*f2),['coeffA','schmidtDenom','schmidtNumer','f1','f2','f3']),
 ('row_zero','m = f4 s + (f1 s u + f3 s u) * coeffA m s u + f2 s * coeffB m s',m-f4-(f1+f3)*a-f2*b,['f4','f1','f3','coeffA','f2','coeffB']),
 ('row_one','m * coeffA m s u = f1 s u + f3 s u + f2 s * coeffA m s u + f1 s u * coeffB m s',m*a-f1-f3-f2*a-f1*b,['coeffA','f1','f3','f2','coeffB']),
 ('row_two','m * coeffB m s = 2 * f2 s + 2 * f1 s u * coeffA m s u',m*b-2*f2-2*f1*a,['coeffB','f2','f1','coeffA'])]
out=head
for name,stmt,p,defs in lemmas:
 out+=f'theorem {name} : {stmt} := by\n  unfold '+ ' '.join(defs)+'\n  linear_combination '+cert(p)+'\n\n'
out+='end\nend CGLMP5.Attainment\n'
Path('CGLMP5/AttainmentAlgebra.lean').write_text(out)
