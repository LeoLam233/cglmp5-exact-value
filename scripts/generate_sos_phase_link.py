#!/usr/bin/env python3
"""Generate source-bound semantic links; Lean checks every definitional list and supplied equality."""
from pathlib import Path
import re
root=Path(__file__).resolve().parents[1]/'lean'/'CGLMP5'
s=(root/'SOSCompressedData.lean').read_text()
block=s.split('def phaseTerms')[1].split('def localCore')[0]
rows={int(j):re.findall(r'⟨(⟨.*?⟩), (\d+), (\d+)⟩', line) for j,line in re.findall(r'^  \| (\d+) => (.*)$',block,re.M)}
base='''import CGLMP5.ScalarDefs
import CGLMP5.SOSGramSemantics
import CGLMP5.SOSCompressedData
namespace CGLMP5.SOSFinite
noncomputable section
lemma phase_zero_eval : Scalar.eval (phase 0) = 1 := by
  have h : phase 0 = Scalar.ofRat 1 := by
    funext k
    fin_cases k <;> norm_num [phase, Scalar.ofRat, Scalar.ofCanonical]
  rw [h, Scalar.eval_ofRat]
  norm_num
end
end CGLMP5.SOSFinite
'''
(root/'SOSPhaseLinkBase.lean').write_text(base)
for j,terms in rows.items():
 out=[f'import CGLMP5.SOSCompressedCheck{j:02d}', 'import CGLMP5.SOSPhaseLinkBase', '\nnamespace CGLMP5.SOSFinite\nnoncomputable section', 'set_option maxRecDepth 200000\nset_option maxHeartbeats 2000000',f'lemma source_phase_polynomial_{j}', '(hmul : ∀ a b : Scalar, Scalar.eval (Scalar.mul a b) = Scalar.eval a * Scalar.eval b) :' ,f'    SOS.phasePolynomial (fun c => Scalar.eval (core (localCore {j} c)))',f'      (fun p => Scalar.eval (phase p)) (localTerms {j}) =',f'      (CanonicalData.polynomial {j}).map (fun t => (t.1, Scalar.eval t.2)) := by']
 for i,_ in enumerate(terms):
  out.append(f'  have h{i} := congrArg Scalar.eval (funext source_phase_{j}_{i})')
 out.append('  simp only [hmul] at '+ ' '.join('h'+str(i) for i in range(len(terms))))
 lhs=',\n    '.join(f'({w}, Scalar.eval (core {c}) * Scalar.eval (phase {p}))' for w,c,p in terms)
 rhs=',\n    '.join(f'({w}, Scalar.eval (canonicalCoefficient {j} {i}))' for i,(w,c,p) in enumerate(terms))
 out += ['  change (['+lhs+'] : SOS.Polynomial) =\n    ['+rhs+']', '  simp only ['+', '.join('h'+str(i) for i in range(len(terms)))+', phase_zero_eval, mul_one]', '\nend\nend CGLMP5.SOSFinite\n']
 (root/f'SOSPhaseLink{j:02d}.lean').write_text('\n'.join(out))
imports='import CGLMP5.Scalar\n'+'\n'.join(f'import CGLMP5.SOSPhaseLink{j:02d}' for j in range(14))
agg='''
namespace CGLMP5.SOSFinite
noncomputable section
lemma phasePolynomial_eq_canonical (j : Fin 14) :
    SOS.phasePolynomial (fun c => Scalar.eval (core (localCore j c)))
      (fun p => Scalar.eval (phase p)) (localTerms j) =
      (CanonicalData.polynomial j).map (fun t => (t.1, Scalar.eval t.2)) := by
  fin_cases j
'''+''.join(f'  · exact source_phase_polynomial_{j} Scalar.eval_mul\n' for j in range(14))+'''end
end CGLMP5.SOSFinite
'''
(root/'SOSPhaseLink.lean').write_text(imports+'\n'+agg)
print('Generated14sourcepolynomial links; term counts:',[len(rows[j]) for j in range(14)])
