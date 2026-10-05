import CGLMP5.SOSFeatureData

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

/-- The literal seventeen target terms and the indexed representation are identical. -/
theorem target_index_word_map :
    targetIndexedPolynomial.map (fun t => (wordAt t.1, t.2)) = targetPolynomial := by
  rfl

/-- Target extraction is itself kernel checked, independently of the compact expansion. -/
theorem target_index_coefficients : ∀ (i : Fin 273) (k : Fin 24),
    sumScalars (((targetIndexedPolynomial.filter fun t => t.1 = i).map Prod.snd)) k =
      targetAt i k := by
  decide +kernel

end CGLMP5.SOSFinite
