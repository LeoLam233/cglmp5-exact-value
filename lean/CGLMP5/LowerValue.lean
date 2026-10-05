import CGLMP5.Attainment
import CGLMP5.StrategyTransport

namespace CGLMP5
universe u v

/-- The explicit physical attainer belongs to the complete model in every universe. -/
theorem mu_mem_quantumValues : mu ∈ quantumValues.{u,v} := by
  refine ⟨Attainment.explicitStrategy.lift, ?_⟩
  rw [Strategy.lift_value, Attainment.explicitStrategy_value]

theorem quantumValues_nonempty : (quantumValues.{u,v}).Nonempty :=
  ⟨mu, mu_mem_quantumValues⟩

/-- Every claimed uniform bound for the full model must be at least the physical attained value. -/
theorem mu_le_every_uniform_bound (b : ℝ)
    (h : ∀ S : Strategy.{u,v}, S.value ≤ b) : mu ≤ b := by
  have hb := h Attainment.explicitStrategy.lift
  rwa [Strategy.lift_value, Attainment.explicitStrategy_value] at hb

end CGLMP5
