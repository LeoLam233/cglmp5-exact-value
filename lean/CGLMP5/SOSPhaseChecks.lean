import CGLMP5.SOSPhaseBaseChecks
import CGLMP5.SOSPhasePair00
import CGLMP5.SOSPhasePair01
import CGLMP5.SOSPhasePair02
import CGLMP5.SOSPhasePair03
import CGLMP5.SOSPhasePair04
import CGLMP5.SOSPhasePair05
import CGLMP5.SOSPhasePair06
import CGLMP5.SOSPhasePair07
import CGLMP5.SOSPhasePair08
import CGLMP5.SOSPhasePair09
import CGLMP5.SOSPhasePair10
import CGLMP5.SOSPhasePair11
import CGLMP5.SOSPhasePair12
import CGLMP5.SOSPhasePair13
import CGLMP5.SOSPhasePair14
import CGLMP5.SOSPhasePair15
import CGLMP5.SOSPhasePair16
import CGLMP5.SOSPhasePair17
import CGLMP5.SOSPhasePair18
import CGLMP5.SOSPhasePair19

namespace CGLMP5.SOSFinite
set_option Elab.async false
set_option maxRecDepth 200000

/-- The full phase-pair table, assembled without reevaluating its checked numeric leaves. -/
theorem phase_pair_check : ∀ (p q : Fin 20) (k : Fin 24),
    Scalar.mul (Scalar.conj (phase p)) (phase q) k = phase (phaseDifference p q) k :=
  Fin.cases phase_pair_row_0 (Fin.cases phase_pair_row_1 (Fin.cases phase_pair_row_2 (Fin.cases phase_pair_row_3 (Fin.cases phase_pair_row_4 (Fin.cases phase_pair_row_5 (Fin.cases phase_pair_row_6 (Fin.cases phase_pair_row_7 (Fin.cases phase_pair_row_8 (Fin.cases phase_pair_row_9 (Fin.cases phase_pair_row_10 (Fin.cases phase_pair_row_11 (Fin.cases phase_pair_row_12 (Fin.cases phase_pair_row_13 (Fin.cases phase_pair_row_14 (Fin.cases phase_pair_row_15 (Fin.cases phase_pair_row_16 (Fin.cases phase_pair_row_17 (Fin.cases phase_pair_row_18 (Fin.cases phase_pair_row_19 ((fun p => Fin.elim0 p)))))))))))))))))))))
end CGLMP5.SOSFinite
