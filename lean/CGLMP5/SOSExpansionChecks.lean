import CGLMP5.SOSExpansion00
import CGLMP5.SOSExpansion01
import CGLMP5.SOSExpansion02
import CGLMP5.SOSExpansion03
import CGLMP5.SOSExpansion04
import CGLMP5.SOSExpansion05
import CGLMP5.SOSExpansion06
import CGLMP5.SOSExpansion07
import CGLMP5.SOSExpansion08
import CGLMP5.SOSExpansion09
import CGLMP5.SOSExpansion10
import CGLMP5.SOSExpansion11
import CGLMP5.SOSExpansion12
import CGLMP5.SOSExpansion13

namespace CGLMP5.SOSFinite

theorem feature_expansion_checked : ∀ (j : Fin 14),
    computedFeatures j = (indexedFeatures j).map (fun t => (wordAt t.1, t.2)) :=
  (Fin.cases feature_expansion_00 (Fin.cases feature_expansion_01 (Fin.cases feature_expansion_02 (Fin.cases feature_expansion_03 (Fin.cases feature_expansion_04 (Fin.cases feature_expansion_05 (Fin.cases feature_expansion_06 (Fin.cases feature_expansion_07 (Fin.cases feature_expansion_08 (Fin.cases feature_expansion_09 (Fin.cases feature_expansion_10 (Fin.cases feature_expansion_11 (Fin.cases feature_expansion_12 (Fin.cases feature_expansion_13 (fun k => Fin.elim0 k)))))))))))))))

end CGLMP5.SOSFinite
