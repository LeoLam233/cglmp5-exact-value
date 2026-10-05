import CGLMP5.SOSFeatureData

namespace CGLMP5.SOSFinite

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem feature_expansion_08 : computedFeatures 8 = ((indexedFeatures 8).map fun t => (wordAt t.1, t.2)) := by
  decide +kernel

end CGLMP5.SOSFinite
