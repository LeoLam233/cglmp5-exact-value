import CGLMP5.SOSFeatureData

namespace CGLMP5.SOSFinite

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem feature_expansion_03 : computedFeatures 3 = ((indexedFeatures 3).map fun t => (wordAt t.1, t.2)) := by
  decide +kernel

end CGLMP5.SOSFinite
