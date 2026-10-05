import CGLMP5.SOSFeatureData

namespace CGLMP5.SOSFinite

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem index_fiber_161 : ((allIndexedFeatures.filter fun t => t.1 = 161).map Prod.snd) = fiber 161 := by
  decide +kernel

end CGLMP5.SOSFinite
