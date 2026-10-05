import CGLMP5.SOSFeatureData

namespace CGLMP5.SOSFinite

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem index_fiber_237 : ((allIndexedFeatures.filter fun t => t.1 = 237).map Prod.snd) = fiber 237 := by
  decide +kernel

end CGLMP5.SOSFinite
