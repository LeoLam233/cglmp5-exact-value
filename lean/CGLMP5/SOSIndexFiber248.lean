import CGLMP5.SOSFeatureData

namespace CGLMP5.SOSFinite

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem index_fiber_248 : ((allIndexedFeatures.filter fun t => t.1 = 248).map Prod.snd) = fiber 248 := by
  decide +kernel

end CGLMP5.SOSFinite
