import CGLMP5.SOSFeatureData

namespace CGLMP5.SOSFinite

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem index_fiber_028 : ((allIndexedFeatures.filter fun t => t.1 = 28).map Prod.snd) = fiber 28 := by
  decide +kernel

end CGLMP5.SOSFinite
