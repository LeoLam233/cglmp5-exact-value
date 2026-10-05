import CGLMP5.SOSFeatureData

namespace CGLMP5.SOSFinite

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem index_fiber_035 : ((allIndexedFeatures.filter fun t => t.1 = 35).map Prod.snd) = fiber 35 := by
  decide +kernel

end CGLMP5.SOSFinite
