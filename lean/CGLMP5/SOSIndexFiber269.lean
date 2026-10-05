import CGLMP5.SOSFeatureData

namespace CGLMP5.SOSFinite

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem index_fiber_269 : ((allIndexedFeatures.filter fun t => t.1 = 269).map Prod.snd) = fiber 269 := by
  decide +kernel

end CGLMP5.SOSFinite
