import CGLMP5.SOSFeatureData

namespace CGLMP5.SOSFinite

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem index_fiber_144 : ((allIndexedFeatures.filter fun t => t.1 = 144).map Prod.snd) = fiber 144 := by
  decide +kernel

end CGLMP5.SOSFinite
