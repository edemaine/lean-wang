/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5/5.6
-/
import LeanWang.Robinson.Closed104.ShadedCarrierBorderHierarchyData

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace ShadedCarrierBorderHierarchy

set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

theorem statesValid_group15 : (stateGroup15.all stateValid) = true := by
  decide +kernel

theorem closedValid_group15 : (stateGroup15.all fun candidate => (stateChildren candidate).all fun child => child ∈ states) = true := by
  decide +kernel

theorem cornerTransitionsValid_group15 : (stateGroup15.all fun candidate => (List.range 4).all fun childY => (List.range 4).all fun childX => cornerTransitionValid candidate childX childY) = true := by
  decide +kernel


end ShadedCarrierBorderHierarchy
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
