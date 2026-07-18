/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.ShadedCarrierBorderHierarchyData

/-! Native certificate for the finite concrete-node border hierarchy. -/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace ShadedCarrierBorderHierarchy

set_option linter.style.nativeDecide false in
theorem statesValid_eq_true : statesValid = true := by
  native_decide

set_option linter.style.nativeDecide false in
theorem closedValid_eq_true : closedValid = true := by
  native_decide

set_option linter.style.nativeDecide false in
theorem initialState_mem : state 0 0 0 ∈ states := by
  native_decide

set_option linter.style.nativeDecide false in
theorem cornerTransitionsValid_eq_true : cornerTransitionsValid = true := by
  native_decide

end ShadedCarrierBorderHierarchy
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
