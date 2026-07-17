/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.ShadedSubstitutionData

/-!
# Native checks for the finite-state red-shade substitution

This module isolates the expensive executable checks from their proof-facing
wrappers so changes to the latter reuse the cached certificates.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace ShadedSubstitution

set_option maxRecDepth 20000

set_option linter.style.nativeDecide false in
theorem reachableClosed_eq_true : reachableClosed = true := by
  native_decide

set_option linter.style.nativeDecide false in
theorem reachablePairsValid_eq_true : reachablePairsValid = true := by
  native_decide

set_option linter.style.nativeDecide false in
theorem reachableStructureValid_eq_true : reachableStructureValid = true := by
  native_decide

end ShadedSubstitution
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
