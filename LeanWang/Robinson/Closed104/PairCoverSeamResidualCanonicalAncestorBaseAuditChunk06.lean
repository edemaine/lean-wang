/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.PairCoverSeamResidualCanonicalAncestorBaseAuditDefs

/-! Cached even and odd base-ancestor checks for parents 24 through 27. -/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamResidualCanonicalAncestorBaseAudit

set_option linter.style.nativeDecide false in
theorem completeEven06 : ∀ parent : Index, 24 ≤ parent.val → parent.val < 28 →
    checkParent .even parent = true := by
  native_decide

set_option linter.style.nativeDecide false in
theorem completeOdd06 : ∀ parent : Index, 24 ≤ parent.val → parent.val < 28 →
    checkParent .odd parent = true := by
  native_decide

end PairCoverSeamResidualCanonicalAncestorBaseAudit
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
