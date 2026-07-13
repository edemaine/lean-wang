/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamResidualCanonicalAncestorBaseAuditDefs

/-! Cached even and odd base-ancestor checks for parents 76 through 79. -/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamResidualCanonicalAncestorBaseAudit

set_option linter.style.nativeDecide false in
theorem completeEven19 : ∀ parent : Index, 76 ≤ parent.val → parent.val < 80 →
    checkParent .even parent = true := by
  native_decide

set_option linter.style.nativeDecide false in
theorem completeOdd19 : ∀ parent : Index, 76 ≤ parent.val → parent.val < 80 →
    checkParent .odd parent = true := by
  native_decide

end PairCoverSeamResidualCanonicalAncestorBaseAudit
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
