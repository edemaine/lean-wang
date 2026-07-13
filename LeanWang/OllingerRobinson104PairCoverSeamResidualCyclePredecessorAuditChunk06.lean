/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamResidualCyclePredecessorAuditDefs

/-! Cached residual-cycle predecessor audit for parents 78 through 90. -/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace PairCoverSeamResidualCyclePredecessorAuditChunk06

open PairCoverSeamResidualCyclePredecessorAudit

set_option linter.style.nativeDecide false in
theorem complete : ∀ parent : Index,
    78 ≤ parent.val → parent.val < 91 → checkParent parent = true := by
  native_decide

end PairCoverSeamResidualCyclePredecessorAuditChunk06
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
