/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.PairCoverSeamResidualDirectPathExactPredecessorAuditDefs

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamResidualDirectPathExactPredecessorAuditChunk01

open PairCoverSeamResidualDirectPathExactPredecessorAudit

set_option linter.style.nativeDecide false in
theorem complete : ∀ parent : Index,
    13 ≤ parent.val → parent.val < 26 → checkParent parent = true := by
  native_decide

end PairCoverSeamResidualDirectPathExactPredecessorAuditChunk01
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
