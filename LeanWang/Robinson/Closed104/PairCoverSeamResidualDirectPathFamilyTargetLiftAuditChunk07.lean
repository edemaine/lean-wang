/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.PairCoverSeamResidualDirectPathFamilyTargetLiftAuditDefs

/-! Cached forward family-target lift audit for parents 92 through 103. -/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamResidualDirectPathFamilyTargetLiftAuditChunk07

open PairCoverSeamResidualDirectPathFamilyTargetLiftAudit

set_option linter.style.nativeDecide false in
theorem complete : forall parent : Index,
    92 <= parent.val -> parent.val < 104 -> checkParent parent = true := by
  native_decide

end PairCoverSeamResidualDirectPathFamilyTargetLiftAuditChunk07
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
