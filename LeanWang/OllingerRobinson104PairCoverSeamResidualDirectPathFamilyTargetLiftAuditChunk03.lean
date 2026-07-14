/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathFamilyTargetLiftAuditDefs

/-! Cached forward family-target lift audit for parents 44 through 55. -/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamResidualDirectPathFamilyTargetLiftAuditChunk03

open PairCoverSeamResidualDirectPathFamilyTargetLiftAudit

set_option linter.style.nativeDecide false in
theorem complete : forall parent : Index,
    44 <= parent.val -> parent.val < 56 -> checkParent parent = true := by
  native_decide

end PairCoverSeamResidualDirectPathFamilyTargetLiftAuditChunk03
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
