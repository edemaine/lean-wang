/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathFamilyTargetLiftAuditChunk00
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathFamilyTargetLiftAuditChunk01
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathFamilyTargetLiftAuditChunk02
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathFamilyTargetLiftAuditChunk03
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathFamilyTargetLiftAuditChunk04
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathFamilyTargetLiftAuditChunk05
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathFamilyTargetLiftAuditChunk06
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathFamilyTargetLiftAuditChunk07

/-! Assemble the cached forward family-target lift audit for all 104 parents. -/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamResidualDirectPathFamilyTargetLiftAudit

theorem complete (parent : Index) : checkParent parent = true := by
  by_cases h20 : parent.val < 20
  · exact PairCoverSeamResidualDirectPathFamilyTargetLiftAuditChunk00.complete
      parent (by omega) h20
  by_cases h32 : parent.val < 32
  · exact PairCoverSeamResidualDirectPathFamilyTargetLiftAuditChunk01.complete
      parent (by omega) h32
  by_cases h44 : parent.val < 44
  · exact PairCoverSeamResidualDirectPathFamilyTargetLiftAuditChunk02.complete
      parent (by omega) h44
  by_cases h56 : parent.val < 56
  · exact PairCoverSeamResidualDirectPathFamilyTargetLiftAuditChunk03.complete
      parent (by omega) h56
  by_cases h68 : parent.val < 68
  · exact PairCoverSeamResidualDirectPathFamilyTargetLiftAuditChunk04.complete
      parent (by omega) h68
  by_cases h80 : parent.val < 80
  · exact PairCoverSeamResidualDirectPathFamilyTargetLiftAuditChunk05.complete
      parent (by omega) h80
  by_cases h92 : parent.val < 92
  · exact PairCoverSeamResidualDirectPathFamilyTargetLiftAuditChunk06.complete
      parent (by omega) h92
  exact PairCoverSeamResidualDirectPathFamilyTargetLiftAuditChunk07.complete
    parent (by omega) parent.isLt

end PairCoverSeamResidualDirectPathFamilyTargetLiftAudit
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
