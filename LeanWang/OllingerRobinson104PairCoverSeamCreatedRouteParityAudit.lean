/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamCreatedRouteParityAuditChunk00
import LeanWang.OllingerRobinson104PairCoverSeamCreatedRouteParityAuditChunk01
import LeanWang.OllingerRobinson104PairCoverSeamCreatedRouteParityAuditChunk02
import LeanWang.OllingerRobinson104PairCoverSeamCreatedRouteParityAuditChunk03
import LeanWang.OllingerRobinson104PairCoverSeamCreatedRouteParityAuditChunk04
import LeanWang.OllingerRobinson104PairCoverSeamCreatedRouteParityAuditChunk05
import LeanWang.OllingerRobinson104PairCoverSeamCreatedRouteParityAuditChunk06
import LeanWang.OllingerRobinson104PairCoverSeamCreatedRouteParityAuditChunk07

/-! Assemble the cached exact-parity audit for all 104 closed tiles. -/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamCreatedRouteParityAudit

theorem complete (parent : Index) : checkParent parent = true := by
  by_cases h13 : parent.val < 13
  · exact complete00 parent h13
  by_cases h26 : parent.val < 26
  · exact complete01 parent (by omega) h26
  by_cases h39 : parent.val < 39
  · exact complete02 parent (by omega) h39
  by_cases h52 : parent.val < 52
  · exact complete03 parent (by omega) h52
  by_cases h65 : parent.val < 65
  · exact complete04 parent (by omega) h65
  by_cases h78 : parent.val < 78
  · exact complete05 parent (by omega) h78
  by_cases h91 : parent.val < 91
  · exact complete06 parent (by omega) h91
  · exact complete07 parent (by omega)

end PairCoverSeamCreatedRouteParityAudit
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
