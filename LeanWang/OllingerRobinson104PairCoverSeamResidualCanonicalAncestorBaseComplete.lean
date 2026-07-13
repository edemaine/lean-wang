/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamResidualCanonicalAncestorBaseAuditChunk00
import LeanWang.OllingerRobinson104PairCoverSeamResidualCanonicalAncestorBaseAuditChunk01
import LeanWang.OllingerRobinson104PairCoverSeamResidualCanonicalAncestorBaseAuditChunk02
import LeanWang.OllingerRobinson104PairCoverSeamResidualCanonicalAncestorBaseAuditChunk03
import LeanWang.OllingerRobinson104PairCoverSeamResidualCanonicalAncestorBaseAuditChunk04
import LeanWang.OllingerRobinson104PairCoverSeamResidualCanonicalAncestorBaseAuditChunk05
import LeanWang.OllingerRobinson104PairCoverSeamResidualCanonicalAncestorBaseAuditChunk06
import LeanWang.OllingerRobinson104PairCoverSeamResidualCanonicalAncestorBaseAuditChunk07
import LeanWang.OllingerRobinson104PairCoverSeamResidualCanonicalAncestorBaseAuditChunk08
import LeanWang.OllingerRobinson104PairCoverSeamResidualCanonicalAncestorBaseAuditChunk09
import LeanWang.OllingerRobinson104PairCoverSeamResidualCanonicalAncestorBaseAuditChunk10
import LeanWang.OllingerRobinson104PairCoverSeamResidualCanonicalAncestorBaseAuditChunk11
import LeanWang.OllingerRobinson104PairCoverSeamResidualCanonicalAncestorBaseAuditChunk12
import LeanWang.OllingerRobinson104PairCoverSeamResidualCanonicalAncestorBaseAuditChunk13
import LeanWang.OllingerRobinson104PairCoverSeamResidualCanonicalAncestorBaseAuditChunk14
import LeanWang.OllingerRobinson104PairCoverSeamResidualCanonicalAncestorBaseAuditChunk15
import LeanWang.OllingerRobinson104PairCoverSeamResidualCanonicalAncestorBaseAuditChunk16
import LeanWang.OllingerRobinson104PairCoverSeamResidualCanonicalAncestorBaseAuditChunk17
import LeanWang.OllingerRobinson104PairCoverSeamResidualCanonicalAncestorBaseAuditChunk18
import LeanWang.OllingerRobinson104PairCoverSeamResidualCanonicalAncestorBaseAuditChunk19
import LeanWang.OllingerRobinson104PairCoverSeamResidualCanonicalAncestorBaseAuditChunk20
import LeanWang.OllingerRobinson104PairCoverSeamResidualCanonicalAncestorBaseAuditChunk21
import LeanWang.OllingerRobinson104PairCoverSeamResidualCanonicalAncestorBaseAuditChunk22
import LeanWang.OllingerRobinson104PairCoverSeamResidualCanonicalAncestorBaseAuditChunk23
import LeanWang.OllingerRobinson104PairCoverSeamResidualCanonicalAncestorBaseAuditChunk24
import LeanWang.OllingerRobinson104PairCoverSeamResidualCanonicalAncestorBaseAuditChunk25

/-!
# Complete finite base for canonical residual-source ancestors

This module assembles the independently cached four-parent audits into one
all-parent theorem and applies the executable check's soundness theorem.
-/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamResidualCanonicalAncestorBaseAudit

open ShadedFreeLineRecurrence

private theorem completeEven (parent : Index) :
    checkParent .even parent = true := by
  by_cases h04 : parent.val < 4
  · exact completeEven00 parent h04
  by_cases h08 : parent.val < 8
  · exact completeEven01 parent (by omega) h08
  by_cases h12 : parent.val < 12
  · exact completeEven02 parent (by omega) h12
  by_cases h16 : parent.val < 16
  · exact completeEven03 parent (by omega) h16
  by_cases h20 : parent.val < 20
  · exact completeEven04 parent (by omega) h20
  by_cases h24 : parent.val < 24
  · exact completeEven05 parent (by omega) h24
  by_cases h28 : parent.val < 28
  · exact completeEven06 parent (by omega) h28
  by_cases h32 : parent.val < 32
  · exact completeEven07 parent (by omega) h32
  by_cases h36 : parent.val < 36
  · exact completeEven08 parent (by omega) h36
  by_cases h40 : parent.val < 40
  · exact completeEven09 parent (by omega) h40
  by_cases h44 : parent.val < 44
  · exact completeEven10 parent (by omega) h44
  by_cases h48 : parent.val < 48
  · exact completeEven11 parent (by omega) h48
  by_cases h52 : parent.val < 52
  · exact completeEven12 parent (by omega) h52
  by_cases h56 : parent.val < 56
  · exact completeEven13 parent (by omega) h56
  by_cases h60 : parent.val < 60
  · exact completeEven14 parent (by omega) h60
  by_cases h64 : parent.val < 64
  · exact completeEven15 parent (by omega) h64
  by_cases h68 : parent.val < 68
  · exact completeEven16 parent (by omega) h68
  by_cases h72 : parent.val < 72
  · exact completeEven17 parent (by omega) h72
  by_cases h76 : parent.val < 76
  · exact completeEven18 parent (by omega) h76
  by_cases h80 : parent.val < 80
  · exact completeEven19 parent (by omega) h80
  by_cases h84 : parent.val < 84
  · exact completeEven20 parent (by omega) h84
  by_cases h88 : parent.val < 88
  · exact completeEven21 parent (by omega) h88
  by_cases h92 : parent.val < 92
  · exact completeEven22 parent (by omega) h92
  by_cases h96 : parent.val < 96
  · exact completeEven23 parent (by omega) h96
  by_cases h100 : parent.val < 100
  · exact completeEven24 parent (by omega) h100
  exact completeEven25 parent (by omega)

private theorem completeOdd (parent : Index) :
    checkParent .odd parent = true := by
  by_cases h04 : parent.val < 4
  · exact completeOdd00 parent h04
  by_cases h08 : parent.val < 8
  · exact completeOdd01 parent (by omega) h08
  by_cases h12 : parent.val < 12
  · exact completeOdd02 parent (by omega) h12
  by_cases h16 : parent.val < 16
  · exact completeOdd03 parent (by omega) h16
  by_cases h20 : parent.val < 20
  · exact completeOdd04 parent (by omega) h20
  by_cases h24 : parent.val < 24
  · exact completeOdd05 parent (by omega) h24
  by_cases h28 : parent.val < 28
  · exact completeOdd06 parent (by omega) h28
  by_cases h32 : parent.val < 32
  · exact completeOdd07 parent (by omega) h32
  by_cases h36 : parent.val < 36
  · exact completeOdd08 parent (by omega) h36
  by_cases h40 : parent.val < 40
  · exact completeOdd09 parent (by omega) h40
  by_cases h44 : parent.val < 44
  · exact completeOdd10 parent (by omega) h44
  by_cases h48 : parent.val < 48
  · exact completeOdd11 parent (by omega) h48
  by_cases h52 : parent.val < 52
  · exact completeOdd12 parent (by omega) h52
  by_cases h56 : parent.val < 56
  · exact completeOdd13 parent (by omega) h56
  by_cases h60 : parent.val < 60
  · exact completeOdd14 parent (by omega) h60
  by_cases h64 : parent.val < 64
  · exact completeOdd15 parent (by omega) h64
  by_cases h68 : parent.val < 68
  · exact completeOdd16 parent (by omega) h68
  by_cases h72 : parent.val < 72
  · exact completeOdd17 parent (by omega) h72
  by_cases h76 : parent.val < 76
  · exact completeOdd18 parent (by omega) h76
  by_cases h80 : parent.val < 80
  · exact completeOdd19 parent (by omega) h80
  by_cases h84 : parent.val < 84
  · exact completeOdd20 parent (by omega) h84
  by_cases h88 : parent.val < 88
  · exact completeOdd21 parent (by omega) h88
  by_cases h92 : parent.val < 92
  · exact completeOdd22 parent (by omega) h92
  by_cases h96 : parent.val < 96
  · exact completeOdd23 parent (by omega) h96
  by_cases h100 : parent.val < 100
  · exact completeOdd24 parent (by omega) h100
  exact completeOdd25 parent (by omega)

theorem complete (phase : Phase) (parent : Index) :
    checkParent phase parent = true := by
  cases phase
  · exact completeEven parent
  · exact completeOdd parent

theorem sourceAncestorsIn (phase : Phase) (parent : Index) :
    PairCoverSeamResidualCanonicalAncestorRecurrence.SourceAncestorsIn
      (baseGrid phase parent)
      (largeWest phase) (largeEast phase)
      (largeWest phase) (largeEast phase) :=
  checkParent_sound (complete phase parent)

end PairCoverSeamResidualCanonicalAncestorBaseAudit
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
