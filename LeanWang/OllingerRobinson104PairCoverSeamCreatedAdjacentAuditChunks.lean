/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamCreatedAdjacentAuditChunk00
import LeanWang.OllingerRobinson104PairCoverSeamCreatedAdjacentAuditChunk01
import LeanWang.OllingerRobinson104PairCoverSeamCreatedAdjacentAuditChunk02
import LeanWang.OllingerRobinson104PairCoverSeamCreatedAdjacentAuditChunk03
import LeanWang.OllingerRobinson104PairCoverSeamCreatedAdjacentAuditChunk04
import LeanWang.OllingerRobinson104PairCoverSeamCreatedAdjacentAuditChunk05
import LeanWang.OllingerRobinson104PairCoverSeamCreatedAdjacentAuditChunk06
import LeanWang.OllingerRobinson104PairCoverSeamCreatedAdjacentAuditChunk07
import LeanWang.OllingerRobinson104PairCoverSeamCreatedAdjacentAuditChunk08
import LeanWang.OllingerRobinson104PairCoverSeamCreatedAdjacentAuditChunk09
import LeanWang.OllingerRobinson104PairCoverSeamCreatedAdjacentAuditChunk10
import LeanWang.OllingerRobinson104PairCoverSeamCreatedAdjacentAuditChunk11
import LeanWang.OllingerRobinson104PairCoverSeamCreatedAdjacentAuditChunk12
import LeanWang.OllingerRobinson104PairCoverSeamCreatedAdjacentAuditChunk13
import LeanWang.OllingerRobinson104PairCoverSeamCreatedAdjacentAuditChunk14
import LeanWang.OllingerRobinson104PairCoverSeamCreatedAdjacentAuditChunk15
import LeanWang.OllingerRobinson104PairCoverSeamCreatedAdjacentAuditChunk16
import LeanWang.OllingerRobinson104PairCoverSeamCreatedAdjacentAuditChunk17
import LeanWang.OllingerRobinson104PairCoverSeamCreatedAdjacentAuditChunk18
import LeanWang.OllingerRobinson104PairCoverSeamCreatedAdjacentAuditChunk19
import LeanWang.OllingerRobinson104PairCoverSeamCreatedAdjacentAuditChunk20
import LeanWang.OllingerRobinson104PairCoverSeamCreatedAdjacentAuditChunk21
import LeanWang.OllingerRobinson104PairCoverSeamCreatedAdjacentAuditChunk22
import LeanWang.OllingerRobinson104PairCoverSeamCreatedAdjacentAuditChunk23
import LeanWang.OllingerRobinson104PairCoverSeamCreatedAdjacentAuditChunk24

/-! Assemble the cached adjacent-macrocell seam audit chunks. -/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace PairCoverSeamCreatedAdjacentAudit

set_option maxRecDepth 20000

def allVerticalChunks : List PairState :=
  verticalChunk 0 ++
    verticalChunk 1 ++
    verticalChunk 2 ++
    verticalChunk 3 ++
    verticalChunk 4 ++
    verticalChunk 5 ++
    verticalChunk 6 ++
    verticalChunk 7 ++
    verticalChunk 8 ++
    verticalChunk 9 ++
    verticalChunk 10 ++
    verticalChunk 11 ++
    verticalChunk 12 ++
    verticalChunk 13 ++
    verticalChunk 14 ++
    verticalChunk 15 ++
    verticalChunk 16 ++
    verticalChunk 17 ++
    verticalChunk 18 ++
    verticalChunk 19 ++
    verticalChunk 20 ++
    verticalChunk 21 ++
    verticalChunk 22 ++
    verticalChunk 23 ++
    verticalChunk 24

def allHorizontalChunks : List PairState :=
  horizontalChunk 0 ++
    horizontalChunk 1 ++
    horizontalChunk 2 ++
    horizontalChunk 3 ++
    horizontalChunk 4 ++
    horizontalChunk 5 ++
    horizontalChunk 6 ++
    horizontalChunk 7 ++
    horizontalChunk 8 ++
    horizontalChunk 9 ++
    horizontalChunk 10 ++
    horizontalChunk 11 ++
    horizontalChunk 12 ++
    horizontalChunk 13 ++
    horizontalChunk 14 ++
    horizontalChunk 15 ++
    horizontalChunk 16 ++
    horizontalChunk 17 ++
    horizontalChunk 18 ++
    horizontalChunk 19 ++
    horizontalChunk 20 ++
    horizontalChunk 21 ++
    horizontalChunk 22 ++
    horizontalChunk 23 ++
    horizontalChunk 24

set_option linter.style.nativeDecide false in
theorem verticalPairs_eq_chunks : verticalPairs = allVerticalChunks := by
  native_decide

set_option linter.style.nativeDecide false in
theorem horizontalPairs_eq_chunks : horizontalPairs = allHorizontalChunks := by
  native_decide

theorem vertical_complete : verticalPairs.all checkVerticalPair = true := by
  rw [verticalPairs_eq_chunks]
  simp only [allVerticalChunks, List.all_append,
    verticalChunk00,
    verticalChunk01,
    verticalChunk02,
    verticalChunk03,
    verticalChunk04,
    verticalChunk05,
    verticalChunk06,
    verticalChunk07,
    verticalChunk08,
    verticalChunk09,
    verticalChunk10,
    verticalChunk11,
    verticalChunk12,
    verticalChunk13,
    verticalChunk14,
    verticalChunk15,
    verticalChunk16,
    verticalChunk17,
    verticalChunk18,
    verticalChunk19,
    verticalChunk20,
    verticalChunk21,
    verticalChunk22,
    verticalChunk23,
    verticalChunk24]
  rfl

theorem horizontal_complete : horizontalPairs.all checkHorizontalPair = true := by
  rw [horizontalPairs_eq_chunks]
  simp only [allHorizontalChunks, List.all_append,
    horizontalChunk00,
    horizontalChunk01,
    horizontalChunk02,
    horizontalChunk03,
    horizontalChunk04,
    horizontalChunk05,
    horizontalChunk06,
    horizontalChunk07,
    horizontalChunk08,
    horizontalChunk09,
    horizontalChunk10,
    horizontalChunk11,
    horizontalChunk12,
    horizontalChunk13,
    horizontalChunk14,
    horizontalChunk15,
    horizontalChunk16,
    horizontalChunk17,
    horizontalChunk18,
    horizontalChunk19,
    horizontalChunk20,
    horizontalChunk21,
    horizontalChunk22,
    horizontalChunk23,
    horizontalChunk24]
  rfl

end PairCoverSeamCreatedAdjacentAudit
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
