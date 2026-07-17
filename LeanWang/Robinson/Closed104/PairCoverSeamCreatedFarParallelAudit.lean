/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.PairCoverSeamCreatedFarParallelAuditChunk00
import LeanWang.Robinson.Closed104.PairCoverSeamCreatedFarParallelAuditChunk01
import LeanWang.Robinson.Closed104.PairCoverSeamCreatedFarParallelAuditChunk02
import LeanWang.Robinson.Closed104.PairCoverSeamCreatedFarParallelAuditChunk03
import LeanWang.Robinson.Closed104.PairCoverSeamCreatedFarParallelAuditChunk04
import LeanWang.Robinson.Closed104.PairCoverSeamCreatedFarParallelAuditChunk05
import LeanWang.Robinson.Closed104.PairCoverSeamCreatedFarParallelAuditChunk06
import LeanWang.Robinson.Closed104.PairCoverSeamCreatedFarParallelAuditChunk07
import LeanWang.Robinson.Closed104.PairCoverSeamCreatedFarParallelAuditChunk08
import LeanWang.Robinson.Closed104.PairCoverSeamCreatedFarParallelAuditChunk09
import LeanWang.Robinson.Closed104.PairCoverSeamCreatedFarParallelAuditChunk10
import LeanWang.Robinson.Closed104.PairCoverSeamCreatedFarParallelAuditChunk11
import LeanWang.Robinson.Closed104.PairCoverSeamCreatedFarParallelAuditChunk12
import LeanWang.Robinson.Closed104.PairCoverSeamCreatedFarParallelAuditChunk13
import LeanWang.Robinson.Closed104.PairCoverSeamCreatedFarParallelAuditChunk14
import LeanWang.Robinson.Closed104.PairCoverSeamCreatedFarParallelAuditChunk15
import LeanWang.Robinson.Closed104.PairCoverSeamCreatedFarParallelAuditChunk16
import LeanWang.Robinson.Closed104.PairCoverSeamCreatedFarParallelAuditChunk17
import LeanWang.Robinson.Closed104.PairCoverSeamCreatedFarParallelAuditChunk18
import LeanWang.Robinson.Closed104.PairCoverSeamCreatedFarParallelAuditChunk19
import LeanWang.Robinson.Closed104.PairCoverSeamCreatedFarParallelAuditChunk20
import LeanWang.Robinson.Closed104.PairCoverSeamCreatedFarParallelAuditChunk21
import LeanWang.Robinson.Closed104.PairCoverSeamCreatedFarParallelAuditChunk22
import LeanWang.Robinson.Closed104.PairCoverSeamCreatedFarParallelAuditChunk23
import LeanWang.Robinson.Closed104.PairCoverSeamCreatedFarParallelAuditChunk24

/-! Assemble the cached local parallel-target audit chunks. -/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamCreatedFarParallelAudit

open PairCoverSeamCreatedAdjacentAudit

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
theorem verticalPairs_eq_chunks :
    PairCoverSeamCreatedAdjacentAudit.verticalPairs = allVerticalChunks := by
  native_decide

set_option linter.style.nativeDecide false in
theorem horizontalPairs_eq_chunks :
    PairCoverSeamCreatedAdjacentAudit.horizontalPairs = allHorizontalChunks := by
  native_decide

theorem vertical_complete :
    PairCoverSeamCreatedAdjacentAudit.verticalPairs.all
      checkVerticalPair = true := by
  rw [verticalPairs_eq_chunks]
  simp only [allVerticalChunks, List.all_append,
    complete00.1,
    complete01.1,
    complete02.1,
    complete03.1,
    complete04.1,
    complete05.1,
    complete06.1,
    complete07.1,
    complete08.1,
    complete09.1,
    complete10.1,
    complete11.1,
    complete12.1,
    complete13.1,
    complete14.1,
    complete15.1,
    complete16.1,
    complete17.1,
    complete18.1,
    complete19.1,
    complete20.1,
    complete21.1,
    complete22.1,
    complete23.1,
    complete24.1
  ]
  rfl

theorem horizontal_complete :
    PairCoverSeamCreatedAdjacentAudit.horizontalPairs.all
      checkHorizontalPair = true := by
  rw [horizontalPairs_eq_chunks]
  simp only [allHorizontalChunks, List.all_append,
    complete00.2,
    complete01.2,
    complete02.2,
    complete03.2,
    complete04.2,
    complete05.2,
    complete06.2,
    complete07.2,
    complete08.2,
    complete09.2,
    complete10.2,
    complete11.2,
    complete12.2,
    complete13.2,
    complete14.2,
    complete15.2,
    complete16.2,
    complete17.2,
    complete18.2,
    complete19.2,
    complete20.2,
    complete21.2,
    complete22.2,
    complete23.2,
    complete24.2
  ]
  rfl

end PairCoverSeamCreatedFarParallelAudit
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
