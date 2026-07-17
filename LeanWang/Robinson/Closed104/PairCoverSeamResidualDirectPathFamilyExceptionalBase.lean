/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import Mathlib.Tactic.FinCases
import LeanWang.Robinson.Closed104.PairCoverSeamResidualDirectPathFamilyExceptionalBaseChunk00
import LeanWang.Robinson.Closed104.PairCoverSeamResidualDirectPathFamilyExceptionalBaseChunk01
import LeanWang.Robinson.Closed104.PairCoverSeamResidualDirectPathFamilyExceptionalBaseChunk02
import LeanWang.Robinson.Closed104.PairCoverSeamResidualDirectPathFamilyExceptionalBaseChunk03
import LeanWang.Robinson.Closed104.PairCoverSeamResidualDirectPathFamilyExceptionalBaseChunk04
import LeanWang.Robinson.Closed104.PairCoverSeamResidualDirectPathFamilyExceptionalBaseChunk05
import LeanWang.Robinson.Closed104.PairCoverSeamResidualDirectPathFamilyExceptionalBaseChunk06
import LeanWang.Robinson.Closed104.PairCoverSeamResidualDirectPathFamilyExceptionalBaseChunk07
import LeanWang.Robinson.Closed104.PairCoverSeamResidualDirectPathFamilyExceptionalBaseChunk08
import LeanWang.Robinson.Closed104.PairCoverSeamResidualDirectPathFamilyExceptionalBaseChunk09
import LeanWang.Robinson.Closed104.PairCoverSeamResidualDirectPathFamilyExceptionalBaseChunk10
import LeanWang.Robinson.Closed104.PairCoverSeamResidualDirectPathFamilyExceptionalBaseChunk11
import LeanWang.Robinson.Closed104.PairCoverSeamResidualDirectPathFamilyExceptionalBaseChunk12
import LeanWang.Robinson.Closed104.PairCoverSeamResidualDirectPathFamilyExceptionalBaseChunk13
import LeanWang.Robinson.Closed104.PairCoverSeamResidualDirectPathFamilyExceptionalBaseChunk14
import LeanWang.Robinson.Closed104.PairCoverSeamResidualDirectPathFamilyExceptionalBaseChunk15
import LeanWang.Robinson.Closed104.PairCoverSeamResidualDirectPathFamilyExceptionalBaseChunk16
import LeanWang.Robinson.Closed104.PairCoverSeamResidualDirectPathFamilyExceptionalBaseChunk17
import LeanWang.Robinson.Closed104.PairCoverSeamResidualDirectPathFamilyExceptionalBaseChunk18
import LeanWang.Robinson.Closed104.PairCoverSeamResidualDirectPathFamilyExceptionalBaseChunk19
import LeanWang.Robinson.Closed104.PairCoverSeamResidualDirectPathFamilyExceptionalBaseChunk20
import LeanWang.Robinson.Closed104.PairCoverSeamResidualDirectPathFamilyExceptionalBaseChunk21
import LeanWang.Robinson.Closed104.PairCoverSeamResidualDirectPathFamilyExceptionalBaseChunk22
import LeanWang.Robinson.Closed104.PairCoverSeamResidualDirectPathFamilyExceptionalBaseChunk23
import LeanWang.Robinson.Closed104.PairCoverSeamResidualDirectPathFamilyExceptionalBaseChunk24
import LeanWang.Robinson.Closed104.PairCoverSeamResidualDirectPathFamilyExceptionalBaseChunk25

/-! Assemble the cached exceptional family-target certificates. -/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamResidualDirectPathFamilyExceptionalBase

open PairCoverSeamResidualDirectPathFamilyBaseCheck
  PairCoverSeamResidualDirectPathFamilyExceptionalBaseCheck

theorem evenChunkChecks :
    ChunkChecks .even 0 (exhaustiveFuel .even 0) := by
  intro chunk
  fin_cases chunk
  · exact completeEven00
  · exact completeEven01
  · exact completeEven02
  · exact completeEven03
  · exact completeEven04
  · exact completeEven05
  · exact completeEven06
  · exact completeEven07
  · exact completeEven08
  · exact completeEven09
  · exact completeEven10
  · exact completeEven11
  · exact completeEven12
  · exact completeEven13
  · exact completeEven14
  · exact completeEven15
  · exact completeEven16
  · exact completeEven17
  · exact completeEven18
  · exact completeEven19
  · exact completeEven20
  · exact completeEven21
  · exact completeEven22
  · exact completeEven23
  · exact completeEven24
  · exact completeEven25

theorem oddChunkChecks :
    ChunkChecks .odd 0 (exhaustiveFuel .odd 0) := by
  intro chunk
  fin_cases chunk
  · exact completeOdd00
  · exact completeOdd01
  · exact completeOdd02
  · exact completeOdd03
  · exact completeOdd04
  · exact completeOdd05
  · exact completeOdd06
  · exact completeOdd07
  · exact completeOdd08
  · exact completeOdd09
  · exact completeOdd10
  · exact completeOdd11
  · exact completeOdd12
  · exact completeOdd13
  · exact completeOdd14
  · exact completeOdd15
  · exact completeOdd16
  · exact completeOdd17
  · exact completeOdd18
  · exact completeOdd19
  · exact completeOdd20
  · exact completeOdd21
  · exact completeOdd22
  · exact completeOdd23
  · exact completeOdd24
  · exact completeOdd25

theorem evenTargets :
    BoundedExceptionalTargetsAt .even 0 (exhaustiveFuel .even 0) :=
  evenChunkChecks.targets

theorem oddTargets :
    BoundedExceptionalTargetsAt .odd 0 (exhaustiveFuel .odd 0) :=
  oddChunkChecks.targets

end PairCoverSeamResidualDirectPathFamilyExceptionalBase
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
