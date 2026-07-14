/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathFamilyExceptionalBaseCheck

/-! Cached exceptional family-target checks for parents 96 through 99. -/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamResidualDirectPathFamilyExceptionalBase

open PairCoverSeamResidualDirectPathFamilyBaseCheck
  PairCoverSeamResidualDirectPathFamilyExceptionalBaseCheck

set_option linter.style.nativeDecide false in
theorem completeEven24 :
    checkChunk .even 0 (exhaustiveFuel .even 0) ⟨24, by decide⟩ = true := by
  native_decide

set_option linter.style.nativeDecide false in
theorem completeOdd24 :
    checkChunk .odd 0 (exhaustiveFuel .odd 0) ⟨24, by decide⟩ = true := by
  native_decide

end PairCoverSeamResidualDirectPathFamilyExceptionalBase
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
