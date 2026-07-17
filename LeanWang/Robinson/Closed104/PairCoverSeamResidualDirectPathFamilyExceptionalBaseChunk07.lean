/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.PairCoverSeamResidualDirectPathFamilyExceptionalBaseCheck

/-! Cached exceptional family-target checks for parents 28 through 31. -/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamResidualDirectPathFamilyExceptionalBase

open PairCoverSeamResidualDirectPathFamilyBaseCheck
  PairCoverSeamResidualDirectPathFamilyExceptionalBaseCheck

set_option linter.style.nativeDecide false in
theorem completeEven07 :
    checkChunk .even 0 (exhaustiveFuel .even 0) ⟨7, by decide⟩ = true := by
  native_decide

set_option linter.style.nativeDecide false in
theorem completeOdd07 :
    checkChunk .odd 0 (exhaustiveFuel .odd 0) ⟨7, by decide⟩ = true := by
  native_decide

end PairCoverSeamResidualDirectPathFamilyExceptionalBase
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
