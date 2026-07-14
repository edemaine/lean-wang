/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathAllFamilyTargetsRecurrence
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathAllFamilyTargetsOddBase
import LeanWang.OllingerRobinson104PairCoverSeamFaceRecurrence

/-!
# All-depth family targets

The projection-closed parity bases and semantic successor theorem reduce the
all-depth target family to two independent inputs: created-coordinate paths
and exceptional projected-query targets.
-/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamResidualDirectPathAllFamilyTargetsAllDepth

open PairCoverSeamCreatedPaths PairCoverSeamFaceRecurrence
  PairCoverSeamResidualDirectPathAllFamilyTargets
  PairCoverSeamResidualDirectPathAllFamilyTargetsRecurrence
  PairCoverSeamResidualDirectPathFamilyExceptionalTargets
  ShadedFreeLineRecurrence

/-- Iterate the semantic target recurrence from any depth-zero base. -/
theorem allDepth
    {phase : Phase}
    (base : AllFamilyTargetsAt phase 0)
    (exceptional : ∀ depth, ExceptionalFamilyTargetsAt phase (depth + 1))
    (created : ∀ depth, CoveredCreatedPathsAt phase depth) :
    ∀ depth, AllFamilyTargetsAt phase depth := by
  intro depth
  induction depth with
  | zero => exact base
  | succ depth ih =>
      exact PairCoverSeamResidualDirectPathAllFamilyTargetsRecurrence.AllFamilyTargetsAt.succ
        ih (exceptional depth) (created depth)

/-- All even target depths, conditional only on the two local semantic inputs. -/
theorem even
    (exceptional : ∀ depth, ExceptionalFamilyTargetsAt .even (depth + 1))
    (created : ∀ depth, CoveredCreatedPathsAt .even depth) :
    ∀ depth, AllFamilyTargetsAt .even depth :=
  allDepth PairCoverSeamResidualDirectPathAllFamilyTargets.evenBase
    exceptional created

/-- All odd target depths, conditional only on the two local semantic inputs. -/
theorem odd
    (exceptional : ∀ depth, ExceptionalFamilyTargetsAt .odd (depth + 1))
    (created : ∀ depth, CoveredCreatedPathsAt .odd depth) :
    ∀ depth, AllFamilyTargetsAt .odd depth :=
  allDepth PairCoverSeamResidualDirectPathAllFamilyTargetsOddBase.oddBase
    exceptional created

/-- The all-depth target recurrence supplies every odd face-refinement step. -/
theorem oddStepData
    (exceptional : ∀ depth, ExceptionalFamilyTargetsAt .odd (depth + 1))
    (created : ∀ depth, CoveredCreatedPathsAt .odd depth) :
    ∀ depth, StepData .odd depth := by
  intro depth
  exact StepData.ofFamilyTargets (created depth)
    ((odd exceptional created depth).toFamilyTargetsAt)

/-- The all-depth target recurrence supplies every required even step. -/
theorem evenStepData
    (exceptional : ∀ depth, ExceptionalFamilyTargetsAt .even (depth + 1))
    (created : ∀ depth, CoveredCreatedPathsAt .even depth) :
    ∀ depth, StepData .even (1 + depth) := by
  intro depth
  exact StepData.ofFamilyTargets (created (1 + depth))
    ((even exceptional created (1 + depth)).toFamilyTargetsAt)

end PairCoverSeamResidualDirectPathAllFamilyTargetsAllDepth
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
