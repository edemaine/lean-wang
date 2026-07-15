/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathAllFamilyTargetsRecurrence
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathAllFamilyTargetsOddBase
import LeanWang.OllingerRobinson104PairCoverSeamCreatedBoundaryPaths
import LeanWang.OllingerRobinson104PairCoverSeamFaceRecurrence

/-!
# All-depth family targets

The projection-closed parity bases and semantic successor theorem jointly
construct target states and their covered seam paths.  Sparse selected
boundaries come from the target state itself, so the remaining independent
inputs are created-boundary paths and exceptional projected-query targets.
-/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamResidualDirectPathAllFamilyTargetsAllDepth

open PairCoverSeamCreatedBoundaryPaths PairCoverSeamCreatedPaths
  PairCoverSeamFaceRecurrence
  PairCoverSeamResidualDirectPathAllFamilyTargets
  PairCoverSeamResidualDirectPathAllFamilyTargetsRecurrence
  PairCoverSeamResidualDirectPathFamilyExceptionalTargets
  ShadedFreeLineRecurrence

/-- Jointly iterate target states and the covered paths needed by the next
projection step. -/
theorem allDepthState
    {phase : Phase}
    (base : AllFamilyTargetsAt phase 0)
    (exceptional : ∀ depth, ExceptionalFamilyTargetsAt phase (depth + 1))
    (created : ∀ depth, CreatedBoundaryPathsAt phase depth) :
    ∀ depth,
      AllFamilyTargetsAt phase depth ∧ CoveredCreatedPathsAt phase depth := by
  intro depth
  induction depth with
  | zero => exact ⟨base, (created 0).toCovered base⟩
  | succ depth ih =>
      let next :=
        PairCoverSeamResidualDirectPathAllFamilyTargetsRecurrence.AllFamilyTargetsAt.succ
          ih.1 (exceptional depth) ih.2
      exact ⟨next, (created (depth + 1)).toCovered next⟩

/-- Target-only projection of the joint all-depth recurrence. -/
theorem allDepth
    {phase : Phase}
    (base : AllFamilyTargetsAt phase 0)
    (exceptional : ∀ depth, ExceptionalFamilyTargetsAt phase (depth + 1))
    (created : ∀ depth, CreatedBoundaryPathsAt phase depth) :
    ∀ depth, AllFamilyTargetsAt phase depth := fun depth =>
  (allDepthState base exceptional created depth).1

/-- All even target depths, conditional only on the two local semantic inputs. -/
theorem even
    (exceptional : ∀ depth, ExceptionalFamilyTargetsAt .even (depth + 1))
    (created : ∀ depth, CreatedBoundaryPathsAt .even depth) :
    ∀ depth, AllFamilyTargetsAt .even depth :=
  allDepth PairCoverSeamResidualDirectPathAllFamilyTargets.evenBase
    exceptional created

/-- All odd target depths, conditional only on the two local semantic inputs. -/
theorem odd
    (exceptional : ∀ depth, ExceptionalFamilyTargetsAt .odd (depth + 1))
    (created : ∀ depth, CreatedBoundaryPathsAt .odd depth) :
    ∀ depth, AllFamilyTargetsAt .odd depth :=
  allDepth PairCoverSeamResidualDirectPathAllFamilyTargetsOddBase.oddBase
    exceptional created

/-- The all-depth target recurrence supplies every odd face-refinement step. -/
theorem oddStepData
    (exceptional : ∀ depth, ExceptionalFamilyTargetsAt .odd (depth + 1))
    (created : ∀ depth, CreatedBoundaryPathsAt .odd depth) :
    ∀ depth, StepData .odd depth := by
  intro depth
  have state := allDepthState
    PairCoverSeamResidualDirectPathAllFamilyTargetsOddBase.oddBase
    exceptional created depth
  exact StepData.ofFamilyTargets state.2 state.1.toFamilyTargetsAt

/-- The all-depth target recurrence supplies every required even step. -/
theorem evenStepData
    (exceptional : ∀ depth, ExceptionalFamilyTargetsAt .even (depth + 1))
    (created : ∀ depth, CreatedBoundaryPathsAt .even depth) :
    ∀ depth, StepData .even (1 + depth) := by
  intro depth
  have state := allDepthState
    PairCoverSeamResidualDirectPathAllFamilyTargets.evenBase
    exceptional created (1 + depth)
  exact StepData.ofFamilyTargets state.2 state.1.toFamilyTargetsAt

end PairCoverSeamResidualDirectPathAllFamilyTargetsAllDepth
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
