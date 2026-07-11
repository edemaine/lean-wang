/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104BorderCoverageOffsets

/-!
# Local template interface for the free-line recurrence

The successor offset decomposition reduces a whole-pattern projection to six
families of bounded local templates: two side cases and one child family in
each orientation. This module packages that exact interface and reconnects it
to the semantic recurrence.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace BorderCoverageLocalStep

open RedCycles ShadedFreeLineGraph ShadedFreeLineOffsets
  ShadedFreeLinePatternRefinement ShadedFreeLineRecurrence

def LocalProjectionStep : Prop :=
  ∀ phase depth parent,
    (∀ offset ∈ freeOffsets depth,
      LiveRowCertificate
        (ShadedFreeLineRecurrence.localGrid phase depth parent)
        (west phase depth) (east phase depth)
        (west phase depth) (east phase depth)
        (lineCoordinate phase depth offset)) →
    (∀ offset ∈ freeOffsets depth,
      LiveColumnCertificate
        (ShadedFreeLineRecurrence.localGrid phase depth parent)
        (west phase depth) (east phase depth)
        (west phase depth) (east phase depth)
        (lineCoordinate phase depth offset)) →
    let grid := ShadedFreeLineRecurrence.localGrid phase depth parent
    let west := west phase depth
    let east := east phase depth
    let fineCoordinate := lineCoordinate phase (depth + 1)
    VerticalProjectionAt grid west east west east (fineCoordinate 1) ∧
    (∀ oldOffset ∈ freeOffsets depth, ∀ child ∈ expandOffset oldOffset,
      VerticalProjectionAt grid west east west east (fineCoordinate child)) ∧
    VerticalProjectionAt grid west east west east
      (fineCoordinate (4 ^ (depth + 2) - 2)) ∧
    HorizontalProjectionAt grid west east west east (fineCoordinate 1) ∧
    (∀ oldOffset ∈ freeOffsets depth, ∀ child ∈ expandOffset oldOffset,
      HorizontalProjectionAt grid west east west east (fineCoordinate child)) ∧
    HorizontalProjectionAt grid west east west east
      (fineCoordinate (4 ^ (depth + 2) - 2))

theorem projectionStep_of_localProjectionStep
    (templates : LocalProjectionStep) : ProjectionStep := by
  intro phase depth parent rows columns
  rcases templates phase depth parent rows columns with
    ⟨leftVertical, childVertical, rightVertical,
      leftHorizontal, childHorizontal, rightHorizontal⟩
  exact PatternProjection.ofSuccOffsets
    leftVertical childVertical rightVertical
    leftHorizontal childHorizontal rightHorizontal

theorem graphPeriodicStep_of_localProjectionStep
    (templates : LocalProjectionStep) : GraphPeriodicStep :=
  graphPeriodicStep_of_projectionStep
    (projectionStep_of_localProjectionStep templates)

end BorderCoverageLocalStep
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
