/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.Tiles

/-!
Finite recognizability facts for the corrected Ollinger alphabet.

The thin layer fixes the phase of the global `2 x 2` decomposition. The other
two checks below supply the local boundary reflection needed to turn decoded
child blocks back into a valid parent tiling.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104

/-- Thin-layer phase immediately east of a given phase. -/
def phaseEast : Figure16.Thin → Figure16.Thin
  | .a => .c
  | .b => .d
  | .c => .a
  | .d => .b

/-- Thin-layer phase immediately north of a given phase. -/
def phaseNorth : Figure16.Thin → Figure16.Thin
  | .a => .d
  | .b => .c
  | .c => .b
  | .d => .a

@[simp]
theorem phaseEast_involutive (thin : Figure16.Thin) :
    phaseEast (phaseEast thin) = thin := by
  cases thin <;> rfl

@[simp]
theorem phaseNorth_involutive (thin : Figure16.Thin) :
    phaseNorth (phaseNorth thin) = thin := by
  cases thin <;> rfl

theorem phaseEast_phaseNorth_comm (thin : Figure16.Thin) :
    phaseEast (phaseNorth thin) = phaseNorth (phaseEast thin) := by
  cases thin <;> rfl

set_option linter.style.nativeDecide false in
set_option maxRecDepth 20000 in
private theorem equalTilesHaveEqualThin :
    ∀ i j : Index, tile (components i) = tile (components j) →
      (components i).1 = (components j).1 := by
  native_decide

theorem thin_eq_of_tile_eq {i j : Index}
    (h : tile (components i) = tile (components j)) :
    (components i).1 = (components j).1 :=
  equalTilesHaveEqualThin i j h

set_option linter.style.nativeDecide false in
set_option maxRecDepth 20000 in
private theorem horizontalMatchesHaveExpectedThin :
    ∀ left right : Index,
      WangTile.HMatches (tile (components left)) (tile (components right)) →
        (components right).1 = phaseEast (components left).1 := by
  native_decide

theorem thin_eq_thinEast_of_hMatches {left right : Index}
    (h : WangTile.HMatches
      (tile (components left)) (tile (components right))) :
    (components right).1 = phaseEast (components left).1 :=
  horizontalMatchesHaveExpectedThin left right h

set_option linter.style.nativeDecide false in
set_option maxRecDepth 20000 in
private theorem verticalMatchesHaveExpectedThin :
    ∀ lower upper : Index,
      WangTile.VMatches (tile (components lower)) (tile (components upper)) →
        (components upper).1 = phaseNorth (components lower).1 := by
  native_decide

theorem thin_eq_thinNorth_of_vMatches {lower upper : Index}
    (h : WangTile.VMatches
      (tile (components lower)) (tile (components upper))) :
    (components upper).1 = phaseNorth (components lower).1 :=
  verticalMatchesHaveExpectedThin lower upper h

/-- Counterexamples to horizontal boundary reflection in the current edge code. -/
def horizontalBoundaryReflectionFailures : List (Nat × Nat) :=
  (List.finRange 104).flatMap fun left =>
    ((List.finRange 104).filter fun right =>
      decide (ChildHMatches left right) &&
        !decide (WangTile.HMatches
          (tile (components left)) (tile (components right)))).map fun right =>
            (left.val, right.val)

/-- Counterexamples to vertical boundary reflection in the current edge code. -/
def verticalBoundaryReflectionFailures : List (Nat × Nat) :=
  (List.finRange 104).flatMap fun lower =>
    ((List.finRange 104).filter fun upper =>
      decide (ChildVMatches lower upper) &&
        !decide (WangTile.VMatches
          (tile (components lower)) (tile (components upper)))).map fun upper =>
            (lower.val, upper.val)

set_option linter.style.nativeDecide false in
set_option maxRecDepth 20000 in
theorem horizontalBoundaryReflectionFailures_eq_nil :
    horizontalBoundaryReflectionFailures = [] := by
  native_decide

set_option linter.style.nativeDecide false in
set_option maxRecDepth 20000 in
theorem verticalBoundaryReflectionFailures_eq_nil :
    verticalBoundaryReflectionFailures = [] := by
  native_decide

end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
