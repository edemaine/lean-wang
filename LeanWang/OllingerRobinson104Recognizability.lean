/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104StableTilesCorrect
import LeanWang.OllingerRobinson104Tiling

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

/-- Equal corrected Wang tiles always have the same thin-layer phase. -/
def allEqualTilesHaveEqualThinBool : Bool :=
  (List.finRange 104).all fun i =>
    (List.finRange 104).all fun j =>
      decide (tile (components i) = tile (components j) →
        (components i).1 = (components j).1)

set_option linter.style.nativeDecide false in
set_option maxRecDepth 20000 in
theorem allEqualTilesHaveEqualThinBool_eq_true :
    allEqualTilesHaveEqualThinBool = true := by
  native_decide

theorem thin_eq_of_tile_eq {i j : Index}
    (h : tile (components i) = tile (components j)) :
    (components i).1 = (components j).1 := by
  have hi := List.all_eq_true.1 allEqualTilesHaveEqualThinBool_eq_true
    i (List.mem_finRange i)
  have hij := List.all_eq_true.1 hi j (List.mem_finRange j)
  exact (of_decide_eq_true hij) h

/-- Horizontal matching forces the checkerboard's east phase. -/
def allHorizontalMatchesHaveExpectedThinBool : Bool :=
  (List.finRange 104).all fun left =>
    (List.finRange 104).all fun right =>
      decide (WangTile.HMatches
        (tile (components left)) (tile (components right)) →
          (components right).1 = phaseEast (components left).1)

set_option linter.style.nativeDecide false in
set_option maxRecDepth 20000 in
theorem allHorizontalMatchesHaveExpectedThinBool_eq_true :
    allHorizontalMatchesHaveExpectedThinBool = true := by
  native_decide

theorem thin_eq_thinEast_of_hMatches {left right : Index}
    (h : WangTile.HMatches
      (tile (components left)) (tile (components right))) :
    (components right).1 = phaseEast (components left).1 := by
  have hleft := List.all_eq_true.1
    allHorizontalMatchesHaveExpectedThinBool_eq_true
    left (List.mem_finRange left)
  have hright := List.all_eq_true.1 hleft right (List.mem_finRange right)
  exact (of_decide_eq_true hright) h

/-- Vertical matching forces the checkerboard's north phase. -/
def allVerticalMatchesHaveExpectedThinBool : Bool :=
  (List.finRange 104).all fun lower =>
    (List.finRange 104).all fun upper =>
      decide (WangTile.VMatches
        (tile (components lower)) (tile (components upper)) →
          (components upper).1 = phaseNorth (components lower).1)

set_option linter.style.nativeDecide false in
set_option maxRecDepth 20000 in
theorem allVerticalMatchesHaveExpectedThinBool_eq_true :
    allVerticalMatchesHaveExpectedThinBool = true := by
  native_decide

theorem thin_eq_thinNorth_of_vMatches {lower upper : Index}
    (h : WangTile.VMatches
      (tile (components lower)) (tile (components upper))) :
    (components upper).1 = phaseNorth (components lower).1 := by
  have hlower := List.all_eq_true.1
    allVerticalMatchesHaveExpectedThinBool_eq_true
    lower (List.mem_finRange lower)
  have hupper := List.all_eq_true.1 hlower upper (List.mem_finRange upper)
  exact (of_decide_eq_true hupper) h

/-- Equal stable derived tiles still determine a unique thin-layer phase. -/
def allDerivedOneEqualTilesHaveEqualThinBool : Bool :=
  (List.finRange 104).all fun i =>
    (List.finRange 104).all fun j =>
      decide (derivedTile 1 i = derivedTile 1 j →
        (components i).1 = (components j).1)

set_option linter.style.nativeDecide false in
set_option maxRecDepth 20000 in
theorem allDerivedOneEqualTilesHaveEqualThinBool_eq_true :
    allDerivedOneEqualTilesHaveEqualThinBool = true := by
  native_decide

theorem thin_eq_of_derivedTile_one_eq {i j : Index}
    (h : derivedTile 1 i = derivedTile 1 j) :
    (components i).1 = (components j).1 := by
  have hi := List.all_eq_true.1 allDerivedOneEqualTilesHaveEqualThinBool_eq_true
    i (List.mem_finRange i)
  have hij := List.all_eq_true.1 hi j (List.mem_finRange j)
  exact (of_decide_eq_true hij) h

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

end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
