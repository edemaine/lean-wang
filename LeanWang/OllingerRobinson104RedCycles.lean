/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104

/-!
Red-border topology in finite corrected-Ollinger supertiles.

The four thick corner components connect the two red ports indicated by their
names below. The remaining thick components are sums of straight line atoms.
This gives a finite, proof-facing definition of a red rectangular cycle.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace RedCycles

/-- A finite supertile represented by rows from south to north. -/
abbrev Grid := List (List Index)

def expandRowSouth (row : List Index) : List Index :=
  row.flatMap fun parent =>
    [childBlock parent ⟨0, by decide⟩ ⟨0, by decide⟩,
      childBlock parent ⟨1, by decide⟩ ⟨0, by decide⟩]

def expandRowNorth (row : List Index) : List Index :=
  row.flatMap fun parent =>
    [childBlock parent ⟨0, by decide⟩ ⟨1, by decide⟩,
      childBlock parent ⟨1, by decide⟩ ⟨1, by decide⟩]

def expandGrid (grid : Grid) : Grid :=
  grid.flatMap fun row => [expandRowSouth row, expandRowNorth row]

/-- `2^level x 2^level` substitution patch below one parent. -/
def supertile : Nat → Index → Grid
  | 0, parent => [[parent]]
  | level + 1, parent => expandGrid (supertile level parent)

private def fallback : Index := ⟨0, by decide⟩

def gridAt (grid : Grid) (x y : Nat) : Index :=
  (grid.getD y []).getD x fallback

def thickAt (grid : Grid) (x y : Nat) : Figure16.Thick :=
  (components (gridAt grid x y)).2.1

def isRedHorizontalLine : Figure16.ThickLine → Bool
  | .r1 | .r3 => true
  | _ => false

def isRedVerticalLine : Figure16.ThickLine → Bool
  | .r0 | .r2 => true
  | _ => false

def hasRedHorizontal : Figure16.Thick → Bool
  | thick => match thick.lineSum? with
    | none => false
    | some sum =>
        isRedHorizontalLine sum.first || isRedHorizontalLine sum.second

def hasRedVertical : Figure16.Thick → Bool
  | thick => match thick.lineSum? with
    | none => false
    | some sum =>
        isRedVerticalLine sum.first || isRedVerticalLine sum.second

def betweenAll (lower upper : Nat) (predicate : Nat → Bool) : Bool :=
  (List.range (upper - lower - 1)).all fun offset =>
    predicate (lower + 1 + offset)

/-- A red rectangular cycle with its four turning components at the corners. -/
def redCycle (grid : Grid) (west east south north : Nat) : Bool :=
  thickAt grid west south == .b &&
    thickAt grid east south == .c &&
    thickAt grid west north == .a &&
    thickAt grid east north == .d &&
    (betweenAll west east fun x =>
      hasRedHorizontal (thickAt grid x south) &&
        hasRedHorizontal (thickAt grid x north)) &&
    (betweenAll south north fun y =>
      hasRedVertical (thickAt grid west y) &&
        hasRedVertical (thickAt grid east y))


/- In fact, the depth-two cycle has the same coordinates below every parent. -/
set_option linter.style.nativeDecide false in
set_option maxRecDepth 20000 in
theorem every_depthTwo_supertile_has_fixed_redCycle :
    ∀ parent : Index,
      redCycle (supertile 2 parent) 1 3 1 3 = true := by
  native_decide

theorem depthTwo_supertile_has_fixed_redCycle (parent : Index) :
    redCycle (supertile 2 parent) 1 3 1 3 = true :=
  every_depthTwo_supertile_has_fixed_redCycle parent

end RedCycles
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
