/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104ShadedFreeLineCoordinates

/-!
# Executable coordinate checks for pair-cover seams

This lightweight module contains the coordinate-only data used by the finite
seam audits.  It deliberately excludes the semantic pair-cover recurrence so
native certificates do not rebuild that proof cone.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace PairCoverSeamArithmetic

open RedShadeCycles ShadedFreeLineRecurrence

/-- The southwest/northeast child selector as an ordinary block index. -/
def childBlock (side : Fin 2) : Nat := side.val + 1

def absoluteChildBlock (parent : Nat) (side : Fin 2) : Nat :=
  4 * parent + childBlock side

/-- Strict membership in one recursive child's quarter-coordinate interval. -/
def InChildInterval (phase : Phase) (depth : Nat)
    (side : Fin 2) (coordinate : Nat) : Prop :=
  quarterWest
      (2 ^ refinementDepth phase depth * childBlock side + west phase depth) <
      coordinate ∧
    coordinate < quarterEast
      (2 ^ refinementDepth phase depth * childBlock side + east phase depth)

def InAbsoluteChildInterval (phase : Phase) (depth parent : Nat)
    (side : Fin 2) (coordinate : Nat) : Prop :=
  quarterWest
      (2 ^ refinementDepth phase depth * absoluteChildBlock parent side +
        west phase depth) < coordinate ∧
    coordinate < quarterEast
      (2 ^ refinementDepth phase depth * absoluteChildBlock parent side +
        east phase depth)

def InSomeChild (phase : Phase) (depth coordinate : Nat) : Prop :=
  ∃ side : Fin 2, InChildInterval phase depth side coordinate

def InSameChild (phase : Phase) (depth first second : Nat) : Prop :=
  ∃ side : Fin 2,
    InChildInterval phase depth side first ∧
      InChildInterval phase depth side second

def InSomeAbsoluteChild (phase : Phase) (depth parent coordinate : Nat) : Prop :=
  ∃ side : Fin 2, InAbsoluteChildInterval phase depth parent side coordinate

def InSameAbsoluteChild (phase : Phase) (depth parent first second : Nat) : Prop :=
  ∃ side : Fin 2,
    InAbsoluteChildInterval phase depth parent side first ∧
      InAbsoluteChildInterval phase depth parent side second

def inAbsoluteChildIntervalCheck (phase : Phase) (depth parent : Nat)
    (side : Fin 2) (coordinate : Nat) : Bool :=
  decide (quarterWest
      (2 ^ refinementDepth phase depth * absoluteChildBlock parent side +
        west phase depth) < coordinate) &&
    decide (coordinate < quarterEast
      (2 ^ refinementDepth phase depth * absoluteChildBlock parent side +
        east phase depth))

def inSomeAbsoluteChildCheck (phase : Phase)
    (depth parent coordinate : Nat) : Bool :=
  inAbsoluteChildIntervalCheck phase depth parent ⟨0, by decide⟩ coordinate ||
    inAbsoluteChildIntervalCheck phase depth parent ⟨1, by decide⟩ coordinate

def inSameAbsoluteChildCheck (phase : Phase)
    (depth parent first second : Nat) : Bool :=
  (inAbsoluteChildIntervalCheck phase depth parent ⟨0, by decide⟩ first &&
      inAbsoluteChildIntervalCheck phase depth parent ⟨0, by decide⟩ second) ||
    (inAbsoluteChildIntervalCheck phase depth parent ⟨1, by decide⟩ first &&
      inAbsoluteChildIntervalCheck phase depth parent ⟨1, by decide⟩ second)

def containedVerticalSeamCheck (phase : Phase)
    (depth parentX parentY column row boundary : Nat) : Bool :=
  !inSomeAbsoluteChildCheck phase depth parentX column ||
    !inSameAbsoluteChildCheck phase depth parentY row boundary

def containedHorizontalSeamCheck (phase : Phase)
    (depth parentX parentY column row boundary : Nat) : Bool :=
  !inSameAbsoluteChildCheck phase depth parentX column boundary ||
    !inSomeAbsoluteChildCheck phase depth parentY row

def successorWest (phase : Phase) (depth block : Nat) : Nat :=
  2 ^ refinementDepth phase (depth + 1) * block + west phase (depth + 1)

def successorEast (phase : Phase) (depth block : Nat) : Nat :=
  2 ^ refinementDepth phase (depth + 1) * block + east phase (depth + 1)

end PairCoverSeamArithmetic
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
