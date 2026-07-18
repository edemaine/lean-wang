/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.ShadedCarrierBorderFactorSupertiles
import LeanWang.Robinson.Closed104.ShadedCarrierHierarchy

/-!
# Executable finite hierarchy formula for the selected shaded borders

The selected border is the outer opening or a boundary from one of the
finitely many frame depths present at the requested level.  A finite
extended-patch invariant connects this arithmetic formula to the sixteen-state
substitution factor.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace ShadedCarrierBorderHierarchy

open ShadedCarrierHierarchy ShadedCarrierBorderFactor
open ShadedCarrierBorderFactorSupertiles

def ceilDivFour (coordinate : Nat) : Nat := (coordinate + 3) / 4

/-- The border contributed by one frame depth. -/
def frameBorder (depth coordinate transverse : Nat) : Option Bool :=
  if inFrame depth transverse then
    if coordinate % period depth = frameStartResidue depth then some true
    else if coordinate % period depth = frameEndResidue depth then some false
    else none
  else none

/-- Lift an old selected border through one two-substitution. -/
def liftBorder (coordinate : Nat) : Option Bool → Option Bool
  | none => none
  | some true => if coordinate % 4 = 1 then some true else none
  | some false => if coordinate % 4 = 0 then some false else none

def firstBorder (first second : Option Bool) : Option Bool :=
  match first with
  | some orientation => some orientation
  | none => second

/-- The persistent opening on the west or south side of every finite
supertile. -/
def outerBorder (coordinate transverse : Nat) : Option Bool :=
  if coordinate = 1 ∧ 1 ≤ transverse then some true else none

/-- Index zero is the outer border; every positive index is the corresponding
frame depth. -/
def borderCandidate (coordinate transverse : Nat) {level : Nat}
    (index : Fin (level + 1)) : Option Bool :=
  if index.val = 0 then outerBorder coordinate transverse
  else frameBorder index.val coordinate transverse

/-- All selected borders in a canonical level supertile, as a direct bounded
search through its frame depths. -/
def selectedBorder (level coordinate transverse : Nat) : Option Bool :=
  Fin.findSome? (borderCandidate coordinate transverse : Fin (level + 1) → _)

/-- A `3 x 3` row-border patch followed by the transposed `3 x 3`
column-border patch.  The one-cell halo makes refinement local. -/
abbrev ExtendedPatch := List (Option Bool)

def extendedPatch (level blockX blockY : Nat) : ExtendedPatch :=
  let rows := (List.range 3).flatMap fun y => (List.range 3).map fun x =>
    selectedBorder level (2 * blockX + x) (2 * blockY + y)
  let columns := (List.range 3).flatMap fun y => (List.range 3).map fun x =>
    selectedBorder level (2 * blockY + y) (2 * blockX + x)
  rows ++ columns

def patchEntry (patch : ExtendedPatch) (index : Nat) : Option Bool :=
  patch[index]?.getD none

/-- Forget the one-cell halo and return the factor's `2 x 2` visible patch. -/
def visiblePatch (patch : ExtendedPatch) : BorderPatch :=
  [patchEntry patch 0, patchEntry patch 1,
    patchEntry patch 3, patchEntry patch 4,
    patchEntry patch 9, patchEntry patch 10,
    patchEntry patch 12, patchEntry patch 13]

theorem ceilDivFour_eight_mul_add (block offset : Nat) :
    ceilDivFour (8 * block + offset) =
      2 * block + ceilDivFour offset := by
  unfold ceilDivFour
  rw [show 8 * block + offset + 3 =
      (offset + 3) + 4 * (2 * block) by omega]
  simp [Nat.add_mul_div_left, Nat.add_comm]

theorem frameBorder_zero_parity (coordinate transverse offsetX offsetY : Nat) :
    frameBorder 0 (2 * coordinate + offsetX) (2 * transverse + offsetY) =
      frameBorder 0 (2 * (coordinate % 2) + offsetX)
        (2 * (transverse % 2) + offsetY) := by
  have coordinateMod :
      (2 * coordinate + offsetX) % 4 =
        (2 * (coordinate % 2) + offsetX) % 4 := by
    omega
  have transverseMod :
      (2 * transverse + offsetY) % 4 =
        (2 * (transverse % 2) + offsetY) % 4 := by
    omega
  simp [frameBorder, inFrame, period, frameStartResidue, frameEndResidue,
    scale, coordinateMod, transverseMod]

theorem liftBorder_eight_mul_add (block offset : Nat)
    (border : Option Bool) :
    liftBorder (8 * block + offset) border = liftBorder offset border := by
  cases border with
  | none => rfl
  | some orientation =>
      cases orientation <;>
        simp [liftBorder, Nat.add_mod, Nat.mul_mod]

structure State where
  classId : Nat
  blockXParity : Nat
  blockYParity : Nat
  patch : ExtendedPatch
deriving DecidableEq, Repr

def state (level blockX blockY : Nat) : State where
  classId := generatedClass level 15 blockX blockY
  blockXParity := blockX % 2
  blockYParity := blockY % 2
  patch := extendedPatch level blockX blockY

def refinedBorder (candidate : State) (childX childY x y : Nat) : Option Bool :=
  let coarseX := ceilDivFour (2 * childX + x)
  let coarseY := ceilDivFour (2 * childY + y)
  firstBorder
    (liftBorder (2 * childX + x) <|
      patchEntry candidate.patch (coarseX + 3 * coarseY))
    (liftBorder (2 * childX + x) <|
      frameBorder 0 (2 * candidate.blockXParity + coarseX)
        (2 * candidate.blockYParity + coarseY))

def refinedColumnBorder (candidate : State)
    (childX childY x y : Nat) : Option Bool :=
  let coarseX := ceilDivFour (2 * childX + x)
  let coarseY := ceilDivFour (2 * childY + y)
  firstBorder
    (liftBorder (2 * childY + y) <|
      patchEntry candidate.patch (9 + coarseX + 3 * coarseY))
    (liftBorder (2 * childY + y) <|
      frameBorder 0 (2 * candidate.blockYParity + coarseY)
        (2 * candidate.blockXParity + coarseX))

def refinePatch (candidate : State) (childX childY : Nat) : ExtendedPatch :=
  let rows := (List.range 3).flatMap fun y => (List.range 3).map fun x =>
    refinedBorder candidate childX childY x y
  let columns := (List.range 3).flatMap fun y => (List.range 3).map fun x =>
    refinedColumnBorder candidate childX childY x y
  rows ++ columns

def refineState (candidate : State) (childX childY : Nat) : State where
  classId := childClass candidate.classId (childX + 4 * childY)
  blockXParity := childX % 2
  blockYParity := childY % 2
  patch := refinePatch candidate childX childY

/-- The complete finite state set already appears in the level-two
supertile. -/
def states : List State :=
  ((List.range 16).flatMap fun blockY =>
    (List.range 16).map fun blockX => state 2 blockX blockY).eraseDups

def stateValid (candidate : State) : Bool :=
  candidate.classId < 16 &&
    candidate.blockXParity < 2 && candidate.blockYParity < 2 &&
    decide (visiblePatch candidate.patch = classPatch candidate.classId)

def statesValid : Bool :=
  decide (states.length = 25) && states.all stateValid

def refinementValid : Bool :=
  (List.range 16).all fun blockY =>
    (List.range 16).all fun blockX =>
      (List.range 4).all fun childY =>
        (List.range 4).all fun childX =>
          state 3 (4 * blockX + childX) (4 * blockY + childY) =
            refineState (state 2 blockX blockY) childX childY

def closedValid : Bool :=
  states.all fun candidate =>
    (List.range 4).all fun childY =>
      (List.range 4).all fun childX =>
        refineState candidate childX childY ∈ states

end ShadedCarrierBorderHierarchy
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
