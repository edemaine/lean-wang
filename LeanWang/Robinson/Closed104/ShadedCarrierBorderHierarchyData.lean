/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.ShadedCarrierHierarchy
import LeanWang.Robinson.Closed104.ShadedSignalRectangle
import LeanWang.Robinson.Closed104.ShadedSubstitutionSupertiles

/-!
# Executable finite hierarchy formula for the selected shaded borders

The selected border is the outer opening or a boundary from one of the
finitely many frame depths present at the requested level. A finite
extended-patch invariant connects this arithmetic formula directly to the
reachable decorated substitution nodes.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace ShadedCarrierBorderHierarchy

open Signals.FreeCellLocal ShadedCarrierHierarchy ShadedSubstitution

/-- The four row-border and four column-border observations in one `2 x 2`
quarter block, in row-major order. -/
abbrev BorderPatch := List (Option Bool)

def emptyPatch : BorderPatch := List.replicate 8 none

def patchData (data : DecoratedData) : BorderPatch :=
  let indexGrid : Nat → Nat → Index := fun _ _ => data.parent
  let shadeGrid : Nat → Nat → RedShades.State := fun x y =>
    data.block.at (x % 2) (y % 2)
  let rows := (List.range 2).flatMap fun y => (List.range 2).map fun x =>
    ShadedSignalRectangle.horizontalInteriorCode <|
      ShadedSignals.selectedVerticalFor
        (componentAt indexGrid x y) (quadrantAt x y) (shadeGrid x y)
  let columns := (List.range 2).flatMap fun y => (List.range 2).map fun x =>
    ShadedSignalRectangle.verticalInteriorCode <|
      ShadedSignals.selectedHorizontalFor
        (componentAt indexGrid x y) (quadrantAt x y) (shadeGrid x y)
  rows ++ columns

def nodePatch (node : Nat) : BorderPatch :=
  ((modelData node).map patchData).getD emptyPatch

def horizontalOutput (node x y : Nat) : Option Bool :=
  (nodePatch node)[x + 2 * y]?.getD none

def verticalOutput (node x y : Nat) : Option Bool :=
  (nodePatch node)[4 + x + 2 * y]?.getD none

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
column-border patch. The one-cell halo makes refinement local. -/
abbrev ExtendedPatch := List (Option Bool)

def extendedPatch (level blockX blockY : Nat) : ExtendedPatch :=
  let rows := (List.range 3).flatMap fun y => (List.range 3).map fun x =>
    selectedBorder level (2 * blockX + x) (2 * blockY + y)
  let columns := (List.range 3).flatMap fun y => (List.range 3).map fun x =>
    selectedBorder level (2 * blockY + y) (2 * blockX + x)
  rows ++ columns

def patchEntry (patch : ExtendedPatch) (index : Nat) : Option Bool :=
  patch[index]?.getD none

/-- Forget the one-cell halo and return the node's `2 x 2` visible patch. -/
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

/-- Finite recursion state: the actual decorated node, coordinate parities,
and the arithmetic border patch around it. -/
structure State where
  node : Nat
  blockXParity : Nat
  blockYParity : Nat
  patch : ExtendedPatch
deriving DecidableEq, Repr

/-- Executable decorated-node index generated below one root node. -/
def generatedNode : Nat → Nat → Nat → Nat → Nat
  | 0, rootNode, _, _ => rootNode
  | level + 1, rootNode, x, y =>
      (childNode (generatedNode level rootNode (x / 4) (y / 4))
        (x % 4 + 4 * (y % 4))).getD 0

def state (level blockX blockY : Nat) : State where
  node := generatedNode level (encodeNode false 0) blockX blockY
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
  node := (childNode candidate.node (childX + 4 * childY)).getD 0
  blockXParity := childX % 2
  blockYParity := childY % 2
  patch := refinePatch candidate childX childY

def stateChildren (candidate : State) : List State :=
  (List.range 4).flatMap fun childY =>
    (List.range 4).map fun childX => refineState candidate childX childY

def closureAux : Nat → List State → List State → List State
  | 0, _, visited => visited
  | _ + 1, [], visited => visited
  | fuel + 1, candidate :: queue, visited =>
      if candidate ∈ visited then closureAux fuel queue visited
      else closureAux fuel (queue ++ stateChildren candidate) (candidate :: visited)

/-- Complete finite state closure below the concrete seed. -/
def states : List State := closureAux 10000 [state 0 0 0] []

def stateValid (candidate : State) : Bool :=
  decide (candidate.node ∈ reachable) &&
    decide (visiblePatch candidate.patch = nodePatch candidate.node)

def statesValid : Bool := states.all stateValid

def closedValid : Bool :=
  states.all fun candidate =>
    (stateChildren candidate).all fun child => child ∈ states

end ShadedCarrierBorderHierarchy
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
