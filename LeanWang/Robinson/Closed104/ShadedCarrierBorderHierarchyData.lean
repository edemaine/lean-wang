/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5/5.6
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

def nodeParent (node : Nat) : Option Index :=
  (modelData node).map DecoratedData.parent

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

/-- Stored witnesses; the certificate checks validity, seed membership, and closure. -/
def stateGroup0 : List State := [
  ⟨133, 0, 1, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, some false, some false, some false]⟩,
  ⟨192, 1, 0, [none, none, some false, none, none, some false, none, none, some false, none, none, none, none, none, none, none, none, none]⟩,
  ⟨89, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨301, 0, 1, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, some false, some false, some false]⟩,
  ⟨263, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨155, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨149, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨143, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨137, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨157, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨226, 1, 0, [none, none, some false, none, none, some false, none, none, some false, none, none, none, none, none, none, none, none, none]⟩,
  ⟨151, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨111, 0, 1, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨83, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨321, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨315, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨275, 0, 1, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨257, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨167, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨58, 0, 0, [none, none, none, none, none, none, none, none, none, some false, some false, some false, none, none, none, none, none, none]⟩,
  ⟨76, 0, 0, [none, none, none, none, none, none, none, none, none, some false, some false, some false, none, none, none, none, none, none]⟩,
  ⟨194, 1, 0, [none, none, none, none, none, none, none, none, none, some false, some false, some false, none, none, none, none, none, none]⟩,
  ⟨86, 0, 0, [none, none, none, none, none, none, none, none, none, some false, some false, some false, none, none, none, none, none, none]⟩,
  ⟨46, 1, 0, [none, none, none, none, none, none, none, none, none, some false, some false, some false, none, none, none, none, none, none]⟩
]

def stateGroup1 : List State := [
  ⟨67, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨85, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨117, 0, 1, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, some false, some false, some false]⟩,
  ⟨102, 0, 1, [none, some true, none, none, some true, none, none, some true, none, none, none, none, none, none, none, none, some false, some false]⟩,
  ⟨142, 0, 0, [none, some true, none, none, some true, none, none, some true, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨140, 0, 0, [none, some true, none, none, some true, none, none, some true, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨102, 0, 1, [none, some true, none, none, some true, none, none, some true, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨136, 0, 0, [none, some true, none, none, some true, none, none, some true, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨96, 0, 1, [none, some true, none, none, some true, none, none, some true, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨309, 0, 1, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, some false, some false, some false]⟩,
  ⟨16, 1, 0, [none, none, some false, none, none, some false, none, none, some false, none, none, none, none, none, none, none, none, none]⟩,
  ⟨61, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨237, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨265, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨125, 0, 1, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, some false, some false, some false]⟩,
  ⟨165, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨223, 1, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨235, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨59, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨161, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨121, 0, 1, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨87, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨47, 1, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨57, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩
]

def stateGroup2 : List State := [
  ⟨331, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨325, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨319, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨313, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨349, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨351, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨232, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨251, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨345, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨305, 0, 1, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨260, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨220, 1, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨20, 1, 0, [none, none, some false, none, none, none, none, none, none, some false, some false, some false, none, none, none, none, none, none]⟩,
  ⟨236, 0, 0, [none, none, none, none, none, none, none, none, none, some false, some false, some false, none, none, none, none, none, none]⟩,
  ⟨244, 0, 0, [none, none, none, none, none, none, none, none, none, some false, some false, some false, none, none, none, none, none, none]⟩,
  ⟨20, 1, 0, [none, none, none, none, none, none, none, none, none, some false, some false, some false, none, none, none, none, none, none]⟩,
  ⟨264, 0, 0, [none, none, none, none, none, none, none, none, none, some false, some false, some false, none, none, none, none, none, none]⟩,
  ⟨224, 1, 0, [none, none, none, none, none, none, none, none, none, some false, some false, some false, none, none, none, none, none, none]⟩,
  ⟨290, 0, 1, [some false, none, none, some false, none, none, some false, none, none, none, none, none, none, none, none, some false, none, none]⟩,
  ⟨330, 0, 0, [some false, none, none, some false, none, none, some false, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨328, 0, 0, [some false, none, none, some false, none, none, some false, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨15, 1, 1, [none, none, some false, none, none, some false, none, none, some false, none, none, none, none, none, none, some false, some false, some false]⟩,
  ⟨135, 0, 1, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, some false, some false, some false]⟩,
  ⟨333, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩
]

def stateGroup3 : List State := [
  ⟨290, 0, 1, [some false, none, none, some false, none, none, some false, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨324, 0, 0, [some false, none, none, some false, none, none, some false, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨284, 0, 1, [some false, none, none, some false, none, none, some false, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨50, 1, 0, [none, none, some false, none, none, some false, none, none, some false, none, none, none, none, none, none, none, none, none]⟩,
  ⟨327, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨287, 0, 1, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨95, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨271, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨259, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨173, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨175, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨56, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨75, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨169, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨129, 0, 1, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨84, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨44, 1, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨196, 1, 0, [none, none, some false, none, none, none, none, none, none, some false, some false, some false, none, none, none, none, none, none]⟩,
  ⟨60, 0, 0, [none, none, none, none, none, none, none, none, none, some false, some false, some false, none, none, none, none, none, none]⟩,
  ⟨68, 0, 0, [none, none, none, none, none, none, none, none, none, some false, some false, some false, none, none, none, none, none, none]⟩,
  ⟨196, 1, 0, [none, none, none, none, none, none, none, none, none, some false, some false, some false, none, none, none, none, none, none]⟩,
  ⟨88, 0, 0, [none, none, none, none, none, none, none, none, none, some false, some false, some false, none, none, none, none, none, none]⟩,
  ⟨48, 1, 0, [none, none, none, none, none, none, none, none, none, some false, some false, some false, none, none, none, none, none, none]⟩,
  ⟨114, 0, 1, [some false, none, none, some false, none, none, some false, none, none, none, none, none, none, none, none, some false, none, none]⟩
]

def stateGroup4 : List State := [
  ⟨154, 0, 0, [some false, none, none, some false, none, none, some false, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨152, 0, 0, [some false, none, none, some false, none, none, some false, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨191, 1, 1, [none, none, some false, none, none, some false, none, none, some false, none, none, none, none, none, none, some false, some false, some false]⟩,
  ⟨281, 0, 1, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, some false, some false, some false]⟩,
  ⟨53, 1, 0, [none, none, some false, none, none, some false, none, none, some false, none, none, none, none, none, none, none, none, none]⟩,
  ⟨15, 1, 1, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, some false, some false, some false]⟩,
  ⟨127, 0, 1, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, some false, some false, some false]⟩,
  ⟨189, 1, 1, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, some false, some false, some false]⟩,
  ⟨105, 0, 1, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, some false, some false, some false]⟩,
  ⟨145, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨217, 1, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨269, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨114, 0, 1, [some false, none, none, some false, none, none, some false, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨148, 0, 0, [some false, none, none, some false, none, none, some false, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨108, 0, 1, [some false, none, none, some false, none, none, some false, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨229, 1, 0, [none, none, some false, none, none, some false, none, none, some false, none, none, none, none, none, none, none, none, none]⟩,
  ⟨93, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨139, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨99, 0, 1, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨81, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨41, 1, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨341, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨343, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨234, 0, 0, [none, none, none, none, none, none, none, none, none, some false, some false, some false, none, none, none, none, none, none]⟩
]

def stateGroup5 : List State := [
  ⟨252, 0, 0, [none, none, none, none, none, none, none, none, none, some false, some false, some false, none, none, none, none, none, none]⟩,
  ⟨337, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨297, 0, 1, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨18, 1, 0, [none, none, none, none, none, none, none, none, none, some false, some false, some false, none, none, none, none, none, none]⟩,
  ⟨262, 0, 0, [none, none, none, none, none, none, none, none, none, some false, some false, some false, none, none, none, none, none, none]⟩,
  ⟨222, 1, 0, [none, none, none, none, none, none, none, none, none, some false, some false, some false, none, none, none, none, none, none]⟩,
  ⟨233, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨243, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨261, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨311, 0, 1, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, some false, some false, some false]⟩,
  ⟨293, 0, 1, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, some false, some false, some false]⟩,
  ⟨191, 1, 1, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, some false, some false, some false]⟩,
  ⟨303, 0, 1, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, some false, some false, some false]⟩,
  ⟨13, 1, 1, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, some false, some false, some false]⟩,
  ⟨278, 0, 1, [none, some true, none, none, some true, none, none, some true, none, none, none, none, none, none, none, none, some false, some false]⟩,
  ⟨318, 0, 0, [none, some true, none, none, some true, none, none, some true, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨316, 0, 0, [none, some true, none, none, some true, none, none, some true, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨278, 0, 1, [none, some true, none, none, some true, none, none, some true, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨312, 0, 0, [none, some true, none, none, some true, none, none, some true, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨272, 0, 1, [none, some true, none, none, some true, none, none, some true, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨156, 0, 0, [some false, none, none, some false, none, none, some false, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨159, 0, 0, [some false, none, none, some false, none, none, some false, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨211, 1, 0, [none, none, some false, none, none, some false, none, none, some false, none, none, none, none, none, none, none, none, none]⟩,
  ⟨19, 1, 0, [none, none, some false, none, none, some false, none, none, some false, none, none, none, none, none, none, none, none, none]⟩
]

def stateGroup6 : List State := [
  ⟨90, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨71, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨116, 0, 1, [some false, none, none, some false, none, none, some false, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨150, 0, 0, [some false, none, none, some false, none, none, some false, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨110, 0, 1, [some false, none, none, some false, none, none, some false, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨78, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨38, 1, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨31, 1, 0, [none, none, some false, none, none, some false, none, none, some false, none, none, none, none, none, none, none, none, none]⟩,
  ⟨230, 1, 0, [none, none, none, none, none, some false, none, none, some false, none, none, none, some true, some true, some true, none, none, none]⟩,
  ⟨94, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, some true, some true, some true, none, none, none]⟩,
  ⟨65, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, some true, some true, some true, none, none, none]⟩,
  ⟨230, 1, 0, [none, none, none, none, none, none, none, none, none, none, none, none, some true, some true, some true, none, none, none]⟩,
  ⟨82, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, some true, some true, some true, none, none, none]⟩,
  ⟨42, 1, 0, [none, none, none, none, none, none, none, none, none, none, none, none, some true, some true, some true, none, none, none]⟩,
  ⟨171, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨172, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨168, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨332, 0, 0, [some false, none, none, some false, none, none, some false, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨335, 0, 0, [some false, none, none, some false, none, none, some false, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨15, 1, 1, [none, none, some false, none, none, some false, none, none, some false, none, none, none, none, none, none, none, none, none]⟩,
  ⟨35, 1, 0, [none, none, some false, none, none, some false, none, none, some false, none, none, none, none, none, none, none, none, none]⟩,
  ⟨11, 1, 1, [none, none, some false, none, none, some false, none, none, some false, none, none, none, none, none, none, none, none, none]⟩,
  ⟨195, 1, 0, [none, none, some false, none, none, some false, none, none, some false, none, none, none, none, none, none, none, none, none]⟩,
  ⟨266, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩
]

def stateGroup7 : List State := [
  ⟨247, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨292, 0, 1, [some false, none, none, some false, none, none, some false, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨326, 0, 0, [some false, none, none, some false, none, none, some false, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨286, 0, 1, [some false, none, none, some false, none, none, some false, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨254, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨214, 1, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨191, 1, 1, [none, none, some false, none, none, some false, none, none, some false, none, none, none, none, none, none, none, none, none]⟩,
  ⟨207, 1, 0, [none, none, some false, none, none, some false, none, none, some false, none, none, none, none, none, none, none, none, none]⟩,
  ⟨187, 1, 1, [none, none, some false, none, none, some false, none, none, some false, none, none, none, none, none, none, none, none, none]⟩,
  ⟨54, 1, 0, [none, none, none, none, none, some false, none, none, some false, none, none, none, some true, some true, some true, none, none, none]⟩,
  ⟨270, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, some true, some true, some true, none, none, none]⟩,
  ⟨241, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, some true, some true, some true, none, none, none]⟩,
  ⟨54, 1, 0, [none, none, none, none, none, none, none, none, none, none, none, none, some true, some true, some true, none, none, none]⟩,
  ⟨258, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, some true, some true, some true, none, none, none]⟩,
  ⟨218, 1, 0, [none, none, none, none, none, none, none, none, none, none, none, none, some true, some true, some true, none, none, none]⟩,
  ⟨348, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨347, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨344, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨309, 0, 1, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨350, 0, 0, [none, none, none, none, none, none, none, none, none, some false, some false, some false, none, none, none, none, none, none]⟩,
  ⟨305, 0, 1, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, some false, some false, some false]⟩,
  ⟨16, 1, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨250, 0, 0, [some false, none, none, some false, none, none, some false, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨220, 1, 0, [none, none, some false, none, none, some false, none, none, some false, none, none, none, none, none, none, none, none, none]⟩
]

def stateGroup8 : List State := [
  ⟨183, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨21, 1, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨245, 0, 0, [none, some true, none, none, some true, none, none, some true, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨225, 1, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨323, 0, 0, [none, some true, none, none, some true, none, none, some true, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨125, 0, 1, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨166, 0, 0, [none, none, none, none, none, none, none, none, none, some false, some false, some false, none, none, none, none, none, none]⟩,
  ⟨121, 0, 1, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, some false, some false, some false]⟩,
  ⟨195, 1, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨77, 0, 0, [some false, none, none, some false, none, none, some false, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨47, 1, 0, [none, none, some false, none, none, some false, none, none, some false, none, none, none, none, none, none, none, none, none]⟩,
  ⟨5, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨17, 1, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨242, 0, 0, [none, some true, none, none, some true, none, none, some true, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨221, 1, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨291, 0, 1, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨329, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, some true, some true, some true, none, none, none]⟩,
  ⟨285, 0, 1, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨249, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, some true, some true, some true, none, none, none]⟩,
  ⟨279, 0, 1, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨317, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, some true, some true, some true, none, none, none]⟩,
  ⟨273, 0, 1, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨267, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨239, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩
]

def stateGroup9 : List State := [
  ⟨255, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨293, 0, 1, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨334, 0, 0, [none, none, none, none, none, none, none, none, none, some false, some false, some false, none, none, none, none, none, none]⟩,
  ⟨287, 0, 1, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, some false, some false, some false]⟩,
  ⟨50, 1, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨246, 0, 0, [some false, none, none, some false, none, none, some false, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨214, 1, 0, [none, none, some false, none, none, some false, none, none, some false, none, none, none, none, none, none, none, none, none]⟩,
  ⟨179, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨340, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨55, 1, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨240, 0, 0, [none, some true, none, none, some true, none, none, some true, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨219, 1, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨339, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨105, 0, 1, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨146, 0, 0, [none, none, none, none, none, none, none, none, none, some false, some false, some false, none, none, none, none, none, none]⟩,
  ⟨99, 0, 1, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, some false, some false, some false]⟩,
  ⟨229, 1, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨72, 0, 0, [some false, none, none, some false, none, none, some false, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨41, 1, 0, [none, none, some false, none, none, some false, none, none, some false, none, none, none, none, none, none, none, none, none]⟩,
  ⟨1, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨303, 0, 1, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨212, 1, 0, [none, none, none, none, none, none, none, none, none, some false, some false, some false, none, none, none, none, none, none]⟩,
  ⟨180, 0, 0, [none, some true, none, none, none, none, none, none, none, none, some false, some false, none, none, none, none, none, none]⟩,
  ⟨203, 1, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩
]

def stateGroup10 : List State := [
  ⟨320, 0, 0, [none, some true, none, none, some true, none, none, some true, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨187, 1, 1, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, some false, some false, some false]⟩,
  ⟨276, 0, 1, [none, some true, none, none, some true, none, none, some true, none, none, none, none, none, none, none, none, some false, some false]⟩,
  ⟨51, 1, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨238, 0, 0, [none, some true, none, none, some true, none, none, some true, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨215, 1, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨132, 0, 1, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨170, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, some true, some true, some true, none, none, none]⟩,
  ⟨128, 0, 1, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨336, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨300, 0, 1, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨338, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, some true, some true, some true, none, none, none]⟩,
  ⟨296, 0, 1, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨133, 0, 1, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨174, 0, 0, [none, none, none, none, none, none, none, none, none, some false, some false, some false, none, none, none, none, none, none]⟩,
  ⟨129, 0, 1, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, some false, some false, some false]⟩,
  ⟨192, 1, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨74, 0, 0, [some false, none, none, some false, none, none, some false, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨44, 1, 0, [none, none, some false, none, none, some false, none, none, some false, none, none, none, none, none, none, none, none, none]⟩,
  ⟨7, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨197, 1, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨69, 0, 0, [none, some true, none, none, some true, none, none, some true, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨49, 1, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨147, 0, 0, [none, some true, none, none, some true, none, none, some true, none, none, none, none, none, none, none, none, none, none]⟩
]

def stateGroup11 : List State := [
  ⟨301, 0, 1, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨342, 0, 0, [none, none, none, none, none, none, none, none, none, some false, some false, some false, none, none, none, none, none, none]⟩,
  ⟨297, 0, 1, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, some false, some false, some false]⟩,
  ⟨19, 1, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨253, 0, 0, [some false, none, none, some false, none, none, some false, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨223, 1, 0, [none, none, some false, none, none, some false, none, none, some false, none, none, none, none, none, none, none, none, none]⟩,
  ⟨181, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨193, 1, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨66, 0, 0, [none, some true, none, none, some true, none, none, some true, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨45, 1, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨115, 0, 1, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨153, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, some true, some true, some true, none, none, none]⟩,
  ⟨109, 0, 1, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨73, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, some true, some true, some true, none, none, none]⟩,
  ⟨103, 0, 1, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨141, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, some true, some true, some true, none, none, none]⟩,
  ⟨97, 0, 1, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨91, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨63, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨79, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨135, 0, 1, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨117, 0, 1, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨35, 1, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨6, 0, 0, [some false, none, none, none, none, none, none, none, none, some false, none, none, none, none, none, none, none, none]⟩
]

def stateGroup12 : List State := [
  ⟨28, 1, 0, [none, none, some false, none, none, none, none, none, none, some false, some false, some false, none, none, none, none, none, none]⟩,
  ⟨158, 0, 0, [none, none, none, none, none, none, none, none, none, some false, some false, some false, none, none, none, none, none, none]⟩,
  ⟨112, 0, 1, [some false, none, none, some false, none, none, some false, none, none, none, none, none, none, none, none, some false, none, none]⟩,
  ⟨185, 1, 1, [none, none, some false, none, none, some false, none, none, some false, none, none, none, none, none, none, some false, some false, some false]⟩,
  ⟨111, 0, 1, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, some false, some false, some false]⟩,
  ⟨226, 1, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨70, 0, 0, [some false, none, none, some false, none, none, some false, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨38, 1, 0, [none, none, some false, none, none, some false, none, none, some false, none, none, none, none, none, none, none, none, none]⟩,
  ⟨3, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨164, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨231, 1, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨64, 0, 0, [none, some true, none, none, some true, none, none, some true, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨43, 1, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨163, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨311, 0, 1, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨281, 0, 1, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨211, 1, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨182, 0, 0, [some false, none, none, none, none, none, none, none, none, some false, none, none, none, none, none, none, none, none]⟩,
  ⟨204, 1, 0, [none, none, some false, none, none, none, none, none, none, some false, some false, some false, none, none, none, none, none, none]⟩,
  ⟨322, 0, 0, [none, none, none, none, none, none, none, none, none, some false, some false, some false, none, none, none, none, none, none]⟩,
  ⟨288, 0, 1, [some false, none, none, some false, none, none, some false, none, none, none, none, none, none, none, none, some false, none, none]⟩,
  ⟨9, 1, 1, [none, none, some false, none, none, some false, none, none, some false, none, none, none, none, none, none, some false, some false, some false]⟩,
  ⟨275, 0, 1, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, some false, some false, some false]⟩,
  ⟨53, 1, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩
]

def stateGroup13 : List State := [
  ⟨248, 0, 0, [some false, none, none, some false, none, none, some false, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨217, 1, 0, [none, none, some false, none, none, some false, none, none, some false, none, none, none, none, none, none, none, none, none]⟩,
  ⟨177, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨127, 0, 1, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨36, 1, 0, [none, none, none, none, none, none, none, none, none, some false, some false, some false, none, none, none, none, none, none]⟩,
  ⟨4, 0, 0, [none, some true, none, none, none, none, none, none, none, none, some false, some false, none, none, none, none, none, none]⟩,
  ⟨27, 1, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨144, 0, 0, [none, some true, none, none, some true, none, none, some true, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨11, 1, 1, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, some false, some false, some false]⟩,
  ⟨100, 0, 1, [none, some true, none, none, some true, none, none, some true, none, none, none, none, none, none, none, none, some false, some false]⟩,
  ⟨227, 1, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨62, 0, 0, [none, some true, none, none, some true, none, none, some true, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨39, 1, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨295, 0, 1, [some false, none, none, some false, none, none, some false, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨13, 1, 1, [none, none, some false, none, none, some false, none, none, some false, none, none, none, none, none, none, none, none, none]⟩,
  ⟨308, 0, 1, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨207, 1, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨178, 0, 0, [none, none, none, some false, none, none, some false, none, none, none, none, none, some true, none, none, none, none, none]⟩,
  ⟨201, 1, 0, [none, none, none, none, none, some false, none, none, some false, none, none, none, some true, some true, some true, none, none, none]⟩,
  ⟨346, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, some true, some true, some true, none, none, none]⟩,
  ⟨307, 0, 1, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨304, 0, 1, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨268, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, some true, some true, some true, none, none, none]⟩,
  ⟨160, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩
]

def stateGroup14 : List State := [
  ⟨119, 0, 1, [some false, none, none, some false, none, none, some false, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨189, 1, 1, [none, none, some false, none, none, some false, none, none, some false, none, none, none, none, none, none, none, none, none]⟩,
  ⟨124, 0, 1, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨31, 1, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨2, 0, 0, [none, none, none, some false, none, none, some false, none, none, none, none, none, some true, none, none, none, none, none]⟩,
  ⟨25, 1, 0, [none, none, none, none, none, some false, none, none, some false, none, none, none, some true, some true, some true, none, none, none]⟩,
  ⟨162, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, some true, some true, some true, none, none, none]⟩,
  ⟨131, 0, 1, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨120, 0, 1, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨92, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, some true, some true, some true, none, none, none]⟩,
  ⟨15, 1, 1, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨107, 0, 1, [none, some true, none, none, some true, none, none, some true, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨189, 1, 1, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨104, 0, 1, [none, some true, none, none, some true, none, none, some true, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨33, 1, 0, [none, none, none, none, none, none, none, none, none, none, none, none, some true, some true, some true, none, none, none]⟩,
  ⟨23, 1, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨138, 0, 0, [none, some true, none, none, some true, none, none, some true, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨11, 1, 1, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨123, 0, 1, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨185, 1, 1, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨98, 0, 1, [none, some true, none, none, some true, none, none, some true, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨228, 1, 0, [none, none, none, none, none, none, none, none, none, none, none, none, some true, some true, some true, none, none, none]⟩,
  ⟨80, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, some true, some true, some true, none, none, none]⟩,
  ⟨40, 1, 0, [none, none, none, none, none, none, none, none, none, none, none, none, some true, some true, some true, none, none, none]⟩
]

def stateGroup15 : List State := [
  ⟨191, 1, 1, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨283, 0, 1, [none, some true, none, none, some true, none, none, some true, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨13, 1, 1, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨280, 0, 1, [none, some true, none, none, some true, none, none, some true, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨209, 1, 0, [none, none, none, none, none, none, none, none, none, none, none, none, some true, some true, some true, none, none, none]⟩,
  ⟨199, 1, 0, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨314, 0, 0, [none, some true, none, none, some true, none, none, some true, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨187, 1, 1, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨299, 0, 1, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨9, 1, 1, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨274, 0, 1, [none, some true, none, none, some true, none, none, some true, none, none, none, none, none, none, none, none, none, none]⟩,
  ⟨52, 1, 0, [none, none, none, none, none, none, none, none, none, none, none, none, some true, some true, some true, none, none, none]⟩,
  ⟨256, 0, 0, [none, none, none, none, none, none, none, none, none, none, none, none, some true, some true, some true, none, none, none]⟩,
  ⟨216, 1, 0, [none, none, none, none, none, none, none, none, none, none, none, none, some true, some true, some true, none, none, none]⟩,
  ⟨176, 0, 0, [none, none, none, none, some true, none, none, some true, none, none, none, none, none, some true, some true, none, none, none]⟩,
  ⟨0, 0, 0, [none, none, none, none, some true, none, none, some true, none, none, none, none, none, some true, some true, none, none, none]⟩
]

/-- A finite invariant containing the seed and closed under all children. -/
def states : List State :=
  stateGroup0 ++
  stateGroup1 ++
  stateGroup2 ++
  stateGroup3 ++
  stateGroup4 ++
  stateGroup5 ++
  stateGroup6 ++
  stateGroup7 ++
  stateGroup8 ++
  stateGroup9 ++
  stateGroup10 ++
  stateGroup11 ++
  stateGroup12 ++
  stateGroup13 ++
  stateGroup14 ++
  stateGroup15

def stateValid (candidate : State) : Bool :=
  decide (candidate.node ∈ reachable) &&
    decide (visiblePatch candidate.patch = nodePatch candidate.node)

def statesValid : Bool := states.all stateValid

def closedValid : Bool :=
  states.all fun candidate =>
    (stateChildren candidate).all fun child => child ∈ states

/-- Every index-zero child is either inherited from index zero, introduced at
the center of index four, or the non-carrier copy on a new frame boundary.
The coordinate parities are the thin-layer information needed to distinguish
these cases arithmetically. -/
def cornerTransitionValid (candidate : State) (childX childY : Nat) : Bool :=
  decide (nodeParent (refineState candidate childX childY).node = some 0 →
    (childX = 0 ∧ childY = 0 ∧
      nodeParent candidate.node = some 0 ∧
      candidate.blockXParity = 0 ∧ candidate.blockYParity = 0) ∨
    (childX = 0 ∧ childY = 0 ∧
      nodeParent candidate.node = some 4 ∧
      candidate.blockXParity = 1 ∧ candidate.blockYParity = 1) ∨
    (childX = 2 ∧ childY = 2 ∧
      candidate.blockXParity = 0 ∧ candidate.blockYParity = 0))

def cornerTransitionsValid : Bool :=
  states.all fun candidate =>
    (List.range 4).all fun childY =>
      (List.range 4).all fun childX =>
        cornerTransitionValid candidate childX childY

end ShadedCarrierBorderHierarchy
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
