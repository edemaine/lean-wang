/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.UniversalTM0TableauCells

/-!
# Local dynamics of the direct folded TM0 tableau

This module expresses one Mathlib `TM0` step as a radius-one synchronous rule
on folded cells.  Halting is represented by the absence of a successor for the
cell carrying the head.
-/

noncomputable section

namespace LeanWang
namespace UniversalTM0Tableau

open UniversalTM0Semantic

def Side.opposite : Side → Side
  | .left => .right
  | .right => .left

def Side.isOutward : Side → Turing.Dir → Bool
  | .left, .left | .right, .right => true
  | _, _ => false

def Side.isInward (side : Side) (dir : Turing.Dir) : Bool :=
  !(side.isOutward dir)

def Cell.withHead (cell : Cell) (head : Head) : Cell :=
  { cell with head := head }

def Cell.writeActive (cell : Cell) (side : Side) (symbol : Symbol) : Cell :=
  match side with
  | .left => { cell with left := symbol }
  | .right => { cell with right := symbol }

/-- A head in the left neighbor enters the center exactly on an outward move. -/
def incomingFromLeft? (cell : Cell) : Option (Side × Label) :=
  match cell.head with
  | none => none
  | some (side, q) =>
      match tm0 q (cell.activeSymbol side) with
      | some (q', .move dir) => if side.isOutward dir then some (side, q') else none
      | _ => none

/-- A head in the right neighbor enters the center exactly on an inward move. -/
def incomingFromRight? (cell : Cell) : Option (Side × Label) :=
  match cell.head with
  | none => none
  | some (side, q) =>
      match tm0 q (cell.activeSymbol side) with
      | some (q', .move dir) => if side.isInward dir then some (side, q') else none
      | _ => none

/-- Update the cell currently carrying the head. -/
def updateHeadCell? (atOrigin : Bool) (cell : Cell)
    (side : Side) (q : Label) : Option Cell :=
  match tm0 q (cell.activeSymbol side) with
  | none => none
  | some (q', .write symbol) =>
      some ((cell.writeActive side symbol).withHead (some (side, q')))
  | some (q', .move dir) =>
      if atOrigin && side.isInward dir then
        some (cell.withHead (some (side.opposite, q')))
      else
        some (cell.withHead none)

def incoming? (left right : Cell) : Head :=
  match incomingFromLeft? left with
  | some head => some head
  | none => incomingFromRight? right

/--
The deterministic radius-one update. `atOrigin` says that the left neighbor is
the quarter-plane boundary.  Only an inward move at the origin stays in the
same folded cell; it switches between the two stored tape halves.
-/
def localNextCell? (atOrigin : Bool) (left center right : Cell) : Option Cell :=
  match center.head with
  | some (side, q) => updateHeadCell? atOrigin center side q
  | none => some (center.withHead (incoming? left right))

end UniversalTM0Tableau
end LeanWang
