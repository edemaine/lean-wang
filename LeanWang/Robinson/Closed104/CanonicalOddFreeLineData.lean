/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.CanonicalFreeLineData

/-!
# Static certificate data for odd canonical free lines

The raw selected substitution has two interior state classes and one boundary
state class for each orientation and offset parity.  These lists are the least
classes found by closing the deterministic seed under the three refinement
positions used by the sparse line recurrence.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace CanonicalOddFreeLineData

open ShadedSubstitution CanonicalFreeLine

def rowEven : List Nat :=
  [227, 177, 217, 91, 39, 1, 41, 81, 229, 93, 267, 215, 255, 51,
    257, 53, 269, 79]

def rowOdd : List Nat :=
  [128, 185, 131, 11, 99, 123, 120, 304, 9, 299, 187, 296, 307,
    275, 308, 13, 303, 191, 105, 189, 135, 15, 293, 311, 281, 300,
    132, 127, 124, 117, 301, 125, 133, 309]

def rowBoundaryEven : List Nat := [62, 238]
def rowBoundaryOdd : List Nat := [272, 96, 102, 278]

def columnEven : List Nat :=
  [124, 177, 275, 340, 296, 300, 1, 99, 139, 105, 145, 164, 120,
    160, 315, 281, 321, 336]

def columnOdd : List Nat :=
  [221, 9, 203, 13, 41, 185, 23, 189, 39, 27, 45, 217, 199, 215,
    193, 11, 31, 15, 53, 187, 211, 191, 19, 207, 229, 35, 51, 195,
    17, 227, 50, 16, 226, 192]

def columnBoundaryEven : List Nat := [162, 338]
def columnBoundaryOdd : List Nat := [218, 42, 230, 54]

inductive StripAxis where
  | row
  | column
deriving DecidableEq

inductive StripParity where
  | even
  | odd
deriving DecidableEq

structure StripTransition where
  source : StripParity
  target : StripParity
  localFixed : Fin 4
deriving DecidableEq

def evenZeroTransition : StripTransition := ⟨.even, .even, 0⟩
def evenOneTransition : StripTransition := ⟨.even, .odd, 1⟩
def oddThreeTransition : StripTransition := ⟨.odd, .odd, 3⟩

def stripTransitions : List StripTransition :=
  [evenZeroTransition, evenOneTransition, oddThreeTransition]

def interiorClass : StripAxis → StripParity → List Nat
  | .row, .even => rowEven
  | .row, .odd => rowOdd
  | .column, .even => columnEven
  | .column, .odd => columnOdd

def boundaryClass : StripAxis → StripParity → List Nat
  | .row, .even => rowBoundaryEven
  | .row, .odd => rowBoundaryOdd
  | .column, .even => columnBoundaryEven
  | .column, .odd => columnBoundaryOdd

def childAt? (node childX childY : Nat) : Option Nat :=
  childNode node (childX + 4 * childY)

def childAtAxis? : StripAxis → Nat → Nat → Nat → Option Nat
  | .row, node, along, fixed => childAt? node along fixed
  | .column, node, along, fixed => childAt? node fixed along

def childrenInStripClass (axis : StripAxis) (sources targets : List Nat)
    (localFixed : Nat) : Bool :=
  sources.all fun node =>
    (List.range 4).all fun along =>
      (childAtAxis? axis node along localFixed).any fun child => child ∈ targets

def boundaryChildInStripClass (axis : StripAxis) (sources targets : List Nat)
    (localFixed : Nat) : Bool :=
  sources.all fun node =>
    (childAtAxis? axis node 0 localFixed).any fun child => child ∈ targets

def boundaryEntersStripClass (axis : StripAxis) (sources targets : List Nat)
    (localFixed : Nat) : Bool :=
  sources.all fun node =>
    (List.range 3).all fun offset =>
      (childAtAxis? axis node (offset + 1) localFixed).any fun child =>
        child ∈ targets

def stripTransitionComplete (axis : StripAxis)
    (transition : StripTransition) : Bool :=
  childrenInStripClass axis (interiorClass axis transition.source)
      (interiorClass axis transition.target) transition.localFixed &&
    boundaryChildInStripClass axis (boundaryClass axis transition.source)
      (boundaryClass axis transition.target) transition.localFixed &&
    boundaryEntersStripClass axis (boundaryClass axis transition.source)
      (interiorClass axis transition.target) transition.localFixed

def seed : Nat := encodeNode false 0

def seedNodeAt? (x y : Nat) : Option Nat :=
  levelTwoNode? seed x y

def optionIn (node : Option Nat) (members : List Nat) : Bool :=
  node.any fun value => value ∈ members

def rowClearComplete : Bool :=
  (rowEven.all fun node => rawRowClear node 1) &&
    (rowOdd.all fun node => rawRowClear node 1)

def columnClearComplete : Bool :=
  (columnEven.all fun node => rawColumnClear node 1) &&
    (columnOdd.all fun node => rawColumnClear node 1)

def stripTransitionsComplete : Bool :=
  [.row, .column].all fun axis =>
    stripTransitions.all (stripTransitionComplete axis)

def baseComplete : Bool :=
  ((List.range 3).all fun dx => optionIn (seedNodeAt? (dx + 3) 4) rowEven) &&
    optionIn (seedNodeAt? 2 4) rowBoundaryEven &&
    ((List.range 3).all fun dy =>
      optionIn (seedNodeAt? 4 (dy + 3)) columnEven) &&
    optionIn (seedNodeAt? 4 2) columnBoundaryEven

def rootCycleComplete : Bool := oddRootCycleLight seed

def checks : List Bool :=
  [rowClearComplete, columnClearComplete,
    stripTransitionsComplete, baseComplete, rootCycleComplete]

def complete : Bool := checks.all id

end CanonicalOddFreeLineData
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
