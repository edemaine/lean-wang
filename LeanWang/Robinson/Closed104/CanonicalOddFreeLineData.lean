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

def childAt? (node childX childY : Nat) : Option Nat :=
  childNode node (childX + 4 * childY)

def childrenInRowClass (sources targets : List Nat) (childY : Nat) : Bool :=
  sources.all fun node =>
    (List.range 4).all fun childX =>
      (childAt? node childX childY).any fun child => child ∈ targets

def childrenInColumnClass (sources targets : List Nat) (childX : Nat) : Bool :=
  sources.all fun node =>
    (List.range 4).all fun childY =>
      (childAt? node childX childY).any fun child => child ∈ targets

def boundaryChildInClass (sources targets : List Nat)
    (childX childY : Nat) : Bool :=
  sources.all fun node =>
    (childAt? node childX childY).any fun child => child ∈ targets

def rowBoundaryEnters (sources targets : List Nat) (childY : Nat) : Bool :=
  sources.all fun node =>
    (List.range 3).all fun dx =>
      (childAt? node (dx + 1) childY).any fun child => child ∈ targets

def columnBoundaryEnters (sources targets : List Nat) (childX : Nat) : Bool :=
  sources.all fun node =>
    (List.range 3).all fun dy =>
      (childAt? node childX (dy + 1)).any fun child => child ∈ targets

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

def rowTransitionsComplete : Bool :=
  childrenInRowClass rowEven rowEven 0 &&
    childrenInRowClass rowEven rowOdd 1 &&
    childrenInRowClass rowOdd rowOdd 3

def columnTransitionsComplete : Bool :=
  childrenInColumnClass columnEven columnEven 0 &&
    childrenInColumnClass columnEven columnOdd 1 &&
    childrenInColumnClass columnOdd columnOdd 3

def rowBoundaryComplete : Bool :=
  boundaryChildInClass rowBoundaryEven rowBoundaryEven 0 0 &&
    boundaryChildInClass rowBoundaryEven rowBoundaryOdd 0 1 &&
    boundaryChildInClass rowBoundaryOdd rowBoundaryOdd 0 3 &&
    rowBoundaryEnters rowBoundaryEven rowEven 0 &&
    rowBoundaryEnters rowBoundaryEven rowOdd 1 &&
    rowBoundaryEnters rowBoundaryOdd rowOdd 3

def columnBoundaryComplete : Bool :=
  boundaryChildInClass columnBoundaryEven columnBoundaryEven 0 0 &&
    boundaryChildInClass columnBoundaryEven columnBoundaryOdd 1 0 &&
    boundaryChildInClass columnBoundaryOdd columnBoundaryOdd 3 0 &&
    columnBoundaryEnters columnBoundaryEven columnEven 0 &&
    columnBoundaryEnters columnBoundaryEven columnOdd 1 &&
    columnBoundaryEnters columnBoundaryOdd columnOdd 3

def baseComplete : Bool :=
  ((List.range 3).all fun dx => optionIn (seedNodeAt? (dx + 3) 4) rowEven) &&
    optionIn (seedNodeAt? 2 4) rowBoundaryEven &&
    ((List.range 3).all fun dy =>
      optionIn (seedNodeAt? 4 (dy + 3)) columnEven) &&
    optionIn (seedNodeAt? 4 2) columnBoundaryEven

def rootCycleComplete : Bool := oddRootCycleLight seed

def checks : List Bool :=
  [rowClearComplete, columnClearComplete,
    rowTransitionsComplete, columnTransitionsComplete,
    rowBoundaryComplete, columnBoundaryComplete,
    baseComplete, rootCycleComplete]

def complete : Bool := checks.all id

end CanonicalOddFreeLineData
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
