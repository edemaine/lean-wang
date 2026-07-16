/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.RoutedScaffold

/-!
# One-dimensional hierarchy behind the shaded carrier grids

At depth `d >= 1`, Robinson frames have period `4^(d+1)`, side
`2 * 4^d`, and begin at residue `4^d + 1`.  A coordinate is owned by its
smallest enclosing frame.  Pairing the owners of a column and row gives the
routed carrier role: equal interior owners are active, while unequal owners
form the horizontal or vertical channel crossing the smaller frame.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace ShadedCarrierHierarchy

def scale (depth : Nat) : Nat := 4 ^ depth

def period (depth : Nat) : Nat := 4 ^ (depth + 1)

def frameStartResidue (depth : Nat) : Nat := scale depth + 1

def frameEndResidue (depth : Nat) : Nat := 3 * scale depth

def inFrame (depth coordinate : Nat) : Bool :=
  frameStartResidue depth ≤ coordinate % period depth &&
    coordinate % period depth ≤ frameEndResidue depth

def onFrameBoundary (depth coordinate : Nat) : Bool :=
  coordinate % period depth = frameStartResidue depth ||
    coordinate % period depth = frameEndResidue depth

/-- Smallest frame depth at most `bound` containing a coordinate. -/
def depthAt : Nat → Nat → Option Nat
  | 0, _ => none
  | bound + 1, coordinate =>
      match depthAt bound coordinate with
      | some depth => some depth
      | none => if inFrame (bound + 1) coordinate then some (bound + 1)
          else none

/-- A row's owner frame carries horizontally through every nonboundary column
inside that frame, including across complete nested frames. -/
def isHorizontalCarrier (level x y : Nat) : Bool :=
  match depthAt (level - 1) y with
  | none => false
  | some depth => inFrame depth x && !onFrameBoundary depth x

/-- A column's owner frame carries vertically through every nonboundary row
inside that frame, including across complete nested frames. -/
def isVerticalCarrier (level x y : Nat) : Bool :=
  match depthAt (level - 1) x with
  | none => false
  | some depth => inFrame depth y && !onFrameBoundary depth y

/-- Carrier role predicted by the nested frame hierarchy.  The corner marker
is deliberately erased to `.active`; marker placement is a separate centered
coordinate property. -/
def carrierRole (level x y : Nat) : RouteRole :=
  match isHorizontalCarrier level x y, isVerticalCarrier level x y with
  | false, false => .inactive
  | true, false => .horizontal
  | false, true => .vertical
  | true, true => .active

def eraseCorner : RouteRole → RouteRole
  | .corner => .active
  | role => role

/-- Coordinates that become logical vertices of their depth's carrier grid. -/
def isFreeCoordinate (depth coordinate : Nat) : Bool :=
  depthAt depth coordinate == some depth &&
    !onFrameBoundary depth coordinate

/-- Number of depth-`depth` logical vertices strictly before a coordinate. -/
def freeCount (depth coordinate : Nat) : Nat :=
  ((List.range coordinate).filter (isFreeCoordinate depth)).length

@[simp] theorem freeCount_succ (depth coordinate : Nat) :
    freeCount depth (coordinate + 1) =
      freeCount depth coordinate + if isFreeCoordinate depth coordinate then 1
        else 0 := by
  cases hfree : isFreeCoordinate depth coordinate <;>
    simp [freeCount, List.range_succ, hfree]

/-- Geometric center of the depth-`depth` frame containing a coordinate. -/
def frameCenter (depth coordinate : Nat) : Nat :=
  coordinate - coordinate % period depth + (2 * scale depth + 1)

/-- Logical vertex coordinate centered at the geometric frame center. -/
def axisCoordinate (depth coordinate : Nat) : Int :=
  (freeCount depth coordinate : Int) -
    freeCount depth (frameCenter depth coordinate)

/-- Logical source immediately before the next step across a channel gap. -/
def axisSource (depth coordinate : Nat) : Int :=
  (freeCount depth coordinate : Int) - 1 -
    freeCount depth (frameCenter depth coordinate)

/-- Physical coordinates of the logical vertices in the first depth-`depth`
frame. -/
def componentCoordinates (depth : Nat) : List Nat :=
  (List.range (2 * scale depth)).filterMap fun offset =>
    let coordinate := frameStartResidue depth + offset
    if isFreeCoordinate depth coordinate then
      some coordinate
    else none

set_option linter.style.nativeDecide false in
theorem componentCoordinates_one :
    componentCoordinates 1 = [6, 7, 8, 9, 10, 11] := by
  native_decide

set_option linter.style.nativeDecide false in
theorem componentCoordinates_two :
    componentCoordinates 2 =
      [18, 19, 20, 29, 30, 31, 32, 33, 34, 35, 36, 45, 46, 47] := by
  native_decide

end ShadedCarrierHierarchy
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
