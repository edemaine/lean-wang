/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Scaffold.Routed

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

@[simp] theorem depthAt_zero (coordinate : Nat) :
    depthAt 0 coordinate = none := by
  rfl

/-- Once a coordinate acquires an owner, increasing the search bound preserves
that smallest owner. -/
theorem depthAt_eq_some_mono {small bound coordinate depth : Nat}
    (owner : depthAt small coordinate = some depth) (hsmall : small ≤ bound) :
    depthAt bound coordinate = some depth := by
  induction bound, hsmall using Nat.le_induction with
  | base => exact owner
  | succ bound _ inductionHypothesis =>
      simp [depthAt, inductionHypothesis]

/-- Every owner depth lies inside the bound searched by `depthAt`. -/
theorem depthAt_le {bound coordinate depth : Nat}
    (owner : depthAt bound coordinate = some depth) : depth ≤ bound := by
  induction bound with
  | zero => simp at owner
  | succ bound inductionHypothesis =>
      simp only [depthAt] at owner
      cases previous : depthAt bound coordinate with
      | some previousDepth =>
          simp only [previous] at owner
          cases owner
          exact Nat.le.step (inductionHypothesis previous)
      | none =>
          simp only [previous] at owner
          split at owner
          · cases owner
            exact le_rfl
          · simp at owner

/-- `depthAt` never returns the unsearched depth zero. -/
theorem depthAt_pos {bound coordinate depth : Nat}
    (owner : depthAt bound coordinate = some depth) : 0 < depth := by
  induction bound with
  | zero => simp at owner
  | succ bound inductionHypothesis =>
      simp only [depthAt] at owner
      cases previous : depthAt bound coordinate with
      | some previousDepth =>
          simp only [previous] at owner
          cases owner
          exact inductionHypothesis previous
      | none =>
          simp only [previous] at owner
          split at owner
          · cases owner
            omega
          · simp at owner

/-- An owner is a frame that actually contains the coordinate. -/
theorem inFrame_eq_true_of_depthAt_eq_some {bound coordinate depth : Nat}
    (owner : depthAt bound coordinate = some depth) :
    inFrame depth coordinate = true := by
  induction bound with
  | zero => simp at owner
  | succ bound inductionHypothesis =>
      simp only [depthAt] at owner
      cases previous : depthAt bound coordinate with
      | some previousDepth =>
          simp only [previous] at owner
          cases owner
          exact inductionHypothesis previous
      | none =>
          simp only [previous] at owner
          split at owner
          · rename_i contained
            cases owner
            exact contained
          · simp at owner

/-- If no owner was found, none of the searched positive-depth frames contains
the coordinate. -/
theorem inFrame_eq_false_of_depthAt_eq_none
    {bound coordinate depth : Nat} (owner : depthAt bound coordinate = none)
    (hpositive : 0 < depth) (hbound : depth ≤ bound) :
    inFrame depth coordinate = false := by
  induction bound with
  | zero => omega
  | succ bound inductionHypothesis =>
      simp only [depthAt] at owner
      cases previous : depthAt bound coordinate with
      | some previousDepth => simp [previous] at owner
      | none =>
          simp only [previous] at owner
          split at owner
          · simp at owner
          · rename_i currentOutside
            by_cases hdepth : depth ≤ bound
            · exact inductionHypothesis previous hdepth
            · have : depth = bound + 1 := by omega
              subst depth
              simpa using currentOutside

/-- The returned owner is the smallest searched frame containing the
coordinate. -/
theorem depthAt_le_of_inFrame
    {bound coordinate ownerDepth depth : Nat}
    (owner : depthAt bound coordinate = some ownerDepth)
    (hpositive : 0 < depth) (hbound : depth ≤ bound)
    (contained : inFrame depth coordinate = true) : ownerDepth ≤ depth := by
  induction bound with
  | zero => simp at owner
  | succ bound inductionHypothesis =>
      simp only [depthAt] at owner
      cases previous : depthAt bound coordinate with
      | some previousDepth =>
          have previousLe : previousDepth ≤ bound :=
            ShadedCarrierHierarchy.depthAt_le previous
          simp only [previous] at owner
          cases owner
          by_cases hdepth : depth ≤ bound
          · exact inductionHypothesis previous hdepth
          · omega
      | none =>
          simp only [previous] at owner
          split at owner
          · cases owner
            by_contra notLe
            have hdepth : depth ≤ bound := by omega
            have outside := inFrame_eq_false_of_depthAt_eq_none previous
              hpositive hdepth
            simp [contained] at outside
          · simp at owner

/-- Restricting the search to the returned depth still finds the same owner. -/
theorem depthAt_self_of_depthAt_eq_some {bound coordinate depth : Nat}
    (owner : depthAt bound coordinate = some depth) :
    depthAt depth coordinate = some depth := by
  cases restricted : depthAt depth coordinate with
  | none =>
      have outside := inFrame_eq_false_of_depthAt_eq_none restricted
        (depthAt_pos owner) le_rfl
      simp [inFrame_eq_true_of_depthAt_eq_some owner] at outside
  | some restrictedDepth =>
      have restrictedLe : restrictedDepth ≤ depth := depthAt_le restricted
      have ownerLe : depth ≤ restrictedDepth := depthAt_le_of_inFrame owner
        (depthAt_pos restricted)
        (restrictedLe.trans (depthAt_le owner))
        (inFrame_eq_true_of_depthAt_eq_some restricted)
      have : restrictedDepth = depth := Nat.le_antisymm restrictedLe ownerLe
      simpa [this] using restricted

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

@[simp] theorem carrierRole_isHorizontalCarrier (level x y : Nat) :
    (carrierRole level x y).isHorizontalCarrier =
      isHorizontalCarrier level x y := by
  cases horizontal : isHorizontalCarrier level x y <;>
    cases vertical : isVerticalCarrier level x y <;>
    simp [carrierRole, horizontal, vertical, RouteRole.isHorizontalCarrier]

@[simp] theorem carrierRole_isVerticalCarrier (level x y : Nat) :
    (carrierRole level x y).isVerticalCarrier =
      isVerticalCarrier level x y := by
  cases horizontal : isHorizontalCarrier level x y <;>
    cases vertical : isVerticalCarrier level x y <;>
    simp [carrierRole, horizontal, vertical, RouteRole.isVerticalCarrier]

/-- Coordinates that become logical vertices of their depth's carrier grid. -/
def isFreeCoordinate (depth coordinate : Nat) : Bool :=
  depthAt depth coordinate == some depth &&
    !onFrameBoundary depth coordinate

theorem isFreeCoordinate_eq_true_of_owner
    {bound coordinate depth : Nat}
    (owner : depthAt bound coordinate = some depth)
    (interior : onFrameBoundary depth coordinate = false) :
    isFreeCoordinate depth coordinate = true := by
  simp [isFreeCoordinate, depthAt_self_of_depthAt_eq_some owner, interior]

theorem depthAt_self_eq_some_of_isFreeCoordinate
    {depth coordinate : Nat} (free : isFreeCoordinate depth coordinate = true) :
    depthAt depth coordinate = some depth := by
  have free' : depthAt depth coordinate = some depth ∧
      onFrameBoundary depth coordinate = false := by
    simpa [isFreeCoordinate] using free
  exact free'.1

theorem onFrameBoundary_eq_false_of_isFreeCoordinate
    {depth coordinate : Nat} (free : isFreeCoordinate depth coordinate = true) :
    onFrameBoundary depth coordinate = false := by
  have free' : depthAt depth coordinate = some depth ∧
      onFrameBoundary depth coordinate = false := by
    simpa [isFreeCoordinate] using free
  exact free'.2

/-- At a mutual horizontal/vertical crossing, the row and column have the
same smallest owner depth. -/
theorem ownerDepth_eq_of_mutual_containment
    {bound x y xDepth yDepth : Nat}
    (xOwner : depthAt bound x = some xDepth)
    (yOwner : depthAt bound y = some yDepth)
    (xInYFrame : inFrame yDepth x = true)
    (yInXFrame : inFrame xDepth y = true) : xDepth = yDepth := by
  apply Nat.le_antisymm
  · exact depthAt_le_of_inFrame xOwner (depthAt_pos yOwner)
      (depthAt_le yOwner) xInYFrame
  · exact depthAt_le_of_inFrame yOwner (depthAt_pos xOwner)
      (depthAt_le xOwner) yInXFrame

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

theorem scale_pos (depth : Nat) : 0 < scale depth := by
  simp [scale]

theorem period_eq_four_mul_scale (depth : Nat) :
    period depth = 4 * scale depth := by
  simp [period, scale, pow_succ, Nat.mul_comm]

theorem frameEndResidue_lt_period (depth : Nat) :
    frameEndResidue depth < period depth := by
  rw [frameEndResidue, period_eq_four_mul_scale]
  have positive := scale_pos depth
  omega

/-- Moving one physical cell inside a frame cannot cross its period boundary,
so both cells use the same centered logical origin. -/
theorem frameCenter_succ_of_inFrame_not_boundary
    {depth coordinate : Nat} (inside : inFrame depth coordinate = true)
    (interior : onFrameBoundary depth coordinate = false) :
    frameCenter depth (coordinate + 1) = frameCenter depth coordinate := by
  have inside' :
      frameStartResidue depth ≤ coordinate % period depth ∧
        coordinate % period depth ≤ frameEndResidue depth := by
    simpa [inFrame] using inside
  have interior' :
      coordinate % period depth ≠ frameStartResidue depth ∧
        coordinate % period depth ≠ frameEndResidue depth := by
    simpa [onFrameBoundary] using interior
  have residueSuccLt : coordinate % period depth + 1 < period depth := by
    have endLt := frameEndResidue_lt_period depth
    omega
  have oneLt : 1 < period depth := by
    rw [period_eq_four_mul_scale]
    have positive := scale_pos depth
    omega
  have successorMod :
      (coordinate + 1) % period depth = coordinate % period depth + 1 := by
    calc
      (coordinate + 1) % period depth =
          (coordinate % period depth + 1 % period depth) % period depth := by
            rw [Nat.add_mod]
      _ = (coordinate % period depth + 1) % period depth := by
            rw [Nat.mod_eq_of_lt oneLt]
      _ = coordinate % period depth + 1 :=
            Nat.mod_eq_of_lt residueSuccLt
  have residueLe : coordinate % period depth ≤ coordinate := Nat.mod_le _ _
  simp only [frameCenter, successorMod]
  omega

theorem frameCenter_eq_self_of_centerResidue
    {depth coordinate : Nat}
    (center : coordinate % period depth = 2 * scale depth + 1) :
    frameCenter depth coordinate = coordinate := by
  have residueLe : coordinate % period depth ≤ coordinate := Nat.mod_le _ _
  simp only [frameCenter, center]
  omega

/-- Logical vertex coordinate centered at the geometric frame center. -/
def axisCoordinate (depth coordinate : Nat) : Int :=
  (freeCount depth coordinate : Int) -
    freeCount depth (frameCenter depth coordinate)

theorem axisCoordinate_eq_zero_of_centerResidue
    {depth coordinate : Nat}
    (center : coordinate % period depth = 2 * scale depth + 1) :
    axisCoordinate depth coordinate = 0 := by
  rw [axisCoordinate, frameCenter_eq_self_of_centerResidue center]
  omega

/-- Logical source immediately before the next step across a channel gap. -/
def axisSource (depth coordinate : Nat) : Int :=
  (freeCount depth coordinate : Int) - 1 -
    freeCount depth (frameCenter depth coordinate)

theorem axisCoordinate_succ_of_free
    {depth coordinate : Nat} (free : isFreeCoordinate depth coordinate = true)
    (sameCenter : frameCenter depth (coordinate + 1) =
      frameCenter depth coordinate) :
    axisCoordinate depth (coordinate + 1) =
      axisCoordinate depth coordinate + 1 := by
  simp [axisCoordinate, freeCount_succ, free, sameCenter]
  omega

theorem axisSource_succ_of_free
    {depth coordinate : Nat} (free : isFreeCoordinate depth coordinate = true)
    (sameCenter : frameCenter depth (coordinate + 1) =
      frameCenter depth coordinate) :
    axisSource depth (coordinate + 1) =
      axisCoordinate depth coordinate := by
  simp [axisSource, axisCoordinate, freeCount_succ, free, sameCenter]

theorem axisSource_succ_of_not_free
    {depth coordinate : Nat} (notFree : isFreeCoordinate depth coordinate = false)
    (sameCenter : frameCenter depth (coordinate + 1) =
      frameCenter depth coordinate) :
    axisSource depth (coordinate + 1) = axisSource depth coordinate := by
  simp [axisSource, freeCount_succ, notFree, sameCenter]

theorem axisCoordinate_succ_of_not_free
    {depth coordinate : Nat} (notFree : isFreeCoordinate depth coordinate = false)
    (sameCenter : frameCenter depth (coordinate + 1) =
      frameCenter depth coordinate) :
    axisCoordinate depth (coordinate + 1) = axisSource depth coordinate + 1 := by
  simp [axisCoordinate, axisSource, freeCount_succ, notFree, sameCenter]
  omega

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
