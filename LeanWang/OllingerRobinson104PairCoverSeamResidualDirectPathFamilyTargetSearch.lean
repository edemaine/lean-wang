/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathFamilySearch
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathTargets

/-!
# Executable joint-family target search

These checks choose one hierarchy family reached evenly by the source and then
find an even-family endpoint either across the query line or strictly between
the query and source.  Their soundness theorems produce exactly the joint
source/target certificates consumed by `FamilyTargetsAt`.
-/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamResidualDirectPathFamilyTargetSearch

open RedCycles RedShadeCycles RedShadeGraph RedShadeGraphRefinement
  RedShadeGraphSearch
  PairCoverSeamArithmetic PairCoverSeamPathSearch PairCoverSeamShadePaths
  PairCoverSeamResidualDirectPathBridges
  PairCoverSeamResidualDirectPathFamilySearch
  PairCoverSeamResidualDirectPathTargets Signals.FreeCellLocal

set_option maxRecDepth 20000

/-- A local row target whose family route remains confined to the complete
refined parent block. -/
def BoundedRowFamilyTarget
    (root : Nat → Nat → Index) (outerLevel : Nat)
    (outerWest outerEast column row boundary : Nat)
    (family : HierarchyFamily) : Prop :=
  (∃ targetX,
    quarterWest outerWest < targetX ∧
    targetX < quarterEast outerEast ∧
    Signals.verticalInterior?
      (componentAt (iterateRefine (outerLevel + 2) root) targetX row)
      (quadrantAt targetX row) ≠ none ∧
    BoundedCanonicalCycleReachWithinFamily root
      (verticalPort (iterateRefine (outerLevel + 2) root) targetX row)
      outerLevel (familyWidth outerLevel) family) ∨
  (∃ targetY,
    StrictBetween row boundary targetY ∧
    Signals.horizontalInterior?
      (componentAt (iterateRefine (outerLevel + 2) root) column targetY)
      (quadrantAt column targetY) ≠ none ∧
    BoundedCanonicalCycleReachWithinFamily root
      (horizontalPort (iterateRefine (outerLevel + 2) root) column targetY)
      outerLevel (familyWidth outerLevel) family)

/-- Horizontal dual of `BoundedRowFamilyTarget`. -/
def BoundedColumnFamilyTarget
    (root : Nat → Nat → Index) (outerLevel : Nat)
    (outerSouth outerNorth row column boundary : Nat)
    (family : HierarchyFamily) : Prop :=
  (∃ targetY,
    quarterSouth outerSouth < targetY ∧
    targetY < quarterNorth outerNorth ∧
    Signals.horizontalInterior?
      (componentAt (iterateRefine (outerLevel + 2) root) column targetY)
      (quadrantAt column targetY) ≠ none ∧
    BoundedCanonicalCycleReachWithinFamily root
      (horizontalPort (iterateRefine (outerLevel + 2) root) column targetY)
      outerLevel (familyWidth outerLevel) family) ∨
  (∃ targetX,
    StrictBetween column boundary targetX ∧
    Signals.verticalInterior?
      (componentAt (iterateRefine (outerLevel + 2) root) targetX row)
      (quadrantAt targetX row) ≠ none ∧
    BoundedCanonicalCycleReachWithinFamily root
      (verticalPort (iterateRefine (outerLevel + 2) root) targetX row)
      outerLevel (familyWidth outerLevel) family)

/-- A checked row target using one already-computed family flood. -/
def rowTargetCheckFound
    (root : Nat → Nat → Index) (outerLevel width : Nat)
    (found : List ReachNode) (outerWest outerEast column row boundary : Nat) :
    Bool :=
  ((List.range width).any fun targetX =>
    decide (quarterWest outerWest < targetX) &&
    decide (targetX < quarterEast outerEast) &&
    (Signals.verticalInterior?
      (componentAt (iterateRefine (outerLevel + 2) root) targetX row)
      (quadrantAt targetX row)).isSome &&
    reaches root outerLevel found
      (verticalPort (iterateRefine (outerLevel + 2) root) targetX row)) ||
  ((List.range width).any fun targetY =>
    decide (StrictBetween row boundary targetY) &&
    (Signals.horizontalInterior?
      (componentAt (iterateRefine (outerLevel + 2) root) column targetY)
      (quadrantAt column targetY)).isSome &&
    reaches root outerLevel found
      (horizontalPort (iterateRefine (outerLevel + 2) root) column targetY))

theorem rowTargetCheckFound_sound
    {root : Nat → Nat → Index} {outerLevel width fuel : Nat}
    {family : HierarchyFamily} {outerWest outerEast column row boundary : Nat}
    (checked : rowTargetCheckFound root outerLevel width
      (nodes root outerLevel width fuel family)
      outerWest outerEast column row boundary = true) :
    RowFamilyTarget root outerLevel 0 0 outerWest outerEast
      column row boundary family := by
  rw [rowTargetCheckFound] at checked
  simp only [Bool.or_eq_true] at checked
  rcases checked with checked | checked
  · rcases List.any_eq_true.mp checked with
      ⟨targetX, _targetXMember, targetCheck⟩
    simp only [Bool.and_eq_true] at targetCheck
    exact Or.inl ⟨targetX,
      of_decide_eq_true targetCheck.1.1.1,
      of_decide_eq_true targetCheck.1.1.2,
      Option.isSome_iff_ne_none.mp targetCheck.1.2,
      reaches_sound targetCheck.2⟩
  · rcases List.any_eq_true.mp checked with
      ⟨targetY, _targetYMember, targetCheck⟩
    simp only [Bool.and_eq_true] at targetCheck
    exact Or.inr ⟨targetY,
      of_decide_eq_true targetCheck.1.1,
      Option.isSome_iff_ne_none.mp targetCheck.1.2,
      reaches_sound targetCheck.2⟩

/-- Exact-parent-width soundness retaining bounded routes for later block
translation. -/
theorem rowTargetCheckFound_familyWidth_sound
    {root : Nat → Nat → Index} {outerLevel fuel : Nat}
    {family : HierarchyFamily} {outerWest outerEast column row boundary : Nat}
    (checked : rowTargetCheckFound root outerLevel (familyWidth outerLevel)
      (nodes root outerLevel (familyWidth outerLevel) fuel family)
      outerWest outerEast column row boundary = true) :
    BoundedRowFamilyTarget root outerLevel outerWest outerEast
      column row boundary family := by
  rw [rowTargetCheckFound] at checked
  simp only [Bool.or_eq_true] at checked
  rcases checked with checked | checked
  · rcases List.any_eq_true.mp checked with
      ⟨targetX, _targetXMember, targetCheck⟩
    simp only [Bool.and_eq_true] at targetCheck
    exact Or.inl ⟨targetX,
      of_decide_eq_true targetCheck.1.1.1,
      of_decide_eq_true targetCheck.1.1.2,
      Option.isSome_iff_ne_none.mp targetCheck.1.2,
      reaches_familyWidth_bounded_sound targetCheck.2⟩
  · rcases List.any_eq_true.mp checked with
      ⟨targetY, _targetYMember, targetCheck⟩
    simp only [Bool.and_eq_true] at targetCheck
    exact Or.inr ⟨targetY,
      of_decide_eq_true targetCheck.1.1,
      Option.isSome_iff_ne_none.mp targetCheck.1.2,
      reaches_familyWidth_bounded_sound targetCheck.2⟩
/-- Horizontal dual of `rowTargetCheckFound`. -/
def columnTargetCheckFound
    (root : Nat → Nat → Index) (outerLevel width : Nat)
    (found : List ReachNode) (outerSouth outerNorth row column boundary : Nat) :
    Bool :=
  ((List.range width).any fun targetY =>
    decide (quarterSouth outerSouth < targetY) &&
    decide (targetY < quarterNorth outerNorth) &&
    (Signals.horizontalInterior?
      (componentAt (iterateRefine (outerLevel + 2) root) column targetY)
      (quadrantAt column targetY)).isSome &&
    reaches root outerLevel found
      (horizontalPort (iterateRefine (outerLevel + 2) root) column targetY)) ||
  ((List.range width).any fun targetX =>
    decide (StrictBetween column boundary targetX) &&
    (Signals.verticalInterior?
      (componentAt (iterateRefine (outerLevel + 2) root) targetX row)
      (quadrantAt targetX row)).isSome &&
    reaches root outerLevel found
      (verticalPort (iterateRefine (outerLevel + 2) root) targetX row))

theorem columnTargetCheckFound_sound
    {root : Nat → Nat → Index} {outerLevel width fuel : Nat}
    {family : HierarchyFamily} {outerSouth outerNorth row column boundary : Nat}
    (checked : columnTargetCheckFound root outerLevel width
      (nodes root outerLevel width fuel family)
      outerSouth outerNorth row column boundary = true) :
    ColumnFamilyTarget root outerLevel 0 0 outerSouth outerNorth
      row column boundary family := by
  rw [columnTargetCheckFound] at checked
  simp only [Bool.or_eq_true] at checked
  rcases checked with checked | checked
  · rcases List.any_eq_true.mp checked with
      ⟨targetY, _targetYMember, targetCheck⟩
    simp only [Bool.and_eq_true] at targetCheck
    exact Or.inl ⟨targetY,
      of_decide_eq_true targetCheck.1.1.1,
      of_decide_eq_true targetCheck.1.1.2,
      Option.isSome_iff_ne_none.mp targetCheck.1.2,
      reaches_sound targetCheck.2⟩
  · rcases List.any_eq_true.mp checked with
      ⟨targetX, _targetXMember, targetCheck⟩
    simp only [Bool.and_eq_true] at targetCheck
    exact Or.inr ⟨targetX,
      of_decide_eq_true targetCheck.1.1,
      Option.isSome_iff_ne_none.mp targetCheck.1.2,
      reaches_sound targetCheck.2⟩

/-- Exact-parent-width horizontal target soundness retaining bounded routes. -/
theorem columnTargetCheckFound_familyWidth_sound
    {root : Nat → Nat → Index} {outerLevel fuel : Nat}
    {family : HierarchyFamily} {outerSouth outerNorth row column boundary : Nat}
    (checked : columnTargetCheckFound root outerLevel (familyWidth outerLevel)
      (nodes root outerLevel (familyWidth outerLevel) fuel family)
      outerSouth outerNorth row column boundary = true) :
    BoundedColumnFamilyTarget root outerLevel outerSouth outerNorth
      row column boundary family := by
  rw [columnTargetCheckFound] at checked
  simp only [Bool.or_eq_true] at checked
  rcases checked with checked | checked
  · rcases List.any_eq_true.mp checked with
      ⟨targetY, _targetYMember, targetCheck⟩
    simp only [Bool.and_eq_true] at targetCheck
    exact Or.inl ⟨targetY,
      of_decide_eq_true targetCheck.1.1.1,
      of_decide_eq_true targetCheck.1.1.2,
      Option.isSome_iff_ne_none.mp targetCheck.1.2,
      reaches_familyWidth_bounded_sound targetCheck.2⟩
  · rcases List.any_eq_true.mp checked with
      ⟨targetX, _targetXMember, targetCheck⟩
    simp only [Bool.and_eq_true] at targetCheck
    exact Or.inr ⟨targetX,
      of_decide_eq_true targetCheck.1.1,
      Option.isSome_iff_ne_none.mp targetCheck.1.2,
      reaches_familyWidth_bounded_sound targetCheck.2⟩
/-- Choose a common source/target family for one row query from two cached
family floods. -/
def rowJointCheckFound
    (root : Nat → Nat → Index) (outerLevel width : Nat)
    (evenFound oddFound : List ReachNode)
    (outerWest outerEast column row boundary : Nat) : Bool :=
  let source := horizontalPort
    (iterateRefine (outerLevel + 2) root) column boundary
  (reaches root outerLevel evenFound source &&
      rowTargetCheckFound root outerLevel width evenFound
        outerWest outerEast column row boundary) ||
    (reaches root outerLevel oddFound source &&
      rowTargetCheckFound root outerLevel width oddFound
        outerWest outerEast column row boundary)

theorem rowJointCheckFound_sound
    {root : Nat → Nat → Index} {outerLevel width fuel : Nat}
    {outerWest outerEast column row boundary : Nat}
    (checked : rowJointCheckFound root outerLevel width
      (nodes root outerLevel width fuel .even)
      (nodes root outerLevel width fuel .odd)
      outerWest outerEast column row boundary = true) :
    ∃ family,
      CanonicalCycleAncestorWithinFamily
        (iterateRefine (outerLevel + 2) root)
        (horizontalPort (iterateRefine (outerLevel + 2) root) column boundary)
        outerLevel 0 0 family ∧
      RowFamilyTarget root outerLevel 0 0 outerWest outerEast
        column row boundary family := by
  simp only [rowJointCheckFound, Bool.or_eq_true, Bool.and_eq_true] at checked
  rcases checked with checked | checked
  · exact ⟨.even, reaches_sound checked.1,
      rowTargetCheckFound_sound checked.2⟩
  · exact ⟨.odd, reaches_sound checked.1,
      rowTargetCheckFound_sound checked.2⟩

/-- Joint row soundness retaining bounded source and target routes. -/
theorem rowJointCheckFound_familyWidth_sound
    {root : Nat → Nat → Index} {outerLevel fuel : Nat}
    {outerWest outerEast column row boundary : Nat}
    (checked : rowJointCheckFound root outerLevel (familyWidth outerLevel)
      (nodes root outerLevel (familyWidth outerLevel) fuel .even)
      (nodes root outerLevel (familyWidth outerLevel) fuel .odd)
      outerWest outerEast column row boundary = true) :
    ∃ family,
      BoundedCanonicalCycleReachWithinFamily root
        (horizontalPort (iterateRefine (outerLevel + 2) root) column boundary)
        outerLevel (familyWidth outerLevel) family ∧
      BoundedRowFamilyTarget root outerLevel outerWest outerEast
        column row boundary family := by
  simp only [rowJointCheckFound, Bool.or_eq_true, Bool.and_eq_true] at checked
  rcases checked with checked | checked
  · exact ⟨.even, reaches_familyWidth_bounded_sound checked.1,
      rowTargetCheckFound_familyWidth_sound checked.2⟩
  · exact ⟨.odd, reaches_familyWidth_bounded_sound checked.1,
      rowTargetCheckFound_familyWidth_sound checked.2⟩

/-- Horizontal dual of `rowJointCheckFound`. -/
def columnJointCheckFound
    (root : Nat → Nat → Index) (outerLevel width : Nat)
    (evenFound oddFound : List ReachNode)
    (outerSouth outerNorth row column boundary : Nat) : Bool :=
  let source := verticalPort
    (iterateRefine (outerLevel + 2) root) boundary row
  (reaches root outerLevel evenFound source &&
      columnTargetCheckFound root outerLevel width evenFound
        outerSouth outerNorth row column boundary) ||
    (reaches root outerLevel oddFound source &&
      columnTargetCheckFound root outerLevel width oddFound
        outerSouth outerNorth row column boundary)

theorem columnJointCheckFound_sound
    {root : Nat → Nat → Index} {outerLevel width fuel : Nat}
    {outerSouth outerNorth row column boundary : Nat}
    (checked : columnJointCheckFound root outerLevel width
      (nodes root outerLevel width fuel .even)
      (nodes root outerLevel width fuel .odd)
      outerSouth outerNorth row column boundary = true) :
    ∃ family,
      CanonicalCycleAncestorWithinFamily
        (iterateRefine (outerLevel + 2) root)
        (verticalPort (iterateRefine (outerLevel + 2) root) boundary row)
        outerLevel 0 0 family ∧
      ColumnFamilyTarget root outerLevel 0 0 outerSouth outerNorth
        row column boundary family := by
  simp only [columnJointCheckFound, Bool.or_eq_true, Bool.and_eq_true] at checked
  rcases checked with checked | checked
  · exact ⟨.even, reaches_sound checked.1,
      columnTargetCheckFound_sound checked.2⟩
  · exact ⟨.odd, reaches_sound checked.1,
      columnTargetCheckFound_sound checked.2⟩

/-- Joint column soundness retaining bounded source and target routes. -/
theorem columnJointCheckFound_familyWidth_sound
    {root : Nat → Nat → Index} {outerLevel fuel : Nat}
    {outerSouth outerNorth row column boundary : Nat}
    (checked : columnJointCheckFound root outerLevel (familyWidth outerLevel)
      (nodes root outerLevel (familyWidth outerLevel) fuel .even)
      (nodes root outerLevel (familyWidth outerLevel) fuel .odd)
      outerSouth outerNorth row column boundary = true) :
    ∃ family,
      BoundedCanonicalCycleReachWithinFamily root
        (verticalPort (iterateRefine (outerLevel + 2) root) boundary row)
        outerLevel (familyWidth outerLevel) family ∧
      BoundedColumnFamilyTarget root outerLevel outerSouth outerNorth
        row column boundary family := by
  simp only [columnJointCheckFound, Bool.or_eq_true, Bool.and_eq_true] at checked
  rcases checked with checked | checked
  · exact ⟨.even, reaches_familyWidth_bounded_sound checked.1,
      columnTargetCheckFound_familyWidth_sound checked.2⟩
  · exact ⟨.odd, reaches_familyWidth_bounded_sound checked.1,
      columnTargetCheckFound_familyWidth_sound checked.2⟩

end PairCoverSeamResidualDirectPathFamilyTargetSearch
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
