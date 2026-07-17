/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.PairCoverSeamPathTranslation
import LeanWang.Robinson.Closed104.PairCoverSeamResidualDirectPathFamilyTargetSearch
import LeanWang.Robinson.Closed104.PairCoverSeamResidualDirectPathFamilyTransport

/-!
# Transport joint family targets into arbitrary parent blocks

This module translates both the bounded family routes and the local endpoint
geometry retained by a constant-parent target check.
-/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamResidualDirectPathFamilyTargetTransport

open RedCycles RedShadeCycles RedShadeGraph RedShadeGraphBoards
  RedShadeGraphSearchSoundness RedShadeGraphTranslation RefinementTranslation
  PairCoverSeamArithmetic PairCoverSeamPathSearch PairCoverSeamPathTranslation
  PairCoverSeamShadePaths
  PairCoverSeamResidualDirectPathBridges
  PairCoverSeamResidualDirectPathFamilySearch
  PairCoverSeamResidualDirectPathFamilyTargetSearch
  PairCoverSeamResidualDirectPathFamilyTransport
  PairCoverSeamResidualDirectPathTargets Signals.FreeCellLocal

set_option maxRecDepth 20000

def familyIndexOffset (outerLevel parent : Nat) : Nat :=
  2 ^ (outerLevel + 2) * parent

def familyQuarterOffset (outerLevel parent : Nat) : Nat :=
  familyWidth outerLevel * parent

private theorem quarterOffset_eq_twiceIndexOffset
    (outerLevel parent : Nat) :
    familyQuarterOffset outerLevel parent =
      2 * familyIndexOffset outerLevel parent := by
  simp [familyQuarterOffset, familyIndexOffset, familyWidth, pow_add]
  ring

private theorem quarterWest_add (outerLevel parent value : Nat) :
    quarterWest (familyIndexOffset outerLevel parent + value) =
      familyQuarterOffset outerLevel parent + quarterWest value := by
  rw [quarterOffset_eq_twiceIndexOffset]
  simp [quarterWest]
  ring

private theorem quarterEast_add (outerLevel parent value : Nat) :
    quarterEast (familyIndexOffset outerLevel parent + value) =
      familyQuarterOffset outerLevel parent + quarterEast value := by
  rw [quarterOffset_eq_twiceIndexOffset]
  simp [quarterEast]
  ring

private theorem quarterSouth_add (outerLevel parent value : Nat) :
    quarterSouth (familyIndexOffset outerLevel parent + value) =
      familyQuarterOffset outerLevel parent + quarterSouth value := by
  simpa [quarterSouth, quarterWest] using
    quarterWest_add outerLevel parent value

private theorem quarterNorth_add (outerLevel parent value : Nat) :
    quarterNorth (familyIndexOffset outerLevel parent + value) =
      familyQuarterOffset outerLevel parent + quarterNorth value := by
  simpa [quarterNorth, quarterEast] using
    quarterEast_add outerLevel parent value

private theorem strictBetween_add (offset first second target : Nat) :
    StrictBetween (offset + first) (offset + second) (offset + target) ↔
      StrictBetween first second target := by
  unfold StrictBetween
  omega

private theorem target_inBounds
    {root : Nat → Nat → Index} {target : Port}
    {outerLevel : Nat} {family : HierarchyFamily}
    (reach : BoundedCanonicalCycleReachWithinFamily root target outerLevel
      (familyWidth outerLevel) family) :
    PortInBounds target (familyWidth outerLevel) (familyWidth outerLevel) := by
  rcases reach with
    ⟨_level, _blockX, _blockY, _xWithin, _yWithin, _inFamily,
      _cycle, _entry, _onCycle, path⟩
  exact path.second_inBounds

private theorem verticalPort_inBounds_iff
    (grid : Nat → Nat → Index) (x y width height : Nat) :
    PortInBounds (verticalPort grid x y) width height ↔
      x < width ∧ y < height := by
  simp only [PortInBounds, verticalPort]
  split <;> rfl

private theorem horizontalPort_inBounds_iff
    (grid : Nat → Nat → Index) (x y width height : Nat) :
    PortInBounds (horizontalPort grid x y) width height ↔
      x < width ∧ y < height := by
  simp only [PortInBounds, horizontalPort]
  split <;> rfl

private theorem componentAt_constant_eq_shift
    (grid : Nat → Nat → Index) (outerLevel parentX parentY x y : Nat)
    (hx : x < familyWidth outerLevel) (hy : y < familyWidth outerLevel) :
    componentAt
        (iterateRefine (outerLevel + 2)
          (fun _ _ => grid parentX parentY)) x y =
      componentAt
        (iterateRefine (outerLevel + 2)
          (shiftGrid grid parentX parentY)) x y := by
  exact (componentAt_shift_eq_constant (outerLevel + 2) grid
    parentX parentY x y (by simpa [familyWidth] using hx)
    (by simpa [familyWidth] using hy)).symm

private theorem verticalInterior_constant_translate
    (grid : Nat → Nat → Index) (outerLevel parentX parentY x y : Nat)
    (hx : x < familyWidth outerLevel) (hy : y < familyWidth outerLevel) :
    Signals.verticalInterior?
        (componentAt
          (iterateRefine (outerLevel + 2)
            (fun _ _ => grid parentX parentY)) x y)
        (quadrantAt x y) =
      Signals.verticalInterior?
        (componentAt (iterateRefine (outerLevel + 2) grid)
          (familyQuarterOffset outerLevel parentX + x)
          (familyQuarterOffset outerLevel parentY + y))
        (quadrantAt (familyQuarterOffset outerLevel parentX + x)
          (familyQuarterOffset outerLevel parentY + y)) := by
  rw [componentAt_constant_eq_shift grid outerLevel parentX parentY x y hx hy]
  simpa [familyQuarterOffset, familyWidth] using
    verticalInterior_iterateRefine_shift (outerLevel + 2)
      grid parentX parentY x y

private theorem horizontalInterior_constant_translate
    (grid : Nat → Nat → Index) (outerLevel parentX parentY x y : Nat)
    (hx : x < familyWidth outerLevel) (hy : y < familyWidth outerLevel) :
    Signals.horizontalInterior?
        (componentAt
          (iterateRefine (outerLevel + 2)
            (fun _ _ => grid parentX parentY)) x y)
        (quadrantAt x y) =
      Signals.horizontalInterior?
        (componentAt (iterateRefine (outerLevel + 2) grid)
          (familyQuarterOffset outerLevel parentX + x)
          (familyQuarterOffset outerLevel parentY + y))
        (quadrantAt (familyQuarterOffset outerLevel parentX + x)
          (familyQuarterOffset outerLevel parentY + y)) := by
  rw [componentAt_constant_eq_shift grid outerLevel parentX parentY x y hx hy]
  simpa [familyQuarterOffset, familyWidth] using
    horizontalInterior_iterateRefine_shift (outerLevel + 2)
      grid parentX parentY x y

private theorem verticalPort_constant_translate
    (grid : Nat → Nat → Index) (outerLevel parentX parentY x y : Nat)
    (hx : x < familyWidth outerLevel) (hy : y < familyWidth outerLevel) :
    translatePort
        (verticalPort
          (iterateRefine (outerLevel + 2)
            (fun _ _ => grid parentX parentY)) x y)
        (familyQuarterOffset outerLevel parentX)
        (familyQuarterOffset outerLevel parentY) =
      verticalPort (iterateRefine (outerLevel + 2) grid)
        (familyQuarterOffset outerLevel parentX + x)
        (familyQuarterOffset outerLevel parentY + y) := by
  have portEq : verticalPort
      (iterateRefine (outerLevel + 2) (fun _ _ => grid parentX parentY)) x y =
      verticalPort
        (iterateRefine (outerLevel + 2) (shiftGrid grid parentX parentY)) x y := by
    simp only [verticalPort]
    rw [componentAt_constant_eq_shift grid outerLevel parentX parentY x y hx hy]
  rw [portEq]
  simpa only [familyQuarterOffset, familyWidth, Nat.add_assoc] using
    verticalPort_translate (outerLevel + 2) grid parentX parentY x y

private theorem horizontalPort_constant_translate
    (grid : Nat → Nat → Index) (outerLevel parentX parentY x y : Nat)
    (hx : x < familyWidth outerLevel) (hy : y < familyWidth outerLevel) :
    translatePort
        (horizontalPort
          (iterateRefine (outerLevel + 2)
            (fun _ _ => grid parentX parentY)) x y)
        (familyQuarterOffset outerLevel parentX)
        (familyQuarterOffset outerLevel parentY) =
      horizontalPort (iterateRefine (outerLevel + 2) grid)
        (familyQuarterOffset outerLevel parentX + x)
        (familyQuarterOffset outerLevel parentY + y) := by
  have portEq : horizontalPort
      (iterateRefine (outerLevel + 2) (fun _ _ => grid parentX parentY)) x y =
      horizontalPort
        (iterateRefine (outerLevel + 2) (shiftGrid grid parentX parentY)) x y := by
    simp only [horizontalPort]
    rw [componentAt_constant_eq_shift grid outerLevel parentX parentY x y hx hy]
  rw [portEq]
  simpa only [familyQuarterOffset, familyWidth, Nat.add_assoc] using
    horizontalPort_translate (outerLevel + 2) grid parentX parentY x y

private theorem translateReach
    {grid : Nat → Nat → Index} {outerLevel parentX parentY : Nat}
    {family : HierarchyFamily} {target : Port}
    (reach : BoundedCanonicalCycleReachWithinFamily
      (fun _ _ => grid parentX parentY) target outerLevel
      (familyWidth outerLevel) family) :
    CanonicalCycleAncestorWithinFamily (iterateRefine (outerLevel + 2) grid)
      (translatePort target (familyWidth outerLevel * parentX)
        (familyWidth outerLevel * parentY))
      outerLevel parentX parentY family :=
  BoundedCanonicalCycleReachWithinFamily.translate reach

/-- Translate a bounded local row target into the corresponding global
hierarchy block. -/
theorem BoundedRowFamilyTarget.translate
    {grid : Nat → Nat → Index} {outerLevel parentX parentY : Nat}
    {outerWest outerEast column row boundary : Nat}
    {family : HierarchyFamily}
    (target : BoundedRowFamilyTarget (fun _ _ => grid parentX parentY)
      outerLevel outerWest outerEast column row boundary family) :
    RowFamilyTarget grid outerLevel parentX parentY
      (familyIndexOffset outerLevel parentX + outerWest)
      (familyIndexOffset outerLevel parentX + outerEast)
      (familyQuarterOffset outerLevel parentX + column)
      (familyQuarterOffset outerLevel parentY + row)
      (familyQuarterOffset outerLevel parentY + boundary) family := by
  rcases target with target | target
  · rcases target with
      ⟨targetX, targetWest, targetEast, targetInterior, targetReach⟩
    have targetBounds := (verticalPort_inBounds_iff _ _ _ _ _).1
      (target_inBounds targetReach)
    have targetXLt := targetBounds.1
    have rowLt := targetBounds.2
    refine Or.inl ⟨familyQuarterOffset outerLevel parentX + targetX,
      ?_, ?_, ?_, ?_⟩
    · rw [quarterWest_add]
      omega
    · rw [quarterEast_add]
      omega
    · rw [← verticalInterior_constant_translate grid outerLevel
        parentX parentY targetX row targetXLt rowLt]
      exact targetInterior
    · have translated :=
        translateReach
          (grid := grid) (parentX := parentX) (parentY := parentY) targetReach
      change CanonicalCycleAncestorWithinFamily _
        (translatePort _ (familyQuarterOffset outerLevel parentX)
          (familyQuarterOffset outerLevel parentY))
        outerLevel parentX parentY family at translated
      rw [verticalPort_constant_translate grid outerLevel parentX parentY
        targetX row targetXLt rowLt] at translated
      exact translated
  · rcases target with
      ⟨targetY, between, targetInterior, targetReach⟩
    have targetBounds := (horizontalPort_inBounds_iff _ _ _ _ _).1
      (target_inBounds targetReach)
    have columnLt := targetBounds.1
    have targetYLt := targetBounds.2
    refine Or.inr ⟨familyQuarterOffset outerLevel parentY + targetY,
      ?_, ?_, ?_⟩
    · exact (strictBetween_add
        (familyQuarterOffset outerLevel parentY) row boundary targetY).2 between
    · rw [← horizontalInterior_constant_translate grid outerLevel
        parentX parentY column targetY columnLt targetYLt]
      exact targetInterior
    · have translated :=
        translateReach
          (grid := grid) (parentX := parentX) (parentY := parentY) targetReach
      change CanonicalCycleAncestorWithinFamily _
        (translatePort _ (familyQuarterOffset outerLevel parentX)
          (familyQuarterOffset outerLevel parentY))
        outerLevel parentX parentY family at translated
      rw [horizontalPort_constant_translate grid outerLevel parentX parentY
        column targetY columnLt targetYLt] at translated
      exact translated

/-- Horizontal dual of `BoundedRowFamilyTarget.translate`. -/
theorem BoundedColumnFamilyTarget.translate
    {grid : Nat → Nat → Index} {outerLevel parentX parentY : Nat}
    {outerSouth outerNorth row column boundary : Nat}
    {family : HierarchyFamily}
    (target : BoundedColumnFamilyTarget (fun _ _ => grid parentX parentY)
      outerLevel outerSouth outerNorth row column boundary family) :
    ColumnFamilyTarget grid outerLevel parentX parentY
      (familyIndexOffset outerLevel parentY + outerSouth)
      (familyIndexOffset outerLevel parentY + outerNorth)
      (familyQuarterOffset outerLevel parentY + row)
      (familyQuarterOffset outerLevel parentX + column)
      (familyQuarterOffset outerLevel parentX + boundary) family := by
  rcases target with target | target
  · rcases target with
      ⟨targetY, targetSouth, targetNorth, targetInterior, targetReach⟩
    have targetBounds := (horizontalPort_inBounds_iff _ _ _ _ _).1
      (target_inBounds targetReach)
    have columnLt := targetBounds.1
    have targetYLt := targetBounds.2
    refine Or.inl ⟨familyQuarterOffset outerLevel parentY + targetY,
      ?_, ?_, ?_, ?_⟩
    · rw [quarterSouth_add]
      omega
    · rw [quarterNorth_add]
      omega
    · rw [← horizontalInterior_constant_translate grid outerLevel
        parentX parentY column targetY columnLt targetYLt]
      exact targetInterior
    · have translated :=
        translateReach
          (grid := grid) (parentX := parentX) (parentY := parentY) targetReach
      change CanonicalCycleAncestorWithinFamily _
        (translatePort _ (familyQuarterOffset outerLevel parentX)
          (familyQuarterOffset outerLevel parentY))
        outerLevel parentX parentY family at translated
      rw [horizontalPort_constant_translate grid outerLevel parentX parentY
        column targetY columnLt targetYLt] at translated
      exact translated
  · rcases target with
      ⟨targetX, between, targetInterior, targetReach⟩
    have targetBounds := (verticalPort_inBounds_iff _ _ _ _ _).1
      (target_inBounds targetReach)
    have targetXLt := targetBounds.1
    have rowLt := targetBounds.2
    refine Or.inr ⟨familyQuarterOffset outerLevel parentX + targetX,
      ?_, ?_, ?_⟩
    · exact (strictBetween_add
        (familyQuarterOffset outerLevel parentX) column boundary targetX).2 between
    · rw [← verticalInterior_constant_translate grid outerLevel
        parentX parentY targetX row targetXLt rowLt]
      exact targetInterior
    · have translated :=
        translateReach
          (grid := grid) (parentX := parentX) (parentY := parentY) targetReach
      change CanonicalCycleAncestorWithinFamily _
        (translatePort _ (familyQuarterOffset outerLevel parentX)
          (familyQuarterOffset outerLevel parentY))
        outerLevel parentX parentY family at translated
      rw [verticalPort_constant_translate grid outerLevel parentX parentY
        targetX row targetXLt rowLt] at translated
      exact translated

/-- An accepted constant-parent row check transports directly to the joint
global source/target family certificate. -/
theorem rowJointCheckFound_familyWidth_translate
    {grid : Nat → Nat → Index} {outerLevel parentX parentY fuel : Nat}
    {outerWest outerEast column row boundary : Nat}
    (checked : rowJointCheckFound (fun _ _ => grid parentX parentY)
      outerLevel (familyWidth outerLevel)
      (nodes (fun _ _ => grid parentX parentY) outerLevel
        (familyWidth outerLevel) fuel .even)
      (nodes (fun _ _ => grid parentX parentY) outerLevel
        (familyWidth outerLevel) fuel .odd)
      outerWest outerEast column row boundary = true) :
    ∃ family,
      CanonicalCycleAncestorWithinFamily
        (iterateRefine (outerLevel + 2) grid)
        (horizontalPort (iterateRefine (outerLevel + 2) grid)
          (familyQuarterOffset outerLevel parentX + column)
          (familyQuarterOffset outerLevel parentY + boundary))
        outerLevel parentX parentY family ∧
      RowFamilyTarget grid outerLevel parentX parentY
        (familyIndexOffset outerLevel parentX + outerWest)
        (familyIndexOffset outerLevel parentX + outerEast)
        (familyQuarterOffset outerLevel parentX + column)
        (familyQuarterOffset outerLevel parentY + row)
        (familyQuarterOffset outerLevel parentY + boundary) family := by
  rcases rowJointCheckFound_familyWidth_sound checked with
    ⟨family, sourceReach, target⟩
  have sourceBounds := (horizontalPort_inBounds_iff _ _ _ _ _).1
    (target_inBounds sourceReach)
  have sourceTranslated := translateReach
    (grid := grid) (parentX := parentX) (parentY := parentY) sourceReach
  change CanonicalCycleAncestorWithinFamily _
    (translatePort _ (familyQuarterOffset outerLevel parentX)
      (familyQuarterOffset outerLevel parentY))
    outerLevel parentX parentY family at sourceTranslated
  rw [horizontalPort_constant_translate grid outerLevel parentX parentY
    column boundary sourceBounds.1 sourceBounds.2] at sourceTranslated
  exact ⟨family, sourceTranslated, BoundedRowFamilyTarget.translate target⟩

/-- Horizontal dual of `rowJointCheckFound_familyWidth_translate`. -/
theorem columnJointCheckFound_familyWidth_translate
    {grid : Nat → Nat → Index} {outerLevel parentX parentY fuel : Nat}
    {outerSouth outerNorth row column boundary : Nat}
    (checked : columnJointCheckFound (fun _ _ => grid parentX parentY)
      outerLevel (familyWidth outerLevel)
      (nodes (fun _ _ => grid parentX parentY) outerLevel
        (familyWidth outerLevel) fuel .even)
      (nodes (fun _ _ => grid parentX parentY) outerLevel
        (familyWidth outerLevel) fuel .odd)
      outerSouth outerNorth row column boundary = true) :
    ∃ family,
      CanonicalCycleAncestorWithinFamily
        (iterateRefine (outerLevel + 2) grid)
        (verticalPort (iterateRefine (outerLevel + 2) grid)
          (familyQuarterOffset outerLevel parentX + boundary)
          (familyQuarterOffset outerLevel parentY + row))
        outerLevel parentX parentY family ∧
      ColumnFamilyTarget grid outerLevel parentX parentY
        (familyIndexOffset outerLevel parentY + outerSouth)
        (familyIndexOffset outerLevel parentY + outerNorth)
        (familyQuarterOffset outerLevel parentY + row)
        (familyQuarterOffset outerLevel parentX + column)
        (familyQuarterOffset outerLevel parentX + boundary) family := by
  rcases columnJointCheckFound_familyWidth_sound checked with
    ⟨family, sourceReach, target⟩
  have sourceBounds := (verticalPort_inBounds_iff _ _ _ _ _).1
    (target_inBounds sourceReach)
  have sourceTranslated := translateReach
    (grid := grid) (parentX := parentX) (parentY := parentY) sourceReach
  change CanonicalCycleAncestorWithinFamily _
    (translatePort _ (familyQuarterOffset outerLevel parentX)
      (familyQuarterOffset outerLevel parentY))
    outerLevel parentX parentY family at sourceTranslated
  rw [verticalPort_constant_translate grid outerLevel parentX parentY
    boundary row sourceBounds.1 sourceBounds.2] at sourceTranslated
  exact ⟨family, sourceTranslated,
    BoundedColumnFamilyTarget.translate target⟩

end PairCoverSeamResidualDirectPathFamilyTargetTransport
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
