/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.PairCoverSeamResidualDirectPathFamilyReachIndex
import LeanWang.Robinson.Closed104.PairCoverSeamResidualDirectPathFamilyTargetSearch

/-!
# Indexed joint-family target search

These checks replace repeated linear scans of retained family floods with the
dense index.  Their soundness theorems recover the original target checks, so
the existing bounded-route and transport proofs remain the trusted interface.
-/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamResidualDirectPathFamilyTargetIndexedSearch

open RedCycles RedShadeCycles RedShadeGraph RedShadeGraphSearch
  PairCoverSeamArithmetic PairCoverSeamPathSearch PairCoverSeamShadePaths
  PairCoverSeamResidualDirectPathFamilyReachIndex
  PairCoverSeamResidualDirectPathFamilySearch
  PairCoverSeamResidualDirectPathFamilyTargetSearch Signals.FreeCellLocal

set_option maxRecDepth 20000

def rowTargetCheckIndexed
    (root : Nat → Nat → Index) (outerLevel width : Nat)
    (found : List ReachNode) (index : Array (Option Nat))
    (outerWest outerEast column row boundary : Nat) : Bool :=
  ((List.range width).any fun targetX =>
    decide (quarterWest outerWest < targetX) &&
    decide (targetX < quarterEast outerEast) &&
    (Signals.verticalInterior?
      (componentAt (iterateRefine (outerLevel + 2) root) targetX row)
      (quadrantAt targetX row)).isSome &&
    indexedReaches root outerLevel width found index
      (verticalPort (iterateRefine (outerLevel + 2) root) targetX row)) ||
  ((List.range width).any fun targetY =>
    decide (StrictBetween row boundary targetY) &&
    (Signals.horizontalInterior?
      (componentAt (iterateRefine (outerLevel + 2) root) column targetY)
      (quadrantAt column targetY)).isSome &&
    indexedReaches root outerLevel width found index
      (horizontalPort (iterateRefine (outerLevel + 2) root) column targetY))

theorem rowTargetCheckIndexed_sound
    {root : Nat → Nat → Index} {outerLevel width : Nat}
    {found : List ReachNode} {index : Array (Option Nat)}
    {outerWest outerEast column row boundary : Nat}
    (checked : rowTargetCheckIndexed root outerLevel width found index
      outerWest outerEast column row boundary = true) :
    rowTargetCheckFound root outerLevel width found
      outerWest outerEast column row boundary = true := by
  rw [rowTargetCheckIndexed] at checked
  rw [rowTargetCheckFound]
  simp only [Bool.or_eq_true] at checked ⊢
  rcases checked with checked | checked
  · left
    rcases List.any_eq_true.mp checked with
      ⟨targetX, targetXMember, targetCheck⟩
    apply List.any_eq_true.mpr
    refine ⟨targetX, targetXMember, ?_⟩
    simp only [Bool.and_eq_true] at targetCheck ⊢
    exact ⟨targetCheck.1,
      indexedReaches_sound targetCheck.2⟩
  · right
    rcases List.any_eq_true.mp checked with
      ⟨targetY, targetYMember, targetCheck⟩
    apply List.any_eq_true.mpr
    refine ⟨targetY, targetYMember, ?_⟩
    simp only [Bool.and_eq_true] at targetCheck ⊢
    exact ⟨targetCheck.1,
      indexedReaches_sound targetCheck.2⟩

def columnTargetCheckIndexed
    (root : Nat → Nat → Index) (outerLevel width : Nat)
    (found : List ReachNode) (index : Array (Option Nat))
    (outerSouth outerNorth row column boundary : Nat) : Bool :=
  ((List.range width).any fun targetY =>
    decide (quarterSouth outerSouth < targetY) &&
    decide (targetY < quarterNorth outerNorth) &&
    (Signals.horizontalInterior?
      (componentAt (iterateRefine (outerLevel + 2) root) column targetY)
      (quadrantAt column targetY)).isSome &&
    indexedReaches root outerLevel width found index
      (horizontalPort (iterateRefine (outerLevel + 2) root) column targetY)) ||
  ((List.range width).any fun targetX =>
    decide (StrictBetween column boundary targetX) &&
    (Signals.verticalInterior?
      (componentAt (iterateRefine (outerLevel + 2) root) targetX row)
      (quadrantAt targetX row)).isSome &&
    indexedReaches root outerLevel width found index
      (verticalPort (iterateRefine (outerLevel + 2) root) targetX row))

theorem columnTargetCheckIndexed_sound
    {root : Nat → Nat → Index} {outerLevel width : Nat}
    {found : List ReachNode} {index : Array (Option Nat)}
    {outerSouth outerNorth row column boundary : Nat}
    (checked : columnTargetCheckIndexed root outerLevel width found index
      outerSouth outerNorth row column boundary = true) :
    columnTargetCheckFound root outerLevel width found
      outerSouth outerNorth row column boundary = true := by
  rw [columnTargetCheckIndexed] at checked
  rw [columnTargetCheckFound]
  simp only [Bool.or_eq_true] at checked ⊢
  rcases checked with checked | checked
  · left
    rcases List.any_eq_true.mp checked with
      ⟨targetY, targetYMember, targetCheck⟩
    apply List.any_eq_true.mpr
    refine ⟨targetY, targetYMember, ?_⟩
    simp only [Bool.and_eq_true] at targetCheck ⊢
    exact ⟨targetCheck.1,
      indexedReaches_sound targetCheck.2⟩
  · right
    rcases List.any_eq_true.mp checked with
      ⟨targetX, targetXMember, targetCheck⟩
    apply List.any_eq_true.mpr
    refine ⟨targetX, targetXMember, ?_⟩
    simp only [Bool.and_eq_true] at targetCheck ⊢
    exact ⟨targetCheck.1,
      indexedReaches_sound targetCheck.2⟩

def rowJointCheckIndexed
    (root : Nat → Nat → Index) (outerLevel width : Nat)
    (evenFound oddFound : List ReachNode)
    (evenIndex oddIndex : Array (Option Nat))
    (outerWest outerEast column row boundary : Nat) : Bool :=
  let source := horizontalPort
    (iterateRefine (outerLevel + 2) root) column boundary
  (indexedReaches root outerLevel width evenFound evenIndex source &&
      rowTargetCheckIndexed root outerLevel width evenFound evenIndex
        outerWest outerEast column row boundary) ||
    (indexedReaches root outerLevel width oddFound oddIndex source &&
      rowTargetCheckIndexed root outerLevel width oddFound oddIndex
        outerWest outerEast column row boundary)

theorem rowJointCheckIndexed_sound
    {root : Nat → Nat → Index} {outerLevel width : Nat}
    {evenFound oddFound : List ReachNode}
    {evenIndex oddIndex : Array (Option Nat)}
    {outerWest outerEast column row boundary : Nat}
    (checked : rowJointCheckIndexed root outerLevel width
      evenFound oddFound evenIndex oddIndex
      outerWest outerEast column row boundary = true) :
    rowJointCheckFound root outerLevel width evenFound oddFound
      outerWest outerEast column row boundary = true := by
  simp only [rowJointCheckIndexed, rowJointCheckFound,
    Bool.or_eq_true, Bool.and_eq_true] at checked ⊢
  rcases checked with checked | checked
  · exact Or.inl ⟨indexedReaches_sound checked.1,
      rowTargetCheckIndexed_sound checked.2⟩
  · exact Or.inr ⟨indexedReaches_sound checked.1,
      rowTargetCheckIndexed_sound checked.2⟩

def columnJointCheckIndexed
    (root : Nat → Nat → Index) (outerLevel width : Nat)
    (evenFound oddFound : List ReachNode)
    (evenIndex oddIndex : Array (Option Nat))
    (outerSouth outerNorth row column boundary : Nat) : Bool :=
  let source := verticalPort
    (iterateRefine (outerLevel + 2) root) boundary row
  (indexedReaches root outerLevel width evenFound evenIndex source &&
      columnTargetCheckIndexed root outerLevel width evenFound evenIndex
        outerSouth outerNorth row column boundary) ||
    (indexedReaches root outerLevel width oddFound oddIndex source &&
      columnTargetCheckIndexed root outerLevel width oddFound oddIndex
        outerSouth outerNorth row column boundary)

theorem columnJointCheckIndexed_sound
    {root : Nat → Nat → Index} {outerLevel width : Nat}
    {evenFound oddFound : List ReachNode}
    {evenIndex oddIndex : Array (Option Nat)}
    {outerSouth outerNorth row column boundary : Nat}
    (checked : columnJointCheckIndexed root outerLevel width
      evenFound oddFound evenIndex oddIndex
      outerSouth outerNorth row column boundary = true) :
    columnJointCheckFound root outerLevel width evenFound oddFound
      outerSouth outerNorth row column boundary = true := by
  simp only [columnJointCheckIndexed, columnJointCheckFound,
    Bool.or_eq_true, Bool.and_eq_true] at checked ⊢
  rcases checked with checked | checked
  · exact Or.inl ⟨indexedReaches_sound checked.1,
      columnTargetCheckIndexed_sound checked.2⟩
  · exact Or.inr ⟨indexedReaches_sound checked.1,
      columnTargetCheckIndexed_sound checked.2⟩

end PairCoverSeamResidualDirectPathFamilyTargetIndexedSearch
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
