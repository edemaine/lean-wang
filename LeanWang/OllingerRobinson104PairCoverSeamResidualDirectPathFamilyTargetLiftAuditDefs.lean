/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104RefinedCoordinateProjection
import LeanWang.OllingerRobinson104PairCoverSeamResidualCyclePredecessorAuditDefs

/-!
# Finite forward lift audit for residual family targets

Starting from the literal sparse copy of one exact coarse horizontal or
vertical interior, search its two-substitution `8 x 8` macrocell for an even
route to a requested aligned fine coordinate.  The target is constrained to
the coarse source's own sparse interval, so it can later preserve strict
betweenness without inspecting the surrounding hierarchy.
-/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamResidualDirectPathFamilyTargetLiftAudit

open RedCycles RedShadeGraph RedShadeGraphRefinement
  RedShadeGraphSearchSoundness RedShadeGraphWeightedSearch
  PairCoverSeamShadePaths Signals.FreeCellLocal
  RefinedCoordinateProjection

set_option maxRecDepth 20000

/-- Exclusive end of a local old-coordinate sparse interval. -/
def intervalEnd (source : Nat) : Nat :=
  if source = 0 then 1 else 8

def horizontalStart (parent : Index) (sourceX sourceY : Nat) : WeightedStart :=
  ⟨sparsePort (horizontalPort (coarseGrid parent) sourceX sourceY), false⟩

def horizontalNodes (parent : Index) (sourceX sourceY : Nat) :
    List RedShadeGraphSearch.Node :=
  exploreFastWeighted (fineGrid parent) 8 8 1000
    [horizontalStart parent sourceX sourceY]

def horizontalTargetFound
    (parent : Index) (sourceX sourceY targetX : Nat) : Bool :=
  let grid := fineGrid parent
  let found := horizontalNodes parent sourceX sourceY
  (List.range 8).any fun targetY =>
    decide (sparseCoordinate sourceY ≤ targetY) &&
    decide (targetY < intervalEnd sourceY) &&
    (Signals.horizontalInterior?
      (componentAt grid targetX targetY) (quadrantAt targetX targetY)).isSome &&
    found.any fun node => !node.parity &&
      decide (node.current = horizontalPort grid targetX targetY)

def horizontalSourceRequired (parent : Index) (sourceX sourceY : Nat) : Bool :=
  (Signals.horizontalInterior?
    (componentAt (coarseGrid parent) sourceX sourceY)
    (quadrantAt sourceX sourceY)).isSome

def horizontalCheckParent (parent : Index) : Bool :=
  (List.range 2).all fun sourceX =>
    (List.range 2).all fun sourceY =>
      !horizontalSourceRequired parent sourceX sourceY ||
        (List.range 8).all fun targetX =>
          !decide (coarseCoordinate targetX = sourceX) ||
            horizontalTargetFound parent sourceX sourceY targetX

def verticalStart (parent : Index) (sourceX sourceY : Nat) : WeightedStart :=
  ⟨sparsePort (verticalPort (coarseGrid parent) sourceX sourceY), false⟩

def verticalNodes (parent : Index) (sourceX sourceY : Nat) :
    List RedShadeGraphSearch.Node :=
  exploreFastWeighted (fineGrid parent) 8 8 1000
    [verticalStart parent sourceX sourceY]

def verticalTargetFound
    (parent : Index) (sourceX sourceY targetY : Nat) : Bool :=
  let grid := fineGrid parent
  let found := verticalNodes parent sourceX sourceY
  (List.range 8).any fun targetX =>
    decide (sparseCoordinate sourceX ≤ targetX) &&
    decide (targetX < intervalEnd sourceX) &&
    (Signals.verticalInterior?
      (componentAt grid targetX targetY) (quadrantAt targetX targetY)).isSome &&
    found.any fun node => !node.parity &&
      decide (node.current = verticalPort grid targetX targetY)

def verticalSourceRequired (parent : Index) (sourceX sourceY : Nat) : Bool :=
  (Signals.verticalInterior?
    (componentAt (coarseGrid parent) sourceX sourceY)
    (quadrantAt sourceX sourceY)).isSome

def verticalCheckParent (parent : Index) : Bool :=
  (List.range 2).all fun sourceX =>
    (List.range 2).all fun sourceY =>
      !verticalSourceRequired parent sourceX sourceY ||
        (List.range 8).all fun targetY =>
          !decide (coarseCoordinate targetY = sourceY) ||
            verticalTargetFound parent sourceX sourceY targetY

def checkParent (parent : Index) : Bool :=
  horizontalCheckParent parent && verticalCheckParent parent

private theorem horizontalStart_inBounds
    (parent : Index) {sourceX sourceY : Nat}
    (sourceXLt : sourceX < 2) (sourceYLt : sourceY < 2) :
    PortInBounds (horizontalStart parent sourceX sourceY).port 8 8 := by
  unfold horizontalStart horizontalPort
  split <;>
    simp [PortInBounds, sparsePort, sparseCoordinate, macroOrigin,
      localCoordinate] <;> omega

private theorem verticalStart_inBounds
    (parent : Index) {sourceX sourceY : Nat}
    (sourceXLt : sourceX < 2) (sourceYLt : sourceY < 2) :
    PortInBounds (verticalStart parent sourceX sourceY).port 8 8 := by
  unfold verticalStart verticalPort
  split <;>
    simp [PortInBounds, sparsePort, sparseCoordinate, macroOrigin,
      localCoordinate] <;> omega

/-- Soundness of one accepted horizontal forward-lift target. -/
theorem horizontalTargetFound_sound
    {parent : Index} {sourceX sourceY targetX : Nat}
    (sourceXLt : sourceX < 2) (sourceYLt : sourceY < 2)
    (checked : horizontalTargetFound parent sourceX sourceY targetX = true) :
    ∃ targetY,
      sparseCoordinate sourceY ≤ targetY ∧
      targetY < intervalEnd sourceY ∧
      Signals.horizontalInterior?
        (componentAt (fineGrid parent) targetX targetY)
        (quadrantAt targetX targetY) ≠ none ∧
      BoundedPath (fineGrid parent) 8 8
        (sparsePort (horizontalPort (coarseGrid parent) sourceX sourceY))
        (horizontalPort (fineGrid parent) targetX targetY) false := by
  simp only [horizontalTargetFound, List.any_eq_true, List.mem_range,
    Bool.and_eq_true, decide_eq_true_eq, Option.isSome_iff_ne_none] at checked
  rcases checked with
    ⟨targetY, targetYLt, ⟨⟨sourceYLe, targetYEnd⟩, interior⟩,
      node, nodeMem, nodeParity, nodeCurrent⟩
  refine ⟨targetY, sourceYLe, targetYEnd, interior, ?_⟩
  have sound := exploreFastWeighted_bounded_sound
    (starts := [horizontalStart parent sourceX sourceY])
    (fun start hstart => by
      simp only [List.mem_singleton] at hstart
      subst start
      exact horizontalStart_inBounds parent sourceXLt sourceYLt)
    nodeMem
  rcases sound with ⟨start, startMem, path⟩
  simp only [List.mem_singleton] at startMem
  subst start
  have parity : node.parity = false := by
    cases h : node.parity <;> simp_all
  rw [nodeCurrent] at path
  simpa [horizontalStart, parity] using path

/-- Vertical dual of `horizontalTargetFound_sound`. -/
theorem verticalTargetFound_sound
    {parent : Index} {sourceX sourceY targetY : Nat}
    (sourceXLt : sourceX < 2) (sourceYLt : sourceY < 2)
    (checked : verticalTargetFound parent sourceX sourceY targetY = true) :
    ∃ targetX,
      sparseCoordinate sourceX ≤ targetX ∧
      targetX < intervalEnd sourceX ∧
      Signals.verticalInterior?
        (componentAt (fineGrid parent) targetX targetY)
        (quadrantAt targetX targetY) ≠ none ∧
      BoundedPath (fineGrid parent) 8 8
        (sparsePort (verticalPort (coarseGrid parent) sourceX sourceY))
        (verticalPort (fineGrid parent) targetX targetY) false := by
  simp only [verticalTargetFound, List.any_eq_true, List.mem_range,
    Bool.and_eq_true, decide_eq_true_eq, Option.isSome_iff_ne_none] at checked
  rcases checked with
    ⟨targetX, targetXLt, ⟨⟨sourceXLe, targetXEnd⟩, interior⟩,
      node, nodeMem, nodeParity, nodeCurrent⟩
  refine ⟨targetX, sourceXLe, targetXEnd, interior, ?_⟩
  have sound := exploreFastWeighted_bounded_sound
    (starts := [verticalStart parent sourceX sourceY])
    (fun start hstart => by
      simp only [List.mem_singleton] at hstart
      subst start
      exact verticalStart_inBounds parent sourceXLt sourceYLt)
    nodeMem
  rcases sound with ⟨start, startMem, path⟩
  simp only [List.mem_singleton] at startMem
  subst start
  have parity : node.parity = false := by
    cases h : node.parity <;> simp_all
  rw [nodeCurrent] at path
  simpa [verticalStart, parity] using path

/-- Extract one required horizontal target from a successful parent audit. -/
theorem horizontalTargetFound_of_checkParent
    {parent : Index} {sourceX sourceY targetX : Nat}
    (checked : checkParent parent = true)
    (sourceXLt : sourceX < 2) (sourceYLt : sourceY < 2)
    (targetXLt : targetX < 8)
    (targetAligned : coarseCoordinate targetX = sourceX)
    (sourceInterior : Signals.horizontalInterior?
      (componentAt (coarseGrid parent) sourceX sourceY)
      (quadrantAt sourceX sourceY) ≠ none) :
    horizontalTargetFound parent sourceX sourceY targetX = true := by
  have required : horizontalSourceRequired parent sourceX sourceY = true := by
    exact Option.isSome_iff_ne_none.mpr sourceInterior
  simp only [checkParent, Bool.and_eq_true] at checked
  have horizontal := checked.1
  simp only [horizontalCheckParent, List.all_eq_true, List.mem_range] at horizontal
  have source := horizontal sourceX sourceXLt sourceY sourceYLt
  simp only [required, Bool.not_true, Bool.false_or] at source
  simp only [List.all_eq_true, List.mem_range] at source
  have target := source targetX targetXLt
  simp only [targetAligned, decide_true, Bool.not_true, Bool.false_or] at target
  exact target

/-- Vertical dual of `horizontalTargetFound_of_checkParent`. -/
theorem verticalTargetFound_of_checkParent
    {parent : Index} {sourceX sourceY targetY : Nat}
    (checked : checkParent parent = true)
    (sourceXLt : sourceX < 2) (sourceYLt : sourceY < 2)
    (targetYLt : targetY < 8)
    (targetAligned : coarseCoordinate targetY = sourceY)
    (sourceInterior : Signals.verticalInterior?
      (componentAt (coarseGrid parent) sourceX sourceY)
      (quadrantAt sourceX sourceY) ≠ none) :
    verticalTargetFound parent sourceX sourceY targetY = true := by
  have required : verticalSourceRequired parent sourceX sourceY = true := by
    exact Option.isSome_iff_ne_none.mpr sourceInterior
  simp only [checkParent, Bool.and_eq_true] at checked
  have vertical := checked.2
  simp only [verticalCheckParent, List.all_eq_true, List.mem_range] at vertical
  have source := vertical sourceX sourceXLt sourceY sourceYLt
  simp only [required, Bool.not_true, Bool.false_or] at source
  simp only [List.all_eq_true, List.mem_range] at source
  have target := source targetY targetYLt
  simp only [targetAligned, decide_true, Bool.not_true, Bool.false_or] at target
  exact target

end PairCoverSeamResidualDirectPathFamilyTargetLiftAudit
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
