/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamResidualCyclePredecessorAudit

/-!
# Exact-coordinate predecessor audit

The earlier predecessor audit permits either live coarse selector in the
containing two-cell block.  Target recurrence needs the stronger fact that the
selected predecessor is the exact `coarseCoordinate` of the fine selector.
This file checks that stronger property and proves each accepted result sound.
-/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamResidualDirectPathExactPredecessorAudit

open RedShadeGraph RedShadeGraphRefinement RedShadeGraphSearchSoundness
  RedShadeGraphWeightedSearch
  PairCoverSeamResidualCyclePredecessorAudit PairCoverSeamShadePaths
  RefinedCoordinateProjection Signals.FreeCellLocal

set_option maxRecDepth 20000

def horizontalStart (parent : Index) (sourceY targetX : Nat) : WeightedStart :=
  ⟨sparsePort (horizontalPort (coarseGrid parent)
    (coarseCoordinate targetX) sourceY), false⟩

def horizontalAt (parent : Index) (sourceY targetX : Nat) : Bool :=
  let coarse := coarseGrid parent
  let fine := fineGrid parent
  let sourceX := coarseCoordinate targetX
  let targetY := sparseCoordinate sourceY
  let required := (Signals.horizontalInterior?
    (componentAt fine targetX targetY) (quadrantAt targetX targetY)).isSome
  !required ||
    ((Signals.horizontalInterior?
      (componentAt coarse sourceX sourceY)
      (quadrantAt sourceX sourceY)).isSome &&
    reachesEven parent [horizontalStart parent sourceY targetX]
      (horizontalPort fine targetX targetY))

def verticalStart (parent : Index) (sourceX targetY : Nat) : WeightedStart :=
  ⟨sparsePort (verticalPort (coarseGrid parent)
    sourceX (coarseCoordinate targetY)), false⟩

def verticalAt (parent : Index) (sourceX targetY : Nat) : Bool :=
  let coarse := coarseGrid parent
  let fine := fineGrid parent
  let sourceY := coarseCoordinate targetY
  let targetX := sparseCoordinate sourceX
  let required := (Signals.verticalInterior?
    (componentAt fine targetX targetY) (quadrantAt targetX targetY)).isSome
  !required ||
    ((Signals.verticalInterior?
      (componentAt coarse sourceX sourceY)
      (quadrantAt sourceX sourceY)).isSome &&
    reachesEven parent [verticalStart parent sourceX targetY]
      (verticalPort fine targetX targetY))

def checkParent (parent : Index) : Bool :=
  ((List.range 2).all fun sourceY =>
    (List.range 8).all (horizontalAt parent sourceY)) &&
  ((List.range 2).all fun sourceX =>
    (List.range 8).all (verticalAt parent sourceX))

private theorem coarseCoordinate_lt_two {coordinate : Nat}
    (coordinateLt : coordinate < 8) : coarseCoordinate coordinate < 2 := by
  have divZero : coordinate / 8 = 0 := by omega
  unfold coarseCoordinate
  rw [divZero]
  split <;> omega

private theorem horizontalStart_inBounds
    (parent : Index) {sourceY targetX : Nat}
    (sourceYLt : sourceY < 2) (targetXLt : targetX < 8) :
    PortInBounds (horizontalStart parent sourceY targetX).port 8 8 := by
  have sourceXLt : coarseCoordinate targetX < 2 :=
    coarseCoordinate_lt_two targetXLt
  unfold horizontalStart horizontalPort
  split <;>
    simp [PortInBounds, sparsePort, sparseCoordinate, macroOrigin,
      localCoordinate] <;> omega

private theorem verticalStart_inBounds
    (parent : Index) {sourceX targetY : Nat}
    (sourceXLt : sourceX < 2) (targetYLt : targetY < 8) :
    PortInBounds (verticalStart parent sourceX targetY).port 8 8 := by
  have sourceYLt : coarseCoordinate targetY < 2 :=
    coarseCoordinate_lt_two targetYLt
  unfold verticalStart verticalPort
  split <;>
    simp [PortInBounds, sparsePort, sparseCoordinate, macroOrigin,
      localCoordinate] <;> omega

/-- Recover the exact coarse horizontal predecessor and its bounded even
connector from one accepted local query. -/
theorem horizontalAt_sound
    {parent : Index} {sourceY targetX : Nat}
    (sourceYLt : sourceY < 2) (targetXLt : targetX < 8)
    (checked : horizontalAt parent sourceY targetX = true)
    (interior : Signals.horizontalInterior?
      (componentAt (fineGrid parent) targetX (sparseCoordinate sourceY))
      (quadrantAt targetX (sparseCoordinate sourceY)) ≠ none) :
    Signals.horizontalInterior?
        (componentAt (coarseGrid parent) (coarseCoordinate targetX) sourceY)
        (quadrantAt (coarseCoordinate targetX) sourceY) ≠ none ∧
      BoundedPath (fineGrid parent) 8 8
        (sparsePort (horizontalPort (coarseGrid parent)
          (coarseCoordinate targetX) sourceY))
        (horizontalPort (fineGrid parent) targetX
          (sparseCoordinate sourceY)) false := by
  have required : (Signals.horizontalInterior?
      (componentAt (fineGrid parent) targetX (sparseCoordinate sourceY))
      (quadrantAt targetX (sparseCoordinate sourceY))).isSome = true :=
    Option.isSome_iff_ne_none.mpr interior
  simp only [horizontalAt, required, Bool.not_true, Bool.false_or,
    Bool.and_eq_true] at checked
  refine ⟨Option.isSome_iff_ne_none.mp checked.1, ?_⟩
  rcases reachesEven_bounded_sound
      (starts := [horizontalStart parent sourceY targetX])
      (by
        intro start startMem
        simp only [List.mem_singleton] at startMem
        subst start
        exact horizontalStart_inBounds parent sourceYLt targetXLt)
      (by
        intro start startMem
        simp only [List.mem_singleton] at startMem
        subst start
        rfl)
      checked.2 with ⟨start, startMem, path⟩
  simp only [List.mem_singleton] at startMem
  subst start
  simpa [horizontalStart] using path

/-- Vertical dual of `horizontalAt_sound`. -/
theorem verticalAt_sound
    {parent : Index} {sourceX targetY : Nat}
    (sourceXLt : sourceX < 2) (targetYLt : targetY < 8)
    (checked : verticalAt parent sourceX targetY = true)
    (interior : Signals.verticalInterior?
      (componentAt (fineGrid parent) (sparseCoordinate sourceX) targetY)
      (quadrantAt (sparseCoordinate sourceX) targetY) ≠ none) :
    Signals.verticalInterior?
        (componentAt (coarseGrid parent) sourceX (coarseCoordinate targetY))
        (quadrantAt sourceX (coarseCoordinate targetY)) ≠ none ∧
      BoundedPath (fineGrid parent) 8 8
        (sparsePort (verticalPort (coarseGrid parent)
          sourceX (coarseCoordinate targetY)))
        (verticalPort (fineGrid parent) (sparseCoordinate sourceX) targetY)
        false := by
  have required : (Signals.verticalInterior?
      (componentAt (fineGrid parent) (sparseCoordinate sourceX) targetY)
      (quadrantAt (sparseCoordinate sourceX) targetY)).isSome = true :=
    Option.isSome_iff_ne_none.mpr interior
  simp only [verticalAt, required, Bool.not_true, Bool.false_or,
    Bool.and_eq_true] at checked
  refine ⟨Option.isSome_iff_ne_none.mp checked.1, ?_⟩
  rcases reachesEven_bounded_sound
      (starts := [verticalStart parent sourceX targetY])
      (by
        intro start startMem
        simp only [List.mem_singleton] at startMem
        subst start
        exact verticalStart_inBounds parent sourceXLt targetYLt)
      (by
        intro start startMem
        simp only [List.mem_singleton] at startMem
        subst start
        rfl)
      checked.2 with ⟨start, startMem, path⟩
  simp only [List.mem_singleton] at startMem
  subst start
  simpa [verticalStart] using path

theorem horizontalAt_of_checkParent
    {parent : Index} {sourceY targetX : Nat}
    (checked : checkParent parent = true)
    (sourceYLt : sourceY < 2) (targetXLt : targetX < 8) :
    horizontalAt parent sourceY targetX = true := by
  simp only [checkParent, Bool.and_eq_true, List.all_eq_true,
    List.mem_range] at checked
  exact checked.1 sourceY sourceYLt targetX targetXLt

theorem verticalAt_of_checkParent
    {parent : Index} {sourceX targetY : Nat}
    (checked : checkParent parent = true)
    (sourceXLt : sourceX < 2) (targetYLt : targetY < 8) :
    verticalAt parent sourceX targetY = true := by
  simp only [checkParent, Bool.and_eq_true, List.all_eq_true,
    List.mem_range] at checked
  exact checked.2 sourceX sourceXLt targetY targetYLt

end PairCoverSeamResidualDirectPathExactPredecessorAudit
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
