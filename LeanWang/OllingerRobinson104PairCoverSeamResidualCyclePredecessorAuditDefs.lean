/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamResidualCycleBridges

/-!
# Finite predecessor audit for residual-cycle sources

Inside one two-substitution macrocell, every horizontal segment on a literal
sparse row and every vertical segment on a literal sparse column has an even
route from a live coarse segment of the same orientation.  This module defines
the executable audit and proves its result sound as a bounded path.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace PairCoverSeamResidualCyclePredecessorAudit

open RedCycles RedShadeGraph RedShadeGraphRefinement RedShadeGraphSearch
  RedShadeGraphSearchSoundness RedShadeGraphWeightedSearch
  PairCoverSeamShadePaths Signals.FreeCellLocal

set_option maxRecDepth 20000

def horizontalStarts (parent : Index) (sourceY : Nat) : List WeightedStart :=
  ((List.range 2).filter fun sourceX =>
    (Signals.horizontalInterior?
      (componentAt (coarseGrid parent) sourceX sourceY)
      (quadrantAt sourceX sourceY)).isSome).map fun sourceX =>
    ⟨sparsePort (horizontalPort (coarseGrid parent) sourceX sourceY), false⟩

def verticalStarts (parent : Index) (sourceX : Nat) : List WeightedStart :=
  ((List.range 2).filter fun sourceY =>
    (Signals.verticalInterior?
      (componentAt (coarseGrid parent) sourceX sourceY)
      (quadrantAt sourceX sourceY)).isSome).map fun sourceY =>
    ⟨sparsePort (verticalPort (coarseGrid parent) sourceX sourceY), false⟩

def reachesEven (parent : Index) (starts : List WeightedStart)
    (target : Port) : Bool :=
  let nodes := exploreFastWeighted (fineGrid parent) 8 8 1000 starts
  portPresent (fineGrid parent) target &&
    nodes.any fun node => !node.parity && decide (node.current = target)

def horizontalAt (parent : Index) (sourceY targetX : Nat) : Bool :=
  let grid := fineGrid parent
  let targetY := sparseCoordinate sourceY
  let required := (Signals.horizontalInterior?
    (componentAt grid targetX targetY) (quadrantAt targetX targetY)).isSome
  !required || reachesEven parent (horizontalStarts parent sourceY)
    (horizontalPort grid targetX targetY)

def verticalAt (parent : Index) (sourceX targetY : Nat) : Bool :=
  let grid := fineGrid parent
  let targetX := sparseCoordinate sourceX
  let required := (Signals.verticalInterior?
    (componentAt grid targetX targetY) (quadrantAt targetX targetY)).isSome
  !required || reachesEven parent (verticalStarts parent sourceX)
    (verticalPort grid targetX targetY)

def checkParent (parent : Index) : Bool :=
  ((List.range 2).all fun sourceY =>
    (List.range 8).all (horizontalAt parent sourceY)) &&
  ((List.range 2).all fun sourceX =>
    (List.range 8).all (verticalAt parent sourceX))

private theorem horizontalStarts_inBounds (parent : Index) (sourceY : Nat)
    (hsourceY : sourceY < 2) :
    ∀ start ∈ horizontalStarts parent sourceY,
      PortInBounds start.port 8 8 := by
  intro start hstart
  rw [horizontalStarts, List.mem_map] at hstart
  rcases hstart with ⟨sourceX, hsourceX, rfl⟩
  simp only [List.mem_filter, List.mem_range] at hsourceX
  have hsourceX : sourceX < 2 := by
    exact hsourceX.1
  unfold horizontalPort
  split <;>
    simp [PortInBounds, sparsePort, sparseCoordinate, macroOrigin,
      localCoordinate] <;> omega

private theorem verticalStarts_inBounds (parent : Index) (sourceX : Nat)
    (hsourceX : sourceX < 2) :
    ∀ start ∈ verticalStarts parent sourceX,
      PortInBounds start.port 8 8 := by
  intro start hstart
  rw [verticalStarts, List.mem_map] at hstart
  rcases hstart with ⟨sourceY, hsourceY, rfl⟩
  simp only [List.mem_filter, List.mem_range] at hsourceY
  have hsourceY : sourceY < 2 := by
    exact hsourceY.1
  unfold verticalPort
  split <;>
    simp [PortInBounds, sparsePort, sparseCoordinate, macroOrigin,
      localCoordinate] <;> omega

theorem reachesEven_bounded_sound
    {parent : Index} {starts : List WeightedStart} {target : Port}
    (startsInBounds : ∀ start ∈ starts, PortInBounds start.port 8 8)
    (startsEven : ∀ start ∈ starts, start.parity = false)
    (checked : reachesEven parent starts target = true) :
    ∃ start ∈ starts,
      BoundedPath (fineGrid parent) 8 8 start.port target false := by
  simp only [reachesEven, Bool.and_eq_true, List.any_eq_true,
    decide_eq_true_eq] at checked
  rcases checked.2 with ⟨node, hnode, hparity, hcurrent⟩
  rcases exploreFastWeighted_bounded_sound startsInBounds hnode with
    ⟨start, hstart, path⟩
  refine ⟨start, hstart, ?_⟩
  rw [hcurrent] at path
  have nodeEven : node.parity = false := by
    cases hnodeParity : node.parity <;> simp_all
  simpa [startsEven start hstart, nodeEven] using path

theorem horizontalAt_sound
    {parent : Index} {sourceY targetX : Nat}
    (hsourceY : sourceY < 2)
    (checked : horizontalAt parent sourceY targetX = true)
    (interior : Signals.horizontalInterior?
      (componentAt (fineGrid parent) targetX (sparseCoordinate sourceY))
      (quadrantAt targetX (sparseCoordinate sourceY)) ≠ none) :
    ∃ sourceX, sourceX < 2 ∧
      Signals.horizontalInterior?
        (componentAt (coarseGrid parent) sourceX sourceY)
        (quadrantAt sourceX sourceY) ≠ none ∧
      BoundedPath (fineGrid parent) 8 8
        (sparsePort (horizontalPort (coarseGrid parent) sourceX sourceY))
        (horizontalPort (fineGrid parent) targetX (sparseCoordinate sourceY))
        false := by
  have required : (Signals.horizontalInterior?
      (componentAt (fineGrid parent) targetX (sparseCoordinate sourceY))
      (quadrantAt targetX (sparseCoordinate sourceY))).isSome = true :=
    Option.isSome_iff_ne_none.mpr interior
  simp only [horizontalAt, required, Bool.not_true, Bool.false_or] at checked
  rcases reachesEven_bounded_sound
      (horizontalStarts_inBounds parent sourceY hsourceY)
      (by
        intro start hstart
        rw [horizontalStarts, List.mem_map] at hstart
        rcases hstart with ⟨sourceX, hsourceX, rfl⟩
        rfl)
      checked with
    ⟨start, hstart, path⟩
  rw [horizontalStarts, List.mem_map] at hstart
  rcases hstart with ⟨sourceX, hsourceX, rfl⟩
  simp only [List.mem_filter, List.mem_range] at hsourceX
  exact ⟨sourceX, hsourceX.1, Option.isSome_iff_ne_none.mp hsourceX.2, path⟩

theorem verticalAt_sound
    {parent : Index} {sourceX targetY : Nat}
    (hsourceX : sourceX < 2)
    (checked : verticalAt parent sourceX targetY = true)
    (interior : Signals.verticalInterior?
      (componentAt (fineGrid parent) (sparseCoordinate sourceX) targetY)
      (quadrantAt (sparseCoordinate sourceX) targetY) ≠ none) :
    ∃ sourceY, sourceY < 2 ∧
      Signals.verticalInterior?
        (componentAt (coarseGrid parent) sourceX sourceY)
        (quadrantAt sourceX sourceY) ≠ none ∧
      BoundedPath (fineGrid parent) 8 8
        (sparsePort (verticalPort (coarseGrid parent) sourceX sourceY))
        (verticalPort (fineGrid parent) (sparseCoordinate sourceX) targetY)
        false := by
  have required : (Signals.verticalInterior?
      (componentAt (fineGrid parent) (sparseCoordinate sourceX) targetY)
      (quadrantAt (sparseCoordinate sourceX) targetY)).isSome = true :=
    Option.isSome_iff_ne_none.mpr interior
  simp only [verticalAt, required, Bool.not_true, Bool.false_or] at checked
  rcases reachesEven_bounded_sound
      (verticalStarts_inBounds parent sourceX hsourceX)
      (by
        intro start hstart
        rw [verticalStarts, List.mem_map] at hstart
        rcases hstart with ⟨sourceY, hsourceY, rfl⟩
        rfl)
      checked with
    ⟨start, hstart, path⟩
  rw [verticalStarts, List.mem_map] at hstart
  rcases hstart with ⟨sourceY, hsourceY, rfl⟩
  simp only [List.mem_filter, List.mem_range] at hsourceY
  exact ⟨sourceY, hsourceY.1, Option.isSome_iff_ne_none.mp hsourceY.2, path⟩

theorem horizontalAt_of_checkParent
    {parent : Index} {sourceY targetX : Nat}
    (checked : checkParent parent = true)
    (hsourceY : sourceY < 2) (htargetX : targetX < 8) :
    horizontalAt parent sourceY targetX = true := by
  simp only [checkParent, Bool.and_eq_true, List.all_eq_true,
    List.mem_range] at checked
  exact checked.1 sourceY hsourceY targetX htargetX

theorem verticalAt_of_checkParent
    {parent : Index} {sourceX targetY : Nat}
    (checked : checkParent parent = true)
    (hsourceX : sourceX < 2) (htargetY : targetY < 8) :
    verticalAt parent sourceX targetY = true := by
  simp only [checkParent, Bool.and_eq_true, List.all_eq_true,
    List.mem_range] at checked
  exact checked.2 sourceX hsourceX targetY htargetY

end PairCoverSeamResidualCyclePredecessorAudit
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
