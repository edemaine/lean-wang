/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamResidualCyclePredecessorAudit
import LeanWang.OllingerRobinson104ShadedFreeLineProjectionSourceLists

/-!
# Finite local-cycle audit for created residual sources

Inside one two-substitution macrocell, every live horizontal segment on a
created row and every live vertical segment on a created column reaches the
canonical cell cycle.  The path parity is retained: an even route reaches the
cell cycle directly, while an odd route will compose with the odd bridge to
the cell's hierarchy parent.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace PairCoverSeamResidualCycleLocalAudit

open OrientedRedCycles RedCycles RedShadeCycles RedShadeGraph RedShadeGraphRefinement
  RedShadeGraphBoards RedShadeGraphSearch RedShadeGraphSearchSoundness
  RedShadeGraphWeightedSearch PairCoverSeamShadePaths
  ShadedFreeLineProjectionSourceLists Signals.FreeCellLocal

set_option maxRecDepth 20000

def createdCoordinates : List Nat := [2, 3, 4, 5, 6, 7]

def cycleStarts : List WeightedStart :=
  (cyclePorts 1 3 1 3).map fun port => ⟨port, false⟩

def nodes (parent : Index) : List Node :=
  exploreFastWeighted (fineGrid parent) 8 8 1000 cycleStarts

def reaches (parent : Index) (target : Port) : Bool :=
  portPresent (fineGrid parent) target &&
    (nodes parent).any fun node => decide (node.current = target)

def horizontalAt (parent : Index) (targetX targetY : Nat) : Bool :=
  let grid := fineGrid parent
  let required := (Signals.horizontalInterior?
    (componentAt grid targetX targetY) (quadrantAt targetX targetY)).isSome
  !required || reaches parent (horizontalPort grid targetX targetY)

def verticalAt (parent : Index) (targetX targetY : Nat) : Bool :=
  let grid := fineGrid parent
  let required := (Signals.verticalInterior?
    (componentAt grid targetX targetY) (quadrantAt targetX targetY)).isSome
  !required || reaches parent (verticalPort grid targetX targetY)

def checkParent (parent : Index) : Bool :=
  ((List.range 8).all fun targetX =>
    createdCoordinates.all (horizontalAt parent targetX)) &&
  (createdCoordinates.all fun targetX =>
    (List.range 8).all (verticalAt parent targetX))

def LocalCycleRoute (parent : Index) (target : Port) : Prop :=
  ∃ entry ∈ cyclePorts 1 3 1 3, ∃ parity,
    BoundedPath (fineGrid parent) 8 8 entry target parity

private theorem cyclePort_inBounds {port : Port}
    (onCycle : OnCycle 1 3 1 3 port) : PortInBounds port 8 8 := by
  cases onCycle <;>
    simp_all [PortInBounds, quarterWest, quarterEast,
      quarterSouth, quarterNorth] <;>
    omega

theorem cycleStarts_inBounds :
    ∀ start ∈ cycleStarts, PortInBounds start.port 8 8 := by
  intro start hstart
  rw [cycleStarts, List.mem_map] at hstart
  rcases hstart with ⟨port, hport, rfl⟩
  exact cyclePort_inBounds
    (onCycle_of_mem_cyclePorts (by omega) (by omega) hport)

theorem reaches_bounded_sound {parent : Index} {target : Port}
    (checked : reaches parent target = true) :
    LocalCycleRoute parent target := by
  simp only [reaches, Bool.and_eq_true, List.any_eq_true,
    decide_eq_true_eq] at checked
  rcases checked.2 with ⟨node, hnode, hcurrent⟩
  rcases exploreFastWeighted_bounded_sound cycleStarts_inBounds hnode with
    ⟨start, hstart, path⟩
  rw [hcurrent] at path
  rw [cycleStarts, List.mem_map] at hstart
  rcases hstart with ⟨entry, hentry, rfl⟩
  refine ⟨entry, hentry, node.parity, ?_⟩
  simpa using path

theorem horizontalAt_sound
    {parent : Index} {targetX targetY : Nat}
    (checked : horizontalAt parent targetX targetY = true)
    (interior : Signals.horizontalInterior?
      (componentAt (fineGrid parent) targetX targetY)
      (quadrantAt targetX targetY) ≠ none) :
    LocalCycleRoute parent
      (horizontalPort (fineGrid parent) targetX targetY) := by
  have required : (Signals.horizontalInterior?
      (componentAt (fineGrid parent) targetX targetY)
      (quadrantAt targetX targetY)).isSome = true :=
    Option.isSome_iff_ne_none.mpr interior
  simp only [horizontalAt, required, Bool.not_true, Bool.false_or] at checked
  exact reaches_bounded_sound checked

theorem verticalAt_sound
    {parent : Index} {targetX targetY : Nat}
    (checked : verticalAt parent targetX targetY = true)
    (interior : Signals.verticalInterior?
      (componentAt (fineGrid parent) targetX targetY)
      (quadrantAt targetX targetY) ≠ none) :
    LocalCycleRoute parent
      (verticalPort (fineGrid parent) targetX targetY) := by
  have required : (Signals.verticalInterior?
      (componentAt (fineGrid parent) targetX targetY)
      (quadrantAt targetX targetY)).isSome = true :=
    Option.isSome_iff_ne_none.mpr interior
  simp only [verticalAt, required, Bool.not_true, Bool.false_or] at checked
  exact reaches_bounded_sound checked

theorem horizontalAt_of_checkParent
    {parent : Index} {targetX targetY : Nat}
    (checked : checkParent parent = true)
    (htargetX : targetX < 8) (htargetY : targetY ∈ createdCoordinates) :
    horizontalAt parent targetX targetY = true := by
  simp only [checkParent, Bool.and_eq_true, List.all_eq_true,
    List.mem_range] at checked
  exact checked.1 targetX htargetX targetY htargetY

theorem verticalAt_of_checkParent
    {parent : Index} {targetX targetY : Nat}
    (checked : checkParent parent = true)
    (htargetX : targetX ∈ createdCoordinates) (htargetY : targetY < 8) :
    verticalAt parent targetX targetY = true := by
  simp only [checkParent, Bool.and_eq_true, List.all_eq_true,
    List.mem_range] at checked
  exact checked.2 targetX htargetX targetY htargetY

end PairCoverSeamResidualCycleLocalAudit
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
