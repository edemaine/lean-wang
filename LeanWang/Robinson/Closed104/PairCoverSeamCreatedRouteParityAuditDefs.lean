/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.PairCoverSeamResidualCycleLocalAuditDefs

/-!
# Exact parity audit for created residual sources

The local-cycle audit only retained an existential path parity.  The created
coordinate itself determines that parity: residues three and six reach the
cell cycle evenly, while residues four and five reach it oddly.  Keeping this
fact identifies the exact hierarchy level and family reached by a source.
-/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamCreatedRouteParityAudit

open OrientedRedCycles RedCycles RedShadeCycles RedShadeGraph
  RedShadeGraphRefinement RedShadeGraphBoards RedShadeGraphSearch
  RedShadeGraphSearchSoundness RedShadeGraphWeightedSearch
  PairCoverSeamShadePaths
  PairCoverSeamResidualCycleLocalAudit
  ShadedFreeLineProjectionSourceLists Signals.FreeCellLocal

set_option maxRecDepth 20000

/-- The route parity forced by a local created coordinate. -/
def createdParity (coordinate : Nat) : Bool :=
  coordinate == 4 || coordinate == 5

theorem createdParity_eq_true_iff (coordinate : Nat) :
    createdParity coordinate = true ↔ coordinate = 4 ∨ coordinate = 5 := by
  simp [createdParity]

theorem createdParity_eq_false_iff (coordinate : Nat) :
    createdParity coordinate = false ↔ coordinate ≠ 4 ∧ coordinate ≠ 5 := by
  simp [createdParity]

def reachesParityIn (parent : Index) (found : List Node)
    (target : Port) (parity : Bool) : Bool :=
  portPresent (fineGrid parent) target &&
    found.any fun node =>
      decide (node.current = target) && decide (node.parity = parity)

def horizontalAt (parent : Index) (found : List Node)
    (targetX targetY : Nat) : Bool :=
  let grid := fineGrid parent
  let required := (Signals.horizontalInterior?
    (componentAt grid targetX targetY) (quadrantAt targetX targetY)).isSome
  !required || reachesParityIn parent found
    (horizontalPort grid targetX targetY) (createdParity targetY)

def verticalAt (parent : Index) (found : List Node)
    (targetX targetY : Nat) : Bool :=
  let grid := fineGrid parent
  let required := (Signals.verticalInterior?
    (componentAt grid targetX targetY) (quadrantAt targetX targetY)).isSome
  !required || reachesParityIn parent found
    (verticalPort grid targetX targetY) (createdParity targetX)

/-- The shared `found` list makes each parent perform one weighted flood. -/
def checkParent (parent : Index) : Bool :=
  let found := nodes parent
  ((List.range 8).all fun targetX =>
    createdCoordinates.all (horizontalAt parent found targetX)) &&
  (createdCoordinates.all fun targetX =>
    (List.range 8).all (verticalAt parent found targetX))

def LocalCycleRouteWithParity (parent : Index) (target : Port)
    (parity : Bool) : Prop :=
  ∃ entry ∈ cyclePorts 1 3 1 3,
    BoundedPath (fineGrid parent) 8 8 entry target parity

theorem reachesParityIn_bounded_sound
    {parent : Index} {target : Port} {parity : Bool}
    (checked : reachesParityIn parent (nodes parent) target parity = true) :
    LocalCycleRouteWithParity parent target parity := by
  simp only [reachesParityIn, Bool.and_eq_true, List.any_eq_true,
    decide_eq_true_eq] at checked
  rcases checked.2 with ⟨node, hnode, hcurrent, hparity⟩
  rcases exploreFastWeighted_bounded_sound cycleStarts_inBounds hnode with
    ⟨start, hstart, path⟩
  rw [hcurrent] at path
  rw [cycleStarts, List.mem_map] at hstart
  rcases hstart with ⟨entry, hentry, rfl⟩
  rw [hparity] at path
  exact ⟨entry, hentry, by simpa using path⟩

theorem horizontalAt_sound
    {parent : Index} {targetX targetY : Nat}
    (checked : horizontalAt parent (nodes parent) targetX targetY = true)
    (interior : Signals.horizontalInterior?
      (componentAt (fineGrid parent) targetX targetY)
      (quadrantAt targetX targetY) ≠ none) :
    LocalCycleRouteWithParity parent
      (horizontalPort (fineGrid parent) targetX targetY)
      (createdParity targetY) := by
  have required : (Signals.horizontalInterior?
      (componentAt (fineGrid parent) targetX targetY)
      (quadrantAt targetX targetY)).isSome = true :=
    Option.isSome_iff_ne_none.mpr interior
  simp only [horizontalAt, required, Bool.not_true, Bool.false_or] at checked
  exact reachesParityIn_bounded_sound checked

theorem verticalAt_sound
    {parent : Index} {targetX targetY : Nat}
    (checked : verticalAt parent (nodes parent) targetX targetY = true)
    (interior : Signals.verticalInterior?
      (componentAt (fineGrid parent) targetX targetY)
      (quadrantAt targetX targetY) ≠ none) :
    LocalCycleRouteWithParity parent
      (verticalPort (fineGrid parent) targetX targetY)
      (createdParity targetX) := by
  have required : (Signals.verticalInterior?
      (componentAt (fineGrid parent) targetX targetY)
      (quadrantAt targetX targetY)).isSome = true :=
    Option.isSome_iff_ne_none.mpr interior
  simp only [verticalAt, required, Bool.not_true, Bool.false_or] at checked
  exact reachesParityIn_bounded_sound checked

theorem horizontalAt_of_checkParent
    {parent : Index} {targetX targetY : Nat}
    (checked : checkParent parent = true)
    (targetXLt : targetX < 8)
    (targetYCreated : targetY ∈ createdCoordinates) :
    horizontalAt parent (nodes parent) targetX targetY = true := by
  simp only [checkParent, Bool.and_eq_true, List.all_eq_true,
    List.mem_range] at checked
  exact checked.1 targetX targetXLt targetY targetYCreated

theorem verticalAt_of_checkParent
    {parent : Index} {targetX targetY : Nat}
    (checked : checkParent parent = true)
    (targetXCreated : targetX ∈ createdCoordinates)
    (targetYLt : targetY < 8) :
    verticalAt parent (nodes parent) targetX targetY = true := by
  simp only [checkParent, Bool.and_eq_true, List.all_eq_true,
    List.mem_range] at checked
  exact checked.2 targetX targetXCreated targetY targetYLt

end PairCoverSeamCreatedRouteParityAudit
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
