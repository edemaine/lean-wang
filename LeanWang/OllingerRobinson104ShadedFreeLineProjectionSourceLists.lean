/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104ShadedFreeLineProjectionCandidates

/-!
# Executable whole-pattern projection source lists
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace ShadedFreeLineProjectionSourceLists

open OrientedRedCycles RedCycles RedShadeCycles RedShadeGraph
  RedShadeGraphBoards RedShadeGraphRefinement ShadedFreeLineGraph
  ShadedFreeLinePatternRefinement ShadedFreeLineProjectionCandidates
  Signals.FreeCellLocal

set_option maxRecDepth 20000

def strictCoordinates (lower upper : Nat) : List Nat :=
  (List.range (upper - lower - 1)).map fun delta => lower + 1 + delta

def cyclePorts (west east south north : Nat) : List Port :=
  let qwest := quarterWest west
  let qeast := quarterEast east
  let qsouth := quarterSouth south
  let qnorth := quarterNorth north
  ((strictCoordinates qwest qeast).flatMap fun x =>
    [⟨x, qsouth, .west⟩, ⟨x, qsouth, .east⟩,
      ⟨x, qnorth, .west⟩, ⟨x, qnorth, .east⟩]) ++
  ((strictCoordinates qsouth qnorth).flatMap fun y =>
    [⟨qwest, y, .south⟩, ⟨qwest, y, .north⟩,
      ⟨qeast, y, .south⟩, ⟨qeast, y, .north⟩])

def rowPorts (grid : Nat → Nat → Index)
    (west east row : Nat) : List Port :=
  (strictCoordinates (quarterWest west) (quarterEast east)).flatMap fun x =>
    if (Signals.verticalInterior?
        (componentAt grid x row) (quadrantAt x row)).isSome then
      ([⟨x, row, .south⟩, ⟨x, row, .north⟩].filter fun port =>
        portPresent grid port)
    else []

def columnPorts (grid : Nat → Nat → Index)
    (south north column : Nat) : List Port :=
  (strictCoordinates (quarterSouth south) (quarterNorth north)).flatMap fun y =>
    if (Signals.horizontalInterior?
        (componentAt grid column y) (quadrantAt column y)).isSome then
      ([⟨column, y, .west⟩, ⟨column, y, .east⟩].filter fun port =>
        portPresent grid port)
    else []

def patternCandidates (grid : Nat → Nat → Index)
    (west east south north : Nat) (offsets : List Nat)
    (coordinate : Nat → Nat) : List Candidate :=
  ((cyclePorts west east south north).map fun port => ⟨port, false⟩) ++
  offsets.flatMap (fun offset =>
    (rowPorts grid west east (coordinate offset)).map fun port => ⟨port, true⟩) ++
  offsets.flatMap (fun offset =>
    (columnPorts grid south north (coordinate offset)).map fun port => ⟨port, true⟩)

theorem mem_strictCoordinates {lower upper coordinate : Nat}
    (hboard : lower < upper) (hcoordinate : coordinate ∈ strictCoordinates lower upper) :
    lower < coordinate ∧ coordinate < upper := by
  rw [strictCoordinates, List.mem_map] at hcoordinate
  rcases hcoordinate with ⟨delta, hdelta, rfl⟩
  simp only [List.mem_range] at hdelta
  omega

theorem onCycle_of_mem_cyclePorts
    {west east south north : Nat} {port : Port}
    (hwestEast : west < east) (hsouthNorth : south < north)
    (hport : port ∈ cyclePorts west east south north) :
    OnCycle west east south north port := by
  have hqwestEast : quarterWest west < quarterEast east := by
    simp [quarterWest, quarterEast]
    omega
  have hqsouthNorth : quarterSouth south < quarterNorth north := by
    simp [quarterSouth, quarterNorth]
    omega
  rw [cyclePorts, List.mem_append] at hport
  rcases hport with hport | hport
  · rw [List.mem_flatMap] at hport
    rcases hport with ⟨x, hx, hport⟩
    have hxbounds := mem_strictCoordinates hqwestEast hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hport
    rcases hport with rfl | rfl | rfl | rfl
    · exact OnCycle.southWest _ hxbounds.1 hxbounds.2
    · exact OnCycle.southEast _ hxbounds.1 hxbounds.2
    · exact OnCycle.northWest _ hxbounds.1 hxbounds.2
    · exact OnCycle.northEast _ hxbounds.1 hxbounds.2
  · rw [List.mem_flatMap] at hport
    rcases hport with ⟨y, hy, hport⟩
    have hybounds := mem_strictCoordinates hqsouthNorth hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hport
    rcases hport with rfl | rfl | rfl | rfl
    · exact OnCycle.westSouth _ hybounds.1 hybounds.2
    · exact OnCycle.westNorth _ hybounds.1 hybounds.2
    · exact OnCycle.eastSouth _ hybounds.1 hybounds.2
    · exact OnCycle.eastNorth _ hybounds.1 hybounds.2

set_option maxHeartbeats 1000000 in
-- Normalizing the filtered dependent port list and its local component test.
theorem valid_rowPort
    {grid : Nat → Nat → Index} {west east row : Nat} {port : Port}
    (hwestEast : west < east) (hport : port ∈ rowPorts grid west east row) :
    ∃ x, quarterWest west < x ∧ x < quarterEast east ∧
      Signals.verticalInterior?
        (componentAt grid x row) (quadrantAt x row) ≠ none ∧
      (port = ⟨x, row, .south⟩ ∨ port = ⟨x, row, .north⟩) ∧
      portPresent grid port = true := by
  rw [rowPorts, List.mem_flatMap] at hport
  rcases hport with ⟨x, hx, hport⟩
  have hqwestEast : quarterWest west < quarterEast east := by
    simp [quarterWest, quarterEast]
    omega
  have hxbounds := mem_strictCoordinates hqwestEast hx
  split at hport
  · rename_i hinterior
    simp only [List.mem_filter, List.mem_cons, List.not_mem_nil, or_false] at hport
    have hinterior' : Signals.verticalInterior?
        (componentAt grid x row) (quadrantAt x row) ≠ none := by
      intro hnone
      simp [hnone] at hinterior
    exact ⟨x, hxbounds.1, hxbounds.2, hinterior', hport.1, hport.2⟩
  · contradiction

set_option maxHeartbeats 1000000 in
-- Normalizing the filtered dependent port list and its local component test.
theorem valid_columnPort
    {grid : Nat → Nat → Index} {south north column : Nat} {port : Port}
    (hsouthNorth : south < north)
    (hport : port ∈ columnPorts grid south north column) :
    ∃ y, quarterSouth south < y ∧ y < quarterNorth north ∧
      Signals.horizontalInterior?
        (componentAt grid column y) (quadrantAt column y) ≠ none ∧
      (port = ⟨column, y, .west⟩ ∨ port = ⟨column, y, .east⟩) ∧
      portPresent grid port = true := by
  rw [columnPorts, List.mem_flatMap] at hport
  rcases hport with ⟨y, hy, hport⟩
  have hqsouthNorth : quarterSouth south < quarterNorth north := by
    simp [quarterSouth, quarterNorth]
    omega
  have hybounds := mem_strictCoordinates hqsouthNorth hy
  split at hport
  · rename_i hinterior
    simp only [List.mem_filter, List.mem_cons, List.not_mem_nil, or_false] at hport
    have hinterior' : Signals.horizontalInterior?
        (componentAt grid column y) (quadrantAt column y) ≠ none := by
      intro hnone
      simp [hnone] at hinterior
    exact ⟨y, hybounds.1, hybounds.2, hinterior', hport.1, hport.2⟩
  · contradiction

def cycleFamily
    {grid : Nat → Nat → Index} {west east south north : Nat}
    (cycle : CycleOn grid west east south north) :
    Family grid west east south north :=
  Family.cycle cycle (cyclePorts west east south north) fun _ hport =>
    onCycle_of_mem_cyclePorts cycle.west_lt_east cycle.south_lt_north hport

def rowFamily
    {grid : Nat → Nat → Index} {west east south north row : Nat}
    (cycle : CycleOn grid west east south north)
    (certificate : LiveRowCertificate grid west east south north row) :
    Family grid west east south north :=
  Family.row certificate (rowPorts grid west east row) fun _ hport =>
    valid_rowPort cycle.west_lt_east hport

def columnFamily
    {grid : Nat → Nat → Index} {west east south north column : Nat}
    (cycle : CycleOn grid west east south north)
    (certificate : LiveColumnCertificate grid west east south north column) :
    Family grid west east south north :=
  Family.column certificate (columnPorts grid south north column) fun _ hport =>
    valid_columnPort cycle.south_lt_north hport

/-- The enclosing cycle and every retained row and column as one source family. -/
def patternFamily
    {grid : Nat → Nat → Index} {west east south north : Nat}
    (cycle : CycleOn grid west east south north)
    (offsets : List Nat) (coordinate : Nat → Nat)
    (rowCertificate : ∀ offset ∈ offsets,
      LiveRowCertificate grid west east south north (coordinate offset))
    (columnCertificate : ∀ offset ∈ offsets,
      LiveColumnCertificate grid west east south north (coordinate offset)) :
    Family grid west east south north where
  candidates := patternCandidates grid west east south north offsets coordinate
  backed := by
    intro candidate hcandidate
    simp only [patternCandidates, List.mem_append] at hcandidate
    rcases hcandidate with (hcycle | hrow) | hcolumn
    · rcases List.mem_map.1 hcycle with ⟨port, hport, rfl⟩
      exact backedBy_cycle cycle
        (onCycle_of_mem_cyclePorts cycle.west_lt_east cycle.south_lt_north hport)
    · rcases List.mem_flatMap.1 hrow with ⟨offset, hoffset, hport⟩
      rcases List.mem_map.1 hport with ⟨port, hportSource, heq⟩
      cases heq
      rcases valid_rowPort cycle.west_lt_east hportSource with
        ⟨x, hwest, heast, interior, endpoint, live⟩
      exact backedBy_row (rowCertificate offset hoffset)
        hwest heast interior endpoint live
    · rcases List.mem_flatMap.1 hcolumn with ⟨offset, hoffset, hport⟩
      rcases List.mem_map.1 hport with ⟨port, hportSource, heq⟩
      cases heq
      rcases valid_columnPort cycle.south_lt_north hportSource with
        ⟨y, hsouth, hnorth, interior, endpoint, live⟩
      exact backedBy_column (columnCertificate offset hoffset)
        hsouth hnorth interior endpoint live

theorem patternFamily_candidates
    {grid : Nat → Nat → Index} {west east south north : Nat}
    (cycle : CycleOn grid west east south north)
    (offsets : List Nat) (coordinate : Nat → Nat)
    (rowCertificate : ∀ offset ∈ offsets,
      LiveRowCertificate grid west east south north (coordinate offset))
    (columnCertificate : ∀ offset ∈ offsets,
      LiveColumnCertificate grid west east south north (coordinate offset)) :
    (patternFamily cycle offsets coordinate
      rowCertificate columnCertificate).candidates =
      patternCandidates grid west east south north offsets coordinate := by
  rfl

end ShadedFreeLineProjectionSourceLists
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
