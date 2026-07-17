/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.RedShadeGraphRefinementAudit
import LeanWang.Robinson.Closed104.RedShadeGraphSearchSoundness
import LeanWang.Robinson.Closed104.RedShadeGraphTranslation

/-!
Proof-facing two-substitution red-path refinement lemmas.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace RedShadeGraphRefinement

open RedCycles RedShadeGraph RedShadeGraphSearch RedShadeGraphSearchSoundness
  RedShadeGraphTranslation RefinementTranslation Signals.FreeCellLocal

set_option maxRecDepth 20000

set_option maxHeartbeats 1000000 in
-- Projecting one parent from the native all-parent connector table.
theorem completeFor_eq_true (parent : Index) : completeFor parent = true := by
  have hall : ∀ candidate ∈ List.finRange 104,
      completeFor candidate = true := by
    simpa [complete, List.all_eq_true] using complete_eq_true
  exact hall parent (List.mem_finRange parent)

set_option maxHeartbeats 1000000 in
-- Projecting one parent from the native bounded-connector table.
theorem boundedCompleteFor_eq_true (parent : Index) :
    boundedCompleteFor parent = true := by
  have hall : ∀ candidate ∈ List.finRange 104,
      boundedCompleteFor candidate = true := by
    simpa [boundedComplete, List.all_eq_true] using boundedComplete_eq_true
  exact hall parent (List.mem_finRange parent)

set_option linter.style.nativeDecide false in
/-- Two substitutions retain the old quarter component at local coordinates. -/
theorem componentAt_fineGrid_southwest (parent : Index)
    {x y : Nat} (hx : x < 2) (hy : y < 2) :
    componentAt (fineGrid parent) x y = componentAt (coarseGrid parent) x y := by
  have hxCases : x = 0 ∨ x = 1 := by omega
  have hyCases : y = 0 ∨ y = 1 := by omega
  rcases hxCases with rfl | rfl <;> rcases hyCases with rfl | rfl <;>
    revert parent <;> native_decide

theorem connectorMoves?_eq_some_iff
    (parent : Index) (side : ExitSide) (offset : Nat)
    (moves : List CertificateMove) :
    connectorMoves? parent side offset = some moves ↔
      connectorSearch parent side offset =
        some (externalPort side offset, false, moves) := by
  unfold connectorMoves?
  cases hsearch : connectorSearch parent side offset with
  | none => simp
  | some result =>
      rcases result with ⟨finish, parity, foundMoves⟩
      cases parity
      · by_cases hfinish : finish = externalPort side offset
        · subst finish
          simp
        · simp [hfinish]
      · simp

theorem connectorMoves_exists (parent : Index) (side : ExitSide)
    {offset : Nat} (hoffset : offset < 2)
    (hpresent : portPresent (coarseGrid parent)
      (internalPort side offset) = true) :
    ∃ moves, connectorSearch parent side offset =
      some (externalPort side offset, false, moves) := by
  have hcomplete := completeFor_eq_true parent
  simp only [completeFor, List.all_eq_true] at hcomplete
  have hside : side ∈ exitSides := by cases side <;> simp [exitSides]
  have hoffsetMem : offset ∈ List.range 2 := by simpa using hoffset
  have hcase := hcomplete side hside offset hoffsetMem
  rw [hpresent] at hcase
  simp only [if_true] at hcase
  cases hconnector : connectorMoves? parent side offset with
  | none => simp [hconnector] at hcase
  | some moves =>
      exact ⟨moves,
        (connectorMoves?_eq_some_iff parent side offset moves).1 hconnector⟩

/-- A live old east/north port reaches the same external macro port evenly. -/
theorem connectorPath (parent : Index) (side : ExitSide)
    {offset : Nat} (hoffset : offset < 2)
    (hpresent : portPresent (coarseGrid parent)
      (internalPort side offset) = true) :
    Path (fineGrid parent) (internalPort side offset)
      (externalPort side offset) false := by
  rcases connectorMoves_exists parent side hoffset hpresent with
    ⟨moves, hsearch⟩
  exact search_sound hsearch

/-- The same connector with every intermediate port retained inside its macrocell. -/
theorem boundedConnectorPath (parent : Index) (side : ExitSide)
    {offset : Nat} (hoffset : offset < 2)
    (hpresent : portPresent (coarseGrid parent)
      (internalPort side offset) = true) :
    BoundedPath (fineGrid parent) 8 8 (internalPort side offset)
      (externalPort side offset) false := by
  have hcomplete := boundedCompleteFor_eq_true parent
  simp only [boundedCompleteFor, List.all_eq_true] at hcomplete
  have hside : side ∈ exitSides := by cases side <;> simp [exitSides]
  have hoffsetMem : offset ∈ List.range 2 := by simpa using hoffset
  have hcase := hcomplete side hside offset hoffsetMem
  rw [hpresent] at hcase
  simp only [if_true] at hcase
  cases hnode : connectorNode? parent side offset with
  | none => simp [hnode] at hcase
  | some node =>
      have hmem : node ∈ connectorNodes parent side offset := by
        unfold connectorNode? at hnode
        exact List.mem_of_find?_eq_some hnode
      have haccept := List.find?_some hnode
      simp only [Bool.and_eq_true, decide_eq_true_eq] at haccept
      have hsound := exploreFast_bounded_sound
        (indexGrid := fineGrid parent) (width := 8) (height := 8)
        (fuel := 1000) (starts := [internalPort side offset])
        (by
          intro port hport
          simp only [List.mem_singleton] at hport
          subst port
          cases side <;> simp [PortInBounds, internalPort] <;> omega)
        hmem
      have horigin : node.origin = internalPort side offset := by
        simpa using hsound.1
      have hparity : node.parity = false := by
        cases hparity : node.parity with
        | false => rfl
        | true => simp [hparity] at haccept
      simpa [horigin, haccept.1, hparity] using hsound.2

def macroOrigin (coordinate : Nat) : Nat :=
  8 * (coordinate / 2)

def localCoordinate (coordinate : Nat) : Nat :=
  coordinate % 2

def sparseCoordinate (coordinate : Nat) : Nat :=
  macroOrigin coordinate + localCoordinate coordinate

theorem localCoordinate_lt_two (coordinate : Nat) :
    localCoordinate coordinate < 2 := by
  exact Nat.mod_lt coordinate (by decide)

/-- Exact sparse copy of every coarse quarter after two substitutions. -/
theorem componentAt_iterateRefine_two_sparse
    (grid : Nat → Nat → Index) (x y : Nat) :
    componentAt (iterateRefine 2 grid) (sparseCoordinate x) (sparseCoordinate y) =
      componentAt grid x y := by
  let blockX := x / 2
  let blockY := y / 2
  let localX := localCoordinate x
  let localY := localCoordinate y
  have hx : localX < 2 := localCoordinate_lt_two x
  have hy : localY < 2 := localCoordinate_lt_two y
  calc
    componentAt (iterateRefine 2 grid) (sparseCoordinate x) (sparseCoordinate y) =
        componentAt (iterateRefine 2 (shiftGrid grid blockX blockY))
          localX localY := by
      rw [componentAt_iterateRefine_shift]
      simp [sparseCoordinate, macroOrigin, blockX, blockY, localX, localY]
    _ = componentAt (fineGrid (grid blockX blockY)) localX localY := by
      rw [componentAt_shift_eq_constant 2 grid blockX blockY localX localY]
      · rfl
      · omega
      · omega
    _ = componentAt (coarseGrid (grid blockX blockY)) localX localY :=
      componentAt_fineGrid_southwest _ hx hy
    _ = componentAt grid x y := by
      simp [componentAt, coarseGrid, blockX, blockY]

/-- A local connector transplanted into any two-level refined macrocell. -/
theorem connectorPath_translate (grid : Nat → Nat → Index)
    (blockX blockY : Nat) (side : ExitSide) {offset : Nat}
    (hoffset : offset < 2)
    (hpresent : portPresent (coarseGrid (grid blockX blockY))
      (internalPort side offset) = true) :
    Path (iterateRefine 2 grid)
      (translatePort (internalPort side offset) (8 * blockX) (8 * blockY))
      (translatePort (externalPort side offset) (8 * blockX) (8 * blockY))
      false := by
  have localPath := boundedConnectorPath (grid blockX blockY) side hoffset hpresent
  have componentsEq : ∀ x y, x < 8 → y < 8 →
      componentAt (fineGrid (grid blockX blockY)) x y =
        componentAt (iterateRefine 2 (shiftGrid grid blockX blockY)) x y := by
    intro x y hx hy
    exact (componentAt_shift_eq_constant 2 grid blockX blockY x y hx hy).symm
  have shifted :=
    (RedShadeGraphTranslation.BoundedPath.congr_of_component_eq
      componentsEq localPath).path
  simpa using path_translate (depth := 2) (grid := grid)
    (blockX := blockX) (blockY := blockY) shifted

def sparsePort (port : Port) : Port :=
  ⟨sparseCoordinate port.x, sparseCoordinate port.y, port.side⟩

def exitCoordinate (coordinate : Nat) : Nat :=
  if localCoordinate coordinate = 1 then macroOrigin coordinate + 7
  else sparseCoordinate coordinate

def refinedPort (port : Port) : Port :=
  match port.side with
  | .east => ⟨exitCoordinate port.x, sparseCoordinate port.y, .east⟩
  | .north => ⟨sparseCoordinate port.x, exitCoordinate port.y, .north⟩
  | .west => sparsePort port
  | .south => sparsePort port

theorem exitCoordinate_succ (coordinate : Nat) :
    exitCoordinate coordinate + 1 = sparseCoordinate (coordinate + 1) := by
  have hmod := Nat.mod_lt coordinate (by decide : 0 < 2)
  have hnextMod := Nat.mod_lt (coordinate + 1) (by decide : 0 < 2)
  have hdecompose := Nat.mod_add_div coordinate 2
  have hnextDecompose := Nat.mod_add_div (coordinate + 1) 2
  by_cases heven : coordinate % 2 = 0
  · have hnextOdd : (coordinate + 1) % 2 = 1 := by omega
    have hnextDiv : (coordinate + 1) / 2 = coordinate / 2 := by omega
    simp [exitCoordinate, sparseCoordinate, macroOrigin, localCoordinate,
      heven, hnextOdd, hnextDiv]
  · have hodd : coordinate % 2 = 1 := by omega
    have hnextEven : (coordinate + 1) % 2 = 0 := by omega
    have hnextDiv : (coordinate + 1) / 2 = coordinate / 2 + 1 := by omega
    simp [exitCoordinate, sparseCoordinate, macroOrigin, localCoordinate,
      hodd, hnextEven, hnextDiv]
    omega

theorem sparseCoordinate_mod_two (coordinate : Nat) :
    sparseCoordinate coordinate % 2 = coordinate % 2 := by
  simp [sparseCoordinate, macroOrigin, localCoordinate, Nat.add_mod,
    Nat.mul_mod]

theorem quadrantAt_sparseCoordinate (x y : Nat) :
    quadrantAt (sparseCoordinate x) (sparseCoordinate y) = quadrantAt x y := by
  simp [quadrantAt, sparseCoordinate_mod_two]

theorem portPresent_coarseGrid_local (grid : Nat → Nat → Index)
    (port : Port) :
    portPresent (coarseGrid (grid (port.x / 2) (port.y / 2)))
        ⟨localCoordinate port.x, localCoordinate port.y, port.side⟩ =
      portPresent grid port := by
  unfold portPresent
  change (match port.side with
    | .west => RedShades.hasWest
        (componentAt (coarseGrid (grid (port.x / 2) (port.y / 2)))
          (localCoordinate port.x) (localCoordinate port.y))
        (quadrantAt (localCoordinate port.x) (localCoordinate port.y))
    | .east => RedShades.hasEast
        (componentAt (coarseGrid (grid (port.x / 2) (port.y / 2)))
          (localCoordinate port.x) (localCoordinate port.y))
        (quadrantAt (localCoordinate port.x) (localCoordinate port.y))
    | .south => RedShades.hasSouth
        (componentAt (coarseGrid (grid (port.x / 2) (port.y / 2)))
          (localCoordinate port.x) (localCoordinate port.y))
        (quadrantAt (localCoordinate port.x) (localCoordinate port.y))
    | .north => RedShades.hasNorth
        (componentAt (coarseGrid (grid (port.x / 2) (port.y / 2)))
          (localCoordinate port.x) (localCoordinate port.y))
        (quadrantAt (localCoordinate port.x) (localCoordinate port.y))) = _
  have hcoarse : componentAt
      (coarseGrid (grid (port.x / 2) (port.y / 2)))
        (localCoordinate port.x) (localCoordinate port.y) =
      componentAt grid port.x port.y := by
    simp [componentAt, coarseGrid]
  rw [hcoarse]
  have hquadrantLocal :
      quadrantAt (localCoordinate port.x) (localCoordinate port.y) =
        quadrantAt port.x port.y := by
    simp [quadrantAt, localCoordinate]
  rw [hquadrantLocal]
  cases port.side <;> rfl

theorem path_symm {grid : Nat → Nat → Index} {first second : Port}
    {parity : Bool} (path : Path grid first second parity) :
    Path grid second first parity := by
  induction path with
  | refl port => exact Path.refl port
  | ofLink link => exact Path.ofLink (Link.symm link)
  | trans firstPath secondPath firstIH secondIH =>
      simpa [Bool.xor_comm] using Path.trans secondIH firstIH

set_option maxHeartbeats 1000000 in
-- Normalizing translated macro origins through the side-sensitive port map.
/-- A live coarse port reaches its side-sensitive refined image evenly. -/
theorem livePortPath (grid : Nat → Nat → Index) (port : Port)
    (hlive : portPresent grid port = true) :
    Path (iterateRefine 2 grid) (sparsePort port) (refinedPort port) false := by
  cases hside : port.side with
  | west =>
      simpa [refinedPort, hside] using
        (Path.refl (indexGrid := iterateRefine 2 grid) (sparsePort port))
  | south =>
      simpa [refinedPort, hside] using
        (Path.refl (indexGrid := iterateRefine 2 grid) (sparsePort port))
  | east =>
      by_cases hexit : localCoordinate port.x = 1
      · have hpresent : portPresent
            (coarseGrid (grid (port.x / 2) (port.y / 2)))
            (internalPort .east (localCoordinate port.y)) = true := by
          simpa [internalPort, hside, hexit] using
            (portPresent_coarseGrid_local grid port).trans hlive
        have hexit' : port.x % 2 = 1 := by
          simpa [localCoordinate] using hexit
        have connector := connectorPath_translate grid (port.x / 2) (port.y / 2)
          .east (localCoordinate_lt_two port.y) hpresent
        simpa [sparsePort, refinedPort, exitCoordinate, hside, hexit',
          internalPort, externalPort,
          translatePort, sparseCoordinate, macroOrigin, localCoordinate]
          using connector
      · have hexit' : port.x % 2 ≠ 1 := by
          simpa [localCoordinate] using hexit
        have hrefined : refinedPort port = sparsePort port := by
          rcases port with ⟨portX, portY, portSide⟩
          simp_all [refinedPort, exitCoordinate, sparsePort]
        rw [hrefined]
        exact Path.refl _
  | north =>
      by_cases hexit : localCoordinate port.y = 1
      · have hpresent : portPresent
            (coarseGrid (grid (port.x / 2) (port.y / 2)))
            (internalPort .north (localCoordinate port.x)) = true := by
          simpa [internalPort, hside, hexit] using
            (portPresent_coarseGrid_local grid port).trans hlive
        have hexit' : port.y % 2 = 1 := by
          simpa [localCoordinate] using hexit
        have connector := connectorPath_translate grid (port.x / 2) (port.y / 2)
          .north (localCoordinate_lt_two port.x) hpresent
        simpa [sparsePort, refinedPort, exitCoordinate, hside, hexit',
          internalPort, externalPort,
          translatePort, sparseCoordinate, macroOrigin, localCoordinate]
          using connector
      · have hexit' : port.y % 2 ≠ 1 := by
          simpa [localCoordinate] using hexit
        have hrefined : refinedPort port = sparsePort port := by
          rcases port with ⟨portX, portY, portSide⟩
          simp_all [refinedPort, exitCoordinate, sparsePort]
        rw [hrefined]
        exact Path.refl _

end RedShadeGraphRefinement
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
