/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104SparseFreeLineEvenExtraCreatedPositions
import LeanWang.OllingerRobinson104SparseFreeLineEvenExtraCreatedWindowBacking
import LeanWang.OllingerRobinson104SparseFreeLineEvenExtraWindowCoordinates

/-!
# Recursive even-extra projection

Inherited segments use the preceding live sparse certificate.  The only
remaining residues, `4` and `5`, use the finite created-window routes backed
by the enclosing canonical cycle.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace SparseFreeLineEvenExtraCreatedStep

open RedCycles RedShadeCycles RedShadeGraph RedShadeGraphRefinement
  RedShadeGraphTranslation Signals.FreeCellLocal Signals.FreeCellEmbedding
  BorderCoverageOffsets
  ShadedFreeLinePatternRefinement ShadedFreeLineRecurrence
  SparseFreeLineOffsets SparseFreeLineLocalProjection SparseFreeLineLocalRecurrence
  SparseFreeLineLocalStates SparseFreeLineLocalTransport
  SparseFreeLineEvenExtraCreatedPositions
  SparseFreeLineEvenExtraCreatedWindowAudit
  SparseFreeLineEvenExtraCreatedWindowClosure
  SparseFreeLineEvenExtraCreatedWindowBacking
  SparseFreeLineEvenExtraWindowCoordinates

set_option maxRecDepth 20000

/-- A positive local ancestor check reconstructs the corresponding old
vertical segment. -/
theorem vertical_inherited_of_checked
    {grid : Nat → Nat → Index} {oldRow x : Nat}
    (heven : oldRow % 2 = 0)
    (interior : Signals.verticalInterior?
      (componentAt (iterateRefine 2 grid) x (sparseCoordinate oldRow))
      (quadrantAt x (sparseCoordinate oldRow)) ≠ none)
    (checked : verticalAncestorAt 0 0
      (grid (x / 8) (oldRow / 2)) (x % 8) = true) :
    ∃ oldX, sparseCoordinate oldX = x ∧
      Signals.verticalInterior?
        (componentAt grid oldX oldRow) (quadrantAt oldX oldRow) ≠ none := by
  let blockX := x / 8
  let localX := x % 8
  let blockY := oldRow / 2
  let parent := grid blockX blockY
  have hlocalX : localX < 8 := Nat.mod_lt _ (by decide)
  have hx : 8 * blockX + localX = x := by
    have := Nat.mod_add_div x 8
    dsimp [blockX, localX]
    omega
  have holdRow : 2 * blockY = oldRow := by
    have := Nat.mod_add_div oldRow 2
    dsimp [blockY]
    omega
  have hfineRow : 8 * blockY = sparseCoordinate oldRow := by
    simp [sparseCoordinate, macroOrigin, localCoordinate, blockY, heven]
  have localInterior : Signals.verticalInterior?
      (componentAt (fineGrid parent) localX 0)
      (quadrantAt localX 0) ≠ none := by
    have transported := interior
    rw [← hx, ← hfineRow] at transported
    have hcomponent := componentAt_two_block grid 0 blockX blockY localX 0
      hlocalX (by decide)
    simp only [Nat.zero_add] at hcomponent
    change componentAt (iterateRefine 2 grid)
        (8 * blockX + localX) (8 * blockY + 0) =
      componentAt (iterateRefine 2 (fun _ _ => grid blockX blockY))
        localX 0 at hcomponent
    have hquadrant : quadrantAt (8 * blockX + localX) (8 * blockY + 0) =
        quadrantAt localX 0 := by
      simpa using quadrantAt_block blockX blockY localX 0
    rw [show 8 * blockY = 8 * blockY + 0 by omega,
      hcomponent, hquadrant] at transported
    change Signals.verticalInterior?
      (componentAt (iterateRefine 2 (fun _ _ => parent)) localX 0)
      (quadrantAt localX 0) ≠ none
    simpa [parent] using transported
  have checked' : verticalAncestorAt 0 0 parent localX = true := by
    simpa [parent, blockX, blockY, localX] using checked
  rcases verticalAncestorAt_sound checked' localInterior with
    ⟨sourceX, hsourceX, sourceCoordinate, sourceInterior⟩
  refine ⟨2 * blockX + sourceX, ?_, ?_⟩
  · rw [sparseCoordinate_two_block blockX sourceX hsourceX,
      sourceCoordinate, hx]
  · rw [← holdRow]
    have hcomponent := componentAt_old_block grid 0 blockX blockY sourceX 0
      hsourceX (by decide)
    simp only [iterateRefine, Nat.add_zero] at hcomponent
    have hquadrant : quadrantAt (2 * blockX + sourceX) (2 * blockY) =
        quadrantAt sourceX 0 := by
      simpa using quadrantAt_old_block blockX blockY sourceX 0
        hsourceX (by decide)
    rw [hcomponent, hquadrant]
    simpa [holdRow, parent] using sourceInterior

/-- A positive local ancestor check reconstructs the corresponding old
horizontal segment. -/
theorem horizontal_inherited_of_checked
    {grid : Nat → Nat → Index} {oldColumn y : Nat}
    (heven : oldColumn % 2 = 0)
    (interior : Signals.horizontalInterior?
      (componentAt (iterateRefine 2 grid) (sparseCoordinate oldColumn) y)
      (quadrantAt (sparseCoordinate oldColumn) y) ≠ none)
    (checked : horizontalAncestorAt 0 0
      (grid (oldColumn / 2) (y / 8)) (y % 8) = true) :
    ∃ oldY, sparseCoordinate oldY = y ∧
      Signals.horizontalInterior?
        (componentAt grid oldColumn oldY) (quadrantAt oldColumn oldY) ≠ none := by
  let blockX := oldColumn / 2
  let blockY := y / 8
  let localY := y % 8
  let parent := grid blockX blockY
  have hlocalY : localY < 8 := Nat.mod_lt _ (by decide)
  have hy : 8 * blockY + localY = y := by
    have := Nat.mod_add_div y 8
    dsimp [blockY, localY]
    omega
  have holdColumn : 2 * blockX = oldColumn := by
    have := Nat.mod_add_div oldColumn 2
    dsimp [blockX]
    omega
  have hfineColumn : 8 * blockX = sparseCoordinate oldColumn := by
    simp [sparseCoordinate, macroOrigin, localCoordinate, blockX, heven]
  have localInterior : Signals.horizontalInterior?
      (componentAt (fineGrid parent) 0 localY)
      (quadrantAt 0 localY) ≠ none := by
    have transported := interior
    rw [← hfineColumn, ← hy] at transported
    have hcomponent := componentAt_two_block grid 0 blockX blockY 0 localY
      (by decide) hlocalY
    simp only [Nat.zero_add] at hcomponent
    change componentAt (iterateRefine 2 grid)
        (8 * blockX + 0) (8 * blockY + localY) =
      componentAt (iterateRefine 2 (fun _ _ => grid blockX blockY))
        0 localY at hcomponent
    have hquadrant : quadrantAt (8 * blockX + 0) (8 * blockY + localY) =
        quadrantAt 0 localY := by
      simpa using quadrantAt_block blockX blockY 0 localY
    rw [show 8 * blockX = 8 * blockX + 0 by omega,
      hcomponent, hquadrant] at transported
    change Signals.horizontalInterior?
      (componentAt (iterateRefine 2 (fun _ _ => parent)) 0 localY)
      (quadrantAt 0 localY) ≠ none
    simpa [parent] using transported
  have checked' : horizontalAncestorAt 0 0 parent localY = true := by
    simpa [parent, blockX, blockY, localY] using checked
  rcases horizontalAncestorAt_sound checked' localInterior with
    ⟨sourceY, hsourceY, sourceCoordinate, sourceInterior⟩
  refine ⟨2 * blockY + sourceY, ?_, ?_⟩
  · rw [sparseCoordinate_two_block blockY sourceY hsourceY,
      sourceCoordinate, hy]
  · rw [← holdColumn]
    have hcomponent := componentAt_old_block grid 0 blockX blockY 0 sourceY
      (by decide) hsourceY
    simp only [iterateRefine, Nat.add_zero] at hcomponent
    have hquadrant : quadrantAt (2 * blockX) (2 * blockY + sourceY) =
        quadrantAt 0 sourceY := by
      simpa using quadrantAt_old_block blockX blockY 0 sourceY
        (by decide) hsourceY
    rw [hcomponent, hquadrant]
    simpa [holdColumn, parent] using sourceInterior

theorem exceptionalCoordinate_centerBlock (depth : Nat) :
    exceptionalCoordinate depth = 8 * centerBlock depth := by
  rw [exceptionalCoordinate_eq, centerBlock, firstBlock, pow_succ]
  omega

theorem sourceRow_even (depth : Nat) :
    lineCoordinate .even (depth + 1) (extraChild (pivot depth)) % 2 = 0 := by
  rw [BorderCoverageOffsets.lineCoordinate_even]
  simp [extraChild, pivot, pow_succ]
  omega

set_option maxHeartbeats 5000000 in
-- The inherited/created split normalizes both global and local coordinates.
/-- The recursive exceptional row is covered by inherited or backed created
segments. -/
theorem verticalProjection
    (depth : Nat) (parent : Index)
    (previous : LiveRowCertificate (oldGrid depth parent)
      (west .even (depth + 1)) (east .even (depth + 1))
      (west .even (depth + 1)) (east .even (depth + 1))
      (lineCoordinate .even (depth + 1) (extraChild (pivot depth)))) :
    VerticalProjectionAt (oldGrid depth parent)
      (west .even (depth + 1)) (east .even (depth + 1))
      (west .even (depth + 1)) (east .even (depth + 1))
      (exceptionalCoordinate depth) := by
  intro x hwest heast interior
  let oldRow := lineCoordinate .even (depth + 1) (extraChild (pivot depth))
  have hcoordinate : exceptionalCoordinate depth = sparseCoordinate oldRow := by
    simpa [oldRow] using exceptionalCoordinate_as_sparseSource depth
  have heven : oldRow % 2 = 0 := by
    simpa [oldRow] using sourceRow_even depth
  have interior' : Signals.verticalInterior?
      (componentAt (iterateRefine 2 (oldGrid depth parent)) x
        (sparseCoordinate oldRow))
      (quadrantAt x (sparseCoordinate oldRow)) ≠ none := by
    rwa [← hcoordinate]
  let blockX := x / 8
  let localX := x % 8
  let delta := blockX - firstBlock depth
  have hlocalX : localX < 8 := Nat.mod_lt _ (by decide)
  have hx : 8 * blockX + localX = x := by
    have := Nat.mod_add_div x 8
    dsimp [blockX, localX]
    omega
  have hfirst : firstBlock depth ≤ blockX := by
    rw [firstBlock, pow_succ]
    simp [quarterWest, west, scale, Phase.factor, pow_succ] at hwest
    dsimp [blockX]
    omega
  have hblock : blockX = firstBlock depth + delta := by
    dsimp [delta]
    omega
  have hdelta : delta ≤ blockCount depth := by
    have hblockUpper : blockX < 3 * firstBlock depth := by
      rw [firstBlock, pow_succ]
      simp [quarterEast, east, scale, Phase.factor, pow_succ] at heast
      dsimp [blockX]
      omega
    rw [blockCount]
    dsimp [delta]
    omega
  let center := centerBlock depth
  have hcenterPositive : 0 < center := by
    dsimp [center]
    simp [centerBlock, firstBlock]
  have hblockPositive : 0 < blockX := by
    have hfirstPositive : 0 < firstBlock depth := by
      simp [firstBlock]
    omega
  have hrow : exceptionalCoordinate depth = 8 * center := by
    simpa [center] using exceptionalCoordinate_centerBlock depth
  let cell := oldGrid depth parent blockX center
  by_cases checked : verticalAncestorAt 0 0 cell localX = true
  · have checked' : verticalAncestorAt 0 0
        (oldGrid depth parent (x / 8) (oldRow / 2)) (x % 8) = true := by
      have hcenter : oldRow / 2 = center := by
        have hsparse := hcoordinate
        rw [hrow] at hsparse
        simp [sparseCoordinate, macroOrigin, localCoordinate, heven] at hsparse
        omega
      simpa [cell, blockX, localX, hcenter]
    rcases vertical_inherited_of_checked heven interior' checked' with
      ⟨oldX, oldCoordinate, oldInterior⟩
    have oldWest : quarterWest (west .even (depth + 1)) < oldX := by
      rw [← SparseFreeLineLocalProjection.sparseCoordinate_lt_iff]
      simpa [oldCoordinate, hcoordinate] using hwest
    have oldEast : oldX < quarterEast (east .even (depth + 1)) := by
      rw [← SparseFreeLineLocalProjection.sparseCoordinate_lt_iff]
      simpa [oldCoordinate, hcoordinate] using heast
    rcases previous oldX oldWest oldEast oldInterior with
      ⟨source, sourceOdd, endpoint | endpoint⟩
    · left
      refine ⟨ProjectsTo.ofOddSourcePath sourceOdd ?_ ?_⟩
      · simpa [endpoint, sparsePort, oldCoordinate, hcoordinate] using
          (Path.refl (indexGrid := iterateRefine 2 (oldGrid depth parent))
            (sparsePort source.port))
      · simpa [endpoint, sparsePort, oldCoordinate, hcoordinate,
          WeightedSource.refine] using source.refine.portLive
    · right
      refine ⟨ProjectsTo.ofOddSourcePath sourceOdd ?_ ?_⟩
      · simpa [endpoint, sparsePort, oldCoordinate, hcoordinate] using
          (Path.refl (indexGrid := iterateRefine 2 (oldGrid depth parent))
            (sparsePort source.port))
      · simpa [endpoint, sparsePort, oldCoordinate, hcoordinate,
          WeightedSource.refine] using source.refine.portLive
  · have hcreated : verticalAncestorAt 0 0 cell localX = false :=
      Bool.eq_false_of_not_eq_true checked
    have hlocalCases : localX = 4 ∨ localX = 5 :=
      (vertical_classification cell ⟨localX, hlocalX⟩).resolve_left checked
    have localInterior : Signals.verticalInterior?
        (componentAt (fineGrid cell) localX 0)
        (quadrantAt localX 0) ≠ none := by
      have transported := interior
      rw [← hx, hrow] at transported
      have hcomponent := componentAt_two_block (oldGrid depth parent) 0
        blockX center localX 0 hlocalX (by decide)
      simp only [Nat.zero_add] at hcomponent
      change componentAt (iterateRefine 2 (oldGrid depth parent))
          (8 * blockX + localX) (8 * center + 0) =
        componentAt (fineGrid cell) localX 0 at hcomponent
      have hquadrant : quadrantAt (8 * blockX + localX) (8 * center + 0) =
          quadrantAt localX 0 := by
        simpa using quadrantAt_block blockX center localX 0
      rw [show 8 * center = 8 * center + 0 by omega,
        hcomponent, hquadrant] at transported
      exact transported
    have hwindow := canonical_verticalWindowAt_mem depth parent delta hdelta
    rw [← hblock] at hwindow
    have hcenterEq :
        windowGrid (verticalWindowAt depth parent blockX) 1 1 = cell := by
      rw [windowGrid_verticalWindowAt depth parent blockX 1 1
        (by omega) (by omega)]
      dsimp [cell, center]
      congr 2
      omega
    have required : (Signals.verticalInterior?
        (componentAt
          (fineGrid (windowGrid (verticalWindowAt depth parent blockX) 1 1))
          localX 0) (quadrantAt localX 0)).isSome = true := by
      rw [hcenterEq]
      exact Option.isSome_iff_ne_none.mpr localInterior
    have created : verticalAncestorAt 0 0
        (windowGrid (verticalWindowAt depth parent blockX) 1 1) localX =
        false := by
      rw [hcenterEq]
      exact hcreated
    rcases vertical_actual_route hwindow hlocalCases required created with
      route | route
    · left
      have projected := verticalWindowRoute_projectsTo hblock hdelta route
      have htarget : translatePort ⟨8 + localX, 8, .south⟩
          (8 * (blockX - 1)) (8 * (centerBlock depth - 1)) =
          (⟨x, exceptionalCoordinate depth, .south⟩ : Port) := by
        simp only [translatePort, Port.mk.injEq, and_true]
        constructor
        · omega
        · dsimp [center] at hrow hcenterPositive
          omega
      rw [htarget] at projected
      exact projected
    · right
      have projected := verticalWindowRoute_projectsTo hblock hdelta route
      have htarget : translatePort ⟨8 + localX, 8, .north⟩
          (8 * (blockX - 1)) (8 * (centerBlock depth - 1)) =
          (⟨x, exceptionalCoordinate depth, .north⟩ : Port) := by
        simp only [translatePort, Port.mk.injEq, and_true]
        constructor
        · omega
        · dsimp [center] at hrow hcenterPositive
          omega
      rw [htarget] at projected
      exact projected

set_option maxHeartbeats 5000000 in
-- The inherited/created split normalizes both global and local coordinates.
/-- The recursive exceptional column is covered by inherited or backed created
segments. -/
theorem horizontalProjection
    (depth : Nat) (parent : Index)
    (previous : LiveColumnCertificate (oldGrid depth parent)
      (west .even (depth + 1)) (east .even (depth + 1))
      (west .even (depth + 1)) (east .even (depth + 1))
      (lineCoordinate .even (depth + 1) (extraChild (pivot depth)))) :
    HorizontalProjectionAt (oldGrid depth parent)
      (west .even (depth + 1)) (east .even (depth + 1))
      (west .even (depth + 1)) (east .even (depth + 1))
      (exceptionalCoordinate depth) := by
  intro y hsouth hnorth interior
  let oldColumn := lineCoordinate .even (depth + 1) (extraChild (pivot depth))
  have hcoordinate : exceptionalCoordinate depth = sparseCoordinate oldColumn := by
    simpa [oldColumn] using exceptionalCoordinate_as_sparseSource depth
  have heven : oldColumn % 2 = 0 := by
    simpa [oldColumn] using sourceRow_even depth
  have interior' : Signals.horizontalInterior?
      (componentAt (iterateRefine 2 (oldGrid depth parent))
        (sparseCoordinate oldColumn) y)
      (quadrantAt (sparseCoordinate oldColumn) y) ≠ none := by
    rwa [← hcoordinate]
  let blockY := y / 8
  let localY := y % 8
  let delta := blockY - firstBlock depth
  have hlocalY : localY < 8 := Nat.mod_lt _ (by decide)
  have hy : 8 * blockY + localY = y := by
    have := Nat.mod_add_div y 8
    dsimp [blockY, localY]
    omega
  have hfirst : firstBlock depth ≤ blockY := by
    rw [firstBlock, pow_succ]
    simp [quarterSouth, west, scale, Phase.factor, pow_succ] at hsouth
    dsimp [blockY]
    omega
  have hblock : blockY = firstBlock depth + delta := by
    dsimp [delta]
    omega
  have hdelta : delta ≤ blockCount depth := by
    have hblockUpper : blockY < 3 * firstBlock depth := by
      rw [firstBlock, pow_succ]
      simp [quarterNorth, east, scale, Phase.factor, pow_succ] at hnorth
      dsimp [blockY]
      omega
    rw [blockCount]
    dsimp [delta]
    omega
  let center := centerBlock depth
  have hcenterPositive : 0 < center := by
    dsimp [center]
    simp [centerBlock, firstBlock]
  have hblockPositive : 0 < blockY := by
    have hfirstPositive : 0 < firstBlock depth := by
      simp [firstBlock]
    omega
  have hcolumn : exceptionalCoordinate depth = 8 * center := by
    simpa [center] using exceptionalCoordinate_centerBlock depth
  let cell := oldGrid depth parent center blockY
  by_cases checked : horizontalAncestorAt 0 0 cell localY = true
  · have checked' : horizontalAncestorAt 0 0
        (oldGrid depth parent (oldColumn / 2) (y / 8)) (y % 8) = true := by
      have hcenter : oldColumn / 2 = center := by
        have hsparse := hcoordinate
        rw [hcolumn] at hsparse
        simp [sparseCoordinate, macroOrigin, localCoordinate, heven] at hsparse
        omega
      simpa [cell, blockY, localY, hcenter]
    rcases horizontal_inherited_of_checked heven interior' checked' with
      ⟨oldY, oldCoordinate, oldInterior⟩
    have oldSouth : quarterSouth (west .even (depth + 1)) < oldY := by
      rw [← SparseFreeLineLocalProjection.sparseCoordinate_lt_iff]
      simpa [oldCoordinate, hcoordinate] using hsouth
    have oldNorth : oldY < quarterNorth (east .even (depth + 1)) := by
      rw [← SparseFreeLineLocalProjection.sparseCoordinate_lt_iff]
      simpa [oldCoordinate, hcoordinate] using hnorth
    rcases previous oldY oldSouth oldNorth oldInterior with
      ⟨source, sourceOdd, endpoint | endpoint⟩
    · left
      refine ⟨ProjectsTo.ofOddSourcePath sourceOdd ?_ ?_⟩
      · simpa [endpoint, sparsePort, oldCoordinate, hcoordinate] using
          (Path.refl (indexGrid := iterateRefine 2 (oldGrid depth parent))
            (sparsePort source.port))
      · simpa [endpoint, sparsePort, oldCoordinate, hcoordinate,
          WeightedSource.refine] using source.refine.portLive
    · right
      refine ⟨ProjectsTo.ofOddSourcePath sourceOdd ?_ ?_⟩
      · simpa [endpoint, sparsePort, oldCoordinate, hcoordinate] using
          (Path.refl (indexGrid := iterateRefine 2 (oldGrid depth parent))
            (sparsePort source.port))
      · simpa [endpoint, sparsePort, oldCoordinate, hcoordinate,
          WeightedSource.refine] using source.refine.portLive
  · have hcreated : horizontalAncestorAt 0 0 cell localY = false :=
      Bool.eq_false_of_not_eq_true checked
    have hlocalCases : localY = 4 ∨ localY = 5 :=
      (horizontal_classification cell ⟨localY, hlocalY⟩).resolve_left checked
    have localInterior : Signals.horizontalInterior?
        (componentAt (fineGrid cell) 0 localY)
        (quadrantAt 0 localY) ≠ none := by
      have transported := interior
      rw [hcolumn, ← hy] at transported
      have hcomponent := componentAt_two_block (oldGrid depth parent) 0
        center blockY 0 localY (by decide) hlocalY
      simp only [Nat.zero_add] at hcomponent
      change componentAt (iterateRefine 2 (oldGrid depth parent))
          (8 * center + 0) (8 * blockY + localY) =
        componentAt (fineGrid cell) 0 localY at hcomponent
      have hquadrant : quadrantAt (8 * center + 0) (8 * blockY + localY) =
          quadrantAt 0 localY := by
        simpa using quadrantAt_block center blockY 0 localY
      rw [show 8 * center = 8 * center + 0 by omega,
        hcomponent, hquadrant] at transported
      exact transported
    have hwindow := canonical_horizontalWindowAt_mem depth parent delta hdelta
    rw [← hblock] at hwindow
    have hcenterEq :
        windowGrid (horizontalWindowAt depth parent blockY) 1 1 = cell := by
      rw [windowGrid_horizontalWindowAt depth parent blockY 1 1
        (by omega) (by omega)]
      dsimp [cell, center]
      congr 2
      omega
    have required : (Signals.horizontalInterior?
        (componentAt
          (fineGrid (windowGrid (horizontalWindowAt depth parent blockY) 1 1))
          0 localY) (quadrantAt 0 localY)).isSome = true := by
      rw [hcenterEq]
      exact Option.isSome_iff_ne_none.mpr localInterior
    have created : horizontalAncestorAt 0 0
        (windowGrid (horizontalWindowAt depth parent blockY) 1 1) localY =
        false := by
      rw [hcenterEq]
      exact hcreated
    rcases horizontal_actual_route hwindow hlocalCases required created with
      route | route
    · left
      have projected := horizontalWindowRoute_projectsTo hblock hdelta route
      have htarget : translatePort ⟨8, 8 + localY, .west⟩
          (8 * (centerBlock depth - 1)) (8 * (blockY - 1)) =
          (⟨exceptionalCoordinate depth, y, .west⟩ : Port) := by
        simp only [translatePort, Port.mk.injEq, and_true]
        constructor
        · dsimp [center] at hcolumn hcenterPositive
          omega
        · omega
      rw [htarget] at projected
      exact projected
    · right
      have projected := horizontalWindowRoute_projectsTo hblock hdelta route
      have htarget : translatePort ⟨8, 8 + localY, .east⟩
          (8 * (centerBlock depth - 1)) (8 * (blockY - 1)) =
          (⟨exceptionalCoordinate depth, y, .east⟩ : Port) := by
        simp only [translatePort, Port.mk.injEq, and_true]
        constructor
        · dsimp [center] at hcolumn hcenterPositive
          omega
        · omega
      rw [htarget] at projected
      exact projected

/-- The recursive exceptional row and column certificates. -/
theorem certificates
    (depth : Nat) (parent : Index)
    (rows : ∀ offset ∈ offsets (depth + 1),
      LiveRowCertificate (localGrid .even (depth + 1) parent)
        (west .even (depth + 1)) (east .even (depth + 1))
        (west .even (depth + 1)) (east .even (depth + 1))
        (lineCoordinate .even (depth + 1) offset))
    (columns : ∀ offset ∈ offsets (depth + 1),
      LiveColumnCertificate (localGrid .even (depth + 1) parent)
        (west .even (depth + 1)) (east .even (depth + 1))
        (west .even (depth + 1)) (east .even (depth + 1))
        (lineCoordinate .even (depth + 1) offset)) :
    LiveRowCertificate (localGrid .even (depth + 2) parent)
        (west .even (depth + 2)) (east .even (depth + 2))
        (west .even (depth + 2)) (east .even (depth + 2))
        (lineCoordinate .even (depth + 2)
          (mainChild (extraChild (pivot depth)))) ∧
      LiveColumnCertificate (localGrid .even (depth + 2) parent)
        (west .even (depth + 2)) (east .even (depth + 2))
        (west .even (depth + 2)) (east .even (depth + 2))
        (lineCoordinate .even (depth + 2)
          (mainChild (extraChild (pivot depth)))) := by
  have hextra : extraChild (pivot depth) ∈ offsets (depth + 1) :=
    mem_offsets_succ_of_child depth (pivot_mem_offsets depth)
      (extraChild_mem_children (pivot_even depth))
  have vertical := verticalProjection depth parent
    (rows (extraChild (pivot depth)) hextra)
  have horizontal := horizontalProjection depth parent
    (columns (extraChild (pivot depth)) hextra)
  constructor
  · simpa [oldGrid, localGrid_succ, west_succ, east_succ,
      exceptionalCoordinate] using
      liveRowCertificate_of_verticalProjectionAt vertical
  · simpa [oldGrid, localGrid_succ, west_succ, east_succ,
      exceptionalCoordinate] using
      liveColumnCertificate_of_horizontalProjectionAt horizontal

/-- The formerly conditional whole-pattern even-extra branch. -/
theorem evenExtraMainStep : EvenExtraMainStep := by
  intro depth parent rows columns
  exact certificates depth parent rows columns

end SparseFreeLineEvenExtraCreatedStep
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
