/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104SparseFreeLineOddExtraStep
import LeanWang.OllingerRobinson104SparseFreeLinePlaneHorizontalSideHalfProjection

/-!
# The odd pivot-extra recurrence in arbitrary coarse grids

The finite depth-zero audit is transported into the southwest refined coarse
block. Later extra lines use the arbitrary-grid side-half projections.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace SparseFreeLinePlaneOddExtraStep

open RedCycles RedShadeCycles RedShadeGraph RedShadeGraphRefinement
  RedShadeGraphSearchSoundness RedShadeGraphTranslation RefinementTranslation
  OrientedRedCycles RedShadeCrossingBoards
  Signals.FreeCellLocal BorderGeometry BorderCoverage
  ShadedFreeLinePatternRefinement ShadedFreeLineProjectionCandidates
  ShadedFreeLineProjectionSourceLists ShadedFreeLineRecurrence
  SparseFreeLineOffsets SparseFreeLineRecurrence SparseFreeLineLocalProjection
  SparseFreeLineLocalRecurrence SparseFreeLineOddExtraBaseAudit
  SparseFreeLinePlaneBase

set_option maxRecDepth 20000

def oldGrid (grid : Nat → Nat → Index) : Nat → Nat → Index :=
  refinedGrid .odd 0 grid

theorem componentAt_constant_eq
    (grid : Nat → Nat → Index) (x y : Nat) (hx : x < 16) (hy : y < 16) :
    componentAt (SparseFreeLineOddExtraBaseAudit.oldGrid (grid 0 0)) x y =
      componentAt (oldGrid grid) x y := by
  have hlocal := ShadedFreeLineOddBase.componentAt_localGrid_eq_shift
    grid 0 0 (parent := grid 0 0) rfl hx hy
  rw [SparseFreeLinePlaneBase.shiftGrid_zero] at hlocal
  simpa [oldGrid, refinedGrid, refinementDepth, Phase.extra,
    SparseFreeLineOddExtraBaseAudit.oldGrid,
    ShadedFreeLineOddBase.localGrid,
    ShadedFreeLineRecurrence.localGrid] using hlocal

theorem portPresent_constant_eq
    (grid : Nat → Nat → Index) (port : Port)
    (hport : PortInBounds port 16 16) :
    portPresent (SparseFreeLineOddExtraBaseAudit.oldGrid (grid 0 0)) port =
      portPresent (oldGrid grid) port := by
  rcases port with ⟨x, y, side⟩
  cases side <;> simp only [portPresent] <;>
    rw [componentAt_constant_eq grid x y hport.1 hport.2]

theorem candidate_backed
    (grid : Nat → Nat → Index)
    (row : LiveRowCertificate (oldGrid grid) 2 6 2 6
      (lineCoordinate .odd 0 (pivot 0)))
    (column : LiveColumnCertificate (oldGrid grid) 2 6 2 6
      (lineCoordinate .odd 0 (pivot 0)))
    (candidate : Candidate)
    (hcandidate : candidate ∈ candidates (grid 0 0)) :
    Candidate.BackedBy (grid := oldGrid grid)
      (west := 2) (east := 6) (south := 2) (north := 6) candidate := by
  rw [candidates, patternCandidates, List.mem_append] at hcandidate
  rcases hcandidate with hlines | hcolumn
  · rw [List.mem_append] at hlines
    rcases hlines with hcycle | hrow
    · rcases List.mem_map.1 hcycle with ⟨port, hport, rfl⟩
      have cycle : CycleOn (oldGrid grid) 2 6 2 6 := by
        simpa [oldGrid, refinedGrid, refinementDepth, Phase.extra] using
          largeCycle grid 1
      exact backedBy_cycle cycle
        (onCycle_of_mem_cyclePorts cycle.west_lt_east cycle.south_lt_north hport)
    · rw [List.mem_flatMap] at hrow
      rcases hrow with ⟨offset, hoffset, hrow⟩
      simp only [List.mem_singleton] at hoffset
      subst offset
      rcases List.mem_map.1 hrow with ⟨port, hport, rfl⟩
      rcases valid_rowPort (grid := SparseFreeLineOddExtraBaseAudit.oldGrid
          (grid 0 0)) (by decide) hport with
        ⟨x, hwest, heast, interior, endpoint, live⟩
      have hx : x < 16 := by
        simp [quarterEast] at heast
        omega
      have hy : lineCoordinate .odd 0 (pivot 0) < 16 := by
        rw [odd_pivot_coordinate]
        omega
      have actualInterior : Signals.verticalInterior?
          (componentAt (oldGrid grid) x (lineCoordinate .odd 0 (pivot 0)))
          (quadrantAt x (lineCoordinate .odd 0 (pivot 0))) ≠ none := by
        rw [← componentAt_constant_eq grid x
          (lineCoordinate .odd 0 (pivot 0)) hx hy]
        exact interior
      have actualLive : portPresent (oldGrid grid) port = true := by
        rw [← portPresent_constant_eq grid port]
        · exact live
        · rcases endpoint with rfl | rfl <;> exact ⟨hx, hy⟩
      exact backedBy_row row hwest heast actualInterior endpoint actualLive
  · rw [List.mem_flatMap] at hcolumn
    rcases hcolumn with ⟨offset, hoffset, hcolumn⟩
    simp only [List.mem_singleton] at hoffset
    subst offset
    rcases List.mem_map.1 hcolumn with ⟨port, hport, rfl⟩
    rcases valid_columnPort
        (grid := SparseFreeLineOddExtraBaseAudit.oldGrid (grid 0 0))
        (by decide) hport with
      ⟨y, hsouth, hnorth, interior, endpoint, live⟩
    have hx : lineCoordinate .odd 0 (pivot 0) < 16 := by
      rw [odd_pivot_coordinate]
      omega
    have hy : y < 16 := by
      simp [quarterNorth] at hnorth
      omega
    have actualInterior : Signals.horizontalInterior?
        (componentAt (oldGrid grid) (lineCoordinate .odd 0 (pivot 0)) y)
        (quadrantAt (lineCoordinate .odd 0 (pivot 0)) y) ≠ none := by
      rw [← componentAt_constant_eq grid
        (lineCoordinate .odd 0 (pivot 0)) y hx hy]
      exact interior
    have actualLive : portPresent (oldGrid grid) port = true := by
      rw [← portPresent_constant_eq grid port]
      · exact live
      · rcases endpoint with rfl | rfl <;> exact ⟨hx, hy⟩
    exact backedBy_column column hsouth hnorth actualInterior endpoint actualLive

theorem starts_backed
    (grid : Nat → Nat → Index)
    (row : LiveRowCertificate (oldGrid grid) 2 6 2 6
      (lineCoordinate .odd 0 (pivot 0)))
    (column : LiveColumnCertificate (oldGrid grid) 2 6 2 6
      (lineCoordinate .odd 0 (pivot 0))) :
    SparseFreeLinePlaneSideHalfProjection.StartsBacked
      (grid := oldGrid grid) (west := 2) (east := 6)
      (south := 2) (north := 6) 2 2 (starts (grid 0 0)) := by
  intro start hstart
  rw [starts, List.mem_map] at hstart
  rcases hstart with ⟨candidate, hcandidate, rfl⟩
  have backed := candidate_backed grid row column candidate hcandidate
  have hlower := candidate_sparse_lower (grid 0 0) candidate hcandidate
  rcases candidate with ⟨⟨candidateX, candidateY, candidateSide⟩, candidateParity⟩
  refine ⟨⟨⟨candidateX, candidateY, candidateSide⟩, candidateParity⟩,
    backed, ?_, rfl⟩
  simp only [translatePort, sparsePort] at hlower ⊢
  congr 1 <;> omega

theorem sameComponents_searchGrid
    (grid : Nat → Nat → Index) :
    ∀ x y, x < 33 → y < 33 →
      componentAt (searchGrid (grid 0 0)) x y =
        componentAt (iterateRefine 2 (shiftGrid (oldGrid grid) 2 2)) x y := by
  intro x y hx hy
  apply SparseFreeLinePlaneSideHalfProjection.componentAt_iterateRefine_two_congr_at
  have hlocal := iterateRefine_shift_eq_constant 3 grid 0 0
    (2 + x / 2 / 2 / 2) (2 + y / 2 / 2 / 2)
    (by norm_num; omega) (by norm_num; omega)
  rw [SparseFreeLinePlaneBase.shiftGrid_zero] at hlocal
  simpa [searchGrid, SparseFreeLineOddExtraBaseAudit.oldGrid,
    ShadedFreeLineRecurrence.localGrid, oldGrid, refinedGrid,
    refinementDepth, Phase.extra, shiftGrid] using hlocal.symm

theorem shiftedRoute_of_route
    (grid : Nat → Nat → Index) {target : Port}
    (route : Route (grid 0 0) target) :
    ShiftedBoundedRoute (oldGrid grid) 2 2 33 33
      (starts (grid 0 0)) target := by
  have same := sameComponents_searchGrid grid
  rcases route with ⟨start, hstart, path, targetLive⟩
  have htarget := path.second_inBounds
  refine ⟨start, hstart, BoundedPath.congr_of_component_eq same path, ?_⟩
  simp only [portPresent] at targetLive ⊢
  rw [← same target.x target.y htarget.1 htarget.2]
  exact targetLive

set_option maxHeartbeats 1000000 in
-- Normalizing the transported full-board route is elaboration-intensive.
theorem verticalProjection_base
    (grid : Nat → Nat → Index)
    (row : LiveRowCertificate (oldGrid grid) 2 6 2 6
      (lineCoordinate .odd 0 (pivot 0)))
    (column : LiveColumnCertificate (oldGrid grid) 2 6 2 6
      (lineCoordinate .odd 0 (pivot 0))) :
    VerticalProjectionAt (oldGrid grid) 2 6 2 6 35 := by
  intro targetX hwest heast interior
  let localX := targetX - 16
  have hlocalLower : 2 ≤ localX := by simp [quarterWest] at hwest; omega
  have hlocalUpper : localX < 32 := by simp [quarterEast] at heast; omega
  have hglobalX : 16 + localX = targetX := by simp [quarterWest] at hwest; omega
  have localInterior : Signals.verticalInterior?
      (componentAt (searchGrid (grid 0 0)) localX 19)
      (quadrantAt localX 19) ≠ none := by
    have same := sameComponents_searchGrid grid localX 19
      (by omega) (by omega)
    have hcomponent := componentAt_iterateRefine_shift 2 (oldGrid grid)
      2 2 localX 19
    norm_num at hcomponent
    have hquadrant := quadrantAt_shift 8 2 2 localX 19 (by decide)
    rw [hglobalX] at hquadrant
    rw [same, hcomponent, hglobalX, ← hquadrant]
    simpa using interior
  rcases SparseFreeLineOddExtraStep.auditedVerticalRoutes
      (grid 0 0) localX hlocalLower hlocalUpper localInterior with route | route
  · left
    have projected :=
      SparseFreeLinePlaneSideHalfProjection.projectsTo_of_shiftedRoute_of_backedStarts
        2 2 33 33 (starts_backed grid row column)
        (shiftedRoute_of_route grid route)
    simpa [translatePort, hglobalX] using projected
  · right
    have projected :=
      SparseFreeLinePlaneSideHalfProjection.projectsTo_of_shiftedRoute_of_backedStarts
        2 2 33 33 (starts_backed grid row column)
        (shiftedRoute_of_route grid route)
    simpa [translatePort, hglobalX] using projected

set_option maxHeartbeats 1000000 in
-- Normalizing the transported full-board route is elaboration-intensive.
theorem horizontalProjection_base
    (grid : Nat → Nat → Index)
    (row : LiveRowCertificate (oldGrid grid) 2 6 2 6
      (lineCoordinate .odd 0 (pivot 0)))
    (column : LiveColumnCertificate (oldGrid grid) 2 6 2 6
      (lineCoordinate .odd 0 (pivot 0))) :
    HorizontalProjectionAt (oldGrid grid) 2 6 2 6 35 := by
  intro targetY hsouth hnorth interior
  let localY := targetY - 16
  have hlocalLower : 2 ≤ localY := by simp [quarterSouth] at hsouth; omega
  have hlocalUpper : localY < 32 := by simp [quarterNorth] at hnorth; omega
  have hglobalY : 16 + localY = targetY := by simp [quarterSouth] at hsouth; omega
  have localInterior : Signals.horizontalInterior?
      (componentAt (searchGrid (grid 0 0)) 19 localY)
      (quadrantAt 19 localY) ≠ none := by
    have same := sameComponents_searchGrid grid 19 localY
      (by omega) (by omega)
    have hcomponent := componentAt_iterateRefine_shift 2 (oldGrid grid)
      2 2 19 localY
    norm_num at hcomponent
    have hquadrant := quadrantAt_shift 8 2 2 19 localY (by decide)
    rw [hglobalY] at hquadrant
    rw [same, hcomponent, hglobalY, ← hquadrant]
    simpa using interior
  rcases SparseFreeLineOddExtraStep.auditedHorizontalRoutes
      (grid 0 0) localY hlocalLower hlocalUpper localInterior with route | route
  · left
    have projected :=
      SparseFreeLinePlaneSideHalfProjection.projectsTo_of_shiftedRoute_of_backedStarts
        2 2 33 33 (starts_backed grid row column)
        (shiftedRoute_of_route grid route)
    simpa [translatePort, hglobalY] using projected
  · right
    have projected :=
      SparseFreeLinePlaneSideHalfProjection.projectsTo_of_shiftedRoute_of_backedStarts
        2 2 33 33 (starts_backed grid row column)
        (shiftedRoute_of_route grid route)
    simpa [translatePort, hglobalY] using projected

/-- The odd extra row and column exist at every depth in an arbitrary grid. -/
theorem oddExtraCertificates (depth : Nat) (grid : Nat → Nat → Index) :
    LiveRowCertificate (refinedGrid .odd (depth + 1) grid)
        (west .odd (depth + 1)) (east .odd (depth + 1))
        (west .odd (depth + 1)) (east .odd (depth + 1))
        (lineCoordinate .odd (depth + 1) (extraChild (pivot depth))) ∧
      LiveColumnCertificate (refinedGrid .odd (depth + 1) grid)
        (west .odd (depth + 1)) (east .odd (depth + 1))
        (west .odd (depth + 1)) (east .odd (depth + 1))
        (lineCoordinate .odd (depth + 1) (extraChild (pivot depth))) := by
  induction depth with
  | zero =>
      have base := SparseFreeLinePlaneBase.odd_zero grid
      have hpivot : pivot 0 ∈ offsets 0 := pivot_mem_offsets 0
      have row := base.1 (pivot 0) hpivot
      have column := base.2 (pivot 0) hpivot
      have vertical := verticalProjection_base grid row column
      have horizontal := horizontalProjection_base grid row column
      constructor
      · rw [odd_extra_coordinate]
        simpa [oldGrid, SparseFreeLinePlaneLocalStep.refinedGrid_succ,
          west_succ, east_succ, west, east, scale, Phase.factor] using
          liveRowCertificate_of_verticalProjectionAt vertical
      · rw [odd_extra_coordinate]
        simpa [oldGrid, SparseFreeLinePlaneLocalStep.refinedGrid_succ,
          west_succ, east_succ, west, east, scale, Phase.factor] using
          liveColumnCertificate_of_horizontalProjectionAt horizontal
  | succ depth ih =>
      have vertical :=
        SparseFreeLinePlaneSideHalfProjection.verticalProjection_nextOldRow
          depth grid ih.1
      have horizontal :=
        SparseFreeLinePlaneHorizontalSideHalfProjection.horizontalProjection_nextOldColumn
          depth grid ih.2
      constructor
      · simpa [SparseFreeLinePlaneSideHalfClosure.oldGrid,
          SparseFreeLinePlaneSideHalfClosure.oldRow, Nat.add_assoc,
          SparseFreeLinePlaneLocalStep.refinedGrid_succ, west_succ, east_succ] using
          liveRowCertificate_of_verticalProjectionAt vertical
      · simpa [SparseFreeLinePlaneHorizontalSideHalfClosure.oldGrid,
          SparseFreeLinePlaneHorizontalSideHalfClosure.oldColumn, Nat.add_assoc,
          SparseFreeLinePlaneLocalStep.refinedGrid_succ, west_succ, east_succ] using
          liveColumnCertificate_of_horizontalProjectionAt horizontal

end SparseFreeLinePlaneOddExtraStep
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
