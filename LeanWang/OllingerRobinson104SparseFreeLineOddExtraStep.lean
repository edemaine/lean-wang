/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104SparseFreeLineOddExtraBaseAudit

/-!
# The odd pivot-extra recurrence

The exceptional depth-zero step is supplied by the finite full-board audit.
Every later extra line is obtained by iterating the vertical and horizontal
side-half projections.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace SparseFreeLineOddExtraStep

open RedCycles RedShadeCycles RedShadeGraph RedShadeGraphRefinement
  RedShadeGraphSearchSoundness RedShadeGraphTranslation RefinementTranslation
  Signals.FreeCellLocal BorderGeometry BorderCoverage
  ShadedFreeLinePatternRefinement ShadedFreeLineProjectionCandidates
  ShadedFreeLineProjectionSourceLists ShadedFreeLineRecurrence
  SparseFreeLineOffsets SparseFreeLineRecurrence SparseFreeLineLocalProjection
  SparseFreeLineLocalRecurrence SparseFreeLineOddExtraBaseAudit

set_option maxRecDepth 20000

theorem sameComponents_searchGrid_canonicalIndex (parent : Index) :
    SameComponents (searchGrid (BorderSubstitution.canonicalIndex parent))
      (searchGrid parent) := by
  have sameFine := sameComponents_fineLocalGrid_canonicalIndex .odd 0 parent
  intro x y
  rw [searchGrid, searchGrid, componentAt_iterateRefine_shift,
    componentAt_iterateRefine_shift]
  norm_num
  exact sameFine (16 + x) (16 + y)

theorem starts_canonicalIndex (parent : Index) :
    starts (BorderSubstitution.canonicalIndex parent) = starts parent := by
  have same := sameComponents_localGrid_canonicalIndex .odd 0 parent
  unfold starts candidates oldGrid
  rw [patternCandidates_congr same]

theorem route_of_canonicalIndex {parent : Index} {target : Port}
    (route : Route (BorderSubstitution.canonicalIndex parent) target) :
    Route parent target := by
  have same := sameComponents_searchGrid_canonicalIndex parent
  rcases route with ⟨start, hstart, path, targetLive⟩
  refine ⟨start, ?_, BoundedPath.congr_of_component_eq
    (fun x y _ _ => same x y) path, ?_⟩
  · rwa [starts_canonicalIndex] at hstart
  · rwa [portPresent_congr same target] at targetLive

theorem canonical_check (parent : Index) :
    check (BorderSubstitution.canonicalIndex parent) = true := by
  exact canonical_complete (BorderSubstitution.indexState parent)
    (BorderSubstitution.indexState_mem_states parent)

theorem auditedVerticalRoutes
    (parent : Index) (x : Nat) (hxLower : 2 ≤ x) (hxUpper : x < 32)
    (interior : Signals.verticalInterior?
      (componentAt (searchGrid parent) x 19) (quadrantAt x 19) ≠ none) :
    Route parent ⟨x, 19, .south⟩ ∨ Route parent ⟨x, 19, .north⟩ := by
  have same := sameComponents_searchGrid_canonicalIndex parent
  have canonicalInterior : Signals.verticalInterior?
      (componentAt (searchGrid (BorderSubstitution.canonicalIndex parent)) x 19)
      (quadrantAt x 19) ≠ none := by
    rw [same x 19]
    exact interior
  rcases (check_sound (canonical_check parent)).1 x hxLower hxUpper
      canonicalInterior with route | route
  · exact Or.inl (route_of_canonicalIndex route)
  · exact Or.inr (route_of_canonicalIndex route)

theorem auditedHorizontalRoutes
    (parent : Index) (y : Nat) (hyLower : 2 ≤ y) (hyUpper : y < 32)
    (interior : Signals.horizontalInterior?
      (componentAt (searchGrid parent) 19 y) (quadrantAt 19 y) ≠ none) :
    Route parent ⟨19, y, .west⟩ ∨ Route parent ⟨19, y, .east⟩ := by
  have same := sameComponents_searchGrid_canonicalIndex parent
  have canonicalInterior : Signals.horizontalInterior?
      (componentAt (searchGrid (BorderSubstitution.canonicalIndex parent)) 19 y)
      (quadrantAt 19 y) ≠ none := by
    rw [same 19 y]
    exact interior
  rcases (check_sound (canonical_check parent)).2 y hyLower hyUpper
      canonicalInterior with route | route
  · exact Or.inl (route_of_canonicalIndex route)
  · exact Or.inr (route_of_canonicalIndex route)

theorem starts_backed
    (parent : Index)
    (row : LiveRowCertificate (oldGrid parent) 2 6 2 6
      (lineCoordinate .odd 0 (pivot 0)))
    (column : LiveColumnCertificate (oldGrid parent) 2 6 2 6
      (lineCoordinate .odd 0 (pivot 0))) :
    SparseFreeLineSideHalfProjection.StartsBacked
      (grid := oldGrid parent) (west := 2) (east := 6)
      (south := 2) (north := 6) 2 2 (starts parent) := by
  let family := patternFamily (canonicalCycle .odd 0 parent) [pivot 0]
    (lineCoordinate .odd 0)
    (fun offset hoffset => by
      simp only [List.mem_singleton] at hoffset
      subst offset
      exact row)
    (fun offset hoffset => by
      simp only [List.mem_singleton] at hoffset
      subst offset
      exact column)
  intro start hstart
  rw [starts, List.mem_map] at hstart
  rcases hstart with ⟨candidate, hcandidate, rfl⟩
  have backed : Candidate.BackedBy (grid := oldGrid parent)
      (west := 2) (east := 6) (south := 2) (north := 6) candidate := by
    apply family.backed candidate
    exact hcandidate
  have hlower := candidate_sparse_lower parent candidate hcandidate
  rcases candidate with ⟨⟨candidateX, candidateY, candidateSide⟩, candidateParity⟩
  refine ⟨⟨⟨candidateX, candidateY, candidateSide⟩, candidateParity⟩,
    backed, ?_, rfl⟩
  simp only [translatePort, sparsePort] at hlower ⊢
  congr 1 <;> omega

set_option maxHeartbeats 1000000 in
-- Normalizing the translated full-board route is elaboration-intensive.
/-- The checked depth-zero board projects the odd pivot to its first extra row. -/
theorem verticalProjection_base
    (parent : Index)
    (row : LiveRowCertificate (oldGrid parent) 2 6 2 6
      (lineCoordinate .odd 0 (pivot 0)))
    (column : LiveColumnCertificate (oldGrid parent) 2 6 2 6
      (lineCoordinate .odd 0 (pivot 0))) :
    VerticalProjectionAt (oldGrid parent) 2 6 2 6 35 := by
  intro targetX hwest heast interior
  let localX := targetX - 16
  have hlocalLower : 2 ≤ localX := by
    simp [quarterWest] at hwest
    omega
  have hlocalUpper : localX < 32 := by
    simp [quarterEast] at heast
    omega
  have hglobalX : 16 + localX = targetX := by
    simp [quarterWest] at hwest
    omega
  have localInterior : Signals.verticalInterior?
      (componentAt (searchGrid parent) localX 19) (quadrantAt localX 19) ≠ none := by
    have hcomponent := componentAt_iterateRefine_shift 2 (oldGrid parent)
      2 2 localX 19
    norm_num at hcomponent
    have hquadrant := quadrantAt_shift 8 2 2 localX 19 (by decide)
    rw [hglobalX] at hquadrant
    rw [searchGrid, hcomponent, hglobalX]
    rw [← hquadrant]
    simpa using interior
  rcases auditedVerticalRoutes parent localX hlocalLower hlocalUpper
      localInterior with route | route
  · left
    have projected :=
      SparseFreeLineSideHalfProjection.projectsTo_of_shiftedRoute_of_backedStarts
        2 2 33 33 (starts_backed parent row column) route
    simpa [translatePort, hglobalX] using projected
  · right
    have projected :=
      SparseFreeLineSideHalfProjection.projectsTo_of_shiftedRoute_of_backedStarts
        2 2 33 33 (starts_backed parent row column) route
    simpa [translatePort, hglobalX] using projected

set_option maxHeartbeats 1000000 in
-- Normalizing the translated full-board route is elaboration-intensive.
/-- The checked depth-zero board projects the odd pivot to its first extra column. -/
theorem horizontalProjection_base
    (parent : Index)
    (row : LiveRowCertificate (oldGrid parent) 2 6 2 6
      (lineCoordinate .odd 0 (pivot 0)))
    (column : LiveColumnCertificate (oldGrid parent) 2 6 2 6
      (lineCoordinate .odd 0 (pivot 0))) :
    HorizontalProjectionAt (oldGrid parent) 2 6 2 6 35 := by
  intro targetY hsouth hnorth interior
  let localY := targetY - 16
  have hlocalLower : 2 ≤ localY := by
    simp [quarterSouth] at hsouth
    omega
  have hlocalUpper : localY < 32 := by
    simp [quarterNorth] at hnorth
    omega
  have hglobalY : 16 + localY = targetY := by
    simp [quarterSouth] at hsouth
    omega
  have localInterior : Signals.horizontalInterior?
      (componentAt (searchGrid parent) 19 localY) (quadrantAt 19 localY) ≠ none := by
    have hcomponent := componentAt_iterateRefine_shift 2 (oldGrid parent)
      2 2 19 localY
    norm_num at hcomponent
    have hquadrant := quadrantAt_shift 8 2 2 19 localY (by decide)
    rw [hglobalY] at hquadrant
    rw [searchGrid, hcomponent, hglobalY]
    rw [← hquadrant]
    simpa using interior
  rcases auditedHorizontalRoutes parent localY hlocalLower hlocalUpper
      localInterior with route | route
  · left
    have projected :=
      SparseFreeLineSideHalfProjection.projectsTo_of_shiftedRoute_of_backedStarts
        2 2 33 33 (starts_backed parent row column) route
    simpa [translatePort, hglobalY] using projected
  · right
    have projected :=
      SparseFreeLineSideHalfProjection.projectsTo_of_shiftedRoute_of_backedStarts
        2 2 33 33 (starts_backed parent row column) route
    simpa [translatePort, hglobalY] using projected

/-- The odd extra row and column exist at every depth. -/
theorem oddExtraCertificates (depth : Nat) (parent : Index) :
    LiveRowCertificate (localGrid .odd (depth + 1) parent)
        (west .odd (depth + 1)) (east .odd (depth + 1))
        (west .odd (depth + 1)) (east .odd (depth + 1))
        (lineCoordinate .odd (depth + 1) (extraChild (pivot depth))) ∧
      LiveColumnCertificate (localGrid .odd (depth + 1) parent)
        (west .odd (depth + 1)) (east .odd (depth + 1))
        (west .odd (depth + 1)) (east .odd (depth + 1))
        (lineCoordinate .odd (depth + 1) (extraChild (pivot depth))) := by
  induction depth with
  | zero =>
      have base := SparseFreeLineRecurrence.graphHolds_odd_zero parent
      have hpivot : pivot 0 ∈ offsets 0 := pivot_mem_offsets 0
      have row := base.1 (pivot 0) hpivot
      have column := base.2 (pivot 0) hpivot
      have vertical := verticalProjection_base parent row column
      have horizontal := horizontalProjection_base parent row column
      constructor
      · rw [odd_extra_coordinate]
        simpa [oldGrid, localGrid_succ, west_succ, east_succ,
          west, east, scale, Phase.factor] using
          liveRowCertificate_of_verticalProjectionAt vertical
      · rw [odd_extra_coordinate]
        simpa [oldGrid, localGrid_succ, west_succ, east_succ,
          west, east, scale, Phase.factor] using
          liveColumnCertificate_of_horizontalProjectionAt horizontal
  | succ depth ih =>
      have vertical := SparseFreeLineSideHalfProjection.verticalProjection_nextOldRow
        depth parent ih.1
      have horizontal :=
        SparseFreeLineHorizontalSideHalfProjection.horizontalProjection_nextOldColumn
          depth parent ih.2
      constructor
      · simpa [SparseFreeLineSideHalfClosure.oldGrid,
          SparseFreeLineSideHalfClosure.oldRow, Nat.add_assoc,
          localGrid_succ, west_succ, east_succ] using
          liveRowCertificate_of_verticalProjectionAt vertical
      · simpa [SparseFreeLineHorizontalSideHalfClosure.oldGrid,
          SparseFreeLineHorizontalSideHalfClosure.oldColumn, Nat.add_assoc,
          localGrid_succ, west_succ, east_succ] using
          liveColumnCertificate_of_horizontalProjectionAt horizontal

/-- The formerly residual odd pivot-extra obligation. -/
theorem oddPivotExtraStep : OddPivotExtraStep := by
  intro depth parent _ _
  exact oddExtraCertificates depth parent

end SparseFreeLineOddExtraStep
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
