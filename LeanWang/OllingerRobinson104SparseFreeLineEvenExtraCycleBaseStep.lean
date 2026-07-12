/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104SparseFreeLineEvenExtraBaseStep
import LeanWang.OllingerRobinson104SparseFreeLineEvenExtraCycleBaseAudit

/-!
# The cycle-only first even-extra projection

The enclosing canonical cycle alone backs every audited route to the first
exceptional even-phase row and column.  The old sparse certificates are not
used.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace SparseFreeLineEvenExtraCycleBaseStep

open RedCycles RedShadeCycles RedShadeGraph RedShadeGraphRefinement
  RedShadeGraphTranslation RefinementTranslation Signals.FreeCellLocal
  BorderGeometry BorderCoverageOffsets ShadedFreeLinePatternRefinement
  ShadedFreeLineProjectionCandidates ShadedFreeLineProjectionSourceLists
  ShadedFreeLineRecurrence SparseFreeLineOffsets SparseFreeLineRecurrence
  SparseFreeLineLocalProjection SparseFreeLineLocalRecurrence
  SparseFreeLineEvenExtraCycleBaseAudit

set_option maxRecDepth 20000

abbrev oldGrid := SparseFreeLineEvenExtraBaseAudit.oldGrid

abbrev searchGrid := SparseFreeLineEvenExtraBaseAudit.searchGrid

theorem route_of_canonicalIndex {parent : Index} {target : Port}
    (route : Route (BorderSubstitution.canonicalIndex parent) target) :
    Route parent target := by
  rcases route with ⟨start, hstart, path, targetLive⟩
  refine ⟨start, hstart,
    SparseFreeLineEvenExtraBaseStep.path_congr_of_sameComponents
      (SparseFreeLineEvenExtraBaseStep.sameComponents_searchGrid_canonicalIndex
        parent) path, ?_⟩
  rwa [portPresent_congr
    (SparseFreeLineEvenExtraBaseStep.sameComponents_searchGrid_canonicalIndex
      parent) target] at targetLive

theorem canonical_check (parent : Index) :
    check (BorderSubstitution.canonicalIndex parent) = true := by
  exact canonical_complete (BorderSubstitution.indexState parent)
    (BorderSubstitution.indexState_mem_states parent)

theorem auditedVerticalRoutes
    (parent : Index) (x : Nat) (hxLower : 2 ≤ x) (hxUpper : x < 64)
    (interior : Signals.verticalInterior?
      (componentAt (searchGrid parent) x 40) (quadrantAt x 40) ≠ none) :
    Route parent ⟨x, 40, .south⟩ ∨ Route parent ⟨x, 40, .north⟩ := by
  have same :=
    SparseFreeLineEvenExtraBaseStep.sameComponents_searchGrid_canonicalIndex
      parent
  have canonicalInterior : Signals.verticalInterior?
      (componentAt (searchGrid (BorderSubstitution.canonicalIndex parent)) x 40)
        (quadrantAt x 40) ≠ none := by
    rw [same x 40]
    exact interior
  rcases (check_sound (canonical_check parent)).1 x hxLower hxUpper
      canonicalInterior with route | route
  · exact Or.inl (route_of_canonicalIndex route)
  · exact Or.inr (route_of_canonicalIndex route)

theorem auditedHorizontalRoutes
    (parent : Index) (y : Nat) (hyLower : 2 ≤ y) (hyUpper : y < 64)
    (interior : Signals.horizontalInterior?
      (componentAt (searchGrid parent) 40 y) (quadrantAt 40 y) ≠ none) :
    Route parent ⟨40, y, .west⟩ ∨ Route parent ⟨40, y, .east⟩ := by
  have same :=
    SparseFreeLineEvenExtraBaseStep.sameComponents_searchGrid_canonicalIndex
      parent
  have canonicalInterior : Signals.horizontalInterior?
      (componentAt (searchGrid (BorderSubstitution.canonicalIndex parent)) 40 y)
        (quadrantAt 40 y) ≠ none := by
    rw [same 40 y]
    exact interior
  rcases (check_sound (canonical_check parent)).2 y hyLower hyUpper
      canonicalInterior with route | route
  · exact Or.inl (route_of_canonicalIndex route)
  · exact Or.inr (route_of_canonicalIndex route)

theorem starts_backed (parent : Index) :
    SparseFreeLineSideHalfProjection.StartsBacked
      (grid := oldGrid parent) (west := 4) (east := 12)
      (south := 4) (north := 12) 4 4 starts := by
  intro start hstart
  rw [starts, List.mem_map] at hstart
  rcases hstart with ⟨candidate, hcandidate, rfl⟩
  have backed : Candidate.BackedBy (grid := oldGrid parent)
      (west := 4) (east := 12) (south := 4) (north := 12) candidate := by
    rcases List.mem_map.1 hcandidate with ⟨port, hport, rfl⟩
    exact backedBy_cycle (canonicalCycle .even 1 parent)
      (onCycle_of_mem_cyclePorts
        (canonicalCycle .even 1 parent).west_lt_east
        (canonicalCycle .even 1 parent).south_lt_north hport)
  have hlower := candidates_sparse_lower candidate hcandidate
  rcases candidate with
    ⟨⟨candidateX, candidateY, candidateSide⟩, candidateParity⟩
  refine ⟨⟨⟨candidateX, candidateY, candidateSide⟩, candidateParity⟩,
    backed, ?_, rfl⟩
  simp only [translatePort, sparsePort] at hlower ⊢
  congr 1 <;> omega

theorem projectsTo_of_route {parent : Index} {target : Port}
    (route : Route parent target) :
    Nonempty (ProjectsTo (grid := oldGrid parent) (west := 4) (east := 12)
      (south := 4) (north := 12) (translatePort target 32 32)) := by
  rcases route with ⟨start, hstart, path, targetLive⟩
  rcases starts_backed parent start hstart with
    ⟨candidate, candidateBacked, startCoordinate, startParity⟩
  have translated := path_translate (depth := 2) (grid := oldGrid parent)
    (blockX := 4) (blockY := 4) path
  norm_num at translated
  norm_num at startCoordinate
  have tail : Path (iterateRefine 2 (oldGrid parent))
      (sparsePort candidate.port) (translatePort target 32 32)
      (Bool.xor candidate.parity true) := by
    rw [← startCoordinate]
    simpa only [startParity, Bool.xor_true] using translated
  have globalLive : portPresent (iterateRefine 2 (oldGrid parent))
      (translatePort target 32 32) = true := by
    change portPresent
      (iterateRefine 2 (shiftGrid (oldGrid parent) 4 4)) target = true
      at targetLive
    rw [SparseFreeLineLocalTransport.portPresent_shift] at targetLive
    norm_num at targetLive
    exact targetLive
  rcases candidateBacked with ⟨source, sourceParity, head⟩
  refine ⟨{
    source := source
    path := ?_
    targetLive := globalLive
  }⟩
  simpa only [sourceParity, Bool.false_xor] using Path.trans head tail

set_option maxHeartbeats 1000000 in
-- Normalizing the translated full-board projection is elaboration-intensive.
theorem verticalProjection (parent : Index) :
    VerticalProjectionAt (oldGrid parent) 4 12 4 12 72 := by
  intro targetX hwest heast interior
  let localX := targetX - 32
  have hlocalLower : 2 ≤ localX := by
    simp [quarterWest] at hwest
    omega
  have hlocalUpper : localX < 64 := by
    simp [quarterEast] at heast
    omega
  have hglobalX : 32 + localX = targetX := by
    simp [quarterWest] at hwest
    omega
  have localInterior : Signals.verticalInterior?
      (componentAt (searchGrid parent) localX 40)
        (quadrantAt localX 40) ≠ none := by
    change Signals.verticalInterior?
      (componentAt (iterateRefine 2 (shiftGrid (oldGrid parent) 4 4))
        localX 40) (quadrantAt localX 40) ≠ none
    have hcomponent := componentAt_iterateRefine_shift 2 (oldGrid parent)
      4 4 localX 40
    norm_num at hcomponent
    have hquadrant := quadrantAt_shift 8 4 4 localX 40 (by decide)
    rw [hglobalX] at hquadrant
    rw [hcomponent, hglobalX, ← hquadrant]
    simpa using interior
  rcases auditedVerticalRoutes parent localX hlocalLower hlocalUpper
      localInterior with route | route
  · left
    simpa [translatePort, hglobalX] using projectsTo_of_route route
  · right
    simpa [translatePort, hglobalX] using projectsTo_of_route route

set_option maxHeartbeats 1000000 in
-- Normalizing the translated full-board projection is elaboration-intensive.
theorem horizontalProjection (parent : Index) :
    HorizontalProjectionAt (oldGrid parent) 4 12 4 12 72 := by
  intro targetY hsouth hnorth interior
  let localY := targetY - 32
  have hlocalLower : 2 ≤ localY := by
    simp [quarterSouth] at hsouth
    omega
  have hlocalUpper : localY < 64 := by
    simp [quarterNorth] at hnorth
    omega
  have hglobalY : 32 + localY = targetY := by
    simp [quarterSouth] at hsouth
    omega
  have localInterior : Signals.horizontalInterior?
      (componentAt (searchGrid parent) 40 localY)
        (quadrantAt 40 localY) ≠ none := by
    change Signals.horizontalInterior?
      (componentAt (iterateRefine 2 (shiftGrid (oldGrid parent) 4 4))
        40 localY) (quadrantAt 40 localY) ≠ none
    have hcomponent := componentAt_iterateRefine_shift 2 (oldGrid parent)
      4 4 40 localY
    norm_num at hcomponent
    have hquadrant := quadrantAt_shift 8 4 4 40 localY (by decide)
    rw [hglobalY] at hquadrant
    rw [hcomponent, hglobalY, ← hquadrant]
    simpa using interior
  rcases auditedHorizontalRoutes parent localY hlocalLower hlocalUpper
      localInterior with route | route
  · left
    simpa [translatePort, hglobalY] using projectsTo_of_route route
  · right
    simpa [translatePort, hglobalY] using projectsTo_of_route route

/-- The first exceptional child is backed by its enclosing cycle alone. -/
theorem certificates (parent : Index) :
    LiveRowCertificate (localGrid .even 2 parent) 16 48 16 48
        (lineCoordinate .even 2 (mainChild (extraChild (pivot 0)))) ∧
      LiveColumnCertificate (localGrid .even 2 parent) 16 48 16 48
        (lineCoordinate .even 2 (mainChild (extraChild (pivot 0)))) := by
  have vertical := verticalProjection parent
  have horizontal := horizontalProjection parent
  have hcoordinate :
      lineCoordinate .even 2 (mainChild (extraChild (pivot 0))) = 72 := by
    norm_num [lineCoordinate_even, mainChild, extraChild, pivot]
  constructor
  · rw [hcoordinate]
    simpa [oldGrid, SparseFreeLineEvenExtraBaseAudit.oldGrid,
      localGrid_succ, west_succ, east_succ] using
      liveRowCertificate_of_verticalProjectionAt vertical
  · rw [hcoordinate]
    simpa [oldGrid, SparseFreeLineEvenExtraBaseAudit.oldGrid,
      localGrid_succ, west_succ, east_succ] using
      liveColumnCertificate_of_horizontalProjectionAt horizontal

/-- Depth zero of `EvenExtraMainStep`, with both old-pattern arguments unused. -/
theorem baseStep :
    ∀ parent,
      (∀ offset ∈ offsets 1,
        LiveRowCertificate (localGrid .even 1 parent) 4 12 4 12
          (lineCoordinate .even 1 offset)) →
      (∀ offset ∈ offsets 1,
        LiveColumnCertificate (localGrid .even 1 parent) 4 12 4 12
          (lineCoordinate .even 1 offset)) →
      LiveRowCertificate (localGrid .even 2 parent) 16 48 16 48
          (lineCoordinate .even 2 (mainChild (extraChild (pivot 0)))) ∧
        LiveColumnCertificate (localGrid .even 2 parent) 16 48 16 48
          (lineCoordinate .even 2 (mainChild (extraChild (pivot 0)))) := by
  intro parent _ _
  exact certificates parent

end SparseFreeLineEvenExtraCycleBaseStep
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
