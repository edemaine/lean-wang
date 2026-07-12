/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104SparseFreeLineEvenExtraBaseAudit
import LeanWang.OllingerRobinson104SparseFreeLineSideHalfProjection

/-!
# The first even-extra whole-pattern projection

The canonical finite audit is transported to every 104-symbol parent and its
translated paths are backed by the enclosing cycle and all retained sparse
rows and columns.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace SparseFreeLineEvenExtraBaseStep

open RedCycles RedShadeCycles RedShadeGraph RedShadeGraphRefinement RedShadeGraphSearch
  RedShadeGraphSearchSoundness RedShadeGraphWeightedSearch
  RedShadeGraphTranslation RefinementTranslation
  Signals.FreeCellLocal BorderGeometry BorderCoverage BorderCoverageOffsets
  ShadedFreeLinePatternRefinement
  ShadedFreeLineProjectionCandidates ShadedFreeLineProjectionSourceLists
  ShadedFreeLineRecurrence SparseFreeLineOffsets SparseFreeLineRecurrence
  SparseFreeLineLocalProjection SparseFreeLineEvenExtraBaseAudit

set_option maxRecDepth 20000

theorem sameComponents_searchGrid_canonicalIndex (parent : Index) :
    SameComponents
      (searchGrid (BorderSubstitution.canonicalIndex parent))
      (searchGrid parent) := by
  have sameFine := sameComponents_fineLocalGrid_canonicalIndex .even 1 parent
  intro x y
  rw [searchGrid, searchGrid, componentAt_iterateRefine_shift,
    componentAt_iterateRefine_shift]
  norm_num
  exact sameFine (32 + x) (32 + y)

theorem candidates_canonicalIndex (parent : Index) :
    candidates (BorderSubstitution.canonicalIndex parent) = candidates parent := by
  have same := sameComponents_localGrid_canonicalIndex .even 1 parent
  unfold candidates oldGrid
  exact patternCandidates_congr same 4 12 4 12 (offsets 1)
    (lineCoordinate .even 1)

theorem starts_canonicalIndex (parent : Index) :
    starts (BorderSubstitution.canonicalIndex parent) = starts parent := by
  unfold starts
  rw [candidates_canonicalIndex]

theorem link_congr_of_sameComponents
    {firstGrid secondGrid : Nat → Nat → Index}
    (same : SameComponents firstGrid secondGrid)
    {first second : Port} {parity : Bool}
    (link : Link firstGrid first second parity) :
    Link secondGrid first second parity := by
  let width := max first.x second.x + 1
  let height := max first.y second.y + 1
  apply link_congr_of_component_eq
    (width := width) (height := height) (fun x y _ _ => same x y) link
  · simp [PortInBounds, width, height]
  · simp [PortInBounds, width, height]

theorem path_congr_of_sameComponents
    {firstGrid secondGrid : Nat → Nat → Index}
    (same : SameComponents firstGrid secondGrid)
    {first second : Port} {parity : Bool}
    (path : Path firstGrid first second parity) :
    Path secondGrid first second parity := by
  induction path with
  | refl port => exact Path.refl port
  | ofLink link => exact Path.ofLink (link_congr_of_sameComponents same link)
  | trans _ _ firstIH secondIH => exact Path.trans firstIH secondIH

theorem route_of_canonicalIndex {parent : Index} {target : Port}
    (route : Route (BorderSubstitution.canonicalIndex parent) target) :
    Route parent target := by
  rcases route with ⟨start, hstart, path, targetLive⟩
  refine ⟨start, ?_, path_congr_of_sameComponents
    (sameComponents_searchGrid_canonicalIndex parent) path, ?_⟩
  · rwa [starts_canonicalIndex] at hstart
  · rwa [portPresent_congr
      (sameComponents_searchGrid_canonicalIndex parent) target] at targetLive

theorem canonical_check (parent : Index) :
    check (BorderSubstitution.canonicalIndex parent) = true := by
  exact canonical_complete (BorderSubstitution.indexState parent)
    (BorderSubstitution.indexState_mem_states parent)

theorem auditedVerticalRoutes
    (parent : Index) (x : Nat) (hxLower : 2 ≤ x) (hxUpper : x < 64)
    (interior : Signals.verticalInterior?
      (componentAt (searchGrid parent) x 40) (quadrantAt x 40) ≠ none) :
    Route parent ⟨x, 40, .south⟩ ∨ Route parent ⟨x, 40, .north⟩ := by
  have same := sameComponents_searchGrid_canonicalIndex parent
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
  have same := sameComponents_searchGrid_canonicalIndex parent
  have canonicalInterior : Signals.horizontalInterior?
      (componentAt (searchGrid (BorderSubstitution.canonicalIndex parent)) 40 y)
      (quadrantAt 40 y) ≠ none := by
    rw [same 40 y]
    exact interior
  rcases (check_sound (canonical_check parent)).2 y hyLower hyUpper
      canonicalInterior with route | route
  · exact Or.inl (route_of_canonicalIndex route)
  · exact Or.inr (route_of_canonicalIndex route)

theorem starts_backed
    (parent : Index)
    (rows : ∀ offset ∈ offsets 1,
      LiveRowCertificate (oldGrid parent) 4 12 4 12
        (lineCoordinate .even 1 offset))
    (columns : ∀ offset ∈ offsets 1,
      LiveColumnCertificate (oldGrid parent) 4 12 4 12
        (lineCoordinate .even 1 offset)) :
    SparseFreeLineSideHalfProjection.StartsBacked
      (grid := oldGrid parent) (west := 4) (east := 12)
      (south := 4) (north := 12) 4 4 (starts parent) := by
  let family := patternFamily (canonicalCycle .even 1 parent) (offsets 1)
    (lineCoordinate .even 1) rows columns
  intro start hstart
  rw [starts, List.mem_map] at hstart
  rcases hstart with ⟨candidate, hcandidate, rfl⟩
  have backed : Candidate.BackedBy (grid := oldGrid parent)
      (west := 4) (east := 12) (south := 4) (north := 12) candidate := by
    apply family.backed candidate
    exact hcandidate
  have hlower := candidate_sparse_lower parent candidate hcandidate
  rcases candidate with
    ⟨⟨candidateX, candidateY, candidateSide⟩, candidateParity⟩
  refine ⟨⟨⟨candidateX, candidateY, candidateSide⟩, candidateParity⟩,
    backed, ?_, rfl⟩
  simp only [translatePort, sparsePort] at hlower ⊢
  congr 1 <;> omega

theorem projectsTo_of_route
    {parent : Index} {target : Port}
    (rows : ∀ offset ∈ offsets 1,
      LiveRowCertificate (oldGrid parent) 4 12 4 12
        (lineCoordinate .even 1 offset))
    (columns : ∀ offset ∈ offsets 1,
      LiveColumnCertificate (oldGrid parent) 4 12 4 12
        (lineCoordinate .even 1 offset))
    (route : Route parent target) :
    Nonempty (ProjectsTo (grid := oldGrid parent) (west := 4) (east := 12)
      (south := 4) (north := 12) (translatePort target 32 32)) := by
  rcases route with ⟨start, hstart, path, targetLive⟩
  rcases starts_backed parent rows columns start hstart with
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
theorem verticalProjection
    (parent : Index)
    (rows : ∀ offset ∈ offsets 1,
      LiveRowCertificate (oldGrid parent) 4 12 4 12
        (lineCoordinate .even 1 offset))
    (columns : ∀ offset ∈ offsets 1,
      LiveColumnCertificate (oldGrid parent) 4 12 4 12
        (lineCoordinate .even 1 offset)) :
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
    have hcomponent := componentAt_iterateRefine_shift 2 (oldGrid parent)
      4 4 localX 40
    norm_num at hcomponent
    have hquadrant := quadrantAt_shift 8 4 4 localX 40 (by decide)
    rw [hglobalX] at hquadrant
    rw [searchGrid, hcomponent, hglobalX]
    rw [← hquadrant]
    simpa using interior
  rcases auditedVerticalRoutes parent localX hlocalLower hlocalUpper
      localInterior with route | route
  · left
    simpa [translatePort, hglobalX] using
      projectsTo_of_route rows columns route
  · right
    simpa [translatePort, hglobalX] using
      projectsTo_of_route rows columns route

set_option maxHeartbeats 1000000 in
-- Normalizing the translated full-board projection is elaboration-intensive.
theorem horizontalProjection
    (parent : Index)
    (rows : ∀ offset ∈ offsets 1,
      LiveRowCertificate (oldGrid parent) 4 12 4 12
        (lineCoordinate .even 1 offset))
    (columns : ∀ offset ∈ offsets 1,
      LiveColumnCertificate (oldGrid parent) 4 12 4 12
        (lineCoordinate .even 1 offset)) :
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
    have hcomponent := componentAt_iterateRefine_shift 2 (oldGrid parent)
      4 4 40 localY
    norm_num at hcomponent
    have hquadrant := quadrantAt_shift 8 4 4 40 localY (by decide)
    rw [hglobalY] at hquadrant
    rw [searchGrid, hcomponent, hglobalY]
    rw [← hquadrant]
    simpa using interior
  rcases auditedHorizontalRoutes parent localY hlocalLower hlocalUpper
      localInterior with route | route
  · left
    simpa [translatePort, hglobalY] using
      projectsTo_of_route rows columns route
  · right
    simpa [translatePort, hglobalY] using
      projectsTo_of_route rows columns route

/-- The finite whole-pattern audit proves the first exceptional child. -/
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
  intro parent rows columns
  have vertical := verticalProjection parent rows columns
  have horizontal := horizontalProjection parent rows columns
  have hcoordinate :
      lineCoordinate .even 2 (mainChild (extraChild (pivot 0))) = 72 := by
    norm_num [lineCoordinate_even, mainChild, extraChild, pivot]
  constructor
  · rw [hcoordinate]
    simpa [oldGrid, localGrid_succ, west_succ, east_succ] using
      liveRowCertificate_of_verticalProjectionAt vertical
  · rw [hcoordinate]
    simpa [oldGrid, localGrid_succ, west_succ, east_succ] using
      liveColumnCertificate_of_horizontalProjectionAt horizontal

end SparseFreeLineEvenExtraBaseStep
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
