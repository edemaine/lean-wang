/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104SparseFreeLineSideHalfClosure

/-!
# Transporting audited side-half windows to recursive boards

The finite audit runs on canonical border-state windows. This module transports
its bounded routes first to the corresponding 104-symbol window and then to the
actual shifted recursive grid.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace SparseFreeLineSideHalfProjection

open RedCycles RedShadeCycles RedShadeGraph RedShadeGraphRefinement
  RedShadeGraphSearchSoundness
  RedShadeGraphWeightedSearch RedShadeGraphTranslation RefinementTranslation
  Signals.FreeCellLocal
  BorderCoverageLocalAudit BorderGeometry SparseFreeLineLocalProjection
  ShadedFreeLinePatternRefinement ShadedFreeLineProjectionCandidates
  ShadedFreeLineRecurrence
  SparseFreeLineSideHalfAudit SparseFreeLineSideHalfClosure

set_option maxRecDepth 20000

theorem weightedSparseStarts_congr
    {first second : Index} (kind : SourceKind) (ports : List Port)
    (same : ∀ port, portPresent (coarseGrid first) port =
      portPresent (coarseGrid second) port) :
    weightedSparseStarts first kind ports =
      weightedSparseStarts second kind ports := by
  unfold weightedSparseStarts
  apply congrArg (List.map fun port =>
    ({ port := sparsePort port, parity := kind.parity } : WeightedStart))
  apply List.filter_congr
  intro port _
  exact same port

theorem rowStarts_congr
    {first second : Index} (kind : SourceKind) (sourceY : Nat)
    (same : ∀ port, portPresent (coarseGrid first) port =
      portPresent (coarseGrid second) port) :
    rowStarts first kind sourceY = rowStarts second kind sourceY := by
  unfold rowStarts
  exact weightedSparseStarts_congr kind _ same

theorem rowStarts_canonicalIndex (parent : Index) (kind : SourceKind)
    (sourceY : Nat) :
    rowStarts (BorderSubstitution.canonicalIndex parent) kind sourceY =
      rowStarts parent kind sourceY := by
  have same : SameComponents
      (coarseGrid (BorderSubstitution.canonicalIndex parent))
      (coarseGrid parent) := by
    intro x y
    unfold coarseGrid componentAt
    simpa only [RedCycles.indexThick_eq] using
      BorderSubstitution.indexThick_canonicalIndex parent
  exact rowStarts_congr kind sourceY (portPresent_congr same)

theorem windowStarts_canonicalWindow (window : Window) :
    windowStarts (canonicalWindow window) = windowStarts window := by
  unfold windowStarts
  apply List.flatMap_congr
  intro x _
  rw [windowGrid_canonicalWindow, rowStarts_canonicalIndex]

theorem windowStartsIn_canonicalWindow (window : Window) (lower upper : Nat) :
    windowStartsIn (canonicalWindow window) lower upper =
      windowStartsIn window lower upper := by
  unfold windowStartsIn
  rw [windowStarts_canonicalWindow]

/-- A route certified on the canonical border quotient is a route on the
original 104-symbol window. -/
theorem route_of_canonicalWindow {window : Window} {target : Port}
    (route : Route (canonicalWindow window) target) : Route window target := by
  have hgrid : windowGrid (canonicalWindow window) =
      BorderSubstitution.canonicalizeGrid (windowGrid window) := by
    funext x y
    exact windowGrid_canonicalWindow window x y
  have same : SameComponents
      (iterateRefine 2 (windowGrid (canonicalWindow window)))
      (iterateRefine 2 (windowGrid window)) := by
    rw [hgrid]
    exact sameComponents_iterateRefine_canonicalizeGrid 2 (windowGrid window)
  rcases route with ⟨start, hstart, path, targetLive⟩
  refine ⟨start, ?_, BoundedPath.congr_of_component_eq
    (fun x y _ _ => same x y) path, ?_⟩
  · rwa [windowStarts_canonicalWindow] at hstart
  · rwa [portPresent_congr same target] at targetLive

theorem routeIn_of_canonicalWindow
    {window : Window} {lower upper : Nat} {target : Port}
    (route : RouteIn (canonicalWindow window) lower upper target) :
    RouteIn window lower upper target := by
  have hgrid : windowGrid (canonicalWindow window) =
      BorderSubstitution.canonicalizeGrid (windowGrid window) := by
    funext x y
    exact windowGrid_canonicalWindow window x y
  have same : SameComponents
      (iterateRefine 2 (windowGrid (canonicalWindow window)))
      (iterateRefine 2 (windowGrid window)) := by
    rw [hgrid]
    exact sameComponents_iterateRefine_canonicalizeGrid 2 (windowGrid window)
  rcases route with ⟨start, hstart, path, targetLive⟩
  refine ⟨start, ?_, BoundedPath.congr_of_component_eq
    (fun x y _ _ => same x y) path, ?_⟩
  · rwa [windowStartsIn_canonicalWindow] at hstart
  · rwa [portPresent_congr same target] at targetLive

theorem componentAt_iterateRefine_two_congr_at
    {first second : Nat → Nat → Index} {x y : Nat}
    (hcell : first (x / 2 / 2 / 2) (y / 2 / 2 / 2) =
      second (x / 2 / 2 / 2) (y / 2 / 2 / 2)) :
    componentAt (iterateRefine 2 first) x y =
      componentAt (iterateRefine 2 second) x y := by
  unfold componentAt
  simp only [iterateRefine, refineIndexGrid]
  rw [hcell]

theorem sameComponents_windowAt_shift
    (depth : Nat) (parent : Index) (blockX : Nat) :
    ∀ x y, x < 24 → y < 16 →
      componentAt
          (iterateRefine 2 (windowGrid (windowAt depth parent blockX))) x y =
        componentAt
          (iterateRefine 2
            (shiftGrid (oldGrid depth parent) (blockX - 1)
              (lowerBlockY depth))) x y := by
  intro x y hx hy
  apply componentAt_iterateRefine_two_congr_at
  rw [windowGrid_windowAt]
  · simp [shiftGrid]
  · omega
  · omega

/-- A route in an actual side-half window is a route in the corresponding
shifted recursive board neighborhood. -/
theorem shiftedRoute_of_windowAt
    {depth : Nat} {parent : Index} {blockX : Nat}
    {starts : List WeightedStart} {target : Port}
    (route : BoundedRouteIn
      (iterateRefine 2 (windowGrid (windowAt depth parent blockX)))
      24 16 starts target) :
    ShiftedBoundedRoute (oldGrid depth parent) (blockX - 1)
      (lowerBlockY depth) 24 16 starts target := by
  have same := sameComponents_windowAt_shift depth parent blockX
  rcases route with ⟨start, hstart, path, targetLive⟩
  have htarget := path.second_inBounds
  refine ⟨start, hstart,
    BoundedPath.congr_of_component_eq same path, ?_⟩
  simp only [portPresent] at targetLive ⊢
  rw [← same target.x target.y htarget.1 htarget.2]
  exact targetLive

theorem shiftedRouteIn_of_windowAt
    {depth : Nat} {parent : Index} {blockX lower upper : Nat}
    {target : Port}
    (route : RouteIn (windowAt depth parent blockX) lower upper target) :
    ShiftedBoundedRoute (oldGrid depth parent) (blockX - 1)
      (lowerBlockY depth) 24 16
      (windowStartsIn (windowAt depth parent blockX) lower upper) target := by
  exact shiftedRoute_of_windowAt route

def StartsBacked
    {grid : Nat → Nat → Index} {west east south north : Nat}
    (blockX blockY : Nat) (starts : List WeightedStart) : Prop :=
  ∀ start ∈ starts, ∃ candidate : Candidate,
    candidate.BackedBy (grid := grid) (west := west) (east := east)
      (south := south) (north := north) ∧
    translatePort start.port (8 * blockX) (8 * blockY) =
      sparsePort candidate.port ∧
    start.parity = candidate.parity

theorem projectsTo_of_shiftedRoute_of_backedStarts
    {grid : Nat → Nat → Index} {west east south north : Nat}
    (blockX blockY width height : Nat) {starts : List WeightedStart}
    {target : Port}
    (backed : StartsBacked (grid := grid) (west := west) (east := east)
      (south := south) (north := north) blockX blockY starts)
    (route : ShiftedBoundedRoute grid blockX blockY width height starts target) :
    Nonempty (ProjectsTo (grid := grid) (west := west) (east := east)
      (south := south) (north := north)
      (translatePort target (8 * blockX) (8 * blockY))) := by
  rcases route with ⟨start, hstart, path, targetLive⟩
  rcases backed start hstart with
    ⟨candidate, candidateBacked, startCoordinate, startParity⟩
  have translated := SparseFreeLineLocalTransport.boundedPath_shift
    grid blockX blockY path
  have tail : Path (iterateRefine 2 grid) (sparsePort candidate.port)
      (translatePort target (8 * blockX) (8 * blockY))
      (Bool.xor candidate.parity true) := by
    rw [← startCoordinate]
    simpa only [startParity] using translated
  have globalLive : portPresent (iterateRefine 2 grid)
      (translatePort target (8 * blockX) (8 * blockY)) = true := by
    rw [SparseFreeLineLocalTransport.portPresent_shift] at targetLive
    exact targetLive
  rcases candidateBacked with ⟨source, sourceParity, head⟩
  refine ⟨{
    source := source
    path := ?_
    targetLive := globalLive
  }⟩
  simpa only [sourceParity, Bool.false_xor] using Path.trans head tail

theorem rowStart_mem_alignedSelf
    {parent : Index} {start : WeightedStart}
    (hstart : start ∈ rowStarts parent .retained 1) :
    start ∈ alignedRowStarts parent 1 start.port.x := by
  rcases mem_rowStarts_retained hstart with
    ⟨sourceX, hsourceX, hparity, endpoint⟩
  rcases endpoint with ⟨hport, hlive⟩ | ⟨hport, hlive⟩
  · rw [alignedRowStarts, weightedSparseStarts, List.mem_map]
    refine ⟨⟨sourceX, 1, .south⟩, ?_, ?_⟩
    · simp only [List.mem_filter]
      constructor
      · rw [List.mem_flatMap]
        refine ⟨sourceX, ?_, by simp [rowSourcePorts]⟩
        simp only [List.mem_filter, List.mem_range]
        refine ⟨hsourceX, ?_⟩
        rw [hport]
        simp [sparsePort]
      · exact hlive
    · cases start
      simp_all [SourceKind.parity]
  · rw [alignedRowStarts, weightedSparseStarts, List.mem_map]
    refine ⟨⟨sourceX, 1, .north⟩, ?_, ?_⟩
    · simp only [List.mem_filter]
      constructor
      · rw [List.mem_flatMap]
        refine ⟨sourceX, ?_, by simp [rowSourcePorts]⟩
        simp only [List.mem_filter, List.mem_range]
        refine ⟨hsourceX, ?_⟩
        rw [hport]
        simp [sparsePort]
      · exact hlive
    · cases start
      simp_all [SourceKind.parity]

theorem windowStartsIn_backed
    (depth : Nat) (parent : Index) (blockX lower upper : Nat)
    (row : LiveRowCertificate (oldGrid depth parent)
      (west .odd (depth + 1)) (east .odd (depth + 1))
      (west .odd (depth + 1)) (east .odd (depth + 1)) (oldRow depth))
    (hwindowWest : quarterWest (4 * west .odd (depth + 1)) <
      8 * (blockX - 1) + lower)
    (hwindowEast : 8 * (blockX - 1) + upper ≤
      quarterEast (4 * east .odd (depth + 1))) :
    StartsBacked (grid := oldGrid depth parent)
      (west := west .odd (depth + 1)) (east := east .odd (depth + 1))
      (south := west .odd (depth + 1)) (north := east .odd (depth + 1))
      (blockX - 1) (lowerBlockY depth)
      (windowStartsIn (windowAt depth parent blockX) lower upper) := by
  intro start hstart
  rw [windowStartsIn, List.mem_filter] at hstart
  rcases hstart with ⟨hstart, hbounds⟩
  rw [windowStarts, List.mem_flatMap] at hstart
  rcases hstart with ⟨macroX, hmacroX, hstart⟩
  simp only [List.mem_range] at hmacroX
  rcases List.mem_map.1 hstart with ⟨localStart, hlocalStart, rfl⟩
  have hgrid := windowGrid_windowAt depth parent blockX macroX 1
    hmacroX (by decide)
  rw [hgrid] at hlocalStart
  have hlower : lowerBlockY depth + 1 = oldRow depth / 2 := by
    rw [lowerBlockY, oldRow_eq]
    have hpower : 0 < 4 ^ depth := pow_pos (by decide) depth
    omega
  rw [hlower] at hlocalStart
  have hodd : oldRow depth % 2 = 1 := by
    rw [oldRow_eq]
    omega
  have hlocalParity : localStart.parity = true := by
    rcases mem_rowStarts_retained hlocalStart with
      ⟨_, _, parity, _⟩
    exact parity
  simp only [Bool.and_eq_true, decide_eq_true_eq, translateStart,
    translatePort] at hbounds
  let globalBlock := blockX - 1 + macroX
  have hwestFine : quarterWest (4 * west .odd (depth + 1)) <
      8 * globalBlock + localStart.port.x := by
    dsimp [globalBlock]
    omega
  have heastFine : 8 * globalBlock + localStart.port.x <
      quarterEast (4 * east .odd (depth + 1)) := by
    dsimp [globalBlock]
    omega
  rcases alignedRowStart_backed row hodd globalBlock localStart.port.x
      hwestFine heastFine (rowStart_mem_alignedSelf hlocalStart) with
    ⟨candidate, candidateOdd, candidateBacked, coordinate⟩
  refine ⟨candidate, candidateBacked, ?_, ?_⟩
  · rw [← coordinate]
    simp only [translateStart, translatePort]
    dsimp [globalBlock]
    congr 1 <;> omega
  · simpa only [hlocalParity, candidateOdd]

theorem auditedShiftedRoutesIn
    (depth : Nat) (parent : Index) (blockX x lower upper
      targetLower targetUpper : Nat)
    (hcheck : windowCheckIn (canonicalWindow (windowAt depth parent blockX))
      lower upper targetLower targetUpper = true)
    (hx : x < 8) (htargetLower : targetLower ≤ x)
    (htargetUpper : x < targetUpper)
    (interior : Signals.verticalInterior?
      (componentAt (iterateRefine 2
        (windowGrid (windowAt depth parent blockX))) (8 + x) 3)
      (quadrantAt (8 + x) 3) ≠ none) :
    ShiftedBoundedRoute (oldGrid depth parent) (blockX - 1)
        (lowerBlockY depth) 24 16
        (windowStartsIn (windowAt depth parent blockX) lower upper)
        ⟨8 + x, 3, .south⟩ ∨
      ShiftedBoundedRoute (oldGrid depth parent) (blockX - 1)
        (lowerBlockY depth) 24 16
        (windowStartsIn (windowAt depth parent blockX) lower upper)
        ⟨8 + x, 3, .north⟩ := by
  let window := windowAt depth parent blockX
  have hgrid : windowGrid (canonicalWindow window) =
      BorderSubstitution.canonicalizeGrid (windowGrid window) := by
    funext gridX gridY
    exact windowGrid_canonicalWindow window gridX gridY
  have same : SameComponents
      (iterateRefine 2 (windowGrid (canonicalWindow window)))
      (iterateRefine 2 (windowGrid window)) := by
    rw [hgrid]
    exact sameComponents_iterateRefine_canonicalizeGrid 2 (windowGrid window)
  have canonicalInterior : Signals.verticalInterior?
      (componentAt (iterateRefine 2 (windowGrid (canonicalWindow window)))
        (8 + x) 3)
      (quadrantAt (8 + x) 3) ≠ none := by
    rw [same (8 + x) 3]
    exact interior
  rcases windowCheckIn_sound hcheck x hx htargetLower htargetUpper
      canonicalInterior with route | route
  · exact Or.inl (shiftedRouteIn_of_windowAt
      (routeIn_of_canonicalWindow route))
  · exact Or.inr (shiftedRouteIn_of_windowAt
      (routeIn_of_canonicalWindow route))

theorem auditedLeftmostRoutes
    (depth : Nat) (parent : Index) (x : Nat) (hx : x < 8) (htarget : 2 ≤ x)
    (interior : Signals.verticalInterior?
      (componentAt (iterateRefine 2
        (windowGrid (windowAt depth parent (firstBlock depth)))) (8 + x) 3)
      (quadrantAt (8 + x) 3) ≠ none) :
    ShiftedBoundedRoute (oldGrid depth parent) (firstBlock depth - 1)
        (lowerBlockY depth) 24 16
        (windowStartsIn (windowAt depth parent (firstBlock depth)) 10 24)
        ⟨8 + x, 3, .south⟩ ∨
      ShiftedBoundedRoute (oldGrid depth parent) (firstBlock depth - 1)
        (lowerBlockY depth) 24 16
        (windowStartsIn (windowAt depth parent (firstBlock depth)) 10 24)
        ⟨8 + x, 3, .north⟩ :=
  auditedShiftedRoutesIn depth parent (firstBlock depth) x 10 24 2 8
    (leftmostWindows_complete _ (canonical_leftmost_mem depth parent))
    hx htarget hx interior

theorem auditedNextLeftRoutes
    (depth : Nat) (parent : Index) (x : Nat) (hx : x < 8)
    (interior : Signals.verticalInterior?
      (componentAt (iterateRefine 2
        (windowGrid (windowAt depth parent (firstBlock depth + 1)))) (8 + x) 3)
      (quadrantAt (8 + x) 3) ≠ none) :
    ShiftedBoundedRoute (oldGrid depth parent) (firstBlock depth + 1 - 1)
        (lowerBlockY depth) 24 16
        (windowStartsIn (windowAt depth parent (firstBlock depth + 1)) 2 24)
        ⟨8 + x, 3, .south⟩ ∨
      ShiftedBoundedRoute (oldGrid depth parent) (firstBlock depth + 1 - 1)
        (lowerBlockY depth) 24 16
        (windowStartsIn (windowAt depth parent (firstBlock depth + 1)) 2 24)
        ⟨8 + x, 3, .north⟩ :=
  auditedShiftedRoutesIn depth parent (firstBlock depth + 1) x 2 24 0 8
    (nextLeftWindows_complete _ (canonical_nextLeft_mem depth parent))
    hx (by omega) hx interior

theorem auditedRightmostRelevantRoutes
    (depth : Nat) (parent : Index) (x : Nat) (hx : x < 8)
    (interior : Signals.verticalInterior?
      (componentAt (iterateRefine 2
        (windowGrid (windowAt depth parent (lastRelevantBlock depth))))
        (8 + x) 3)
      (quadrantAt (8 + x) 3) ≠ none) :
    ShiftedBoundedRoute (oldGrid depth parent) (lastRelevantBlock depth - 1)
        (lowerBlockY depth) 24 16
        (windowStartsIn
          (windowAt depth parent (lastRelevantBlock depth)) 0 16)
        ⟨8 + x, 3, .south⟩ ∨
      ShiftedBoundedRoute (oldGrid depth parent) (lastRelevantBlock depth - 1)
        (lowerBlockY depth) 24 16
        (windowStartsIn
          (windowAt depth parent (lastRelevantBlock depth)) 0 16)
        ⟨8 + x, 3, .north⟩ :=
  auditedShiftedRoutesIn depth parent (lastRelevantBlock depth) x 0 16 0 8
    (rightmostRelevantWindows_complete _
      (canonical_rightmostRelevant_mem depth parent))
    hx (by omega) hx interior

/-- The finite quotient supplies a shifted route for every required target in
every recursive side-half window. -/
theorem auditedShiftedRoutes
    (depth : Nat) (parent : Index) (delta x : Nat)
    (hdelta : delta < blockCount depth) (hx : x < 8)
    (interior : Signals.verticalInterior?
      (componentAt (iterateRefine 2
        (windowGrid (windowAt depth parent (firstBlock depth + delta))))
        (8 + x) 3)
      (quadrantAt (8 + x) 3) ≠ none) :
    ShiftedBoundedRoute (oldGrid depth parent)
        (firstBlock depth + delta - 1) (lowerBlockY depth) 24 16
        (windowStarts (windowAt depth parent (firstBlock depth + delta)))
        ⟨8 + x, 3, .south⟩ ∨
      ShiftedBoundedRoute (oldGrid depth parent)
        (firstBlock depth + delta - 1) (lowerBlockY depth) 24 16
        (windowStarts (windowAt depth parent (firstBlock depth + delta)))
        ⟨8 + x, 3, .north⟩ := by
  let window := windowAt depth parent (firstBlock depth + delta)
  have hclosed : canonicalWindow window ∈ closedWindows :=
    canonicalWindow_windowAt_mem_closedWindows depth parent delta hdelta
  have checked := closedWindows_complete (canonicalWindow window) hclosed
  have hgrid : windowGrid (canonicalWindow window) =
      BorderSubstitution.canonicalizeGrid (windowGrid window) := by
    funext gridX gridY
    exact windowGrid_canonicalWindow window gridX gridY
  have same : SameComponents
      (iterateRefine 2 (windowGrid (canonicalWindow window)))
      (iterateRefine 2 (windowGrid window)) := by
    rw [hgrid]
    exact sameComponents_iterateRefine_canonicalizeGrid 2 (windowGrid window)
  have canonicalInterior : Signals.verticalInterior?
      (componentAt (iterateRefine 2 (windowGrid (canonicalWindow window)))
        (8 + x) 3)
      (quadrantAt (8 + x) 3) ≠ none := by
    rw [same (8 + x) 3]
    exact interior
  rcases windowCheck_sound checked x hx canonicalInterior with route | route
  · exact Or.inl (shiftedRoute_of_windowAt
      (route_of_canonicalWindow route))
  · exact Or.inr (shiftedRoute_of_windowAt
      (route_of_canonicalWindow route))

end SparseFreeLineSideHalfProjection
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
