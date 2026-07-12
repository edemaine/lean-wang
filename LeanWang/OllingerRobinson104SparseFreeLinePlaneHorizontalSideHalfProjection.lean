/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104SparseFreeLinePlaneHorizontalSideHalfClosure
import LeanWang.OllingerRobinson104SparseFreeLinePlaneSideHalfProjection

/-!
# Transporting horizontal side-half windows to recursive boards

The finite audit runs on canonical border-state windows. This module transports
its bounded routes to the corresponding 104-symbol window and then to the
actual shifted recursive grid, with every retained-column start backed by the
old live-column certificate.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace SparseFreeLinePlaneHorizontalSideHalfProjection

open RedCycles RedShadeCycles RedShadeGraph RedShadeGraphRefinement
  RedShadeGraphSearchSoundness
  RedShadeGraphWeightedSearch RedShadeGraphTranslation RefinementTranslation
  Signals.FreeCellLocal
  BorderCoverageLocalAudit BorderGeometry SparseFreeLineLocalProjection
  ShadedFreeLinePatternRefinement ShadedFreeLineProjectionCandidates
  ShadedFreeLineRecurrence
  SparseFreeLineHorizontalSideHalfAudit
  SparseFreeLinePlaneHorizontalSideHalfClosure

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

theorem columnStarts_congr
    {first second : Index} (kind : SourceKind) (sourceX : Nat)
    (same : ∀ port, portPresent (coarseGrid first) port =
      portPresent (coarseGrid second) port) :
    columnStarts first kind sourceX = columnStarts second kind sourceX := by
  unfold columnStarts
  exact weightedSparseStarts_congr kind _ same

theorem columnStarts_canonicalIndex (parent : Index) (kind : SourceKind)
    (sourceX : Nat) :
    columnStarts (BorderSubstitution.canonicalIndex parent) kind sourceX =
      columnStarts parent kind sourceX := by
  have same : SameComponents
      (coarseGrid (BorderSubstitution.canonicalIndex parent))
      (coarseGrid parent) := by
    intro x y
    unfold coarseGrid componentAt
    simpa only [RedCycles.indexThick_eq] using
      BorderSubstitution.indexThick_canonicalIndex parent
  exact columnStarts_congr kind sourceX (portPresent_congr same)

theorem windowStarts_canonicalWindow (window : Window) :
    windowStarts (canonicalWindow window) = windowStarts window := by
  unfold windowStarts
  apply List.flatMap_congr
  intro y _
  rw [windowGrid_canonicalWindow, columnStarts_canonicalIndex]

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

theorem sameComponents_windowAt_shift
    (depth : Nat) (grid : Nat → Nat → Index) (blockY : Nat) :
    ∀ x y, x < 16 → y < 24 →
      componentAt
          (iterateRefine 2 (windowGrid (windowAt depth grid blockY))) x y =
        componentAt
          (iterateRefine 2
            (shiftGrid (oldGrid depth grid) (lowerBlockX depth)
              (blockY - 1))) x y := by
  intro x y hx hy
  apply SparseFreeLinePlaneSideHalfProjection.componentAt_iterateRefine_two_congr_at
  rw [windowGrid_windowAt]
  · simp [shiftGrid]
  · omega
  · omega

/-- A route in an actual horizontal side-half window is a route in the
corresponding shifted recursive board neighborhood. -/
theorem shiftedRoute_of_windowAt
    {depth : Nat} {grid : Nat → Nat → Index} {blockY : Nat}
    {starts : List WeightedStart} {target : Port}
    (route : BoundedRouteIn
      (iterateRefine 2 (windowGrid (windowAt depth grid blockY)))
      16 24 starts target) :
    ShiftedBoundedRoute (oldGrid depth grid) (lowerBlockX depth)
      (blockY - 1) 16 24 starts target := by
  have same := sameComponents_windowAt_shift depth grid blockY
  rcases route with ⟨start, hstart, path, targetLive⟩
  have htarget := path.second_inBounds
  refine ⟨start, hstart,
    BoundedPath.congr_of_component_eq same path, ?_⟩
  simp only [portPresent] at targetLive ⊢
  rw [← same target.x target.y htarget.1 htarget.2]
  exact targetLive

theorem shiftedRouteIn_of_windowAt
    {depth : Nat} {grid : Nat → Nat → Index} {blockY lower upper : Nat}
    {target : Port}
    (route : RouteIn (windowAt depth grid blockY) lower upper target) :
    ShiftedBoundedRoute (oldGrid depth grid) (lowerBlockX depth)
      (blockY - 1) 16 24
      (windowStartsIn (windowAt depth grid blockY) lower upper) target := by
  exact shiftedRoute_of_windowAt route

theorem columnStart_mem_alignedSelf
    {grid : Index} {start : WeightedStart}
    (hstart : start ∈ columnStarts grid .retained 1) :
    start ∈ alignedColumnStarts grid 1 start.port.y := by
  rcases mem_columnStarts_retained hstart with
    ⟨sourceY, hsourceY, hparity, endpoint⟩
  rcases endpoint with ⟨hport, hlive⟩ | ⟨hport, hlive⟩
  · rw [alignedColumnStarts, weightedSparseStarts, List.mem_map]
    refine ⟨⟨1, sourceY, .west⟩, ?_, ?_⟩
    · simp only [List.mem_filter]
      constructor
      · rw [List.mem_flatMap]
        refine ⟨sourceY, ?_, by simp [columnSourcePorts]⟩
        simp only [List.mem_filter, List.mem_range]
        refine ⟨hsourceY, ?_⟩
        rw [hport]
        simp [sparsePort]
      · exact hlive
    · cases start
      simp_all [SourceKind.parity]
  · rw [alignedColumnStarts, weightedSparseStarts, List.mem_map]
    refine ⟨⟨1, sourceY, .east⟩, ?_, ?_⟩
    · simp only [List.mem_filter]
      constructor
      · rw [List.mem_flatMap]
        refine ⟨sourceY, ?_, by simp [columnSourcePorts]⟩
        simp only [List.mem_filter, List.mem_range]
        refine ⟨hsourceY, ?_⟩
        rw [hport]
        simp [sparsePort]
      · exact hlive
    · cases start
      simp_all [SourceKind.parity]

theorem windowStartsIn_backed
    (depth : Nat) (grid : Nat → Nat → Index) (blockY lower upper : Nat)
    (column : LiveColumnCertificate (oldGrid depth grid)
      (west .odd (depth + 1)) (east .odd (depth + 1))
      (west .odd (depth + 1)) (east .odd (depth + 1)) (oldColumn depth))
    (hwindowSouth : quarterSouth (4 * west .odd (depth + 1)) <
      8 * (blockY - 1) + lower)
    (hwindowNorth : 8 * (blockY - 1) + upper ≤
      quarterNorth (4 * east .odd (depth + 1))) :
    SparseFreeLinePlaneSideHalfProjection.StartsBacked
      (grid := oldGrid depth grid)
      (west := west .odd (depth + 1)) (east := east .odd (depth + 1))
      (south := west .odd (depth + 1)) (north := east .odd (depth + 1))
      (lowerBlockX depth) (blockY - 1)
      (windowStartsIn (windowAt depth grid blockY) lower upper) := by
  intro start hstart
  rw [windowStartsIn, List.mem_filter] at hstart
  rcases hstart with ⟨hstart, hbounds⟩
  rw [windowStarts, List.mem_flatMap] at hstart
  rcases hstart with ⟨macroY, hmacroY, hstart⟩
  simp only [List.mem_range] at hmacroY
  rcases List.mem_map.1 hstart with ⟨localStart, hlocalStart, rfl⟩
  have hgrid := windowGrid_windowAt depth grid blockY 1 macroY
    (by decide) hmacroY
  rw [hgrid] at hlocalStart
  have hlower : lowerBlockX depth + 1 = oldColumn depth / 2 := by
    rw [lowerBlockX, oldColumn_eq]
    have hpower : 0 < 4 ^ depth := pow_pos (by decide) depth
    omega
  rw [hlower] at hlocalStart
  have hodd : oldColumn depth % 2 = 1 := by
    rw [oldColumn_eq]
    omega
  have hlocalParity : localStart.parity = true := by
    rcases mem_columnStarts_retained hlocalStart with
      ⟨_, _, parity, _⟩
    exact parity
  simp only [Bool.and_eq_true, decide_eq_true_eq, translateStart,
    translatePort] at hbounds
  let globalBlock := blockY - 1 + macroY
  have hsouthFine : quarterSouth (4 * west .odd (depth + 1)) <
      8 * globalBlock + localStart.port.y := by
    dsimp [globalBlock]
    omega
  have hnorthFine : 8 * globalBlock + localStart.port.y <
      quarterNorth (4 * east .odd (depth + 1)) := by
    dsimp [globalBlock]
    omega
  rcases alignedColumnStart_backed column hodd globalBlock localStart.port.y
      hsouthFine hnorthFine (columnStart_mem_alignedSelf hlocalStart) with
    ⟨candidate, candidateOdd, candidateBacked, coordinate⟩
  refine ⟨candidate, candidateBacked, ?_, ?_⟩
  · rw [← coordinate]
    simp only [translateStart, translatePort]
    dsimp [globalBlock]
    congr 1 <;> omega
  · simpa only [hlocalParity, candidateOdd]

theorem windowStartsIn_all (window : Window) :
    windowStartsIn window 0 24 = windowStarts window := by
  unfold windowStartsIn
  apply List.filter_eq_self.2
  intro start hstart
  have bounded := windowStarts_inBounds window start hstart
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨Nat.zero_le _, bounded.2⟩

theorem projectsTo_of_windowRoute
    (depth : Nat) (grid : Nat → Nat → Index) (blockY lower upper : Nat)
    (column : LiveColumnCertificate (oldGrid depth grid)
      (west .odd (depth + 1)) (east .odd (depth + 1))
      (west .odd (depth + 1)) (east .odd (depth + 1)) (oldColumn depth))
    (hwindowSouth : quarterSouth (4 * west .odd (depth + 1)) <
      8 * (blockY - 1) + lower)
    (hwindowNorth : 8 * (blockY - 1) + upper ≤
      quarterNorth (4 * east .odd (depth + 1)))
    {target : Port}
    (route : ShiftedBoundedRoute (oldGrid depth grid) (lowerBlockX depth)
      (blockY - 1) 16 24
      (windowStartsIn (windowAt depth grid blockY) lower upper) target) :
    Nonempty (ProjectsTo (grid := oldGrid depth grid)
      (west := west .odd (depth + 1)) (east := east .odd (depth + 1))
      (south := west .odd (depth + 1)) (north := east .odd (depth + 1))
      (translatePort target (8 * lowerBlockX depth)
        (8 * (blockY - 1)))) := by
  exact SparseFreeLinePlaneSideHalfProjection.projectsTo_of_shiftedRoute_of_backedStarts
    (lowerBlockX depth) (blockY - 1) 16 24
    (windowStartsIn_backed depth grid blockY lower upper column
      hwindowSouth hwindowNorth) route

theorem auditedShiftedRoutesIn
    (depth : Nat) (grid : Nat → Nat → Index) (blockY y lower upper
      targetLower targetUpper : Nat)
    (hcheck : windowCheckIn (canonicalWindow (windowAt depth grid blockY))
      lower upper targetLower targetUpper = true)
    (hy : y < 8) (htargetLower : targetLower ≤ y)
    (htargetUpper : y < targetUpper)
    (interior : Signals.horizontalInterior?
      (componentAt (iterateRefine 2
        (windowGrid (windowAt depth grid blockY))) 3 (8 + y))
      (quadrantAt 3 (8 + y)) ≠ none) :
    ShiftedBoundedRoute (oldGrid depth grid) (lowerBlockX depth)
        (blockY - 1) 16 24
        (windowStartsIn (windowAt depth grid blockY) lower upper)
        ⟨3, 8 + y, .west⟩ ∨
      ShiftedBoundedRoute (oldGrid depth grid) (lowerBlockX depth)
        (blockY - 1) 16 24
        (windowStartsIn (windowAt depth grid blockY) lower upper)
        ⟨3, 8 + y, .east⟩ := by
  let window := windowAt depth grid blockY
  have hgrid : windowGrid (canonicalWindow window) =
      BorderSubstitution.canonicalizeGrid (windowGrid window) := by
    funext gridX gridY
    exact windowGrid_canonicalWindow window gridX gridY
  have same : SameComponents
      (iterateRefine 2 (windowGrid (canonicalWindow window)))
      (iterateRefine 2 (windowGrid window)) := by
    rw [hgrid]
    exact sameComponents_iterateRefine_canonicalizeGrid 2 (windowGrid window)
  have canonicalInterior : Signals.horizontalInterior?
      (componentAt (iterateRefine 2 (windowGrid (canonicalWindow window)))
        3 (8 + y))
      (quadrantAt 3 (8 + y)) ≠ none := by
    rw [same 3 (8 + y)]
    exact interior
  rcases windowCheckIn_sound hcheck y hy htargetLower htargetUpper
      canonicalInterior with route | route
  · exact Or.inl (shiftedRouteIn_of_windowAt
      (routeIn_of_canonicalWindow route))
  · exact Or.inr (shiftedRouteIn_of_windowAt
      (routeIn_of_canonicalWindow route))

theorem auditedBottommostRoutes
    (depth : Nat) (grid : Nat → Nat → Index) (y : Nat) (hy : y < 8) (htarget : 2 ≤ y)
    (interior : Signals.horizontalInterior?
      (componentAt (iterateRefine 2
        (windowGrid (windowAt depth grid (firstBlock depth)))) 3 (8 + y))
      (quadrantAt 3 (8 + y)) ≠ none) :
    ShiftedBoundedRoute (oldGrid depth grid) (lowerBlockX depth)
        (firstBlock depth - 1) 16 24
        (windowStartsIn (windowAt depth grid (firstBlock depth)) 10 24)
        ⟨3, 8 + y, .west⟩ ∨
      ShiftedBoundedRoute (oldGrid depth grid) (lowerBlockX depth)
        (firstBlock depth - 1) 16 24
        (windowStartsIn (windowAt depth grid (firstBlock depth)) 10 24)
        ⟨3, 8 + y, .east⟩ :=
  auditedShiftedRoutesIn depth grid (firstBlock depth) y 10 24 2 8
    (bottommostWindows_complete _ (canonical_bottommost_mem depth grid))
    hy htarget hy interior

theorem auditedNextBottomRoutes
    (depth : Nat) (grid : Nat → Nat → Index) (y : Nat) (hy : y < 8)
    (interior : Signals.horizontalInterior?
      (componentAt (iterateRefine 2
        (windowGrid (windowAt depth grid (firstBlock depth + 1)))) 3 (8 + y))
      (quadrantAt 3 (8 + y)) ≠ none) :
    ShiftedBoundedRoute (oldGrid depth grid) (lowerBlockX depth)
        (firstBlock depth + 1 - 1) 16 24
        (windowStartsIn (windowAt depth grid (firstBlock depth + 1)) 2 24)
        ⟨3, 8 + y, .west⟩ ∨
      ShiftedBoundedRoute (oldGrid depth grid) (lowerBlockX depth)
        (firstBlock depth + 1 - 1) 16 24
        (windowStartsIn (windowAt depth grid (firstBlock depth + 1)) 2 24)
        ⟨3, 8 + y, .east⟩ :=
  auditedShiftedRoutesIn depth grid (firstBlock depth + 1) y 2 24 0 8
    (nextBottomWindows_complete _ (canonical_nextBottom_mem depth grid))
    hy (by omega) hy interior

theorem auditedTopmostRelevantRoutes
    (depth : Nat) (grid : Nat → Nat → Index) (y : Nat) (hy : y < 8)
    (interior : Signals.horizontalInterior?
      (componentAt (iterateRefine 2
        (windowGrid (windowAt depth grid (lastRelevantBlock depth))))
        3 (8 + y))
      (quadrantAt 3 (8 + y)) ≠ none) :
    ShiftedBoundedRoute (oldGrid depth grid) (lowerBlockX depth)
        (lastRelevantBlock depth - 1) 16 24
        (windowStartsIn
          (windowAt depth grid (lastRelevantBlock depth)) 0 16)
        ⟨3, 8 + y, .west⟩ ∨
      ShiftedBoundedRoute (oldGrid depth grid) (lowerBlockX depth)
        (lastRelevantBlock depth - 1) 16 24
        (windowStartsIn
          (windowAt depth grid (lastRelevantBlock depth)) 0 16)
        ⟨3, 8 + y, .east⟩ :=
  auditedShiftedRoutesIn depth grid (lastRelevantBlock depth) y 0 16 0 8
    (topmostRelevantWindows_complete _
      (canonical_topmostRelevant_mem depth grid))
    hy (by omega) hy interior

/-- The finite quotient supplies a shifted route for every required target in
every recursive horizontal side-half window. -/
theorem auditedShiftedRoutes
    (depth : Nat) (grid : Nat → Nat → Index) (delta y : Nat)
    (hdelta : delta < blockCount depth) (hy : y < 8)
    (interior : Signals.horizontalInterior?
      (componentAt (iterateRefine 2
        (windowGrid (windowAt depth grid (firstBlock depth + delta))))
        3 (8 + y))
      (quadrantAt 3 (8 + y)) ≠ none) :
    ShiftedBoundedRoute (oldGrid depth grid) (lowerBlockX depth)
        (firstBlock depth + delta - 1) 16 24
        (windowStarts (windowAt depth grid (firstBlock depth + delta)))
        ⟨3, 8 + y, .west⟩ ∨
      ShiftedBoundedRoute (oldGrid depth grid) (lowerBlockX depth)
        (firstBlock depth + delta - 1) 16 24
        (windowStarts (windowAt depth grid (firstBlock depth + delta)))
        ⟨3, 8 + y, .east⟩ := by
  let window := windowAt depth grid (firstBlock depth + delta)
  have hclosed : canonicalWindow window ∈ closedWindows :=
    canonicalWindow_windowAt_mem_closedWindows depth grid delta hdelta
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
  have canonicalInterior : Signals.horizontalInterior?
      (componentAt (iterateRefine 2 (windowGrid (canonicalWindow window)))
        3 (8 + y))
      (quadrantAt 3 (8 + y)) ≠ none := by
    rw [same 3 (8 + y)]
    exact interior
  rcases windowCheck_sound checked y hy canonicalInterior with route | route
  · exact Or.inl (shiftedRoute_of_windowAt
      (route_of_canonicalWindow route))
  · exact Or.inr (shiftedRoute_of_windowAt
      (route_of_canonicalWindow route))

theorem nextOldColumn_eq (depth : Nat) :
    oldColumn (depth + 1) = 8 * lowerBlockX depth + 3 := by
  rw [oldColumn_eq, lowerBlockX_eq, pow_succ]
  omega

set_option maxHeartbeats 2000000 in
-- The four boundary/interior branches normalize large dependent route types.
/-- The odd pivot-extra column recurs from one side-half layer to the next. -/
theorem horizontalProjection_nextOldColumn
    (depth : Nat) (grid : Nat → Nat → Index)
    (column : LiveColumnCertificate (oldGrid depth grid)
      (west .odd (depth + 1)) (east .odd (depth + 1))
      (west .odd (depth + 1)) (east .odd (depth + 1)) (oldColumn depth)) :
    HorizontalProjectionAt (oldGrid depth grid)
      (west .odd (depth + 1)) (east .odd (depth + 1))
      (west .odd (depth + 1)) (east .odd (depth + 1))
      (oldColumn (depth + 1)) := by
  intro targetY hsouth hnorth interior
  let blockY := targetY / 8
  let localY := targetY % 8
  have hlocalY : localY < 8 := Nat.mod_lt _ (by decide)
  have htargetY : 8 * blockY + localY = targetY := by
    have hdecompose := Nat.mod_add_div targetY 8
    dsimp [blockY, localY]
    omega
  have htargetX : 8 * lowerBlockX depth + 3 = oldColumn (depth + 1) :=
    (nextOldColumn_eq depth).symm
  have hsouthEq : west .odd (depth + 1) = firstBlock depth := by
    rw [firstBlock_eq]
    simp [west, scale, Phase.factor, pow_succ]
    omega
  have hnorthEq : east .odd (depth + 1) = 3 * firstBlock depth := by
    rw [firstBlock_eq]
    simp [east, scale, Phase.factor, pow_succ]
    omega
  have hfirstPositive : 0 < firstBlock depth := by
    rw [firstBlock_eq]
    positivity
  have hfirstEight : 8 ≤ firstBlock depth := by
    rw [firstBlock_eq]
    have hpower : 0 < 4 ^ depth := pow_pos (by decide) depth
    omega
  have hblockLower : firstBlock depth ≤ blockY := by
    rw [hsouthEq, quarterSouth] at hsouth
    omega
  have hblockUpper : blockY < 3 * firstBlock depth := by
    rw [hnorthEq, quarterNorth] at hnorth
    omega
  have hlastRelevant : lastRelevantBlock depth = 3 * firstBlock depth - 1 := by
    rw [lastRelevantBlock_eq, firstBlock_eq]
    omega
  have hblockRelevant : blockY ≤ lastRelevantBlock depth := by
    rw [hlastRelevant]
    omega
  have htranslatedY : 8 * (blockY - 1) + (8 + localY) = targetY := by
    omega
  have localInterior : Signals.horizontalInterior?
      (componentAt (iterateRefine 2
        (windowGrid (windowAt depth grid blockY))) 3 (8 + localY))
      (quadrantAt 3 (8 + localY)) ≠ none := by
    have hcomponent := componentAt_iterateRefine_shift 2 (oldGrid depth grid)
      (lowerBlockX depth) (blockY - 1) 3 (8 + localY)
    norm_num at hcomponent
    have hsame := sameComponents_windowAt_shift depth grid blockY
      3 (8 + localY) (by omega) (by omega)
    have hquadrant := quadrantAt_shift 8 (lowerBlockX depth) (blockY - 1)
      3 (8 + localY) (by decide)
    rw [hsame, hcomponent, htargetX, htranslatedY]
    rw [← hquadrant]
    simpa [htargetX, htranslatedY] using interior
  by_cases hbottommost : blockY = firstBlock depth
  · rw [hbottommost] at localInterior htargetY htranslatedY
    have htargetLower : 2 ≤ localY := by
      rw [hsouthEq, quarterSouth] at hsouth
      omega
    have hwindowSouth : quarterSouth (4 * west .odd (depth + 1)) <
        8 * (firstBlock depth - 1) + 10 := by
      rw [hsouthEq, quarterSouth]
      omega
    have hwindowNorth : 8 * (firstBlock depth - 1) + 24 ≤
        quarterNorth (4 * east .odd (depth + 1)) := by
      rw [hnorthEq, quarterNorth]
      omega
    rcases auditedBottommostRoutes depth grid localY hlocalY htargetLower
        localInterior with route | route
    · left
      simpa [translatePort, htargetX, htranslatedY] using
        projectsTo_of_windowRoute depth grid (firstBlock depth) 10 24 column
          hwindowSouth hwindowNorth route
    · right
      simpa [translatePort, htargetX, htranslatedY] using
        projectsTo_of_windowRoute depth grid (firstBlock depth) 10 24 column
          hwindowSouth hwindowNorth route
  · by_cases hnextBottom : blockY = firstBlock depth + 1
    · rw [hnextBottom] at localInterior htargetY htranslatedY
      have hnextY : 8 * firstBlock depth + (8 + localY) = targetY := by
        omega
      have hwindowSouth : quarterSouth (4 * west .odd (depth + 1)) <
          8 * (firstBlock depth + 1 - 1) + 2 := by
        rw [hsouthEq, quarterSouth]
        omega
      have hwindowNorth : 8 * (firstBlock depth + 1 - 1) + 24 ≤
          quarterNorth (4 * east .odd (depth + 1)) := by
        rw [hnorthEq, quarterNorth]
        omega
      rcases auditedNextBottomRoutes depth grid localY hlocalY localInterior with
        route | route
      · left
        simpa [translatePort, htargetX, hnextY] using
          projectsTo_of_windowRoute depth grid (firstBlock depth + 1) 2 24
            column hwindowSouth hwindowNorth route
      · right
        simpa [translatePort, htargetX, hnextY] using
          projectsTo_of_windowRoute depth grid (firstBlock depth + 1) 2 24
            column hwindowSouth hwindowNorth route
    · by_cases htop : blockY = lastRelevantBlock depth
      · rw [htop] at localInterior htargetY htranslatedY
        have hwindowSouth : quarterSouth (4 * west .odd (depth + 1)) <
            8 * (lastRelevantBlock depth - 1) := by
          rw [hsouthEq, quarterSouth, hlastRelevant]
          omega
        have hwindowNorth : 8 * (lastRelevantBlock depth - 1) + 16 ≤
            quarterNorth (4 * east .odd (depth + 1)) := by
          rw [hnorthEq, quarterNorth, hlastRelevant]
          omega
        rcases auditedTopmostRelevantRoutes depth grid localY hlocalY
            localInterior with route | route
        · left
          simpa [translatePort, htargetX, htranslatedY] using
            projectsTo_of_windowRoute depth grid (lastRelevantBlock depth)
              0 16 column hwindowSouth hwindowNorth route
        · right
          simpa [translatePort, htargetX, htranslatedY] using
            projectsTo_of_windowRoute depth grid (lastRelevantBlock depth)
              0 16 column hwindowSouth hwindowNorth route
      · let delta := blockY - firstBlock depth
        have hblockEq : firstBlock depth + delta = blockY := by
          dsimp [delta]
          omega
        have hdelta : delta < blockCount depth := by
          rw [blockCount_eq]
          dsimp [delta]
          rw [firstBlock_eq] at hblockUpper hblockLower
          omega
        have hwindowSouth : quarterSouth (4 * west .odd (depth + 1)) <
            8 * (blockY - 1) := by
          rw [hsouthEq, quarterSouth]
          omega
        have hwindowNorth : 8 * (blockY - 1) + 24 ≤
            quarterNorth (4 * east .odd (depth + 1)) := by
          rw [hnorthEq, quarterNorth]
          rw [hlastRelevant] at htop hblockRelevant
          omega
        have routes := auditedShiftedRoutes depth grid delta localY hdelta
          hlocalY (by simpa [hblockEq] using localInterior)
        rcases routes with route | route
        · left
          have projected := projectsTo_of_windowRoute depth grid blockY 0 24
            column hwindowSouth hwindowNorth (by
              simpa [hblockEq, windowStartsIn_all] using route)
          change Nonempty (ProjectsTo
            ⟨8 * lowerBlockX depth + 3,
              8 * (blockY - 1) + (8 + localY), .west⟩) at projected
          simpa only [htargetX, htranslatedY] using projected
        · right
          have projected := projectsTo_of_windowRoute depth grid blockY 0 24
            column hwindowSouth hwindowNorth (by
              simpa [hblockEq, windowStartsIn_all] using route)
          change Nonempty (ProjectsTo
            ⟨8 * lowerBlockX depth + 3,
              8 * (blockY - 1) + (8 + localY), .east⟩) at projected
          simpa only [htargetX, htranslatedY] using projected

end SparseFreeLinePlaneHorizontalSideHalfProjection
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
