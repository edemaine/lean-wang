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

open RedCycles RedShadeGraph RedShadeGraphRefinement RedShadeGraphSearchSoundness
  RedShadeGraphWeightedSearch RedShadeGraphTranslation RefinementTranslation
  Signals.FreeCellLocal
  BorderCoverageLocalAudit BorderGeometry SparseFreeLineLocalProjection
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
