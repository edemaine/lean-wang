/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104BorderSubstitution
import LeanWang.OllingerRobinson104ShadedFreeLineProjectionSourceLists

/-!
# Red-geometry invariance of the border substitution quotient

The shaded free-line search observes only the thick red component. This module
connects that observation to the 56-state thin/thick substitution quotient and
proves that erasing the black layer preserves all executable source data.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace BorderGeometry

open RedCycles RedShadeGraph RedShadeGraphCertificate RedShadeGraphRefinement
  RedShadeGraphSearch RedShadeGraphWeightedSearch
  ShadedFreeLineProjectionSourceLists Signals.FreeCellLocal

set_option maxRecDepth 20000

theorem componentAt_canonicalizeGrid (grid : Nat → Nat → Index) (x y : Nat) :
    componentAt (BorderSubstitution.canonicalizeGrid grid) x y =
      componentAt grid x y := by
  unfold componentAt
  simpa [RedCycles.indexThick_eq] using
    BorderSubstitution.indexThick_canonicalizeGrid grid (x / 2) (y / 2)

theorem ofIndexGrid_canonicalizeGrid (grid : Nat → Nat → Index) :
    BorderSubstitution.ofIndexGrid
        (BorderSubstitution.canonicalizeGrid grid) =
      BorderSubstitution.ofIndexGrid grid := by
  funext x y
  exact BorderSubstitution.indexState_canonicalIndex (grid x y)

theorem indexState_iterateRefine_canonicalizeGrid
    (depth : Nat) (grid : Nat → Nat → Index) (x y : Nat) :
    BorderSubstitution.indexState
        (iterateRefine depth (BorderSubstitution.canonicalizeGrid grid) x y) =
      BorderSubstitution.indexState (iterateRefine depth grid x y) := by
  calc
    BorderSubstitution.indexState
        (iterateRefine depth (BorderSubstitution.canonicalizeGrid grid) x y) =
        BorderSubstitution.iterateRefine depth
          (BorderSubstitution.ofIndexGrid
            (BorderSubstitution.canonicalizeGrid grid)) x y := by
      have equality := BorderSubstitution.ofIndexGrid_iterateRefine depth
        (BorderSubstitution.canonicalizeGrid grid)
      exact congrFun (congrFun equality x) y
    _ = BorderSubstitution.iterateRefine depth
          (BorderSubstitution.ofIndexGrid grid) x y := by
      rw [ofIndexGrid_canonicalizeGrid]
    _ = BorderSubstitution.indexState (iterateRefine depth grid x y) := by
      have equality := BorderSubstitution.ofIndexGrid_iterateRefine depth grid
      exact (congrFun (congrFun equality x) y).symm

theorem indexThick_iterateRefine_canonicalizeGrid
    (depth : Nat) (grid : Nat → Nat → Index) (x y : Nat) :
    indexThick
        (iterateRefine depth (BorderSubstitution.canonicalizeGrid grid) x y) =
      indexThick (iterateRefine depth grid x y) := by
  have equality := congrArg Prod.snd
    (indexState_iterateRefine_canonicalizeGrid depth grid x y)
  simpa [BorderSubstitution.indexState, RedCycles.indexThick_eq] using equality

theorem componentAt_iterateRefine_canonicalizeGrid
    (depth : Nat) (grid : Nat → Nat → Index) (x y : Nat) :
    componentAt
        (iterateRefine depth (BorderSubstitution.canonicalizeGrid grid)) x y =
      componentAt (iterateRefine depth grid) x y := by
  unfold componentAt
  simpa [RedCycles.indexThick_eq] using
    indexThick_iterateRefine_canonicalizeGrid depth grid (x / 2) (y / 2)

/-- The complete observation of an index grid made by red-graph search. -/
def SameComponents (first second : Nat → Nat → Index) : Prop :=
  ∀ x y, componentAt first x y = componentAt second x y

theorem link_congr_of_sameComponents
    {firstGrid secondGrid : Nat → Nat → Index}
    (same : SameComponents firstGrid secondGrid)
    {first second : Port} {parity : Bool}
    (link : Link firstGrid first second parity) :
    Link secondGrid first second parity := by
  induction link with
  | horizontalMatch x y => exact Link.horizontalMatch x y
  | verticalMatch x y => exact Link.verticalMatch x y
  | horizontal x y hpath =>
      exact Link.horizontal x y (by simpa [same x y] using hpath)
  | vertical x y hpath =>
      exact Link.vertical x y (by simpa [same x y] using hpath)
  | westNorth x y hwest hnorth =>
      exact Link.westNorth x y
        (by simpa [same x y] using hwest)
        (by simpa [same x y] using hnorth)
  | westSouth x y hwest hsouth =>
      exact Link.westSouth x y
        (by simpa [same x y] using hwest)
        (by simpa [same x y] using hsouth)
  | eastNorth x y heast hnorth =>
      exact Link.eastNorth x y
        (by simpa [same x y] using heast)
        (by simpa [same x y] using hnorth)
  | eastSouth x y heast hsouth =>
      exact Link.eastSouth x y
        (by simpa [same x y] using heast)
        (by simpa [same x y] using hsouth)
  | crossing x y hhorizontal hvertical =>
      exact Link.crossing x y
        (by simpa [same x y] using hhorizontal)
        (by simpa [same x y] using hvertical)
  | symm link ih => exact Link.symm ih

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

theorem sameComponents_canonicalizeGrid (grid : Nat → Nat → Index) :
    SameComponents (BorderSubstitution.canonicalizeGrid grid) grid :=
  componentAt_canonicalizeGrid grid

theorem sameComponents_iterateRefine_canonicalizeGrid
    (depth : Nat) (grid : Nat → Nat → Index) :
    SameComponents
      (iterateRefine depth (BorderSubstitution.canonicalizeGrid grid))
      (iterateRefine depth grid) :=
  componentAt_iterateRefine_canonicalizeGrid depth grid

theorem portPresent_congr
    {first second : Nat → Nat → Index} (same : SameComponents first second)
    (port : Port) :
    portPresent first port = portPresent second port := by
  simp only [portPresent, same port.x port.y]

theorem portPresent_canonicalizeGrid
    (grid : Nat → Nat → Index) (port : Port) :
    portPresent (BorderSubstitution.canonicalizeGrid grid) port =
      portPresent grid port := by
  exact portPresent_congr (sameComponents_canonicalizeGrid grid) port

theorem moveValid_congr
    {first second : Nat → Nat → Index} (same : SameComponents first second)
    (move : RedShadeGraphCertificate.Move) :
    RedShadeGraphCertificate.Move.valid first move =
      RedShadeGraphCertificate.Move.valid second move := by
  simp only [RedShadeGraphCertificate.Move.valid, same move.x move.y]

theorem moveValid_canonicalizeGrid
    (grid : Nat → Nat → Index) (move : RedShadeGraphCertificate.Move) :
    RedShadeGraphCertificate.Move.valid
        (BorderSubstitution.canonicalizeGrid grid) move =
      RedShadeGraphCertificate.Move.valid grid move := by
  exact moveValid_congr (sameComponents_canonicalizeGrid grid) move

theorem advance_congr
    {first second : Nat → Nat → Index} (same : SameComponents first second)
    (width height : Nat) (node : Node) (move : CertificateMove) :
    advance first width height node move =
      advance second width height node move := by
  unfold advance
  rw [moveValid_congr same]

theorem nextNodes_congr
    {first second : Nat → Nat → Index} (same : SameComponents first second)
    (width height : Nat) (node : Node) :
    nextNodes first width height node = nextNodes second width height node := by
  unfold nextNodes
  apply List.filterMap_congr
  intro move _
  exact advance_congr same width height node move

theorem exploreFastAux_congr
    {first second : Nat → Nat → Index} (same : SameComponents first second)
    (width height fuel : Nat) (stack : List Node) (visited : Array Bool)
    (found : List Node) :
    exploreFastAux first width height fuel stack visited found =
      exploreFastAux second width height fuel stack visited found := by
  induction fuel generalizing stack visited found with
  | zero => rfl
  | succ fuel ih =>
      cases stack with
      | nil => rfl
      | cons node stack =>
          simp only [exploreFastAux]
          rw [nextNodes_congr same]
          exact ih _ _ _

theorem exploreFastWeighted_congr
    {first second : Nat → Nat → Index} (same : SameComponents first second)
    (width height fuel : Nat) (starts : List WeightedStart) :
    exploreFastWeighted first width height fuel starts =
      exploreFastWeighted second width height fuel starts := by
  unfold exploreFastWeighted
  exact exploreFastAux_congr same width height fuel _ _ _

theorem advanceReach_congr
    {first second : Nat → Nat → Index} (same : SameComponents first second)
    (width height : Nat) (node : ReachNode) (move : CertificateMove) :
    advanceReach first width height node move =
      advanceReach second width height node move := by
  unfold advanceReach
  rw [moveValid_congr same]

theorem nextReachNodes_congr
    {first second : Nat → Nat → Index} (same : SameComponents first second)
    (width height : Nat) (node : ReachNode) :
    nextReachNodes first width height node =
      nextReachNodes second width height node := by
  unfold nextReachNodes
  apply List.filterMap_congr
  intro move _
  exact advanceReach_congr same width height node move

theorem exploreWeightedReachAux_congr
    {first second : Nat → Nat → Index} (same : SameComponents first second)
    (width height fuel : Nat) (stack : List ReachNode) (visited : Array Bool)
    (found : List ReachNode) :
    exploreWeightedReachAux first width height fuel stack visited found =
      exploreWeightedReachAux second width height fuel stack visited found := by
  induction fuel generalizing stack visited found with
  | zero => rfl
  | succ fuel ih =>
      cases stack with
      | nil => rfl
      | cons node stack =>
          simp only [exploreWeightedReachAux]
          rw [nextReachNodes_congr same]
          exact ih _ _ _

theorem exploreFastWeightedReach_congr
    {first second : Nat → Nat → Index} (same : SameComponents first second)
    (width height fuel : Nat) (starts : List WeightedStart) :
    exploreFastWeightedReach first width height fuel starts =
      exploreFastWeightedReach second width height fuel starts := by
  unfold exploreFastWeightedReach
  exact exploreWeightedReachAux_congr same width height fuel _ _ _

theorem rowPorts_congr
    {first second : Nat → Nat → Index} (same : SameComponents first second)
    (west east row : Nat) :
    rowPorts first west east row = rowPorts second west east row := by
  unfold rowPorts
  apply List.flatMap_congr
  intro x _
  rw [same x row]
  split
  · apply List.filter_congr
    intro port _
    exact portPresent_congr same port
  · rfl

theorem columnPorts_congr
    {first second : Nat → Nat → Index} (same : SameComponents first second)
    (south north column : Nat) :
    columnPorts first south north column =
      columnPorts second south north column := by
  unfold columnPorts
  apply List.flatMap_congr
  intro y _
  rw [same column y]
  split
  · apply List.filter_congr
    intro port _
    exact portPresent_congr same port
  · rfl

theorem patternCandidates_congr
    {first second : Nat → Nat → Index} (same : SameComponents first second)
    (west east south north : Nat) (offsets : List Nat)
    (coordinate : Nat → Nat) :
    patternCandidates first west east south north offsets coordinate =
      patternCandidates second west east south north offsets coordinate := by
  simp only [patternCandidates, rowPorts_congr same,
    columnPorts_congr same]

theorem rowPorts_canonicalizeGrid
    (grid : Nat → Nat → Index) (west east row : Nat) :
    rowPorts (BorderSubstitution.canonicalizeGrid grid) west east row =
      rowPorts grid west east row := by
  exact rowPorts_congr (sameComponents_canonicalizeGrid grid) west east row

theorem columnPorts_canonicalizeGrid
    (grid : Nat → Nat → Index) (south north column : Nat) :
    columnPorts (BorderSubstitution.canonicalizeGrid grid) south north column =
      columnPorts grid south north column := by
  exact columnPorts_congr (sameComponents_canonicalizeGrid grid)
    south north column

theorem patternCandidates_canonicalizeGrid
    (grid : Nat → Nat → Index) (west east south north : Nat)
    (offsets : List Nat) (coordinate : Nat → Nat) :
    patternCandidates (BorderSubstitution.canonicalizeGrid grid)
        west east south north offsets coordinate =
      patternCandidates grid west east south north offsets coordinate := by
  exact patternCandidates_congr (sameComponents_canonicalizeGrid grid)
    west east south north offsets coordinate

end BorderGeometry
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
