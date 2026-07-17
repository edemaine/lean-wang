/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.PairCoverSeamCreatedAdjacentFullAuditDefs
import LeanWang.Robinson.Closed104.RedShadeGraphWeightedReachBounded

/-!
# Parallel targets near far created sources

A query separated from a created source by at least one complete depth-two
macrocell only needs a parallel target near the source.  Any such target on
the query-facing side is automatically strictly between the source and query.
The checks below ask for that local even path in every realizable adjacent
two-cell window.
-/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamCreatedFarParallelAudit

open RedCycles RedShadeCycles RedShadeGraph RedShadeGraphSearchSoundness
  RedShadeGraphWeightedSearch
  RedShadeGraphWeightedReachBounded
  PairCoverSeamPathSearch PairCoverSeamShadePaths
  PairCoverSeamCreatedAdjacentAudit Signals.FreeCellLocal

set_option maxRecDepth 20000

def horizontalParallelCheck (grid : Nat → Nat → Index)
    (width height fuel column query boundary : Nat) : Bool :=
  (exploreFastWeightedReach grid width height fuel
    [⟨horizontalPort grid column boundary, false⟩]).any fun node =>
      !node.parity &&
        horizontalBetweenTarget grid column query boundary node.current

def verticalParallelCheck (grid : Nat → Nat → Index)
    (width height fuel row query boundary : Nat) : Bool :=
  (exploreFastWeightedReach grid width height fuel
    [⟨verticalPort grid boundary row, false⟩]).any fun node =>
      !node.parity &&
        verticalBetweenTarget grid row query boundary node.current

def checkVerticalPair (pair : PairState) : Bool :=
  let grid := iterateRefine 2 (verticalGrid pair)
  (List.range 8).all fun column => createdCoordinates.all fun localBoundary =>
    let upperBoundary := 8 + localBoundary
    let lowerInterior := Signals.horizontalInterior?
      (componentAt grid column localBoundary) (quadrantAt column localBoundary)
    let upperInterior := Signals.horizontalInterior?
      (componentAt grid column upperBoundary) (quadrantAt column upperBoundary)
    (!decide (lowerInterior = some .north) ||
      horizontalParallelCheck grid 8 16 1025 column 16 localBoundary) &&
    (!decide (upperInterior = some .south) ||
      horizontalParallelCheck grid 8 16 1025 column 0 upperBoundary)

def checkHorizontalPair (pair : PairState) : Bool :=
  let grid := iterateRefine 2 (horizontalGrid pair)
  (List.range 8).all fun row => createdCoordinates.all fun localBoundary =>
    let rightBoundary := 8 + localBoundary
    let leftInterior := Signals.verticalInterior?
      (componentAt grid localBoundary row) (quadrantAt localBoundary row)
    let rightInterior := Signals.verticalInterior?
      (componentAt grid rightBoundary row) (quadrantAt rightBoundary row)
    (!decide (leftInterior = some .east) ||
      verticalParallelCheck grid 16 8 1025 row 16 localBoundary) &&
    (!decide (rightInterior = some .west) ||
      verticalParallelCheck grid 16 8 1025 row 0 rightBoundary)

def chunkSize : Nat := 32

def verticalChunk (chunk : Nat) : List PairState :=
  (verticalPairs.drop (chunkSize * chunk)).take chunkSize

def horizontalChunk (chunk : Nat) : List PairState :=
  (horizontalPairs.drop (chunkSize * chunk)).take chunkSize

theorem horizontalParallelCheck_sound
    {grid : Nat → Nat → Index}
    {width height fuel column query boundary : Nat}
    (startBound : PortInBounds
      (horizontalPort grid column boundary) width height)
    (checked : horizontalParallelCheck grid width height fuel
      column query boundary = true) :
    ∃ targetY,
      StrictBetween query boundary targetY ∧
      Signals.horizontalInterior?
        (componentAt grid column targetY) (quadrantAt column targetY) ≠ none ∧
      BoundedPath grid width height (horizontalPort grid column boundary)
        (horizontalPort grid column targetY) false := by
  simp only [horizontalParallelCheck, List.any_eq_true,
    Bool.and_eq_true] at checked
  rcases checked with ⟨node, nodeMember, parity, target⟩
  have sound := exploreFastWeightedReach_bounded_sound
    (starts := [⟨horizontalPort grid column boundary, false⟩])
    (by
      intro start startMember
      simp only [List.mem_singleton] at startMember
      subst start
      exact startBound)
    nodeMember
  rcases sound with ⟨start, startMember, path⟩
  simp only [List.mem_singleton] at startMember
  subst start
  have nodeParity : node.parity = false :=
    Bool.eq_false_of_not_eq_true' parity
  have pathFalse : BoundedPath grid width height
      (horizontalPort grid column boundary) node.current false := by
    simpa [nodeParity] using path
  simp only [horizontalBetweenTarget, Bool.and_eq_true,
    decide_eq_true_eq] at target
  refine ⟨node.current.y, target.1.1.1,
    Option.isSome_iff_ne_none.mp target.2, ?_⟩
  rw [← target.1.2]
  exact pathFalse

theorem verticalParallelCheck_sound
    {grid : Nat → Nat → Index}
    {width height fuel row query boundary : Nat}
    (startBound : PortInBounds
      (verticalPort grid boundary row) width height)
    (checked : verticalParallelCheck grid width height fuel
      row query boundary = true) :
    ∃ targetX,
      StrictBetween query boundary targetX ∧
      Signals.verticalInterior?
        (componentAt grid targetX row) (quadrantAt targetX row) ≠ none ∧
      BoundedPath grid width height (verticalPort grid boundary row)
        (verticalPort grid targetX row) false := by
  simp only [verticalParallelCheck, List.any_eq_true,
    Bool.and_eq_true] at checked
  rcases checked with ⟨node, nodeMember, parity, target⟩
  have sound := exploreFastWeightedReach_bounded_sound
    (starts := [⟨verticalPort grid boundary row, false⟩])
    (by
      intro start startMember
      simp only [List.mem_singleton] at startMember
      subst start
      exact startBound)
    nodeMember
  rcases sound with ⟨start, startMember, path⟩
  simp only [List.mem_singleton] at startMember
  subst start
  have nodeParity : node.parity = false :=
    Bool.eq_false_of_not_eq_true' parity
  have pathFalse : BoundedPath grid width height
      (verticalPort grid boundary row) node.current false := by
    simpa [nodeParity] using path
  simp only [verticalBetweenTarget, Bool.and_eq_true,
    decide_eq_true_eq] at target
  refine ⟨node.current.x, target.1.1.1,
    Option.isSome_iff_ne_none.mp target.2, ?_⟩
  rw [← target.1.2]
  exact pathFalse

theorem verticalLowerNorth
    {pair : PairState} (pairChecked : checkVerticalPair pair = true)
    {column localBoundary : Nat}
    (columnLt : column < 8)
    (boundaryMember : localBoundary ∈ createdCoordinates)
    (north : Signals.horizontalInterior?
      (componentAt (iterateRefine 2 (verticalGrid pair)) column localBoundary)
      (quadrantAt column localBoundary) = some .north) :
    ∃ targetY,
      localBoundary < targetY ∧ targetY < 16 ∧
      Signals.horizontalInterior?
        (componentAt (iterateRefine 2 (verticalGrid pair)) column targetY)
        (quadrantAt column targetY) ≠ none ∧
      BoundedPath (iterateRefine 2 (verticalGrid pair)) 8 16
        (horizontalPort (iterateRefine 2 (verticalGrid pair))
          column localBoundary)
        (horizontalPort (iterateRefine 2 (verticalGrid pair))
          column targetY) false := by
  simp only [checkVerticalPair, List.all_eq_true] at pairChecked
  have checked := pairChecked column (List.mem_range.2 columnLt)
    localBoundary boundaryMember
  simp only [Bool.and_eq_true, Bool.or_eq_true] at checked
  rcases checked.1 with impossible | checked
  · simp [north] at impossible
  · have boundaryLt : localBoundary < 8 := by
      simp only [createdCoordinates, List.mem_cons, List.not_mem_nil,
        or_false] at boundaryMember
      omega
    rcases horizontalParallelCheck_sound (checked := checked) (by
      simp only [PortInBounds, horizontalPort]
      split <;> simp_all <;> omega) with
      ⟨targetY, between, interior, path⟩
    rcases between with impossible | between
    · omega
    · exact ⟨targetY, between.1, between.2, interior, path⟩

theorem verticalUpperSouth
    {pair : PairState} (pairChecked : checkVerticalPair pair = true)
    {column localBoundary : Nat}
    (columnLt : column < 8)
    (boundaryMember : localBoundary ∈ createdCoordinates)
    (south : Signals.horizontalInterior?
      (componentAt (iterateRefine 2 (verticalGrid pair))
        column (8 + localBoundary))
      (quadrantAt column (8 + localBoundary)) = some .south) :
    ∃ targetY,
      0 < targetY ∧ targetY < 8 + localBoundary ∧
      Signals.horizontalInterior?
        (componentAt (iterateRefine 2 (verticalGrid pair)) column targetY)
        (quadrantAt column targetY) ≠ none ∧
      BoundedPath (iterateRefine 2 (verticalGrid pair)) 8 16
        (horizontalPort (iterateRefine 2 (verticalGrid pair))
          column (8 + localBoundary))
        (horizontalPort (iterateRefine 2 (verticalGrid pair))
          column targetY) false := by
  simp only [checkVerticalPair, List.all_eq_true] at pairChecked
  have checked := pairChecked column (List.mem_range.2 columnLt)
    localBoundary boundaryMember
  simp only [Bool.and_eq_true, Bool.or_eq_true] at checked
  rcases checked.2 with impossible | checked
  · simp [south] at impossible
  · have boundaryLt : localBoundary < 8 := by
      simp only [createdCoordinates, List.mem_cons, List.not_mem_nil,
        or_false] at boundaryMember
      omega
    rcases horizontalParallelCheck_sound (checked := checked) (by
      simp only [PortInBounds, horizontalPort]
      split <;> simp_all <;> omega) with
      ⟨targetY, between, interior, path⟩
    rcases between with between | impossible
    · exact ⟨targetY, between.1, between.2, interior, path⟩
    · omega

theorem horizontalLeftEast
    {pair : PairState} (pairChecked : checkHorizontalPair pair = true)
    {row localBoundary : Nat}
    (rowLt : row < 8)
    (boundaryMember : localBoundary ∈ createdCoordinates)
    (east : Signals.verticalInterior?
      (componentAt (iterateRefine 2 (horizontalGrid pair)) localBoundary row)
      (quadrantAt localBoundary row) = some .east) :
    ∃ targetX,
      localBoundary < targetX ∧ targetX < 16 ∧
      Signals.verticalInterior?
        (componentAt (iterateRefine 2 (horizontalGrid pair)) targetX row)
        (quadrantAt targetX row) ≠ none ∧
      BoundedPath (iterateRefine 2 (horizontalGrid pair)) 16 8
        (verticalPort (iterateRefine 2 (horizontalGrid pair))
          localBoundary row)
        (verticalPort (iterateRefine 2 (horizontalGrid pair))
          targetX row) false := by
  simp only [checkHorizontalPair, List.all_eq_true] at pairChecked
  have checked := pairChecked row (List.mem_range.2 rowLt)
    localBoundary boundaryMember
  simp only [Bool.and_eq_true, Bool.or_eq_true] at checked
  rcases checked.1 with impossible | checked
  · simp [east] at impossible
  · have boundaryLt : localBoundary < 8 := by
      simp only [createdCoordinates, List.mem_cons, List.not_mem_nil,
        or_false] at boundaryMember
      omega
    rcases verticalParallelCheck_sound (checked := checked) (by
      simp only [PortInBounds, verticalPort]
      split <;> simp_all <;> omega) with
      ⟨targetX, between, interior, path⟩
    rcases between with impossible | between
    · omega
    · exact ⟨targetX, between.1, between.2, interior, path⟩

theorem horizontalRightWest
    {pair : PairState} (pairChecked : checkHorizontalPair pair = true)
    {row localBoundary : Nat}
    (rowLt : row < 8)
    (boundaryMember : localBoundary ∈ createdCoordinates)
    (west : Signals.verticalInterior?
      (componentAt (iterateRefine 2 (horizontalGrid pair))
        (8 + localBoundary) row)
      (quadrantAt (8 + localBoundary) row) = some .west) :
    ∃ targetX,
      0 < targetX ∧ targetX < 8 + localBoundary ∧
      Signals.verticalInterior?
        (componentAt (iterateRefine 2 (horizontalGrid pair)) targetX row)
        (quadrantAt targetX row) ≠ none ∧
      BoundedPath (iterateRefine 2 (horizontalGrid pair)) 16 8
        (verticalPort (iterateRefine 2 (horizontalGrid pair))
          (8 + localBoundary) row)
        (verticalPort (iterateRefine 2 (horizontalGrid pair))
          targetX row) false := by
  simp only [checkHorizontalPair, List.all_eq_true] at pairChecked
  have checked := pairChecked row (List.mem_range.2 rowLt)
    localBoundary boundaryMember
  simp only [Bool.and_eq_true, Bool.or_eq_true] at checked
  rcases checked.2 with impossible | checked
  · simp [west] at impossible
  · have boundaryLt : localBoundary < 8 := by
      simp only [createdCoordinates, List.mem_cons, List.not_mem_nil,
        or_false] at boundaryMember
      omega
    rcases verticalParallelCheck_sound (checked := checked) (by
      simp only [PortInBounds, verticalPort]
      split <;> simp_all <;> omega) with
      ⟨targetX, between, interior, path⟩
    rcases between with between | impossible
    · exact ⟨targetX, between.1, between.2, interior, path⟩
    · omega

end PairCoverSeamCreatedFarParallelAudit
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
