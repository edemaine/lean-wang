/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamCreatedAdjacentFullAuditDefs

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

open RedCycles RedShadeCycles RedShadeGraph RedShadeGraphWeightedSearch
  PairCoverSeamPathSearch PairCoverSeamShadePaths
  PairCoverSeamCreatedAdjacentAudit Signals.FreeCellLocal

set_option maxRecDepth 20000

def horizontalParallelCheck (grid : Nat → Nat → Index)
    (width height fuel column query boundary : Nat) : Bool :=
  match searchFastWeightedReach grid width height fuel
      [⟨horizontalPort grid column boundary, false⟩] fun node =>
        !node.parity &&
          horizontalBetweenTarget grid column query boundary node.current with
  | none => false
  | some node => !node.parity &&
      horizontalBetweenTarget grid column query boundary node.current

def verticalParallelCheck (grid : Nat → Nat → Index)
    (width height fuel row query boundary : Nat) : Bool :=
  match searchFastWeightedReach grid width height fuel
      [⟨verticalPort grid boundary row, false⟩] fun node =>
        !node.parity &&
          verticalBetweenTarget grid row query boundary node.current with
  | none => false
  | some node => !node.parity &&
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

end PairCoverSeamCreatedFarParallelAudit
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
