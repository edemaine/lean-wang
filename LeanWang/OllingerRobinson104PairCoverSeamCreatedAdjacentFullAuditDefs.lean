/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamCreatedAdjacentAuditDefs

/-!
# Full adjacent-macrocell created-boundary checks

The original adjacent audit asks only for a target on the shared macrocell
edge.  These strengthened checks use one weighted flood to cover every query
coordinate in the neighboring macrocell.  This produces a seam path with the
actual query coordinate, so no monotonicity assumption about the kind of
endpoint selected at the shared edge is needed.
-/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamCreatedAdjacentFullAudit

open RedCycles RedShadeGraph PairCoverSeamPathSearch
  PairCoverSeamCreatedAdjacentAudit Signals.FreeCellLocal

set_option maxRecDepth 20000

def upperQueries : List Nat := (List.range 8).map (8 + ·)

def lowerQueries : List Nat := List.range 8

/-- Check every created source in the lower and upper cells against all query
rows in the opposite cell. -/
def checkVerticalPair (pair : PairState) : Bool :=
  let grid := iterateRefine 2 (verticalGrid pair)
  (List.range 8).all fun column => createdCoordinates.all fun localBoundary =>
    let upperBoundary := 8 + localBoundary
    let lowerInterior := Signals.horizontalInterior?
      (componentAt grid column localBoundary) (quadrantAt column localBoundary)
    let upperInterior := Signals.horizontalInterior?
      (componentAt grid column upperBoundary) (quadrantAt column upperBoundary)
    let lowerFound := verticalReachCover grid 8 16 1025 0 4
      column localBoundary upperQueries
    let upperFound := verticalReachCover grid 8 16 1025 0 4
      column upperBoundary lowerQueries
    (!decide (lowerInterior = some .north) ||
      upperQueries.all fun row =>
        verticalReachSeamCheck grid 0 4 column row localBoundary lowerFound) &&
    (!decide (upperInterior = some .south) ||
      lowerQueries.all fun row =>
        verticalReachSeamCheck grid 0 4 column row upperBoundary upperFound)

def rightQueries : List Nat := (List.range 8).map (8 + ·)

def leftQueries : List Nat := List.range 8

/-- Horizontal dual of `checkVerticalPair`. -/
def checkHorizontalPair (pair : PairState) : Bool :=
  let grid := iterateRefine 2 (horizontalGrid pair)
  (List.range 8).all fun row => createdCoordinates.all fun localBoundary =>
    let rightBoundary := 8 + localBoundary
    let leftInterior := Signals.verticalInterior?
      (componentAt grid localBoundary row) (quadrantAt localBoundary row)
    let rightInterior := Signals.verticalInterior?
      (componentAt grid rightBoundary row) (quadrantAt rightBoundary row)
    let leftFound := horizontalReachCover grid 16 8 1025 0 4
      row localBoundary rightQueries
    let rightFound := horizontalReachCover grid 16 8 1025 0 4
      row rightBoundary leftQueries
    (!decide (leftInterior = some .east) ||
      rightQueries.all fun column =>
        horizontalReachSeamCheck grid 0 4 row column localBoundary leftFound) &&
    (!decide (rightInterior = some .west) ||
      leftQueries.all fun column =>
        horizontalReachSeamCheck grid 0 4 row column rightBoundary rightFound)

def chunkSize : Nat := 32

def verticalChunk (chunk : Nat) : List PairState :=
  (PairCoverSeamCreatedAdjacentAudit.verticalPairs.drop
    (chunkSize * chunk)).take chunkSize

def horizontalChunk (chunk : Nat) : List PairState :=
  (PairCoverSeamCreatedAdjacentAudit.horizontalPairs.drop
    (chunkSize * chunk)).take chunkSize

end PairCoverSeamCreatedAdjacentFullAudit
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
