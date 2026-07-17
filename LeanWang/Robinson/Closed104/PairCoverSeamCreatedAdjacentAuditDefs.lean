/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.PairCoverSeamPathSemantics
import LeanWang.Robinson.Closed104.SparseFreeLineLocalStates

/-!
# Adjacent-macrocell created-boundary seam checks

The final address bit restricts neighboring refined cells to either siblings
or a pair from the two opposite row/column child classes.  After erasing the
graph-invisible black component, this gives 792 states in each orientation.
The checks below search a rectangular two-cell window for the created-boundary
queries that leave one 8-by-8 macrocell.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace PairCoverSeamCreatedAdjacentAudit

open RedCycles RedShadeCycles PairCoverSeamPathSearch
  SparseFreeLineLocalStates Signals.FreeCellLocal

set_option maxRecDepth 20000

abbrev PairState := Index × Index

def canonicalPair (pair : PairState) : PairState :=
  (BorderSubstitution.canonicalIndex pair.1,
    BorderSubstitution.canonicalIndex pair.2)

def crossPairs (first second : List Index) : List PairState :=
  (first.flatMap fun a => second.map fun b => canonicalPair (a, b)).eraseDups

def verticalSiblingPairs : List PairState :=
  ((List.finRange 104).flatMap fun parent =>
    (List.finRange 2).map fun x => canonicalPair
      (childBlock parent x 0, childBlock parent x 1)).eraseDups

def horizontalSiblingPairs : List PairState :=
  ((List.finRange 104).flatMap fun parent =>
    (List.finRange 2).map fun y => canonicalPair
      (childBlock parent 0 y, childBlock parent 1 y)).eraseDups

def verticalPairs : List PairState :=
  (verticalSiblingPairs ++
    crossPairs (rowChildren 1) (rowChildren 0)).eraseDups

def horizontalPairs : List PairState :=
  (horizontalSiblingPairs ++
    crossPairs (columnChildren 1) (columnChildren 0)).eraseDups

def verticalGrid (pair : PairState) (_x y : Nat) : Index :=
  if y = 0 then pair.1 else pair.2

def horizontalGrid (pair : PairState) (x _y : Nat) : Index :=
  if x = 0 then pair.1 else pair.2

def createdCoordinates : List Nat := [2, 3, 4, 5, 6, 7]

def checkVerticalPair (pair : PairState) : Bool :=
  let grid := iterateRefine 2 (verticalGrid pair)
  (List.range 8).all fun column => createdCoordinates.all fun localBoundary =>
    let lowerBoundary := localBoundary
    let upperBoundary := 8 + localBoundary
    let lowerInterior := Signals.horizontalInterior?
      (componentAt grid column lowerBoundary)
      (quadrantAt column lowerBoundary)
    let upperInterior := Signals.horizontalInterior?
      (componentAt grid column upperBoundary)
      (quadrantAt column upperBoundary)
    (!decide (lowerInterior = some .north) ||
      verticalReachSeamCheck grid 0 4 column 8 lowerBoundary
        (verticalReachCover grid 8 16 1025 0 4
          column lowerBoundary [8])) &&
    (!decide (upperInterior = some .south) ||
      verticalReachSeamCheck grid 0 4 column 7 upperBoundary
        (verticalReachCover grid 8 16 1025 0 4
          column upperBoundary [7]))

def checkHorizontalPair (pair : PairState) : Bool :=
  let grid := iterateRefine 2 (horizontalGrid pair)
  (List.range 8).all fun row => createdCoordinates.all fun localBoundary =>
    let leftBoundary := localBoundary
    let rightBoundary := 8 + localBoundary
    let leftInterior := Signals.verticalInterior?
      (componentAt grid leftBoundary row)
      (quadrantAt leftBoundary row)
    let rightInterior := Signals.verticalInterior?
      (componentAt grid rightBoundary row)
      (quadrantAt rightBoundary row)
    (!decide (leftInterior = some .east) ||
      horizontalReachSeamCheck grid 0 4 row 8 leftBoundary
        (horizontalReachCover grid 16 8 1025 0 4
          row leftBoundary [8])) &&
    (!decide (rightInterior = some .west) ||
      horizontalReachSeamCheck grid 0 4 row 7 rightBoundary
        (horizontalReachCover grid 16 8 1025 0 4
          row rightBoundary [7]))

def chunkSize : Nat := 32

def verticalChunk (chunk : Nat) : List PairState :=
  (verticalPairs.drop (chunkSize * chunk)).take chunkSize

def horizontalChunk (chunk : Nat) : List PairState :=
  (horizontalPairs.drop (chunkSize * chunk)).take chunkSize

end PairCoverSeamCreatedAdjacentAudit
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
