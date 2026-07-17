/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.ShadedFreeLineOddBaseAudit
import LeanWang.Robinson.Closed104.ShadedObstructionGeometry

/-!
# Finite obstruction audit for the odd Robinson base

The odd free-line base already computes bounded red-path floods from every side
of the canonical `(2,6) × (2,6)` board.  This audit checks the complete
nearest-boundary geometry on its strict quarter interior for both board shades
and every corrected parent index.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace ShadedObstructionGeometryOddBaseAudit

open RedShadeGraph RedShadeGraphRefinement RedShadeGraphSearch
  ShadedFreeLineOddBase Signals Signals.FreeCellLocal

def reachedBitmap (parentNodes : List Node) : Array Bool :=
  parentNodes.foldl (fun visited node =>
    visited.setIfInBounds (stateCode 16 node.state) true)
    (Array.replicate (16 * 16 * 8) false)

def reachedWithParity (parent : Index) (visited : Array Bool)
    (port : Port) (parity : Bool) : Bool :=
  visited[stateCode 16 (port, parity)]?.getD false &&
    portPresent (localGrid parent) port

def selectedVertical (parent : Index) (visited : Array Bool)
    (parentLight : Bool) (x y : Nat) : Bool :=
  (verticalInterior? (componentAt (localGrid parent) x y)
      (quadrantAt x y)).isSome &&
    (reachedWithParity parent visited ⟨x, y, .south⟩ (!parentLight) ||
      reachedWithParity parent visited ⟨x, y, .north⟩ (!parentLight))

def selectedHorizontal (parent : Index) (visited : Array Bool)
    (parentLight : Bool) (x y : Nat) : Bool :=
  (horizontalInterior? (componentAt (localGrid parent) x y)
      (quadrantAt x y)).isSome &&
    (reachedWithParity parent visited ⟨x, y, .west⟩ (!parentLight) ||
      reachedWithParity parent visited ⟨x, y, .east⟩ (!parentLight))

def coordinates : List Nat := (List.range 6).map (6 + ·)

def freeRow (parent : Index) (visited : Array Bool)
    (parentLight : Bool) (row : Nat) : Bool :=
  coordinates.all fun x => !selectedVertical parent visited parentLight x row

def freeColumn (parent : Index) (visited : Array Bool)
    (parentLight : Bool) (column : Nat) : Bool :=
  coordinates.all fun y => !selectedHorizontal parent visited parentLight column y

def upperWitness (parent : Index) (visited : Array Bool)
    (parentLight : Bool) (column row : Nat) : Bool :=
  coordinates.any fun boundary =>
    decide (row < boundary) &&
      decide (horizontalInterior?
        (componentAt (localGrid parent) column boundary)
        (quadrantAt column boundary) = some .north) &&
      selectedHorizontal parent visited parentLight column boundary &&
      coordinates.all fun y =>
        if row < y && y < boundary then
          !selectedHorizontal parent visited parentLight column y
        else true

def lowerWitness (parent : Index) (visited : Array Bool)
    (parentLight : Bool) (column row : Nat) : Bool :=
  coordinates.any fun boundary =>
    decide (boundary < row) &&
      decide (horizontalInterior?
        (componentAt (localGrid parent) column boundary)
        (quadrantAt column boundary) = some .south) &&
      selectedHorizontal parent visited parentLight column boundary &&
      coordinates.all fun y =>
        if boundary < y && y < row then
          !selectedHorizontal parent visited parentLight column y
        else true

def rightWitness (parent : Index) (visited : Array Bool)
    (parentLight : Bool) (column row : Nat) : Bool :=
  coordinates.any fun boundary =>
    decide (column < boundary) &&
      decide (verticalInterior?
        (componentAt (localGrid parent) boundary row)
        (quadrantAt boundary row) = some .east) &&
      selectedVertical parent visited parentLight boundary row &&
      coordinates.all fun x =>
        if column < x && x < boundary then
          !selectedVertical parent visited parentLight x row
        else true

def leftWitness (parent : Index) (visited : Array Bool)
    (parentLight : Bool) (column row : Nat) : Bool :=
  coordinates.any fun boundary =>
    decide (boundary < column) &&
      decide (verticalInterior?
        (componentAt (localGrid parent) boundary row)
        (quadrantAt boundary row) = some .west) &&
      selectedVertical parent visited parentLight boundary row &&
      coordinates.all fun x =>
        if boundary < x && x < column then
          !selectedVertical parent visited parentLight x row
        else true

def completeFor (parent : Index) (visited : Array Bool)
    (parentLight : Bool) : Bool :=
  coordinates.all fun column => coordinates.all fun row =>
    ((!freeRow parent visited parentLight row ||
        freeColumn parent visited parentLight column) ||
      selectedHorizontal parent visited parentLight column row ||
      upperWitness parent visited parentLight column row ||
      lowerWitness parent visited parentLight column row) &&
    ((!freeColumn parent visited parentLight column ||
        freeRow parent visited parentLight row) ||
      selectedVertical parent visited parentLight column row ||
      rightWitness parent visited parentLight column row ||
      leftWitness parent visited parentLight column row)

def coverageFor (parent : Index) (visited : Array Bool) : Bool :=
  coordinates.all fun x => coordinates.all fun y =>
    (!(verticalInterior? (componentAt (localGrid parent) x y)
        (quadrantAt x y)).isSome ||
      reachedWithParity parent visited ⟨x, y, .south⟩ false ||
      reachedWithParity parent visited ⟨x, y, .south⟩ true ||
      reachedWithParity parent visited ⟨x, y, .north⟩ false ||
      reachedWithParity parent visited ⟨x, y, .north⟩ true) &&
    (!(horizontalInterior? (componentAt (localGrid parent) x y)
        (quadrantAt x y)).isSome ||
      reachedWithParity parent visited ⟨x, y, .west⟩ false ||
      reachedWithParity parent visited ⟨x, y, .west⟩ true ||
      reachedWithParity parent visited ⟨x, y, .east⟩ false ||
      reachedWithParity parent visited ⟨x, y, .east⟩ true)

def complete : Bool :=
  ShadedFreeLineOddBase.allData.all fun data =>
    let visited := reachedBitmap data.2
    coverageFor data.1 visited &&
      completeFor data.1 visited false && completeFor data.1 visited true

set_option linter.style.nativeDecide false in
theorem complete_eq_true : complete = true := by
  native_decide

end ShadedObstructionGeometryOddBaseAudit
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
