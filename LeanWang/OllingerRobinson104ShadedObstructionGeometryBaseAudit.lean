/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104ShadedFreeLineGraphBaseAudit
import LeanWang.OllingerRobinson104ShadedObstructionGeometry
import LeanWang.OllingerRobinson104BorderSubstitution

/-!
# Finite audit for Robinson's nearest-boundary geometry

The existing outer-cycle graph flood determines the shade parity of every red
port in the depth-four base board. This audit checks the complete Section 7
nearest-boundary condition for both possible outer-board shades and all 56
graph-distinct parent states.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace ShadedObstructionGeometryBaseAudit

open RedShadeGraph RedShadeGraphRefinement RedShadeGraphSearch
  ShadedFreeLineGraphBase Signals Signals.FreeCellLocal BorderSubstitution

def reachedBitmap (parentNodes : List Node) : Array Bool :=
  parentNodes.foldl (fun visited node =>
    visited.setIfInBounds (stateCode 32 node.state) true)
    (Array.replicate (32 * 32 * 8) false)

def reachedWithParity (parent : Index) (visited : Array Bool)
    (port : Port) (parity : Bool) : Bool :=
  visited[stateCode 32 (port, parity)]?.getD false &&
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

def coordinates : List Nat := (List.range 14).map (10 + ·)

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
  (states.map representative).all fun parent =>
    let visited := reachedBitmap (nodes parent)
    coverageFor parent visited &&
      completeFor parent visited false && completeFor parent visited true

set_option linter.style.nativeDecide false in
theorem complete_eq_true : complete = true := by
  native_decide

end ShadedObstructionGeometryBaseAudit
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
