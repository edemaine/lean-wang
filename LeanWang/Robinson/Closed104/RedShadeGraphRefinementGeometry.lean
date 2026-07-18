/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.PlaneRedBoards
import LeanWang.Robinson.Closed104.RedShadeGraph

/-! Geometry of the two-substitution local red-graph block. -/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace RedShadeGraphRefinement

open RedCycles RedShadeGraph

inductive ExitSide where
  | east
  | north
deriving DecidableEq, Repr

def exitSides : List ExitSide := [.east, .north]

def coarseGrid (parent : Index) : Nat → Nat → Index := fun _ _ => parent

def fineGrid (parent : Index) : Nat → Nat → Index :=
  iterateRefine 2 (coarseGrid parent)

def internalPort (side : ExitSide) (offset : Nat) : Port :=
  match side with
  | .east => ⟨1, offset, .east⟩
  | .north => ⟨offset, 1, .north⟩

def externalPort (side : ExitSide) (offset : Nat) : Port :=
  match side with
  | .east => ⟨7, offset, .east⟩
  | .north => ⟨offset, 7, .north⟩

def macroOrigin (coordinate : Nat) : Nat :=
  8 * (coordinate / 2)

def localCoordinate (coordinate : Nat) : Nat :=
  coordinate % 2

def sparseCoordinate (coordinate : Nat) : Nat :=
  macroOrigin coordinate + localCoordinate coordinate

def sparsePort (port : Port) : Port :=
  ⟨sparseCoordinate port.x, sparseCoordinate port.y, port.side⟩

end RedShadeGraphRefinement
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
