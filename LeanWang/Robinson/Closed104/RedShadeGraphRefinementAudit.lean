/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.RedShadeGraphSearch

/-!
Finite audit for lifting red paths through two substitutions.

The original quarter component is retained in the southwest `2 x 2` corner of
its `8 x 8` quarter macrocell. A live east or north port there connects with
even crossing parity to the corresponding external macrocell port.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace RedShadeGraphRefinement

open RedCycles RedShadeGraph RedShadeGraphSearch Signals.FreeCellLocal

set_option maxRecDepth 20000

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

def connectorSearch (parent : Index) (side : ExitSide) (offset : Nat) :=
  search (fineGrid parent) 8 8 1000 (internalPort side offset) fun port parity =>
    decide (port = externalPort side offset) && !parity

def connectorMoves? (parent : Index) (side : ExitSide) (offset : Nat) :
    Option (List CertificateMove) :=
  match connectorSearch parent side offset with
  | some (finish, false, moves) =>
      if finish = externalPort side offset then some moves else none
  | _ => none

def connectorNodes (parent : Index) (side : ExitSide) (offset : Nat) :
    List Node :=
  exploreFast (fineGrid parent) 8 8 1000 [internalPort side offset]

def connectorNode? (parent : Index) (side : ExitSide) (offset : Nat) :
    Option Node :=
  (connectorNodes parent side offset).find? fun node =>
    decide (node.current = externalPort side offset) && !node.parity

def completeFor (parent : Index) : Bool :=
  exitSides.all fun side =>
    (List.range 2).all fun offset =>
      if portPresent (coarseGrid parent) (internalPort side offset) then
        (connectorMoves? parent side offset).isSome
      else true

def complete : Bool :=
  (List.finRange 104).all completeFor

def boundedCompleteFor (parent : Index) : Bool :=
  exitSides.all fun side =>
    (List.range 2).all fun offset =>
      if portPresent (coarseGrid parent) (internalPort side offset) then
        (connectorNode? parent side offset).isSome
      else true

def boundedComplete : Bool :=
  (List.finRange 104).all boundedCompleteFor

set_option linter.style.nativeDecide false in
theorem complete_eq_true : complete = true := by
  native_decide

set_option linter.style.nativeDecide false in
theorem boundedComplete_eq_true : boundedComplete = true := by
  native_decide

end RedShadeGraphRefinement
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
