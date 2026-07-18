/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.RedShadeGraphRefinementGeometry
import LeanWang.Robinson.Closed104.RedShadeGraphSearch

/-!
Checked audit for lifting red paths through two substitutions.

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

def connectorRoute? (parent : Index) (side : ExitSide) (offset : Nat) :
    Option Node :=
  let source := internalPort side offset
  (exploreFast (fineGrid parent) 8 8 1000 [source]).find? fun node =>
    decide (node.origin = source) &&
      decide (node.current = externalPort side offset) &&
        decide (node.parity = false) && node.valid (fineGrid parent) 8 8

def completeFor (parent : Index) : Bool :=
  exitSides.all fun side =>
    (List.range 2).all fun offset =>
      if portPresent (coarseGrid parent) (internalPort side offset) then
        (connectorRoute? parent side offset).isSome
      else true

def complete : Bool :=
  (List.finRange 104).all completeFor

def boundedCompleteFor (parent : Index) : Bool := completeFor parent

def boundedComplete : Bool :=
  complete

end RedShadeGraphRefinement
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
