/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.RedShadeGraphRefinementGeometry
import LeanWang.Robinson.Closed104.RedShadeGraphStaticCertificateData

/-!
Static audit for lifting red paths through two substitutions.

The original quarter component is retained in the southwest `2 x 2` corner of
its `8 x 8` quarter macrocell. A live east or north port there connects with
even crossing parity to the corresponding external macrocell port.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace RedShadeGraphRefinement

open RedCycles RedShadeGraph RedShadeGraphStaticCertificate
  RedShadeGraphStaticCertificateData Signals.FreeCellLocal

set_option maxRecDepth 20000

def exitSideCode : ExitSide → Nat
  | .east => 0
  | .north => 1

def connectorForest (parent : Index) (side : ExitSide) (offset : Nat) :
    List Instruction :=
  let bundle := connectorBundles.getD
    (connectorBundleIndices.getD parent.val connectorBundles.length) []
  bundle.getD (2 * exitSideCode side + offset) []

def connectorRoute? (parent : Index) (side : ExitSide) (offset : Nat) :
    Option (Nat × State) :=
  let source := internalPort side offset
  route? (fineGrid parent) 8 8 [source]
    (connectorForest parent side offset) fun state =>
      decide (state.origin = source) &&
        decide (state.current = externalPort side offset) && !state.parity

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
