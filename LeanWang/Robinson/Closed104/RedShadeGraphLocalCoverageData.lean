/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.RedShadeGraphLocalCoverageGeometry
import LeanWang.Robinson.Closed104.RedShadeGraphStaticCertificateData

/-!
# Static local red-graph coverage under two substitutions

Inside the `8 x 8` quarter-cell block replacing one corrected tile, every
present red port is connected either to the new central cell cycle or to the
sparse copy of a present old port. The checked predecessor forests are static;
no graph search runs in this module.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace RedShadeGraphLocalCoverage

open RedShadeCycles RedShadeGraph RedShadeGraphRefinement
  RedShadeGraphStaticCertificate RedShadeGraphStaticCertificateData

set_option maxRecDepth 20000

def forest (parent : Index) : List Instruction :=
  localForests.getD parent.val []

def routes (parent : Index) : List (Nat × State) :=
  evaluated (fineGrid parent) 8 8 (sources parent) (forest parent)

def routeNode? (found : List (Nat × State)) (target : Port) :
    Option (Nat × State) :=
  found.find? fun route => decide (route.2.current = target)

def targetCovered (parent : Index) (found : List (Nat × State))
    (target : Port) : Bool :=
  if portPresent (fineGrid parent) target then
    (routeNode? found target).isSome
  else true

def parentCovered (parent : Index) : Bool :=
  let found := routes parent
  (portsIn 8 8).all (targetCovered parent found)

def allParentsCovered : Bool :=
  (List.finRange 104).all parentCovered

def baseRoutes : List (Nat × State) :=
  evaluated (fineGrid 0) 8 8 [cycleSource] baseForest

def baseRoute? (target : Port) : Option (Nat × State) :=
  routeNode? baseRoutes target

def baseTargetCovered (target : Port) : Bool :=
  if 2 ≤ target.x && target.x < 6 && 2 ≤ target.y && target.y < 6 &&
      portPresent (fineGrid 0) target then
    (baseRoute? target).isSome
  else true

def baseCovered : Bool :=
  (portsIn 8 8).all baseTargetCovered

end RedShadeGraphLocalCoverage
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
