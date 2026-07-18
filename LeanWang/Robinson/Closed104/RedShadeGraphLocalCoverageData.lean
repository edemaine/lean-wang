/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.RedShadeGraphLocalCoverageGeometry
import LeanWang.Robinson.Closed104.RedShadeGraphSearch

/-!
# Checked local red-graph coverage under two substitutions

Inside the `8 x 8` quarter-cell block replacing one corrected tile, every
present red port is connected either to the new central cell cycle or to the
sparse copy of a present old port. The graph flood is untrusted: every selected
node is accepted only after its retained move list passes the bounded checker.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace RedShadeGraphLocalCoverage

open RedShadeCycles RedShadeGraph RedShadeGraphRefinement
  RedShadeGraphSearch

set_option maxRecDepth 20000

def routes (parent : Index) : List Node :=
  exploreFast (fineGrid parent) 8 8 1000 (sources parent)

def routeNode? (parent : Index) (found : List Node) (target : Port) :
    Option Node :=
  found.find? fun node =>
    decide (node.origin ∈ sources parent) &&
      decide (node.current = target) && node.valid (fineGrid parent) 8 8

def targetCovered (parent : Index) (found : List Node)
    (target : Port) : Bool :=
  if portPresent (fineGrid parent) target then
    (routeNode? parent found target).isSome
  else true

def parentCovered (parent : Index) : Bool :=
  let found := routes parent
  (portsIn 8 8).all (targetCovered parent found)

def allParentsCovered : Bool :=
  (List.finRange 104).all parentCovered

def baseRoutes : List Node :=
  exploreFast (fineGrid 0) 8 8 1000 [cycleSource]

def baseRoute? (target : Port) : Option Node :=
  baseRoutes.find? fun node =>
    decide (node.origin = cycleSource) &&
      decide (node.current = target) && node.valid (fineGrid 0) 8 8

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
