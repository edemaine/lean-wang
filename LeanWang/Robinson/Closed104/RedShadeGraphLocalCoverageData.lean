/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.RedShadeGraphRefinement
import LeanWang.Robinson.Closed104.RedShadeGraphSearch
import LeanWang.Robinson.Closed104.RedShadeCycles

/-!
# Local red-graph coverage under two substitutions

Inside the `8 x 8` quarter-cell block replacing one corrected tile, every
present red port is connected either to the new central cell cycle or to the
sparse copy of a present old port.  This file contains only the executable
checker; its soundness and native certificate are separated from the data.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace RedShadeGraphLocalCoverage

open RedShadeCycles RedShadeGraph RedShadeGraphRefinement RedShadeGraphSearch

set_option maxRecDepth 20000

def portsIn (width height : Nat) : List Port :=
  (List.range height).flatMap fun y =>
    (List.range width).flatMap fun x =>
      [.mk x y .west, .mk x y .east, .mk x y .south, .mk x y .north]

/-- One strict side port of the cell cycle created in the southwest depth-two
subtile. -/
def cycleSource : Port :=
  .mk (quarterWest 1 + 1) (quarterSouth 1) .west

def inheritedSources (parent : Index) : List Port :=
  ((portsIn 2 2).filter
    (portPresent (RedShadeGraphRefinement.coarseGrid parent))).map sparsePort

def sources (parent : Index) : List Port :=
  cycleSource :: inheritedSources parent

def nodes (parent : Index) : List Node :=
  exploreFast (fineGrid parent) 8 8 1000 (sources parent)

def routeNode? (found : List Node) (target : Port) : Option Node :=
  found.find? fun node => decide (node.current = target)

def targetCovered (parent : Index) (found : List Node) (target : Port) : Bool :=
  if portPresent (fineGrid parent) target then
    (routeNode? found target).isSome
  else true

def parentCovered (parent : Index) : Bool :=
  let found := nodes parent
  (portsIn 8 8).all (targetCovered parent found)

def allParentsCovered : Bool :=
  (List.finRange 104).all parentCovered

def baseSearch (target : Port) :=
  search (fineGrid 0) 8 8 1000 cycleSource fun port _ =>
    decide (port = target)

def basePath? (target : Port) : Option (Bool × List CertificateMove) :=
  match baseSearch target with
  | none => none
  | some (finish, parity, moves) =>
      if finish = target then some (parity, moves) else none

def baseTargetCovered (target : Port) : Bool :=
  if 2 ≤ target.x && target.x < 6 && 2 ≤ target.y && target.y < 6 &&
      portPresent (fineGrid 0) target then
    (basePath? target).isSome
  else true

def baseCovered : Bool :=
  (portsIn 8 8).all baseTargetCovered

end RedShadeGraphLocalCoverage
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
