/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104RedShadeGraphRefinementAudit
import LeanWang.OllingerRobinson104ShadedFreeLineOffsets

/-!
Finite graph audit for the two odd-phase base free lines.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace ShadedFreeLineOddBase

open RedCycles RedShadeGraph RedShadeGraphSearch ShadedFreeLineOffsets
  Signals.FreeCellLocal

set_option maxRecDepth 20000

def localGrid (parent : Index) : Nat → Nat → Index :=
  iterateRefine 3 (fun _ _ => parent)

def boardPorts : List Port :=
  (List.range 6).flatMap fun offset =>
    let coordinate := 6 + offset
    [⟨coordinate, 5, .west⟩, ⟨coordinate, 5, .east⟩,
      ⟨coordinate, 12, .west⟩, ⟨coordinate, 12, .east⟩,
      ⟨5, coordinate, .south⟩, ⟨5, coordinate, .north⟩,
      ⟨12, coordinate, .south⟩, ⟨12, coordinate, .north⟩]

def nodes (parent : Index) : List Node :=
  exploreFast (localGrid parent) 16 16 4000 boardPorts

def verticalReached (parent : Index) (offset quarterX : Nat) (node : Node) : Bool :=
  node.parity &&
    RedShadeGraphRefinement.portPresent (localGrid parent) node.current &&
    (decide (node.current = ⟨quarterX, 5 + 2 * offset, .south⟩) ||
      decide (node.current = ⟨quarterX, 5 + 2 * offset, .north⟩))

def horizontalReached (parent : Index) (offset quarterY : Nat) (node : Node) : Bool :=
  node.parity &&
    RedShadeGraphRefinement.portPresent (localGrid parent) node.current &&
    (decide (node.current = ⟨5 + 2 * offset, quarterY, .west⟩) ||
      decide (node.current = ⟨5 + 2 * offset, quarterY, .east⟩))

def completeFor (parent : Index) (parentNodes : List Node) : Bool :=
  (freeOffsets 0).all fun offset =>
    (List.range 6).all fun delta =>
      let coordinate := 6 + delta
      (if (Signals.verticalInterior?
            (componentAt (localGrid parent) coordinate (5 + 2 * offset))
            (quadrantAt coordinate (5 + 2 * offset))).isSome then
        parentNodes.any (verticalReached parent offset coordinate)
      else true) &&
      (if (Signals.horizontalInterior?
            (componentAt (localGrid parent) (5 + 2 * offset) coordinate)
            (quadrantAt (5 + 2 * offset) coordinate)).isSome then
        parentNodes.any (horizontalReached parent offset coordinate)
      else true)

abbrev Data := Index × List Node

def allData : List Data :=
  (List.finRange 104).map fun parent => (parent, nodes parent)

def complete : Bool :=
  allData.all fun data => completeFor data.1 data.2

set_option linter.style.nativeDecide false in
theorem complete_eq_true : complete = true := by
  native_decide

end ShadedFreeLineOddBase
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
