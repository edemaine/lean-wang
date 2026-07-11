/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104RedShadeGraphRefinementAudit
import LeanWang.OllingerRobinson104ShadedFreeLineOffsets

/-!
Native finite audit for the six first-level Figure 18 graph certificates.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace ShadedFreeLineGraphBase

open RedCycles RedShadeGraph RedShadeGraphSearch ShadedFreeLineOffsets
  Signals.FreeCellLocal

set_option maxRecDepth 20000

def localGrid (parent : Index) : Nat → Nat → Index :=
  iterateRefine 4 (fun _ _ => parent)

def boardPorts : List Port :=
  (List.range 14).flatMap fun offset =>
    let coordinate := 10 + offset
    [⟨coordinate, 9, .west⟩, ⟨coordinate, 9, .east⟩,
      ⟨coordinate, 24, .west⟩, ⟨coordinate, 24, .east⟩,
      ⟨9, coordinate, .south⟩, ⟨9, coordinate, .north⟩,
      ⟨24, coordinate, .south⟩, ⟨24, coordinate, .north⟩]

def nodes (parent : Index) : List Node :=
  exploreFast (localGrid parent) 32 32 12000 boardPorts

def verticalReached (parent : Index) (offset quarterX : Nat) (node : Node) : Bool :=
  node.parity &&
    RedShadeGraphRefinement.portPresent (localGrid parent) node.current &&
    (decide (node.current = ⟨quarterX, 9 + offset, .south⟩) ||
      decide (node.current = ⟨quarterX, 9 + offset, .north⟩))

def horizontalReached (parent : Index) (offset quarterY : Nat) (node : Node) : Bool :=
  node.parity &&
    RedShadeGraphRefinement.portPresent (localGrid parent) node.current &&
    (decide (node.current = ⟨9 + offset, quarterY, .west⟩) ||
      decide (node.current = ⟨9 + offset, quarterY, .east⟩))

def completeFor (parent : Index) (parentNodes : List Node) : Bool :=
  (freeOffsets 1).all fun offset =>
    (List.range 14).all fun delta =>
      let coordinate := 10 + delta
      (if (Signals.verticalInterior?
            (componentAt (localGrid parent) coordinate (9 + offset))
            (quadrantAt coordinate (9 + offset))).isSome then
        parentNodes.any (verticalReached parent offset coordinate)
      else true) &&
      (if (Signals.horizontalInterior?
            (componentAt (localGrid parent) (9 + offset) coordinate)
            (quadrantAt (9 + offset) coordinate)).isSome then
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

end ShadedFreeLineGraphBase
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
