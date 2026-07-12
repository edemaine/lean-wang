/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104ShadedFreeLineOddBaseAudit

/-! Finite route audit for the odd-phase center marker line. -/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace SparseFreeLineOddMarkerBaseAudit

open RedShadeGraph RedShadeGraphRefinement RedShadeGraphSearch
  ShadedFreeLineOddBase Signals.FreeCellLocal

def verticalReached (parent : Index) (quarterX : Nat) (node : Node) : Bool :=
  node.parity && portPresent (localGrid parent) node.current &&
    (decide (node.current = ⟨quarterX, 8, .south⟩) ||
      decide (node.current = ⟨quarterX, 8, .north⟩))

def horizontalReached (parent : Index) (quarterY : Nat) (node : Node) : Bool :=
  node.parity && portPresent (localGrid parent) node.current &&
    (decide (node.current = ⟨8, quarterY, .west⟩) ||
      decide (node.current = ⟨8, quarterY, .east⟩))

def completeFor (parent : Index) : Bool :=
  (List.range 6).all fun delta =>
    let coordinate := 6 + delta
    (if (Signals.verticalInterior?
          (componentAt (localGrid parent) coordinate 8)
          (quadrantAt coordinate 8)).isSome then
      (nodes parent).any (verticalReached parent coordinate)
    else true) &&
    (if (Signals.horizontalInterior?
          (componentAt (localGrid parent) 8 coordinate)
          (quadrantAt 8 coordinate)).isSome then
      (nodes parent).any (horizontalReached parent coordinate)
    else true)

def complete : Bool :=
  (List.finRange 104).all completeFor

set_option linter.style.nativeDecide false in
theorem complete_eq_true : complete = true := by
  native_decide

end SparseFreeLineOddMarkerBaseAudit
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
