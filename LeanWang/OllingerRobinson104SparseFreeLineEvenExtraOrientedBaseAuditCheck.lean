/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104SparseFreeLineEvenExtraCycleBaseAudit

/-!
# Oriented cycle-only even-extra base check

Every vertical target is reached from the south side of the enclosing cycle;
dually, every horizontal target is reached from its west side.  Keeping this
expensive native certificate isolated makes the source orientation available
to the recursive nested-board proof without rebuilding the graph flood.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace SparseFreeLineEvenExtraOrientedBaseAudit

open RedShadeGraph RedShadeGraphSearch RedShadeGraphWeightedSearch
  SparseFreeLineEvenExtraBaseAudit
  SparseFreeLineEvenExtraCycleBaseAudit

def southStarts : List WeightedStart :=
  starts.filter fun start => start.port.y == 1

def westStarts : List WeightedStart :=
  starts.filter fun start => start.port.x == 1

def subsetNodes (parent : Index) (subset : List WeightedStart) : List ReachNode :=
  exploreFastWeightedReach (searchGrid parent) 65 65 33801 subset

def verticalSubsetCheck (parent : Index) (subset : List WeightedStart) : Bool :=
  let found := subsetNodes parent subset
  (List.range 62).all fun delta =>
    let x := 2 + delta
    let required := (Signals.verticalInterior?
      (Signals.FreeCellLocal.componentAt (searchGrid parent) x 40)
      (Signals.FreeCellLocal.quadrantAt x 40)).isSome
    !required || SparseFreeLineEvenExtraCycleBaseAudit.reached parent found
      ⟨x, 40, .south⟩ ||
      SparseFreeLineEvenExtraCycleBaseAudit.reached parent found
        ⟨x, 40, .north⟩

def horizontalSubsetCheck (parent : Index) (subset : List WeightedStart) : Bool :=
  let found := subsetNodes parent subset
  (List.range 62).all fun delta =>
    let y := 2 + delta
    let required := (Signals.horizontalInterior?
      (Signals.FreeCellLocal.componentAt (searchGrid parent) 40 y)
      (Signals.FreeCellLocal.quadrantAt 40 y)).isSome
    !required || SparseFreeLineEvenExtraCycleBaseAudit.reached parent found
      ⟨40, y, .west⟩ ||
      SparseFreeLineEvenExtraCycleBaseAudit.reached parent found
        ⟨40, y, .east⟩

set_option linter.style.nativeDecide false in
/-- South and west cycle sides suffice for every canonical border state. -/
theorem oriented_complete :
    ∀ state ∈ BorderSubstitution.states,
      verticalSubsetCheck (BorderSubstitution.representative state)
          southStarts = true ∧
        horizontalSubsetCheck (BorderSubstitution.representative state)
          westStarts = true := by
  native_decide

end SparseFreeLineEvenExtraOrientedBaseAudit
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
