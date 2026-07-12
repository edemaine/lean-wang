/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104SparseFreeLineEvenExtraCreatedStep
import LeanWang.OllingerRobinson104SparseFreeLineProjectionStep

/-! The unconditional sparse Robinson free-line recurrence. -/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace SparseFreeLineComplete

open SparseFreeLineRecurrence

/-- All retained sparse lines project through one substitution level. -/
theorem projectionStep : ProjectionStep :=
  SparseFreeLineProjectionStep.projectionStep
    SparseFreeLineEvenExtraCreatedStep.evenExtraMainStep
    SparseFreeLineOddExtraStep.oddPivotExtraStep

/-- Both parity phases have graph certificates at arbitrarily large depth. -/
theorem graphHolds_unbounded (size : Nat) :
    GraphHolds .even (1 + size) ∧ GraphHolds .odd size :=
  SparseFreeLineRecurrence.graphHolds_unbounded projectionStep size

end SparseFreeLineComplete
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
