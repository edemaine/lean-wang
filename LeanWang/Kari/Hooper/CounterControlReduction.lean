/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlOpenSimulation
import LeanWang.Kari.Hooper.CounterControlPlanComputable
import LeanWang.Kari.Hooper.CounterControlDeterministic

/-!
# The effective finite-table endpoint of Hooper's construction

This file fixes the relocation base used by the reduction and packages the
resulting code-dependent finite TM0 table.  Its effectivity and determinism
are independent of the arbitrary-entry converse.  The designated open-frame
simulation supplies the forward implication from fixed nonhalting to
arbitrary-configuration immortality.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlReduction

open BoundedMarkerProgram CounterControlPlan

noncomputable section

/-- A fixed relocation base for the final finite controller. -/
def base : Nat := 0

/-- The finite TM0 transition table produced from a universal program code. -/
def table (c : Nat.Partrec.Code) : FiniteTM0.Table (AlphabetSize numTags) :=
  CounterControlPlan.table base c

/-- The table compiler is primitive recursive. -/
theorem table_primrec : Primrec table := by
  exact (CounterControlPlan.table_primrec base).of_eq fun _ => rfl

/-- In particular, the finite-table compiler is computable. -/
theorem table_computable : Computable table :=
  table_primrec.to_comp

/-- Every generated table has a unique rule for each state-symbol key. -/
theorem table_deterministic (c : Nat.Partrec.Code) :
    FiniteTM0.Deterministic (table c) := by
  simpa [table] using CounterControlDeterministic.table_deterministic base c

/-- Fixed nonhalting supplies an immortal arbitrary configuration of the
compiled finite table. -/
theorem immortal_of_fixedNonhalting (c : Nat.Partrec.Code) :
    DominoProblem.FixedNonhalting c →
      FullTM0.Immortal (FiniteTM0.machine (table c)) := by
  intro hnonhalting
  refine ⟨CounterControlOpenSimulation.canonicalOpenCfg base c, ?_⟩
  change FullTM0.ImmortalFrom (CounterControlNestingBridge.machine base c)
    (CounterControlOpenSimulation.canonicalOpenCfg base c)
  exact CounterControlOpenSimulation.fixedNonhalting_immortalFrom base c
    hnonhalting

end

end CounterControlReduction
end Hooper
end Kari
end LeanWang
