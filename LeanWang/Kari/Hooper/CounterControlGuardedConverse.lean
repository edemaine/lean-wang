/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlGuardedUnnesting
import LeanWang.Kari.Hooper.CounterControlReduction

/-!
# Guarded operational endpoint of Hooper's converse

The global argument needs only two concrete facts about the compiled command
graph when the designated source computation is mortal: monotone entry into
the shared-return guard, and strict escape from every guarded search.  This
file packages those facts and derives the exact immortality equivalence for
the effective finite table.  The command-family modules can therefore be
assembled without mentioning the later affine encoding.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlGuardedConverse

open Turing
open BoundedMarkerProgram
open CounterControlGlobalUnnesting
open CounterControlGuardedUnnesting

noncomputable section

private instance : Inhabited (Symbol CounterControlPlan.numTags) :=
  ⟨blankSymbol⟩

/-- The two local command-graph laws required by the global converse.  They
are requested only under source mortality, which is exactly where generated
searches are forced to have finite genuine gaps. -/
structure Laws (base : Nat) (c : Nat.Partrec.Code) : Prop where
  monotoneEntry : ¬ DominoProblem.FixedNonhalting c →
    MonotoneGuardedEntryLaw base c
  escape : ¬ DominoProblem.FixedNonhalting c →
    GuardedEscapeLaw base c

/-- The guarded laws make every arbitrary controller configuration halt when
the designated source computation is mortal. -/
theorem haltsFrom_of_laws
    (base : Nat) (c : Nat.Partrec.Code)
    (hlaws : Laws base c)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (start : FullTM0.Cfg (Symbol CounterControlPlan.numTags) FiniteTM0.State) :
    FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c) start :=
  haltsFrom_of_escape_and_monotoneEntry base c hmortal
    (hlaws.monotoneEntry hmortal) (hlaws.escape hmortal) start

/-- Consequently the complete controller has no immortal arbitrary
configuration when the fixed source computation halts. -/
theorem not_immortal_of_laws
    (base : Nat) (c : Nat.Partrec.Code)
    (hlaws : Laws base c)
    (hmortal : ¬ DominoProblem.FixedNonhalting c) :
    ¬ FullTM0.Immortal (CounterControlNestingBridge.machine base c) := by
  rintro ⟨start, himmortal⟩
  have hhalts := haltsFrom_of_laws base c hlaws hmortal start
  exact (FullTM0.HaltsFrom.immortalFrom_iff_not
    (CounterControlNestingBridge.machine base c) start).mp
      himmortal hhalts

/-- Exact endpoint at the fixed relocation base used by the reduction. -/
theorem table_immortal_iff_fixedNonhalting_of_laws
    (c : Nat.Partrec.Code)
    (hlaws : Laws CounterControlReduction.base c) :
    FullTM0.Immortal
        (FiniteTM0.machine (CounterControlReduction.table c)) ↔
      DominoProblem.FixedNonhalting c := by
  constructor
  · intro himmortal
    by_contra hmortal
    apply not_immortal_of_laws CounterControlReduction.base c hlaws
      hmortal
    simpa [CounterControlReduction.table, CounterControlPlan.table,
      CounterControlNestingBridge.machine,
      BoundedMarkerProgram.machine] using himmortal
  · exact CounterControlReduction.immortal_of_fixedNonhalting c

end

end CounterControlGuardedConverse
end Hooper
end Kari
end LeanWang
