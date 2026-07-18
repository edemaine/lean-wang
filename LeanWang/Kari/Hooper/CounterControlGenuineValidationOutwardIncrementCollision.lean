/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlGenuineValidationOutwardSuffix
import LeanWang.Kari.Hooper.CounterControlGuardedCleanupProgress

/-!
# Cleanup handoffs for outward-validation increment collisions

Once collision processing has reached any genuine cleanup search whose gap
is at least the original outward-validation gap, the existing cleanup suffix
strictly escapes to a guarded search.  This file packages that common final
step independently of the finite geometry used to locate the appropriate
cleanup stage.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlGenuineValidationOutwardIncrementCollision

open Turing CounterMachine
open BoundedMarkerProgram CounterControlPlan
open CounterControlGlobalUnnesting CounterControlParentContinuation
open CounterControlGuardedSearch
open CounterControlGenuineValidation

noncomputable section

private theorem immortalFrom_of_reaches
    (base : Nat) (c : Nat.Partrec.Code)
    {first second : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) first)
    (hreach : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c) first second) :
    FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) second := by
  rw [FullTM0.HaltsFrom.immortalFrom_iff_not] at himmortal ⊢
  intro hhalts
  exact himmortal (FullTM0.HaltsFrom.of_reaches hreach hhalts)

/-- Any reached cleanup caller whose gap contains the original outward gap
produces the required outward-instruction handoff.  The cleanup suffix itself
grows strictly, so the consumer-facing comparison is weak only because that
is all `OutwardInstructionHandoff.nextSearch` requires. -/
theorem handoff_of_cleanupEntry
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    {current : GenuineSearch base c}
    {growth : Turing.Dir} {source : Nat} {register : Register}
    {targetState : Nat}
    {instruction : CounterMachine.Instruction}
    {obligation : OutwardObligation current growth source instruction}
    (hrule : (source, .increment register targetState) ∈
      GlobalSourceProgram.program)
    (cleanup : GenuineSearch base c)
    (hcleanup : rawCommands.get cleanup.search ∈
      cleanupCommands growth source)
    (hreaches : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      (foundCfg current) cleanup.cfg)
    (hdistance : current.distance ≤ cleanup.distance)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) (foundCfg current)) :
    Nonempty (OutwardInstructionHandoff current obligation) := by
  have himmortalCleanup : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) cleanup.cfg :=
    immortalFrom_of_reaches base c himmortal hreaches
  rcases
      CounterControlGuardedCleanupProgress.reaches_larger_guardedSearch_of_genuine_cleanup
        base c hmortal cleanup growth source register targetState hrule
          hcleanup himmortalCleanup with
    ⟨next, hnext, hstrict⟩
  exact ⟨.nextSearch next
    (hreaches.trans hnext) (hdistance.trans hstrict.le)⟩

end

end CounterControlGenuineValidationOutwardIncrementCollision
end Hooper
end Kari
end LeanWang
