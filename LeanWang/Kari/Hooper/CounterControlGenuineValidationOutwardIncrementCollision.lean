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
open CounterControlCleanupSuffixGeometry

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

/-! ## Agreement on the inward ray -/

/-- Two tapes agree at and inward from their common head.  Cleanup may have
erased markers farther outward, so full tape equality is unnecessarily
strong for replaying the next inward search. -/
def InwardRayEq (inward : Turing.Dir)
    (first second : FullTM0.Tape (Symbol numTags)) : Prop :=
  ∀ distance,
    (first.moveN inward distance).read =
      (second.moveN inward distance).read

@[refl] theorem InwardRayEq.refl
    (inward : Turing.Dir) (T : FullTM0.Tape (Symbol numTags)) :
    InwardRayEq inward T T := by
  intro distance
  rfl

/-- Ray agreement transports an exact search gap. -/
theorem InwardRayEq.searchGap
    {inward : Turing.Dir}
    {first second : FullTM0.Tape (Symbol numTags)}
    (agreement : InwardRayEq inward first second)
    {target : Fin 5} {distance : Nat}
    (gap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary target).Matches second inward distance) :
    SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary target).Matches first inward distance := by
  have hagree : ∀ k,
      first (FullTM0.Tape.offset inward k) =
        second (FullTM0.Tape.offset inward k) := by
    intro k
    have heq := agreement k
    cases inward <;>
      simpa [FullTM0.Tape.read, FullTM0.Tape.moveN,
        FullTM0.Tape.offset] using heq
  constructor
  · intro k hk
    rw [hagree k]
    exact gap.blank hk
  · rw [hagree distance]
    exact gap.marked

/-- Erasing the same reached target and departing inward preserves agreement
on the remaining inward ray. -/
theorem InwardRayEq.eraseDepart
    {inward : Turing.Dir}
    {first second : FullTM0.Tape (Symbol numTags)}
    (agreement : InwardRayEq inward first second)
    (distance : Nat) :
    InwardRayEq inward (eraseDepart first inward distance)
      (eraseDepart second inward distance) := by
  intro k
  have heq := agreement (distance + 1 + k)
  change
    (((((first.moveN inward distance).write blankSymbol).move inward).moveN
      inward k).read) =
    (((((second.moveN inward distance).write blankSymbol).move inward).moveN
      inward k).read)
  cases inward <;>
    simp [FullTM0.Tape.read,
      FullTM0.Tape.move, FullTM0.Tape.moveN,
      FullTM0.Tape.offset] at heq ⊢ <;>
    split_ifs <;> try omega
  all_goals
    ring_nf at heq ⊢
    exact heq

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
