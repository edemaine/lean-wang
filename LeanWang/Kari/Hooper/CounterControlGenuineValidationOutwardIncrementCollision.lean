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

theorem InwardRayEq.trans
    {inward : Turing.Dir}
    {first second third : FullTM0.Tape (Symbol numTags)}
    (firstSecond : InwardRayEq inward first second)
    (secondThird : InwardRayEq inward second third) :
    InwardRayEq inward first third := by
  intro distance
  exact (firstSecond distance).trans (secondThird distance)

/-- Clearing the cell just behind an inward-moving head does not change the
ray at or ahead of that head. -/
theorem InwardRayEq.clearedBehind
    (T : FullTM0.Tape (Symbol numTags)) (inward : Turing.Dir) :
    InwardRayEq inward ((T.write blankSymbol).move inward)
      (T.move inward) := by
  intro distance
  have hread := CanonicalInitializerProgram.read_moveN_write_of_pos
    T blankSymbol inward (distance + 1) (by omega)
  rw [FullTM0.Tape.move_moveN, FullTM0.Tape.move_moveN]
  exact hread

/-! ## Reversing one retained outward gap -/

private theorem move_move_opposite
    (T : FullTM0.Tape (Symbol numTags)) (direction : Turing.Dir) :
    (T.move direction).move (NestingMachine.opposite direction) = T := by
  funext position
  cases direction <;>
    simp [NestingMachine.opposite, FullTM0.Tape.move]

private theorem reverseGap_of_source_boundary
    {T : FullTM0.Tape (Symbol numTags)} {direction : Turing.Dir}
    {distance : Nat} {found source : Fin 5}
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary found).Matches T direction distance)
    (hsource : (T.move (NestingMachine.opposite direction)).read =
      boundarySymbol source) :
    SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary source).Matches
      ((T.moveN direction distance).move
        (NestingMachine.opposite direction))
      (NestingMachine.opposite direction) distance := by
  constructor
  · intro i hi
    let j := distance - i - 1
    have hj : j < distance := by
      dsimp [j]
      omega
    have hblank := hgap.blank hj
    cases direction with
    | left =>
        simp only [NestingMachine.opposite,
          FullTM0.Tape.move_apply_delta, FullTM0.Tape.moveN_apply,
          FullTM0.Tape.offset_left, FullTM0.Tape.offset_right,
          FullTM0.Tape.delta_right] at hblank ⊢
        rw [show -(j : Int) = (i : Int) + 1 - (distance : Int) by
          dsimp [j]
          omega] at hblank
        exact hblank
    | right =>
        simp only [NestingMachine.opposite,
          FullTM0.Tape.move_apply_delta, FullTM0.Tape.moveN_apply,
          FullTM0.Tape.offset_left, FullTM0.Tape.offset_right,
          FullTM0.Tape.delta_left] at hblank ⊢
        rw [show (j : Int) = -(i : Int) - 1 + (distance : Int) by
          dsimp [j]
          omega] at hblank
        exact hblank
  · cases direction <;>
      simpa [Target.Matches, FullTM0.Tape.read,
        NestingMachine.opposite, FullTM0.Tape.move_apply_delta,
        FullTM0.Tape.moveN_apply, FullTM0.Tape.offset_left,
        FullTM0.Tape.offset_right, FullTM0.Tape.delta_left,
        FullTM0.Tape.delta_right] using hsource

/-- After the found endpoint is cleared and the head departs back toward the
source, the preserved outward gap is an exact inward gap of the same length. -/
theorem reverseGap_after_clear_depart
    {sourceTape : FullTM0.Tape (Symbol numTags)}
    {outward : Turing.Dir} {distance : Nat} {found source : Fin 5}
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary found).Matches (sourceTape.move outward)
      outward distance)
    (hsource : sourceTape.read = boundarySymbol source) :
    SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary source).Matches
      ((((sourceTape.move outward).moveN outward distance).write
        blankSymbol).move (NestingMachine.opposite outward))
      (NestingMachine.opposite outward) distance := by
  have hsource' : ((sourceTape.move outward).move
      (NestingMachine.opposite outward)).read = boundarySymbol source := by
    rw [move_move_opposite]
    exact hsource
  have hreverse := reverseGap_of_source_boundary hgap hsource'
  exact (InwardRayEq.clearedBehind
    ((sourceTape.move outward).moveN outward distance)
    (NestingMachine.opposite outward)).searchGap hreverse

/-- At the collision entry the cleared endpoint itself contributes one
additional blank cell before the same reverse gap. -/
theorem reverseGap_from_cleared_endpoint
    {sourceTape : FullTM0.Tape (Symbol numTags)}
    {outward : Turing.Dir} {distance : Nat} {found source : Fin 5}
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary found).Matches (sourceTape.move outward)
      outward distance)
    (hsource : sourceTape.read = boundarySymbol source) :
    SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary source).Matches
      (((sourceTape.move outward).moveN outward distance).write blankSymbol)
      (NestingMachine.opposite outward) (distance + 1) := by
  let foundTape := (sourceTape.move outward).moveN outward distance
  have htail : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary source).Matches
      ((foundTape.write blankSymbol).move
        (NestingMachine.opposite outward))
      (NestingMachine.opposite outward) distance := by
    simpa only [foundTape] using reverseGap_after_clear_depart hgap hsource
  have hmove : (foundTape.write blankSymbol).moveN
      (NestingMachine.opposite outward) 1 =
        (foundTape.write blankSymbol).move
          (NestingMachine.opposite outward) := by
    simpa using (FullTM0.Tape.move_moveN (foundTape.write blankSymbol)
      (NestingMachine.opposite outward) 0).symm
  have hprefix : ∀ i < 1,
      ((foundTape.write blankSymbol)
        (FullTM0.Tape.offset (NestingMachine.opposite outward) i)) =
          blankSymbol := by
    intro i hi
    have hi0 : i = 0 := by omega
    subst i
    simp
  have hfull :=
    CounterControlArbitrarySearch.SearchGap.prepend_moveN hprefix (by
      rw [hmove]
      exact htail)
  simpa [foundTape, Nat.add_comm] using hfull

private theorem outward_then_reverse
    (T : FullTM0.Tape (Symbol numTags)) (outward : Turing.Dir)
    (distance : Nat) :
    ((((T.move outward).moveN outward distance).move
      (NestingMachine.opposite outward)).moveN
        (NestingMachine.opposite outward) distance) = T := by
  funext position
  cases outward <;>
    simp [NestingMachine.opposite, FullTM0.Tape.move,
      FullTM0.Tape.moveN, FullTM0.Tape.offset] <;>
    congr 1 <;> ring

/-- Once a reversed retained gap has been erased, its actual tape agrees on
the remaining inward ray with the canonical tape obtained by clearing its
source boundary and departing inward. -/
theorem clearedRouteStep_ray
    (sourceTape : FullTM0.Tape (Symbol numTags))
    (outward : Turing.Dir) (distance : Nat) :
    InwardRayEq (NestingMachine.opposite outward)
      (eraseDepart
        ((((sourceTape.move outward).moveN outward distance).write
          blankSymbol).move (NestingMachine.opposite outward))
        (NestingMachine.opposite outward) distance)
      ((sourceTape.write blankSymbol).move
        (NestingMachine.opposite outward)) := by
  let foundTape := (sourceTape.move outward).moveN outward distance
  have hagreement := (InwardRayEq.clearedBehind foundTape
    (NestingMachine.opposite outward)).eraseDepart distance
  have hnormalize : eraseDepart
      (foundTape.move (NestingMachine.opposite outward))
        (NestingMachine.opposite outward) distance =
      (sourceTape.write blankSymbol).move
        (NestingMachine.opposite outward) := by
    simp only [eraseDepart]
    rw [outward_then_reverse]
  rw [hnormalize] at hagreement
  exact hagreement

/-- The same ray statement at the first cleanup stage, where the collision
entry is still centered on the cleared final endpoint. -/
theorem clearedEndpointStep_ray
    (sourceTape : FullTM0.Tape (Symbol numTags))
    (outward : Turing.Dir) (distance : Nat) :
    InwardRayEq (NestingMachine.opposite outward)
      (eraseDepart
        (((sourceTape.move outward).moveN outward distance).write blankSymbol)
        (NestingMachine.opposite outward) (distance + 1))
      ((sourceTape.write blankSymbol).move
        (NestingMachine.opposite outward)) := by
  have hstep := clearedRouteStep_ray sourceTape outward distance
  simpa only [eraseDepart, FullTM0.Tape.move_moveN,
    Nat.add_comm] using hstep

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
