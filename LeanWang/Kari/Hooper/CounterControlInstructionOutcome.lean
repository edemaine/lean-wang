/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlDecrementInstructionSemantics

/-!
# Cleanup, collision, and abstract-step outcomes

This module closes the instruction semantics with collision cleanup and the
uniform abstract-step interface shared by increments and decrements.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlInstructionSemantics

open Turing CounterMachine
open BoundedMarkerProgram FramedMarkerTape FramedCounterGeometry
open CounterControlPlan CounterControlCommandAt CounterControlBridge
open CounterControlScheduleSemantics CounterControlCleanupSemantics
  CounterControlFrameBacking CounterControlCoreRoutes

noncomputable section
/-! ## Solved cleanup of a collided frame -/

/-- Under the simultaneous-induction hypothesis, all four boundary erasures
complete without stopping at an intermediate nested frame; the final erase
departs directly onto the adjacent tag at the directional return state. -/
theorem machine_reaches_cleanup_resume_solved
    (base : Nat) (c : Nat.Partrec.Code) (source : Nat)
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T)
    (hreturnDirection :
      (compileCommand base c spec.returnTag).searchDirection = spec.growth)
    (hshort : ShortSearches base c spec.outerDistance)
    (hcommands : ∀ raw, raw ∈ cleanupCommands spec.growth source →
      raw ∈ rawCommands) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨spec.growth, source, cleanupSearchBase⟩,
          atLogical spec.growth (afterFour spec T)
            (layoutEnd spec.registers)⟩
        ⟨resumeState (CanonicalInitializer.radius c)
            (searchState base c
              (rawCommands.get spec.returnTag).address),
          atLogical spec.growth (afterTag spec T) 0⟩ := by
  have hthree :
      RegisterLayout.values spec.registers 3 + 1 < spec.outerDistance := by
    have hcore := spec.core_before_target
    rw [layoutEnd_eq] at hcore
    simp [RegisterLayout.values]
    omega
  have hreturn := machine_reaches_cleanup_return_with base c
    spec.outerDistance source (fun _ => False)
    (solvedCleanupRunner base c spec.outerDistance source spec.growth hshort)
    hthree
    (registerValue_lt_outerDistance h 2)
    (registerValue_lt_outerDistance h 1)
    (registerValue_lt_outerDistance h 0)
    (by simpa [orient_eq_orientDirection] using cleanupGap_three h)
    (by simpa [orient_eq_orientDirection] using cleanupGap_two h)
    (by simpa [orient_eq_orientDirection] using cleanupGap_one h)
    (by simpa [orient_eq_orientDirection] using cleanupGap_zero h)
    hcommands
  rcases hreturn with hreturn | hfailure
  · have hdispatch := machine_sharedReturn_reaches_resume base c
      spec.returnTag (atLogical spec.growth (afterZero spec T) 0)
      (afterZero_read_tag h)
    have hdispatch' : FullTM0.Reaches
        (CounterControlNestingBridge.machine base c)
        ⟨controllerReturn base c spec.growth,
          atLogical spec.growth (afterZero spec T) 0⟩
        ⟨resumeState (CanonicalInitializer.radius c)
            (searchState base c (rawCommands.get spec.returnTag).address),
          atLogical spec.growth (afterTag spec T) 0⟩ := by
      simpa [hreturnDirection, afterTag, atLogical_write] using hdispatch
    exact hreturn.trans hdispatch'
  · exact hfailure.elim

/-- Exact backed-frame cleanup endpoint: after erasing the five boundaries
and the return tag, the suspended outer tape is restored extensionally. -/
theorem machine_reaches_cleanup_outer_solved
    (base : Nat) (c : Nat.Partrec.Code) (source : Nat)
    {spec : Spec numTags} {T outer : FullTM0.Tape (Symbol numTags)}
    (hback : BackedBy spec T outer)
    (hreturnDirection :
      (compileCommand base c spec.returnTag).searchDirection = spec.growth)
    (hshort : ShortSearches base c spec.outerDistance)
    (hcommands : ∀ raw, raw ∈ cleanupCommands spec.growth source →
      raw ∈ rawCommands) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨spec.growth, source, cleanupSearchBase⟩,
          atLogical spec.growth (afterFour spec T)
            (layoutEnd spec.registers)⟩
        ⟨resumeState (CanonicalInitializer.radius c)
            (searchState base c
              (rawCommands.get spec.returnTag).address), outer⟩ := by
  have hrun := machine_reaches_cleanup_resume_solved base c source
    hback.represents hreturnDirection hshort hcommands
  rw [afterTag_eq_outer hback] at hrun
  simpa [atLogical] using hrun

/-- From the exact outward-collision endpoint, the nonblank handoff returns
to erased boundary `4`, and solved cleanup restores the suspended outer tape. -/
theorem machine_reaches_collisionCleanup_solved
    (base : Nat) (c : Nat.Partrec.Code) (source : Nat)
    {spec : Spec numTags} {T outer : FullTM0.Tape (Symbol numTags)}
    (hback : BackedBy spec T outer)
    (hreturnDirection :
      (compileCommand base c spec.returnTag).searchDirection = spec.growth)
    (hcollision : layoutEnd spec.registers + 1 = spec.outerDistance)
    (hshort : ShortSearches base c spec.outerDistance)
    (hentry : cleanupEntryRule spec.growth source ∈ rawDirectRules)
    (hcommands : ∀ raw, raw ∈ cleanupCommands spec.growth source →
      raw ∈ rawCommands) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨resolve base c (directRef spec.growth source testDirectSlot),
          atLogical spec.growth (afterFour spec T) spec.outerDistance⟩
        ⟨resumeState (CanonicalInitializer.radius c)
            (searchState base c
              (rawCommands.get spec.returnTag).address), outer⟩ := by
  have hentryRun := machine_reaches_cleanupEntry base c source
    hback.represents hcollision hentry
  exact hentryRun.trans
    (machine_reaches_cleanup_outer_solved base c source hback
      hreturnDirection hshort hcommands)

/-! ## The outward-collision branch of increment -/

/-- The first (boundary-`4`) increment shift detects an occupied outward
destination exactly when the current frame touches its suspended target. -/
theorem machine_reaches_incrementCollision
    (base : Nat) (c : Nat.Partrec.Code) (source : Nat)
    (success : ControlRef)
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T)
    (hcollision : layoutEnd spec.registers + 1 = spec.outerDistance)
    (hraw : RawCommand.markerShift
      ⟨spec.growth, source, bodySearchBase⟩ 4 .left .right
      success (some .left)
      (some (directRef spec.growth source testDirectSlot)) ∈ rawCommands) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      ⟨searchState base c ⟨spec.growth, source, bodySearchBase⟩,
        atLogical spec.growth T (layoutEnd spec.registers)⟩
      ⟨resolve base c (directRef spec.growth source testDirectSlot),
        atLogical spec.growth
          (CounterControlCleanupSemantics.afterFour spec T)
          spec.outerDistance⟩ := by
  let raw : RawCommand :=
    .markerShift ⟨spec.growth, source, bodySearchBase⟩ 4 .left .right
      success (some .left)
      (some (directRef spec.growth source testDirectSlot))
  let move : MarkerProgram.Move :=
    ⟨4, orient spec.growth .left, orient spec.growth .right⟩
  have hatRaw := CommandAt.compileRawCommand base c raw hraw
  have hspec := compileRawCommand_spec base c raw hraw
  have hat : CommandAt (CanonicalInitializer.radius c) base
      (searchState base c ⟨spec.growth, source, bodySearchBase⟩)
      (.markerShift move
        (resolve base c success)
        (rawTag raw hraw) (some (orient spec.growth .left))
        (some (resolve base c
          (directRef spec.growth source testDirectSlot))))
      (commands base c) := by
    rw [hspec] at hatRaw
    simpa [raw, move, compileRawAtTag, RawCommand.address] using hatRaw
  have hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary 4).Matches
      (atLogical spec.growth T (layoutEnd spec.registers))
      (orient spec.growth .left) 0 := by
    rw [SearchGap.zero]
    change (atLogical spec.growth T (layoutEnd spec.registers)).read =
      boundarySymbol 4
    exact h.read_boundary_four
  have htargetNonblank : logicalTape spec.growth T
      (layoutEnd spec.registers + 1) ≠ blankSymbol := by
    intro hblank
    have htarget : spec.outerTarget.Matches
        (logicalTape spec.growth T (layoutEnd spec.registers + 1)) := by
      rw [show ((layoutEnd spec.registers : Nat) : Int) + 1 =
          (spec.outerDistance : Int) by exact_mod_cast hcollision]
      exact h.target
    exact target_not_blank spec.outerTarget (hblank ▸ htarget)
  have hnonblank :
      (((((atLogical spec.growth T (layoutEnd spec.registers)).moveN
        move.searchDirection 0).write blankSymbol).move
          move.shiftDirection).read ≠ blankSymbol) := by
    rw [FullTM0.Tape.moveN_zero]
    change (((atLogical spec.growth T (layoutEnd spec.registers)).write
      blankSymbol).move (orient spec.growth .right)).read ≠ blankSymbol
    rw [atLogical_write, orient_eq_orientDirection,
      atLogical_move_right, atLogical_read]
    rw [writeLogical_of_ne spec.growth T (layoutEnd spec.registers)
      (layoutEnd spec.registers + 1) blankSymbol (by omega)]
    exact htargetNonblank
  have hrun := CounterControlBridge.machine_reaches_shift_collision
    (coreTable base c) move
    (resolve base c success)
    (resolve base c (directRef spec.growth source testDirectSlot))
    (rawTag raw hraw) (some (orient spec.growth .left)) hat
    (atLogical spec.growth T (layoutEnd spec.registers)) 0 hgap
    (by simp) hnonblank
  have htape :
      (atLogical spec.growth
          (writeLogical spec.growth T (layoutEnd spec.registers) blankSymbol)
          (layoutEnd spec.registers)).move spec.growth =
        atLogical spec.growth
          (writeLogical spec.growth T (layoutEnd spec.registers) blankSymbol)
          spec.outerDistance := by
    have hmove := atLogical_move_right spec.growth
      (writeLogical spec.growth T (layoutEnd spec.registers) blankSymbol)
      (layoutEnd spec.registers)
    rw [OrientedMarkerTape.orientDirection_growth_right, hcollision] at hmove
    exact hmove
  simp only [move, FullTM0.Tape.moveN_zero, atLogical_write,
    orient_eq_orientDirection,
    OrientedMarkerTape.orientDirection_growth_right, htape] at hrun
  simpa [CounterControlNestingBridge.machine,
    BoundedMarkerProgram.entryState,
    CounterControlCleanupSemantics.afterFour,
    CounterControlCleanupSemantics.clearBoundary,
    boundaryOffset_four] using hrun

/-- A colliding compiled increment validates, detects the suspended outer
target on its first shift, erases the active frame, and resumes that outer
search on exactly its original tape. -/
theorem machine_reaches_incrementCollisionInstruction_solved
    (base : Nat) (c : Nat.Partrec.Code) (source next : Nat)
    (register : Register)
    (hrule : (source, .increment register next) ∈
      GlobalSourceProgram.program)
    {spec : Spec numTags}
    {T outer : FullTM0.Tape (Symbol numTags)}
    (hback : BackedBy spec T outer)
    (hreturnDirection :
      (compileCommand base c spec.returnTag).searchDirection = spec.growth)
    (hcollision : layoutEnd spec.registers + 1 = spec.outerDistance)
    (hshort : ShortSearches base c spec.outerDistance) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨logicalState base c spec.growth source,
          atLogical spec.growth T (layoutEnd spec.registers)⟩
        ⟨resumeState (CanonicalInitializer.radius c)
            (searchState base c
              (rawCommands.get spec.returnTag).address), outer⟩ := by
  have h := hback.represents
  have hvalidation := machine_reaches_validation_solved base c spec.growth
    source (.increment register next) hrule h rfl hshort
  let success : ControlRef := match register with
    | .clock => directRef spec.growth source bodyDirectBase
    | _ => searchRef spec.growth source (bodySearchBase + 1)
  have hfirst : RawCommand.markerShift
      ⟨spec.growth, source, bodySearchBase⟩ 4 .left .right success
      (some .left) (some (directRef spec.growth source testDirectSlot)) ∈
        rawCommands := by
    apply command_mem_rawCommands_of_rule spec.growth hrule
    cases register <;>
      simp [success, commandsForRule, incrementCommands,
        incrementShiftCommands, incrementShiftCommandsAux,
        MarkerShift.incrementOrder]
  have hcollisionRun := machine_reaches_incrementCollision base c source
    success h hcollision hfirst
  have hentry : cleanupEntryRule spec.growth source ∈ rawDirectRules := by
    apply directRule_mem_rawDirectRules_of_rule spec.growth hrule
    change cleanupEntryRule spec.growth source ∈
      validationRules spec.growth source ++
        incrementRules spec.growth source next register
    apply List.mem_append_right
    simp [cleanupEntryRule, incrementRules]
  have hcleanupCommands : ∀ raw,
      raw ∈ cleanupCommands spec.growth source → raw ∈ rawCommands := by
    intro raw hraw
    apply command_mem_rawCommands_of_rule spec.growth hrule
    simp [commandsForRule, incrementCommands, hraw]
  have hcleanup := machine_reaches_collisionCleanup_solved base c source
    hback hreturnDirection hcollision hshort hentry hcleanupCommands
  have hvalidation' : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      ⟨logicalState base c spec.growth source,
        atLogical spec.growth T (layoutEnd spec.registers)⟩
      ⟨searchState base c ⟨spec.growth, source, bodySearchBase⟩,
        atLogical spec.growth T (layoutEnd spec.registers)⟩ := by
    simpa [bodyEntry, searchRef, CounterControlPlan.resolve] using hvalidation
  exact hvalidation'.trans (hcollisionRun.trans hcleanup)

/-! ## Uniform abstract-step interface -/

/-- The mandatory first transition of every compiled instruction enters the
first validation search by moving left from boundary `4`. -/
theorem machine_step_validationFirst
    (base : Nat) (c : Nat.Partrec.Code) (source : Nat)
    (instruction : CounterMachine.Instruction)
    (hrule : (source, instruction) ∈ GlobalSourceProgram.program)
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T) :
    FullTM0.step (CounterControlNestingBridge.machine base c)
        ⟨logicalState base c spec.growth source,
          atLogical spec.growth T (layoutEnd spec.registers)⟩ =
      some
        ⟨searchState base c
            ⟨spec.growth, source, validationSearchBase⟩,
          (atLogical spec.growth T (layoutEnd spec.registers)).move
            (orient spec.growth .left)⟩ := by
  let entry : RawDirectRule :=
    ⟨spec.growth, .logical spec.growth source, .boundary 4,
      searchRef spec.growth source validationSearchBase, .left⟩
  have hentry : entry ∈ rawDirectRules := by
    apply directRule_mem_rawDirectRules_of_rule spec.growth hrule
    exact validationRule_mem spec.growth source instruction (by
      simp [entry, validationRules, routeEntryRules,
        MarkerValidation.sweep])
  have hmatch : entry.read.Matches
      (atLogical spec.growth T (layoutEnd spec.registers)).read := by
    change (atLogical spec.growth T (layoutEnd spec.registers)).read =
      boundarySymbol 4
    exact h.read_boundary_four
  have hstep := CounterControlDirectSemantics.step_directRule base c entry
    hentry (atLogical spec.growth T (layoutEnd spec.registers)) hmatch
  change FullTM0.step (CounterControlNestingBridge.machine base c)
      ⟨logicalState base c spec.growth source,
        atLogical spec.growth T (layoutEnd spec.registers)⟩ =
    some
      ⟨searchState base c
          ⟨spec.growth, source, validationSearchBase⟩,
        (atLogical spec.growth T (layoutEnd spec.registers)).move
          (orient spec.growth .left)⟩ at hstep
  exact hstep

/-- The rest of the solved validation sweep, starting strictly after its
mandatory first concrete transition. -/
theorem machine_reaches_validationAfterFirst_solved
    (base : Nat) (c : Nat.Partrec.Code) (source : Nat)
    (instruction : CounterMachine.Instruction)
    (hrule : (source, instruction) ∈ GlobalSourceProgram.program)
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T)
    (hshort : ShortSearches base c spec.outerDistance) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨searchState base c
            ⟨spec.growth, source, validationSearchBase⟩,
          (atLogical spec.growth T (layoutEnd spec.registers)).move
            (orient spec.growth .left)⟩
        ⟨resolve base c (bodyEntry spec.growth source instruction),
          atLogical spec.growth T (layoutEnd spec.registers)⟩ := by
  have hcommands : ∀ raw,
      raw ∈ validationCommands spec.growth source instruction →
        raw ∈ rawCommands := by
    intro raw hraw
    exact command_mem_rawCommands_of_rule spec.growth hrule
      (validationCommand_mem spec.growth source instruction hraw)
  have hcontinuations : ∀ raw,
      raw ∈ routeContinuationRules spec.growth source validationSearchBase
          validationDirectBase MarkerValidation.sweep →
        raw ∈ rawDirectRules := by
    intro raw hraw
    exact directRule_mem_rawDirectRules_of_rule spec.growth hrule
      (validationRule_mem spec.growth source instruction (by
        simp only [validationRules, List.mem_append]
        exact Or.inr hraw))
  have hrun := searches_reach_solved_at base c spec.outerDistance hshort
    spec.growth source validationSearchBase validationDirectBase
    (bodyEntry spec.growth source instruction)
    ⟨3, .left⟩
    [⟨2, .left⟩, ⟨1, .left⟩, ⟨0, .left⟩,
      ⟨1, .right⟩, ⟨2, .right⟩, ⟨3, .right⟩,
      ⟨4, .right⟩]
    T (layoutEnd spec.registers) (layoutEnd spec.registers)
    (by simpa only [MarkerValidation.sweep] using validation_executesWithin h)
    (by
      intro raw hraw
      exact hcommands raw (by
        simpa only [validationCommands, MarkerValidation.sweep] using hraw))
    (by
      intro raw hraw
      exact hcontinuations raw (by
        simpa only [MarkerValidation.sweep] using hraw))
  simpa [searchRef, CounterControlPlan.resolve] using hrun

/-- Data-level evidence that the abstract successor has reached the saved
outer target.  The `Type` wrapper keeps the equality available when
eliminating an `AbstractStepReached` proof. -/
structure AbstractStepCollision (next : CounterMachine.Cfg)
    (spec : Spec numTags) : Type where
  hitsTarget : layoutEnd next.registers = spec.outerDistance

/-- Exact result of one defined abstract counter step.  Each constructor
exposes the mandatory positive first transition and the remaining concrete
execution separately. -/
inductive AbstractStepReached
    (base : Nat) (c : Nat.Partrec.Code) (source : Nat)
    (next : CounterMachine.Cfg) (spec : Spec numTags)
    (T outer : FullTM0.Tape (Symbol numTags)) : Prop where
  | logical
      (hcore : layoutEnd next.registers < spec.outerDistance)
      (nextTape : FullTM0.Tape (Symbol numTags))
      (first : FullTM0.Cfg (Symbol numTags) FiniteTM0.State)
      (firstStep : FullTM0.step (CounterControlNestingBridge.machine base c)
        ⟨logicalState base c spec.growth source,
          atLogical spec.growth T (layoutEnd spec.registers)⟩ = some first)
      (remaining : FullTM0.Reaches
        (CounterControlNestingBridge.machine base c) first
        ⟨logicalState base c spec.growth next.state,
          atLogical spec.growth nextTape (layoutEnd next.registers)⟩)
      (backed : BackedBy (updateSpec spec next.registers hcore)
        nextTape outer) :
      AbstractStepReached base c source next spec T outer
  | boundary
      (collision : AbstractStepCollision next spec)
      (first : FullTM0.Cfg (Symbol numTags) FiniteTM0.State)
      (firstStep : FullTM0.step (CounterControlNestingBridge.machine base c)
        ⟨logicalState base c spec.growth source,
          atLogical spec.growth T (layoutEnd spec.registers)⟩ = some first)
      (remaining : FullTM0.Reaches
        (CounterControlNestingBridge.machine base c) first
        ⟨resumeState (CanonicalInitializer.radius c)
            (searchState base c
              (rawCommands.get spec.returnTag).address), outer⟩) :
      AbstractStepReached base c source next spec T outer

/-- Uniform solved semantics of one defined abstract counter step.  In both
outcomes the mandatory first concrete transition is exposed separately, so
the resulting execution is visibly nonempty.  A noncolliding instruction
reaches the exact backed successor frame; the only other outcome is the
deterministic cleanup caused by an increment colliding with the suspended
outer target. -/
theorem machine_reaches_abstractStep_solved
    (base : Nat) (c : Nat.Partrec.Code) (source : Nat)
    {next : CounterMachine.Cfg}
    {spec : Spec numTags}
    {T outer : FullTM0.Tape (Symbol numTags)}
    (hback : BackedBy spec T outer)
    (hreturnDirection :
      (compileCommand base c spec.returnTag).searchDirection = spec.growth)
    (hstep : CounterMachine.step GlobalSourceProgram.program
      ⟨source, spec.registers⟩ = some next)
    (hshort : ShortSearches base c spec.outerDistance) :
    AbstractStepReached base c source next spec T outer := by
  have hcase := CounterControlStepGeometry.stepCase_of_step_eq_some hstep
  cases hcase with
  | increment register target hlookup hnext =>
      subst next
      have hrule := CounterProgram.rule_mem_of_lookupInstruction_eq_some
        hlookup
      let first : FullTM0.Cfg (Symbol numTags) FiniteTM0.State :=
        ⟨searchState base c ⟨spec.growth, source, validationSearchBase⟩,
          (atLogical spec.growth T (layoutEnd spec.registers)).move
            (orient spec.growth .left)⟩
      have hfirst : FullTM0.step
          (CounterControlNestingBridge.machine base c)
          ⟨logicalState base c spec.growth source,
            atLogical spec.growth T (layoutEnd spec.registers)⟩ =
          some first := by
        simpa [first] using machine_step_validationFirst base c source
          (.increment register target) hrule hback.represents
      have hvalidation : FullTM0.Reaches
          (CounterControlNestingBridge.machine base c) first
          ⟨resolve base c
              (bodyEntry spec.growth source (.increment register target)),
            atLogical spec.growth T (layoutEnd spec.registers)⟩ := by
        simpa [first] using machine_reaches_validationAfterFirst_solved
          base c source (.increment register target) hrule hback.represents
          hshort
      rcases CounterControlStepGeometry.increment_room_or_collision spec
          register with hroom | hcollision
      · have hcommands : ∀ raw,
            raw ∈ incrementShiftCommands spec.growth source register →
              raw ∈ rawCommands := by
          intro raw hraw
          apply command_mem_rawCommands_of_rule spec.growth hrule
          simp [commandsForRule, incrementCommands, hraw]
        have hschedule := machine_reaches_incrementSchedule_solved base c
          source register hback.represents hroom hshort hcommands
        have hhandoff := machine_reaches_incrementHandoff base c source target
          register hrule hback.represents hroom
        have hrecovery :=
          machine_reaches_incrementRecovery_after_increment base c source
            target register hrule hback.represents hroom hshort
        refine .logical hroom (incrementTape spec register T) first hfirst
          (hvalidation.trans
            (hschedule.trans (hhandoff.trans hrecovery))) ?_
        simpa [incrementSpec] using
          (incrementTape_backedBy hback register hroom)
      · let success : ControlRef := match register with
          | .clock => directRef spec.growth source bodyDirectBase
          | _ => searchRef spec.growth source (bodySearchBase + 1)
        have hraw : RawCommand.markerShift
            ⟨spec.growth, source, bodySearchBase⟩ 4 .left .right success
            (some .left)
            (some (directRef spec.growth source testDirectSlot)) ∈
              rawCommands := by
          apply command_mem_rawCommands_of_rule spec.growth hrule
          cases register <;>
            simp [success, commandsForRule, incrementCommands,
              incrementShiftCommands, incrementShiftCommandsAux,
              MarkerShift.incrementOrder]
        have hcollisionRun := machine_reaches_incrementCollision base c
          source success hback.represents hcollision hraw
        have hentry : cleanupEntryRule spec.growth source ∈
            rawDirectRules := by
          apply directRule_mem_rawDirectRules_of_rule spec.growth hrule
          change cleanupEntryRule spec.growth source ∈
            validationRules spec.growth source ++
              incrementRules spec.growth source target register
          apply List.mem_append_right
          simp [cleanupEntryRule, incrementRules]
        have hcleanupCommands : ∀ raw,
            raw ∈ cleanupCommands spec.growth source →
              raw ∈ rawCommands := by
          intro raw hraw'
          apply command_mem_rawCommands_of_rule spec.growth hrule
          simp [commandsForRule, incrementCommands, hraw']
        have hcleanup := machine_reaches_collisionCleanup_solved base c
          source hback hreturnDirection hcollision hshort hentry
          hcleanupCommands
        exact .boundary ⟨by simpa using hcollision⟩ first hfirst
          (hvalidation.trans (hcollisionRun.trans hcleanup))
  | decrementZero register ifZero ifPositive hlookup hzero hnext =>
      subst next
      have hrule := CounterProgram.rule_mem_of_lookupInstruction_eq_some
        hlookup
      let first : FullTM0.Cfg (Symbol numTags) FiniteTM0.State :=
        ⟨searchState base c ⟨spec.growth, source, validationSearchBase⟩,
          (atLogical spec.growth T (layoutEnd spec.registers)).move
            (orient spec.growth .left)⟩
      have hfirst : FullTM0.step
          (CounterControlNestingBridge.machine base c)
          ⟨logicalState base c spec.growth source,
            atLogical spec.growth T (layoutEnd spec.registers)⟩ =
          some first := by
        simpa [first] using machine_step_validationFirst base c source
          (.decrement register ifZero ifPositive) hrule hback.represents
      have hvalidation : FullTM0.Reaches
          (CounterControlNestingBridge.machine base c) first
          ⟨resolve base c (bodyEntry spec.growth source
              (.decrement register ifZero ifPositive)),
            atLogical spec.growth T (layoutEnd spec.registers)⟩ := by
        simpa [first] using machine_reaches_validationAfterFirst_solved
          base c source (.decrement register ifZero ifPositive) hrule
          hback.represents hshort
      have hroute := machine_reaches_decrementToTest_solved base c source
        ifZero ifPositive register hrule hback.represents hshort
      have htest := machine_reaches_decrementTest base c source ifZero
        ifPositive register hrule T (by
          rw [atLogical_read]
          exact hback.represents.boundary _)
      have hzeroRoute := machine_reaches_decrementZeroRecovery_solved base c
        source ifZero ifPositive register hrule hback.represents hzero hshort
      refine .logical spec.core_before_target T first hfirst
        (hvalidation.trans (hroute.trans (htest.trans hzeroRoute))) ?_
      simpa [updateSpec] using hback
  | decrementPositive register ifZero ifPositive hlookup hpositive hnext =>
      subst next
      have hrule := CounterProgram.rule_mem_of_lookupInstruction_eq_some
        hlookup
      let first : FullTM0.Cfg (Symbol numTags) FiniteTM0.State :=
        ⟨searchState base c ⟨spec.growth, source, validationSearchBase⟩,
          (atLogical spec.growth T (layoutEnd spec.registers)).move
            (orient spec.growth .left)⟩
      have hfirst : FullTM0.step
          (CounterControlNestingBridge.machine base c)
          ⟨logicalState base c spec.growth source,
            atLogical spec.growth T (layoutEnd spec.registers)⟩ =
          some first := by
        simpa [first] using machine_step_validationFirst base c source
          (.decrement register ifZero ifPositive) hrule hback.represents
      have hvalidation : FullTM0.Reaches
          (CounterControlNestingBridge.machine base c) first
          ⟨resolve base c (bodyEntry spec.growth source
              (.decrement register ifZero ifPositive)),
            atLogical spec.growth T (layoutEnd spec.registers)⟩ := by
        simpa [first] using machine_reaches_validationAfterFirst_solved
          base c source (.decrement register ifZero ifPositive) hrule
          hback.represents hshort
      have hroute := machine_reaches_decrementToTest_solved base c source
        ifZero ifPositive register hrule hback.represents hshort
      have htest := machine_reaches_decrementTest base c source ifZero
        ifPositive register hrule T (by
          rw [atLogical_read]
          exact hback.represents.boundary _)
      have hhandoff := machine_reaches_decrementPositiveHandoff base c source
        ifZero ifPositive register hrule hback.represents hpositive
      have hcommands : ∀ raw,
          raw ∈ decrementShiftCommands spec.growth source register →
            raw ∈ rawCommands := by
        intro raw hraw
        apply command_mem_rawCommands_of_rule spec.growth hrule
        simp [commandsForRule, decrementCommands, hraw]
      have hschedule := machine_reaches_decrementSchedule_solved base c source
        register hback hpositive hshort hcommands
      have hfinish := machine_reaches_decrementPositiveFinish base c source
        ifZero ifPositive register hrule T hpositive
      let hcore := CounterControlStepGeometry.decrement_has_room spec register
        hpositive
      refine .logical hcore (decrementTape spec register T) first hfirst
        (hvalidation.trans
          (hroute.trans
            (htest.trans
              (hhandoff.trans (hschedule.1.trans hfinish))))) ?_
      simpa [hcore, decrementSpec] using hschedule.2

end

end CounterControlInstructionSemantics
end Hooper
end Kari
end LeanWang
