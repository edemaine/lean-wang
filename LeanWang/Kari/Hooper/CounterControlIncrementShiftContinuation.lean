/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlGuardedIncrementEmbedding
import LeanWang.Kari.Hooper.CounterControlGuardedCleanupProgress
import LeanWang.Kari.Hooper.CounterControlPositiveGuarding
import LeanWang.Kari.Hooper.CounterControlZeroGuarding

/-!
# Completed increment-shift continuations

Positive arbitrary gaps consume one blank cell and reuse the strict guarded
increment theorem.  At distance zero, a later shift has no collision exit and
immortality forces its missing guard.  The first shift can collide; in that
case its exact collision edge enters the existing cleanup suffix, which
returns a guarded generated search.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlIncrementShiftContinuation

open Turing CounterMachine
open BoundedMarkerProgram CounterControlPlan CounterControlSearchSystem
open CounterControlGlobalUnnesting CounterControlGuardedSearch
open CounterControlParentContinuation CounterControlGuardedParentContinuation
open CounterControlExactCommandContinuation
open CounterControlResumedShiftCoordinates CounterControlCleanupRoute
open CounterControlCleanupSemantics

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-! ## The occupied first-shift branch -/

/-- An occupied first increment shift takes its configured collision edge,
then the nonblank direct edge into cleanup.  Generic cleanup progress returns
a guarded search, which is automatically monotone from distance zero. -/
private theorem foundMonotoneGuardedEntryOutcome_of_firstCollision
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (current : GenuineSearch base c)
    (hzero : current.distance = 0)
    (growth : Turing.Dir) (source : Nat) (register : Register) (next : Nat)
    (hrule : (source, .increment register next) ∈
      GlobalSourceProgram.program)
    (expected : Fin 5) (success : ControlRef)
    (hraw : current.selectedRaw = .markerShift
      ⟨growth, source, bodySearchBase⟩ expected .left .right success
      (some .left) (some (directRef growth source testDirectSlot)))
    (hoccupied : ShiftDestinationOccupied current.selectedRaw
      current.foundTape)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) (foundCfg current)) :
    Nonempty (FoundMonotoneGuardedEntryOutcome current) := by
  let move : MarkerProgram.Move :=
    ⟨expected, orient growth .left, orient growth .right⟩
  have hread : current.foundTape.read = boundarySymbol expected := by
    have htarget := current.selectedRaw_target_matches_foundTape
    rw [CounterControlCommandAt.compileRawCommand_spec] at htarget
    simpa [hraw, CounterControlCommandAt.compileRawAtTag,
      Command.target, Target.Matches] using htarget
  have hatRaw := CounterControlCommandAt.CommandAt.compileRawCommand
    base c current.selectedRaw current.selectedRaw_mem
  rw [CounterControlCommandAt.compileRawCommand_spec] at hatRaw
  have hat : CommandAt (CanonicalInitializer.radius c) base
      (searchState base c ⟨growth, source, bodySearchBase⟩)
      (.markerShift move (resolve base c success)
        (CounterControlCommandAt.rawTag current.selectedRaw
          current.selectedRaw_mem)
        (some (orient growth .left))
        (some (resolve base c (directRef growth source testDirectSlot))))
      (commands base c) := by
    simpa [hraw, move, CounterControlCommandAt.compileRawAtTag,
      RawCommand.address] using hatRaw
  let collisionTape := (current.foundTape.write blankSymbol).move
    (orient growth .right)
  have hcollisionLocal :=
    BoundedMarkerContinuation.machine_reaches_shift_collision_native
      (coreTable base c) move (resolve base c success)
      (resolve base c (directRef growth source testDirectSlot))
      (CounterControlCommandAt.rawTag current.selectedRaw
        current.selectedRaw_mem)
      (some (orient growth .left)) hat current.foundTape hread (by
        simpa [hraw, move, ShiftDestinationOccupied] using hoccupied)
  have hcollision : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c) (foundCfg current)
      ⟨resolve base c (directRef growth source testDirectSlot),
        collisionTape⟩ := by
    rw [current.foundCfg_eq, hraw]
    simpa [CounterControlNestingBridge.machine, move, collisionTape,
      controllerCoreEntry_eq, RawCommand.address] using hcollisionLocal
  have hnonblank : collisionTape.read ≠ blankSymbol := by
    simpa [collisionTape, hraw, ShiftDestinationOccupied] using hoccupied
  have hentryRule : cleanupEntryRule growth source ∈ rawDirectRules := by
    apply
      CounterControlInstructionSemantics.directRule_mem_rawDirectRules_of_rule
        growth hrule
    simp [directRulesForRule, incrementRules, cleanupEntryRule]
  have hentryLocal := CounterControlDirectSemantics.reaches_directRule
    base c (cleanupEntryRule growth source) hentryRule collisionTape (by
      simpa [cleanupEntryRule, RawRead.Matches] using hnonblank)
  let cleanupOuter := collisionTape.move (orient growth .left)
  have hentry : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      ⟨resolve base c (directRef growth source testDirectSlot),
        collisionTape⟩
      ⟨searchState base c ⟨growth, source, cleanupSearchBase⟩,
        cleanupOuter⟩ := by
    change FullTM0.Reaches
      (FiniteTM0.machine (CounterControlPlan.table base c)) _ _
    simpa [cleanupEntryRule, searchRef, resolve, cleanupOuter] using
      hentryLocal
  have himmortalEntry : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      ⟨searchState base c ⟨growth, source, cleanupSearchBase⟩,
        cleanupOuter⟩ :=
    FullTM0.ImmortalFrom.of_reaches himmortal (hcollision.trans hentry)
  let cleanupRaw := CounterControlCleanupRoute.command growth source .three
  have hcleanupRaw : cleanupRaw ∈ rawCommands := by
    exact command_mem_rawCommands_of_increment growth source register next
      hrule .three
  rcases
      CounterControlGeneratedSearchGap.gap_of_reachable_search_on_immortal_orbit
        base c hmortal cleanupRaw hcleanupRaw cleanupOuter (by
          simpa [cleanupRaw, CounterControlCleanupRoute.command,
            CounterControlCleanupRoute.Stage.slot, RawCommand.address] using
            himmortalEntry) with
    ⟨distance, hgap⟩
  let cleanupSearch : GenuineSearch base c := {
    search := CounterControlCommandAt.rawTag cleanupRaw hcleanupRaw
    outer := cleanupOuter
    distance := distance
    gap := by
      have hcommand : CounterControlSearchSystem.command base c
          (CounterControlCommandAt.rawTag cleanupRaw hcleanupRaw) =
        CounterControlCommandAt.compileRawCommand base c cleanupRaw
          hcleanupRaw := by
        rfl
      rw [hcommand]
      exact hgap }
  have hcleanupCfg : cleanupSearch.cfg =
      ⟨searchState base c ⟨growth, source, cleanupSearchBase⟩,
        cleanupOuter⟩ := by
    change
      (searchSystem base c).startCfg
          (CounterControlCommandAt.rawTag cleanupRaw hcleanupRaw)
          cleanupOuter = _
    change
      (⟨CounterControlSearchSystem.commandOffset base c
          (CounterControlCommandAt.rawTag cleanupRaw hcleanupRaw),
        cleanupOuter⟩ : FullTM0.Cfg (Symbol numTags) FiniteTM0.State) = _
    unfold CounterControlSearchSystem.commandOffset
    rw [CounterControlCommandAt.rawCommands_get_rawTag]
    simp [cleanupRaw, CounterControlCleanupRoute.command,
      CounterControlCleanupRoute.Stage.slot, RawCommand.address]
  have hcleanupMem : rawCommands.get cleanupSearch.search ∈
      cleanupCommands growth source := by
    change rawCommands.get
        (CounterControlCommandAt.rawTag cleanupRaw hcleanupRaw) ∈ _
    rw [CounterControlCommandAt.rawCommands_get_rawTag]
    exact command_mem_cleanupCommands growth source .three
  have himmortalCleanup : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) cleanupSearch.cfg := by
    rw [hcleanupCfg]
    exact himmortalEntry
  rcases
      CounterControlGuardedCleanupProgress.reaches_larger_guardedSearch_of_genuine_cleanup
        base c hmortal cleanupSearch growth source register next hrule
        hcleanupMem himmortalCleanup with
    ⟨finish, hfinish, _hdistance⟩
  refine ⟨.nextSearch finish ?_ ?_⟩
  · exact hcollision.trans (hentry.trans (by
      rw [← hcleanupCfg]
      exact hfinish))
  · simp [hzero]

/-! ## Positive and total arbitrary continuations -/

/-- A positive arbitrary increment-shift gap consumes one blank cell and
reuses the strict guarded parent continuation. -/
theorem foundMonotoneGuardedEntryOutcome_of_incrementShift_positive
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (current : GenuineSearch base c)
    (hpositive : 0 < current.distance)
    (growth : Turing.Dir) (source : Nat) (register : Register) (next : Nat)
    (hrule : (source, .increment register next) ∈
      GlobalSourceProgram.program)
    (hcommand : current.selectedRaw ∈
      incrementShiftCommands growth source register)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) (foundCfg current)) :
    Nonempty (FoundMonotoneGuardedEntryOutcome current) := by
  let guarded := CounterControlPositiveGuarding.guardedTail current hpositive
  have hselected : guarded.selectedRaw = current.selectedRaw := rfl
  have hcommand' : guarded.selectedRaw ∈
      incrementShiftCommands growth source register := by
    simpa [hselected] using hcommand
  have hfound :=
    CounterControlPositiveGuarding.foundCfg_guardedTail current hpositive
  have himmortalGuarded : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      (foundCfg guarded.current) := by
    simpa [guarded, hfound] using himmortal
  rcases
      CounterControlGuardedIncrementEmbedding.incrementShift_foundGuardedParentOutcome
        base c hmortal guarded himmortalGuarded growth source register next
        hrule hcommand' with
    ⟨parent⟩
  exact ⟨CounterControlPositiveGuarding.monotone_of_guardedTail_parent
    current hpositive (by simpa [guarded] using parent)⟩

/-- Every arbitrary increment shift on an immortal orbit has the exact weak
monotone continuation required by the increment-shift family field. -/
theorem foundMonotoneGuardedEntryOutcome_of_incrementShift
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (current : GenuineSearch base c)
    (growth : Turing.Dir) (source : Nat) (register : Register) (next : Nat)
    (hrule : (source, .increment register next) ∈
      GlobalSourceProgram.program)
    (hcommand : current.selectedRaw ∈
      incrementShiftCommands growth source register)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) (foundCfg current)) :
    Nonempty (FoundMonotoneGuardedEntryOutcome current) := by
  by_cases hzero : current.distance = 0
  · rcases incrementShiftPosition_of_mem growth source register
        current.selectedRaw hcommand with ⟨position⟩
    cases hbefore : position.before with
    | nil =>
        have hraw := position.raw_eq
        simp [hbefore] at hraw
        by_cases hoccupied : ShiftDestinationOccupied current.selectedRaw
            current.foundTape
        · exact foundMonotoneGuardedEntryOutcome_of_firstCollision
            base c hmortal current hzero growth source register next hrule
            position.current
            (match position.remaining with
              | [] => directRef growth source bodyDirectBase
              | _ :: _ => searchRef growth source (bodySearchBase + 1))
            hraw hoccupied himmortal
        · rcases
              CounterControlZeroGuarding.guarded_of_zero_markerShift_destinationFree
                base c current hzero
                ⟨growth, source, bodySearchBase⟩ position.current .left .right
                (match position.remaining with
                  | [] => directRef growth source bodyDirectBase
                  | _ :: _ => searchRef growth source (bodySearchBase + 1))
                (some .left)
                (some (directRef growth source testDirectSlot)) hraw hoccupied
              with ⟨guarded, hcurrent⟩
          have hcommand' : guarded.selectedRaw ∈
              incrementShiftCommands growth source register := by
            simpa only [GuardedSearch.selectedRaw,
              GenuineSearch.selectedRaw, hcurrent] using hcommand
          rcases
              CounterControlGuardedIncrementEmbedding.incrementShift_foundGuardedParentOutcome
                base c hmortal guarded (by simpa [hcurrent] using himmortal)
                growth source register next hrule hcommand' with
            ⟨parent⟩
          exact ⟨CounterControlZeroGuarding.monotone_of_zero_guardedParent
            current hzero guarded hcurrent parent⟩
    | cons first before =>
        have hraw := position.raw_eq
        simp [hbefore] at hraw
        rcases
            CounterControlZeroGuarding.guarded_of_zero_markerShift_noCollision
              base c current hzero
              ⟨growth, source,
                bodySearchBase + (first :: before).length⟩
              position.current .left .right
              (match position.remaining with
                | [] => directRef growth source bodyDirectBase
                | _ :: _ => searchRef growth source
                    (bodySearchBase + (first :: before).length + 1))
              (some .left) hraw himmortal with
          ⟨guarded, hcurrent⟩
        have hcommand' : guarded.selectedRaw ∈
            incrementShiftCommands growth source register := by
          simpa only [GuardedSearch.selectedRaw,
            GenuineSearch.selectedRaw, hcurrent] using hcommand
        rcases
            CounterControlGuardedIncrementEmbedding.incrementShift_foundGuardedParentOutcome
              base c hmortal guarded (by simpa [hcurrent] using himmortal)
              growth source register next hrule hcommand' with
          ⟨parent⟩
        exact ⟨CounterControlZeroGuarding.monotone_of_zero_guardedParent
          current hzero guarded hcurrent parent⟩
  · exact foundMonotoneGuardedEntryOutcome_of_incrementShift_positive
      base c hmortal current (Nat.pos_of_ne_zero hzero) growth source register
      next hrule hcommand himmortal

end

end CounterControlIncrementShiftContinuation
end Hooper
end Kari
end LeanWang
