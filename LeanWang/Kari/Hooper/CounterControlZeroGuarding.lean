/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.BoundedMarkerContinuation
import LeanWang.Kari.Hooper.CounterControlControllerEntrySemantics
import LeanWang.Kari.Hooper.CounterControlGenuineCoordinates
import LeanWang.Kari.Hooper.CounterControlGuardedParentContinuation

/-!
# Guarding immortal distance-zero marker shifts

A distance-zero genuine marker shift has no blank search prefix.  When the
compiled command has no collision exit, however, an occupied shift
destination reaches its verification state and halts.  Immortality therefore
forces that neighboring cell to be blank, which is exactly the missing guard.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlZeroGuarding

open Turing
open BoundedMarkerProgram CounterControlPlan CounterControlSearchSystem
open CounterControlGlobalUnnesting CounterControlGuardedSearch
open CounterControlParentContinuation CounterControlGuardedParentContinuation
open CounterControlExactCommandContinuation

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

private theorem write_neighbor_read
    (T : FullTM0.Tape (Symbol numTags)) (written : Symbol numTags)
    (direction : Turing.Dir) :
    ((T.write written).move direction).read = (T.move direction).read := by
  cases direction <;>
    simp [FullTM0.Tape.read, FullTM0.Tape.move, FullTM0.Tape.write]

/-- A selected distance-zero marker shift without a collision reference is
guarded on every immortal found-state orbit. -/
theorem guarded_of_zero_markerShift_noCollision
    (base : Nat) (c : Nat.Partrec.Code)
    (current : GenuineSearch base c)
    (hzero : current.distance = 0)
    (address : SearchAddress) (expected : Fin 5)
    (search shift : Turing.Dir) (success : ControlRef)
    (departure : Option Turing.Dir)
    (hraw : current.selectedRaw = .markerShift address expected search shift
      success departure none)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) (foundCfg current)) :
    ∃ guarded : GuardedSearch base c, guarded.current = current := by
  let raw : RawCommand := .markerShift address expected search shift success
    departure none
  have hmem : raw ∈ rawCommands := by
    simpa [raw, hraw] using current.selectedRaw_mem
  have hsearch : orient address.growth search = current.direction := by
    have hdirection := current.selectedRaw_direction_eq
    rw [CounterControlCommandAt.compileRawCommand_searchDirection]
      at hdirection
    rw [hraw] at hdirection
    exact hdirection
  have hshift : orient address.growth shift =
      NestingMachine.opposite current.direction := by
    have hopposite :=
      CounterControlRawCallerClassification.markerShift_oriented_shift_eq_opposite_search
        address expected search shift success departure none hmem
    rw [hsearch] at hopposite
    exact hopposite
  have hfound : current.foundTape = current.outer := by
    simp [GenuineSearch.foundTape, hzero]
  have hread : current.foundTape.read = boundarySymbol expected := by
    have hmatch := current.selectedRaw_target_matches_foundTape
    rw [CounterControlCommandAt.compileRawCommand_spec] at hmatch
    simpa [hraw, CounterControlCommandAt.compileRawAtTag,
      Command.target, Target.Matches] using hmatch
  have hfree : ¬ ShiftDestinationOccupied current.selectedRaw
      current.foundTape := by
    intro hoccupied
    have hoccupied' : ((current.foundTape.write blankSymbol).move
        (orient address.growth shift)).read ≠ blankSymbol := by
      simpa [hraw, ShiftDestinationOccupied] using hoccupied
    let move : MarkerProgram.Move :=
      ⟨expected, orient address.growth search, orient address.growth shift⟩
    have hatRaw := CounterControlCommandAt.CommandAt.compileRawCommand
      base c raw hmem
    rw [CounterControlCommandAt.compileRawCommand_spec] at hatRaw
    have hat : CommandAt (CanonicalInitializer.radius c) base
        (searchState base c address)
        (.markerShift move (resolve base c success)
          (CounterControlCommandAt.rawTag raw hmem)
          (departure.map (orient address.growth)) none)
        (commands base c) := by
      simpa [raw, move, CounterControlCommandAt.compileRawAtTag,
        RawCommand.address] using hatRaw
    let destination := (current.foundTape.write blankSymbol).move
      move.shiftDirection
    have hverify : FullTM0.Reaches
        (CounterControlNestingBridge.machine base c) (foundCfg current)
        ⟨verifyState (CanonicalInitializer.radius c)
            (searchState base c address), destination⟩ := by
      have hrun := BoundedMarkerContinuation.machine_reaches_shift_verify_native
        (coreTable base c) move (resolve base c success)
        (CounterControlCommandAt.rawTag raw hmem)
        (departure.map (orient address.growth)) none hat current.foundTape
        (by simpa [move] using hread)
      rw [current.foundCfg_eq, hraw]
      simpa [CounterControlNestingBridge.machine, move, destination,
        controllerCoreEntry_eq, RawCommand.address] using hrun
    let command : Command numTags :=
      .markerShift move (resolve base c success)
        (CounterControlCommandAt.rawTag raw hmem)
        (departure.map (orient address.growth)) none
    let terminal : FullTM0.Cfg (Symbol numTags) FiniteTM0.State :=
      ⟨verifyState (CanonicalInitializer.radius c)
        (searchState base c address), destination⟩
    have hcontinuationSource : terminal.q ∈ FiniteTM0.sourceStates
        (continuationTable (CanonicalInitializer.radius c)
          (searchState base c address) (controllerCoreEntry base c)
          command) := by
      apply List.mem_map.mpr
      refine ⟨FiniteTM0.Rule.mk terminal.q blankSymbol
        (match departure.map (orient address.growth) with
          | none => resolve base c success
          | some _ => departState (CanonicalInitializer.radius c)
              (searchState base c address))
        (.write (boundarySymbol expected)), ?_, rfl⟩
      unfold continuationTable
      dsimp [terminal, command, move]
      aesop
    have hsource : terminal.q ∈ FiniteTM0.sourceStates
        (commandTable (CanonicalInitializer.radius c)
          (searchState base c address) (controllerCoreEntry base c)
          command) := by
      simp only [commandTable, FiniteTM0.sourceStates, List.map_append,
        List.mem_append]
      exact Or.inl hcontinuationSource
    have hlocal : FullTM0.step
        (FiniteTM0.machine
          (commandTable (CanonicalInitializer.radius c)
            (searchState base c address) (controllerCoreEntry base c)
            command)) terminal = none := by
      have hdestination : destination.read ≠ blankSymbol := by
        simpa [destination, move] using hoccupied'
      have hcontinuationLookup : FiniteTM0.lookupAction
          (continuationTable (CanonicalInitializer.radius c)
            (searchState base c address) (controllerCoreEntry base c)
            command) terminal.q terminal.tape.read = none := by
        cases hgrowth : address.growth <;> cases shift <;>
          cases departure <;>
          apply FiniteTM0.lookupAction_eq_none_of_key_not_mem <;>
          simp [command, terminal, continuationTable, move, destination,
            verifyState, launchState, foundState, clearState, departState,
            resumeState, NestingMachine.localLaunchState,
            NestingMachine.localSuccessState, NestingMachine.localWidth,
            NestingMachine.bound, orient, hgrowth, FullTM0.Tape.read,
            FullTM0.Tape.move, FullTM0.Tape.write] at hoccupied' ⊢
        all_goals
          constructor
          · intro
            exact hoccupied'
          constructor
          · intro heq
            have heq'' :
                searchState base c address +
                    ((2 * (CanonicalInitializer.radius c + 1) + 3) + 1) =
                  searchState base c address +
                    (CanonicalInitializer.radius c + 1 + 1) := by
              simpa only [Nat.add_assoc] using heq
            have heq' :
                (2 * (CanonicalInitializer.radius c + 1) + 3) + 1 =
                  CanonicalInitializer.radius c + 1 + 1 := by
              exact Nat.add_left_cancel heq''
            omega
          · exact hoccupied'
      have hcommandLookup :=
        CounterControlControllerNormalization.lookupAction_commandTable_of_continuation
          (CanonicalInitializer.radius c) (searchState base c address)
          (controllerCoreEntry base c) command terminal.q terminal.tape.read
          hcontinuationSource
      rw [hcontinuationLookup] at hcommandLookup
      simp only [FullTM0.step, FiniteTM0.machine_apply]
      rw [hcommandLookup]
      rfl
    have hterminal : FullTM0.step
        (CounterControlNestingBridge.machine base c) terminal = none := by
      rw [CounterControlControllerEntrySemantics.step_table_of_commandAt
        base c hat terminal hsource]
      exact hlocal
    have hhalts : FullTM0.HaltsFrom
        (CounterControlNestingBridge.machine base c) (foundCfg current) :=
      ⟨terminal, hverify, hterminal⟩
    exact
      ((FullTM0.HaltsFrom.immortalFrom_iff_not
        (CounterControlNestingBridge.machine base c) (foundCfg current)).mp
          himmortal) hhalts
  have hblankDestination : ((current.foundTape.write blankSymbol).move
      (NestingMachine.opposite current.direction)).read = blankSymbol := by
    have hfree' : ¬ ((current.foundTape.write blankSymbol).move
        (orient address.growth shift)).read ≠ blankSymbol := by
      simpa [hraw, ShiftDestinationOccupied] using hfree
    rw [hshift] at hfree'
    exact Classical.not_not.mp hfree'
  have hguard : (current.outer.move
      (NestingMachine.opposite current.direction)).read = blankSymbol := by
    rw [← hfound]
    rw [← write_neighbor_read current.foundTape blankSymbol
      (NestingMachine.opposite current.direction)]
    exact hblankDestination
  exact ⟨⟨current, hguard⟩, rfl⟩

/-- With original distance zero, any strict guarded parent outcome is a weak
monotone outcome for the same genuine search. -/
def monotone_of_zero_guardedParent
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GenuineSearch base c) (hzero : current.distance = 0)
    (guarded : GuardedSearch base c)
    (hcurrent : guarded.current = current)
    (outcome : FoundGuardedParentOutcome guarded) :
    FoundMonotoneGuardedEntryOutcome current := by
  subst current
  cases outcome with
  | logical core reaches _hinside =>
      exact .logical core reaches (by simp [hzero])
  | nextSearch next reaches _hdistance =>
      exact .nextSearch next reaches (by simp [hzero])

end

end CounterControlZeroGuarding
end Hooper
end Kari
end LeanWang
