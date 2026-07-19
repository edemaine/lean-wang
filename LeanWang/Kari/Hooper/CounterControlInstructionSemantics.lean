/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlDirectSemantics
import LeanWang.Kari.Hooper.CounterControlNavigationSemantics
import LeanWang.Kari.Hooper.OrientedMarkerTape
import LeanWang.Kari.Hooper.CounterControlScheduleSemantics
import LeanWang.Kari.Hooper.CounterControlCleanupSemantics
import LeanWang.Kari.Hooper.CounterControlSearchSystem
import LeanWang.Kari.Hooper.CounterControlSearchExecution
import LeanWang.Kari.Hooper.CounterControlFrameBacking
import LeanWang.Kari.Hooper.CounterControlStepGeometry
import LeanWang.Kari.Hooper.CounterControlCoreRoutes

/-!
# Semantics of complete counter-controller instructions

This module composes validation, register-update, recovery, and collision
cleanup into instruction-sized executions of the compiled counter controller.
The route layer below works directly on a represented tagged frame, so the
return tag and suspended outer target may already be present on the ambient
tape.
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

/-- All compiled searches shorter than the active frame's outer distance are
already discharged by Hooper's simultaneous strong induction. -/
def ShortSearches (base : Nat) (c : Nat.Partrec.Code) (limit : Nat) : Prop :=
  ∀ j < limit, (CounterControlSearchSystem.searchSystem base c).Solves j

/-! ## Reusing a solved bounded search -/

/-- A generated raw search of a strictly shorter distance reaches its native
`foundState`, regardless of whether that distance exceeds the local finite
radius. -/
theorem rawSearch_reaches_found
    (base : Nat) (c : Nat.Partrec.Code) (limit : Nat)
    (hshort : ShortSearches base c limit)
    (raw : RawCommand) (hraw : raw ∈ rawCommands)
    (outer : FullTM0.Tape (Symbol numTags)) (distance : Nat)
    (hdistance : distance < limit)
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (compileRawCommand base c raw hraw).target.Matches outer
      (compileRawCommand base c raw hraw).searchDirection distance) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      ⟨searchState base c raw.address, outer⟩
      ⟨foundState (CanonicalInitializer.radius c)
          (searchState base c raw.address),
        outer.moveN
          (compileRawCommand base c raw hraw).searchDirection distance⟩ := by
  exact CounterControlSearchExecution.reaches_found_of_solves base c raw hraw
    outer distance (hshort distance hdistance) hgap

/-- A uniform implementation of compiled bounded searches.  The same
continuation proofs can be instantiated with solved searches, resolving
searches, or any other failure predicate stable under finite prefixes. -/
structure CompiledSearchRunner
    (base : Nat) (c : Nat.Partrec.Code) (limit : Nat)
    (Failure : FullTM0.Cfg (Symbol numTags) FiniteTM0.State → Prop) where
  pullback : ∀ {start current},
    FullTM0.Reaches (CounterControlNestingBridge.machine base c) start current →
      Failure current → Failure start
  search : ∀ (raw : RawCommand) (hraw : raw ∈ rawCommands)
      (outer : FullTM0.Tape (Symbol numTags)) (distance : Nat),
    distance < limit →
    SearchGap (fun symbol => symbol = blankSymbol)
      (compileRawCommand base c raw hraw).target.Matches outer
      (compileRawCommand base c raw hraw).searchDirection distance →
    FullTM0.CompletesOr (CounterControlNestingBridge.machine base c) Failure
      ⟨searchState base c raw.address, outer⟩
      ⟨foundState (CanonicalInitializer.radius c)
          (searchState base c raw.address),
        outer.moveN
          (compileRawCommand base c raw hraw).searchDirection distance⟩

/-- The simultaneous solved-search hypothesis is a failure-free compiled
search runner. -/
def solvedSearchRunner
    (base : Nat) (c : Nat.Partrec.Code) (limit : Nat)
    (hshort : ShortSearches base c limit) :
    CompiledSearchRunner base c limit (fun _ => False) where
  pullback := by
    intro _ _ _ hfailure
    exact hfailure.elim
  search := by
    intro raw hraw outer distance hdistance hgap
    exact Or.inl (rawSearch_reaches_found base c limit hshort raw hraw outer
      distance hdistance hgap)

/-! ## Failure-parametric compiled continuations -/

/-- Execute an erasing boundary command using any compiled-search runner. -/
theorem machine_reaches_boundary_erase_with
    (base : Nat) (c : Nat.Partrec.Code) (limit : Nat)
    (Failure : FullTM0.Cfg (Symbol numTags) FiniteTM0.State → Prop)
    (runner : CompiledSearchRunner base c limit Failure)
    (address : SearchAddress) (expected : Fin 5)
    (direction : Turing.Dir) (success : ControlRef)
    (departure : Option Turing.Dir)
    (hraw : RawCommand.boundaryNavigation address expected direction success
      (.erase departure) ∈ rawCommands)
    (outer : FullTM0.Tape (Symbol numTags)) (distance : Nat)
    (hdistance : distance < limit)
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary expected).Matches outer
      (orient address.growth direction) distance) :
    FullTM0.CompletesOr (CounterControlNestingBridge.machine base c) Failure
        ⟨searchState base c address, outer⟩
        ⟨resolve base c success,
          match departure with
          | none =>
              (outer.moveN (orient address.growth direction) distance).write
                blankSymbol
          | some departure =>
              ((outer.moveN (orient address.growth direction) distance).write
                blankSymbol).move (orient address.growth departure)⟩ := by
  let raw : RawCommand :=
    .boundaryNavigation address expected direction success (.erase departure)
  have hspec := compileRawCommand_spec base c raw hraw
  have hcompiledGap : SearchGap (fun symbol => symbol = blankSymbol)
      (compileRawCommand base c raw hraw).target.Matches outer
      (compileRawCommand base c raw hraw).searchDirection distance := by
    rw [hspec]
    simpa [raw, compileRawAtTag, Command.target, Command.searchDirection,
      compileNavigationAction] using hgap
  have hfound := runner.search raw hraw outer distance hdistance hcompiledGap
  refine hfound.imp ?_ id
  intro hfound
  have hfound' : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      ⟨searchState base c address, outer⟩
      ⟨foundState (CanonicalInitializer.radius c)
          (searchState base c address),
        outer.moveN (orient address.growth direction) distance⟩ := by
    rw [hspec] at hfound
    simpa [raw, compileRawAtTag, RawCommand.address,
      Command.searchDirection, compileNavigationAction] using hfound
  have hatRaw := CommandAt.compileRawCommand base c raw hraw
  have hat : CommandAt (CanonicalInitializer.radius c) base
      (searchState base c address)
      (.boundaryNavigation expected (orient address.growth direction)
        (resolve base c success) (rawTag raw hraw)
        (.erase (departure.map (orient address.growth))))
      (commands base c) := by
    rw [hspec] at hatRaw
    simpa [raw, compileRawAtTag, RawCommand.address,
      compileNavigationAction] using hatRaw
  have hread :
      (outer.moveN (orient address.growth direction) distance).read =
        boundarySymbol expected := by
    simpa [FullTM0.Tape.read, Target.Matches] using hgap.marked
  have hcontinue :=
    BoundedMarkerContinuation.machine_reaches_erase_native
      (coreTable base c) expected (orient address.growth direction)
      (resolve base c success) (rawTag raw hraw)
      (departure.map (orient address.growth)) hat
      (outer.moveN (orient address.growth direction) distance) hread
  cases departure <;>
    exact hfound'.trans hcontinue

/-- Solved-search form of an erasing boundary command, with its exact
optional-departure endpoint. -/
theorem machine_reaches_boundary_erase_solved
    (base : Nat) (c : Nat.Partrec.Code) (limit : Nat)
    (hshort : ShortSearches base c limit)
    (address : SearchAddress) (expected : Fin 5)
    (direction : Turing.Dir) (success : ControlRef)
    (departure : Option Turing.Dir)
    (hraw : RawCommand.boundaryNavigation address expected direction success
      (.erase departure) ∈ rawCommands)
    (outer : FullTM0.Tape (Symbol numTags)) (distance : Nat)
    (hdistance : distance < limit)
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary expected).Matches outer
      (orient address.growth direction) distance) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨searchState base c address, outer⟩
        ⟨resolve base c success,
          match departure with
          | none =>
              (outer.moveN (orient address.growth direction) distance).write
                blankSymbol
          | some departure =>
              ((outer.moveN (orient address.growth direction) distance).write
                blankSymbol).move (orient address.growth departure)⟩ := by
  rcases machine_reaches_boundary_erase_with base c limit (fun _ => False)
      (solvedSearchRunner base c limit hshort) address expected direction
      success departure hraw outer distance hdistance hgap with hrun | hfailure
  · exact hrun
  · exact hfailure.elim

/-- Solved searches instantiate the shared four-command cleanup runner. -/
def solvedCleanupRunner
    (base : Nat) (c : Nat.Partrec.Code) (limit source : Nat)
    (growth : Turing.Dir) (hshort : ShortSearches base c limit) :
    CleanupRunner base c limit growth source (fun _ => False) where
  pullback := by
    intro _ _ _ hfailure
    exact hfailure.elim
  erase := by
    intro address expected success _ hraw outer distance hdistance hgap
    exact machine_reaches_boundary_erase_with base c limit (fun _ => False)
      (solvedSearchRunner base c limit hshort) address expected .left success
      (some .left) hraw outer distance hdistance hgap

/-- Execute navigation back to the saved physical tag using any compiled
search runner. -/
theorem machine_reaches_tag_with
    (base : Nat) (c : Nat.Partrec.Code) (limit : Nat)
    (Failure : FullTM0.Cfg (Symbol numTags) FiniteTM0.State → Prop)
    (runner : CompiledSearchRunner base c limit Failure)
    (address : SearchAddress) (direction : Turing.Dir)
    (success : ControlRef)
    (hraw : RawCommand.tagNavigation address direction success ∈ rawCommands)
    (outer : FullTM0.Tape (Symbol numTags)) (distance : Nat)
    (hdistance : distance < limit)
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.anyTag : Target numTags).Matches outer
      (orient address.growth direction) distance) :
    FullTM0.CompletesOr (CounterControlNestingBridge.machine base c) Failure
        ⟨searchState base c address, outer⟩
        ⟨resolve base c success,
          outer.moveN (orient address.growth direction) distance⟩ := by
  let raw : RawCommand := .tagNavigation address direction success
  have hspec := compileRawCommand_spec base c raw hraw
  have hcompiledGap : SearchGap (fun symbol => symbol = blankSymbol)
      (compileRawCommand base c raw hraw).target.Matches outer
      (compileRawCommand base c raw hraw).searchDirection distance := by
    rw [hspec]
    simpa [raw, compileRawAtTag, Command.target,
      Command.searchDirection] using hgap
  have hfound := runner.search raw hraw outer distance hdistance hcompiledGap
  refine hfound.imp ?_ id
  intro hfound
  have hfound' : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      ⟨searchState base c address, outer⟩
      ⟨foundState (CanonicalInitializer.radius c)
          (searchState base c address),
        outer.moveN (orient address.growth direction) distance⟩ := by
    rw [hspec] at hfound
    simpa [raw, compileRawAtTag, RawCommand.address,
      Command.searchDirection] using hfound
  have hatRaw := CommandAt.compileRawCommand base c raw hraw
  have hat : CommandAt (CanonicalInitializer.radius c) base
      (searchState base c address)
      (.tagNavigation (orient address.growth direction)
        (resolve base c success) (rawTag raw hraw))
      (commands base c) := by
    rw [hspec] at hatRaw
    simpa [raw, compileRawAtTag, RawCommand.address] using hatRaw
  have hmatch : (Target.anyTag : Target numTags).Matches
      (outer.moveN (orient address.growth direction) distance).read := by
    simpa [FullTM0.Tape.read] using hgap.marked
  have hcontinue :=
    BoundedMarkerContinuation.machine_reaches_navigation_native
      (coreTable base c) (Target.anyTag : Target numTags)
      (orient address.growth direction) (resolve base c success)
      (rawTag raw hraw) hat
      (outer.moveN (orient address.growth direction) distance) hmatch
  exact hfound'.trans hcontinue

/-- Solved-search form of navigation back to the saved physical tag. -/
theorem machine_reaches_tag_solved
    (base : Nat) (c : Nat.Partrec.Code) (limit : Nat)
    (hshort : ShortSearches base c limit)
    (address : SearchAddress) (direction : Turing.Dir)
    (success : ControlRef)
    (hraw : RawCommand.tagNavigation address direction success ∈ rawCommands)
    (outer : FullTM0.Tape (Symbol numTags)) (distance : Nat)
    (hdistance : distance < limit)
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.anyTag : Target numTags).Matches outer
      (orient address.growth direction) distance) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨searchState base c address, outer⟩
        ⟨resolve base c success,
          outer.moveN (orient address.growth direction) distance⟩ := by
  rcases machine_reaches_tag_with base c limit (fun _ => False)
      (solvedSearchRunner base c limit hshort) address direction success hraw
      outer distance hdistance hgap with hrun | hfailure
  · exact hrun
  · exact hfailure.elim

/-- Execute a preserving boundary command using any compiled-search runner. -/
theorem machine_reaches_boundary_preserve_with
    (base : Nat) (c : Nat.Partrec.Code) (limit : Nat)
    (Failure : FullTM0.Cfg (Symbol numTags) FiniteTM0.State → Prop)
    (runner : CompiledSearchRunner base c limit Failure)
    (address : SearchAddress) (expected : Fin 5)
    (direction : Turing.Dir) (success : ControlRef)
    (hraw : RawCommand.boundaryNavigation address expected direction success
      .preserve ∈ rawCommands)
    (outer : FullTM0.Tape (Symbol numTags)) (distance : Nat)
    (hdistance : distance < limit)
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary expected).Matches outer
      (orient address.growth direction) distance) :
    FullTM0.CompletesOr (CounterControlNestingBridge.machine base c) Failure
      ⟨searchState base c address, outer⟩
      ⟨resolve base c success,
        outer.moveN (orient address.growth direction) distance⟩ := by
  let raw : RawCommand :=
    .boundaryNavigation address expected direction success .preserve
  have hspec := compileRawCommand_spec base c raw hraw
  have hcompiledGap : SearchGap (fun symbol => symbol = blankSymbol)
      (compileRawCommand base c raw hraw).target.Matches outer
      (compileRawCommand base c raw hraw).searchDirection distance := by
    rw [hspec]
    simpa [raw, compileRawAtTag, Command.target,
      Command.searchDirection, compileNavigationAction] using hgap
  have hfound := runner.search raw hraw outer distance hdistance hcompiledGap
  refine hfound.imp ?_ id
  intro hfound
  have hfound' : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      ⟨searchState base c address, outer⟩
      ⟨foundState (CanonicalInitializer.radius c)
          (searchState base c address),
        outer.moveN (orient address.growth direction) distance⟩ := by
    rw [hspec] at hfound
    simpa [raw, compileRawAtTag, RawCommand.address,
      Command.searchDirection, compileNavigationAction] using hfound
  have hatRaw := CommandAt.compileRawCommand base c raw hraw
  have hat : CommandAt (CanonicalInitializer.radius c) base
      (searchState base c address)
      (.boundaryNavigation expected (orient address.growth direction)
        (resolve base c success) (rawTag raw hraw) .preserve)
      (commands base c) := by
    rw [hspec] at hatRaw
    simpa [raw, compileRawAtTag, RawCommand.address,
      compileNavigationAction] using hatRaw
  have hmatch : (Target.boundary expected).Matches
      (outer.moveN (orient address.growth direction) distance).read := by
    simpa [FullTM0.Tape.moveN, FullTM0.Tape.read] using hgap.marked
  have hcontinue :=
    BoundedMarkerContinuation.machine_reaches_navigation_native
      (coreTable base c) (Target.boundary expected)
      (orient address.growth direction) (resolve base c success)
      (rawTag raw hraw) hat
      (outer.moveN (orient address.growth direction) distance) hmatch
  exact hfound'.trans hcontinue

/-- Solved-search form of a preserving boundary command. -/
theorem machine_reaches_boundary_preserve_solved
    (base : Nat) (c : Nat.Partrec.Code) (limit : Nat)
    (hshort : ShortSearches base c limit)
    (address : SearchAddress) (expected : Fin 5)
    (direction : Turing.Dir) (success : ControlRef)
    (hraw : RawCommand.boundaryNavigation address expected direction success
      .preserve ∈ rawCommands)
    (outer : FullTM0.Tape (Symbol numTags)) (distance : Nat)
    (hdistance : distance < limit)
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary expected).Matches outer
      (orient address.growth direction) distance) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      ⟨searchState base c address, outer⟩
      ⟨resolve base c success,
        outer.moveN (orient address.growth direction) distance⟩ := by
  rcases machine_reaches_boundary_preserve_with base c limit (fun _ => False)
      (solvedSearchRunner base c limit hshort) address expected direction
      success hraw outer distance hdistance hgap with hrun | hfailure
  · exact hrun
  · exact hfailure.elim

/-- Execute an outward marker shift using any compiled-search runner. -/
theorem machine_reaches_incrementShift_with
    (base : Nat) (c : Nat.Partrec.Code) (limit : Nat)
    (Failure : FullTM0.Cfg (Symbol numTags) FiniteTM0.State → Prop)
    (runner : CompiledSearchRunner base c limit Failure)
    (growth : Turing.Dir)
    (counterState searchSlot source : Nat) (expected : Fin 5)
    (success : ControlRef) (collision : Option ControlRef)
    (hraw : RawCommand.markerShift
      ⟨growth, counterState, searchSlot⟩ expected .left .right success
        (some .left) collision ∈ rawCommands)
    (T : FullTM0.Tape (Symbol numTags)) (distance : Nat)
    (hdistance : distance < limit)
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary expected).Matches
      (atLogical growth T (source + distance))
      (OrientedMarkerTape.orientDirection growth .left) distance)
    (hblank : logicalTape growth T (source + 1) = blankSymbol) :
    FullTM0.CompletesOr (CounterControlNestingBridge.machine base c) Failure
      ⟨searchState base c ⟨growth, counterState, searchSlot⟩,
        atLogical growth T (source + distance)⟩
      ⟨resolve base c success,
        atLogical growth
          (writeLogical growth
            (writeLogical growth T source blankSymbol) (source + 1)
              (boundarySymbol expected)) source⟩ := by
  let raw : RawCommand :=
    .markerShift ⟨growth, counterState, searchSlot⟩ expected .left .right
      success (some .left) collision
  let move : MarkerProgram.Move :=
    ⟨expected, CounterControlPlan.orient growth .left,
      CounterControlPlan.orient growth .right⟩
  have hspec := compileRawCommand_spec base c raw hraw
  have hcommand : compileRawCommand base c raw hraw =
      .markerShift move (resolve base c success) (rawTag raw hraw)
        (some (CounterControlPlan.orient growth .left))
        (collision.map (resolve base c)) := by
    rw [hspec]
    simp [raw, move, compileRawAtTag, CounterControlPlan.orient]
  have hcompiledGap : SearchGap (fun symbol => symbol = blankSymbol)
      (compileRawCommand base c raw hraw).target.Matches
      (atLogical growth T (source + distance))
      (compileRawCommand base c raw hraw).searchDirection distance := by
    rw [hcommand]
    simpa [move, Command.target, Command.searchDirection,
      orient_eq_orientDirection] using hgap
  have hfound := runner.search raw hraw
    (atLogical growth T (source + distance)) distance hdistance hcompiledGap
  refine hfound.imp ?_ id
  intro hfound
  have hmove :
      (atLogical growth T (source + distance)).moveN
          (CounterControlPlan.orient growth .left) distance =
        atLogical growth T source := by
    simpa only [orient_eq_orientDirection] using
      atLogical_moveN_left growth T source distance
  have hfound' : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      ⟨searchState base c ⟨growth, counterState, searchSlot⟩,
        atLogical growth T (source + distance)⟩
      ⟨foundState (CanonicalInitializer.radius c)
          (searchState base c ⟨growth, counterState, searchSlot⟩),
        atLogical growth T source⟩ := by
    rw [hcommand] at hfound
    change FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      ⟨searchState base c raw.address,
        atLogical growth T (source + distance)⟩
      ⟨foundState (CanonicalInitializer.radius c)
          (searchState base c raw.address),
        (atLogical growth T (source + distance)).moveN
          move.searchDirection distance⟩ at hfound
    rw [show move.searchDirection =
      CounterControlPlan.orient growth .left from rfl, hmove] at hfound
    simpa [raw, RawCommand.address] using hfound
  have hatRaw := CommandAt.compileRawCommand base c raw hraw
  have hat : CommandAt (CanonicalInitializer.radius c) base
      (searchState base c ⟨growth, counterState, searchSlot⟩)
      (.markerShift move (resolve base c success) (rawTag raw hraw)
        (some (CounterControlPlan.orient growth .left))
        (collision.map (resolve base c)))
      (commands base c) := by
    rw [hspec] at hatRaw
    simpa [raw, move, compileRawAtTag, RawCommand.address] using hatRaw
  have hread :
      (atLogical growth T source).read = boundarySymbol expected := by
    rw [← hmove]
    simpa [Target.Matches] using hgap.marked
  have hblankPhysical :
      ((((atLogical growth T source).write blankSymbol).move
            move.shiftDirection).read = blankSymbol) := by
    change (((atLogical growth T source).write blankSymbol).move
      (CounterControlPlan.orient growth .right)).read = blankSymbol
    rw [atLogical_write]
    rw [show CounterControlPlan.orient growth .right =
      OrientedMarkerTape.orientDirection growth .right by
        exact orient_eq_orientDirection growth .right]
    rw [atLogical_move_right, atLogical_read]
    rw [writeLogical_of_ne growth T source (source + 1) blankSymbol (by omega)]
    exact hblank
  have hcontinue :=
    BoundedMarkerContinuation.machine_reaches_shift_success_native
      (coreTable base c) move (resolve base c success) (rawTag raw hraw)
      (some (CounterControlPlan.orient growth .left))
      (collision.map (resolve base c)) hat
      (atLogical growth T source) hread hblankPhysical
  have hrun := hfound'.trans hcontinue
  dsimp only [move] at hrun
  rw [orient_eq_orientDirection growth .right,
    orient_eq_orientDirection growth .left] at hrun
  rw [shiftRight_departLeft_atLogical] at hrun
  exact hrun

/-- Solved-search counterpart of the native outward marker-shift theorem.
The expected marker may lie beyond the local finite radius, provided its
distance is covered by the simultaneous strong-induction hypothesis. -/
theorem machine_reaches_incrementShift_solved
    (base : Nat) (c : Nat.Partrec.Code) (limit : Nat)
    (hshort : ShortSearches base c limit) (growth : Turing.Dir)
    (counterState searchSlot source : Nat) (expected : Fin 5)
    (success : ControlRef) (collision : Option ControlRef)
    (hraw : RawCommand.markerShift
      ⟨growth, counterState, searchSlot⟩ expected .left .right success
        (some .left) collision ∈ rawCommands)
    (T : FullTM0.Tape (Symbol numTags)) (distance : Nat)
    (hdistance : distance < limit)
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary expected).Matches
      (atLogical growth T (source + distance))
      (OrientedMarkerTape.orientDirection growth .left) distance)
    (hblank : logicalTape growth T (source + 1) = blankSymbol) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      ⟨searchState base c ⟨growth, counterState, searchSlot⟩,
        atLogical growth T (source + distance)⟩
      ⟨resolve base c success,
        atLogical growth
          (writeLogical growth
            (writeLogical growth T source blankSymbol) (source + 1)
              (boundarySymbol expected)) source⟩ := by
  rcases machine_reaches_incrementShift_with base c limit (fun _ => False)
      (solvedSearchRunner base c limit hshort) growth counterState searchSlot
      source expected success collision hraw T distance hdistance hgap hblank
      with hrun | hfailure
  · exact hrun
  · exact hfailure.elim

/-- Execute an inward marker shift using any compiled-search runner. -/
theorem machine_reaches_decrementShift_with
    (base : Nat) (c : Nat.Partrec.Code) (limit : Nat)
    (Failure : FullTM0.Cfg (Symbol numTags) FiniteTM0.State → Prop)
    (runner : CompiledSearchRunner base c limit Failure)
    (growth : Turing.Dir)
    (counterState searchSlot origin destination distance : Nat)
    (expected : Fin 5) (success : ControlRef)
    (collision : Option ControlRef)
    (hraw : RawCommand.markerShift
      ⟨growth, counterState, searchSlot⟩ expected .right .left success
        (some .right) collision ∈ rawCommands)
    (T : FullTM0.Tape (Symbol numTags))
    (hposition : origin + distance = destination + 1)
    (hdistance : distance < limit)
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary expected).Matches (atLogical growth T origin)
      (OrientedMarkerTape.orientDirection growth .right) distance)
    (hblank : logicalTape growth T destination = blankSymbol) :
    FullTM0.CompletesOr (CounterControlNestingBridge.machine base c) Failure
      ⟨searchState base c ⟨growth, counterState, searchSlot⟩,
        atLogical growth T origin⟩
      ⟨resolve base c success,
        atLogical growth
          (writeLogical growth
            (writeLogical growth T (destination + 1) blankSymbol) destination
              (boundarySymbol expected)) (destination + 1)⟩ := by
  let raw : RawCommand :=
    .markerShift ⟨growth, counterState, searchSlot⟩ expected .right .left
      success (some .right) collision
  let move : MarkerProgram.Move :=
    ⟨expected, CounterControlPlan.orient growth .right,
      CounterControlPlan.orient growth .left⟩
  have hspec := compileRawCommand_spec base c raw hraw
  have hcommand : compileRawCommand base c raw hraw =
      .markerShift move (resolve base c success) (rawTag raw hraw)
        (some (CounterControlPlan.orient growth .right))
        (collision.map (resolve base c)) := by
    rw [hspec]
    simp [raw, move, compileRawAtTag, CounterControlPlan.orient]
  have hcompiledGap : SearchGap (fun symbol => symbol = blankSymbol)
      (compileRawCommand base c raw hraw).target.Matches
      (atLogical growth T origin)
      (compileRawCommand base c raw hraw).searchDirection distance := by
    rw [hcommand]
    simpa [move, Command.target, Command.searchDirection,
      orient_eq_orientDirection] using hgap
  have hfound := runner.search raw hraw (atLogical growth T origin) distance
    hdistance hcompiledGap
  refine hfound.imp ?_ id
  intro hfound
  have hmove :
      (atLogical growth T origin).moveN
          (CounterControlPlan.orient growth .right) distance =
        atLogical growth T (destination + 1) := by
    rw [show CounterControlPlan.orient growth .right =
      OrientedMarkerTape.orientDirection growth .right by
        exact orient_eq_orientDirection growth .right]
    rw [atLogical_moveN_right, hposition]
  have hfound' : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      ⟨searchState base c ⟨growth, counterState, searchSlot⟩,
        atLogical growth T origin⟩
      ⟨foundState (CanonicalInitializer.radius c)
          (searchState base c ⟨growth, counterState, searchSlot⟩),
        atLogical growth T (destination + 1)⟩ := by
    rw [hcommand] at hfound
    change FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      ⟨searchState base c raw.address, atLogical growth T origin⟩
      ⟨foundState (CanonicalInitializer.radius c)
          (searchState base c raw.address),
        (atLogical growth T origin).moveN move.searchDirection distance⟩ at hfound
    rw [show move.searchDirection =
      CounterControlPlan.orient growth .right from rfl, hmove] at hfound
    simpa [raw, RawCommand.address] using hfound
  have hatRaw := CommandAt.compileRawCommand base c raw hraw
  have hat : CommandAt (CanonicalInitializer.radius c) base
      (searchState base c ⟨growth, counterState, searchSlot⟩)
      (.markerShift move (resolve base c success) (rawTag raw hraw)
        (some (CounterControlPlan.orient growth .right))
        (collision.map (resolve base c)))
      (commands base c) := by
    rw [hspec] at hatRaw
    simpa [raw, move, compileRawAtTag, RawCommand.address] using hatRaw
  have hread :
      (atLogical growth T (destination + 1)).read =
        boundarySymbol expected := by
    rw [← hmove]
    simpa [Target.Matches] using hgap.marked
  have hblankPhysical :
      ((((atLogical growth T (destination + 1)).write blankSymbol).move
            move.shiftDirection).read = blankSymbol) := by
    change (((atLogical growth T (destination + 1)).write blankSymbol).move
      (CounterControlPlan.orient growth .left)).read = blankSymbol
    rw [atLogical_write]
    rw [show CounterControlPlan.orient growth .left =
      OrientedMarkerTape.orientDirection growth .left by
        exact orient_eq_orientDirection growth .left]
    rw [atLogical_move_left, atLogical_read]
    rw [writeLogical_of_ne growth T (destination + 1) destination blankSymbol
      (by omega)]
    exact hblank
  have hcontinue :=
    BoundedMarkerContinuation.machine_reaches_shift_success_native
      (coreTable base c) move (resolve base c success) (rawTag raw hraw)
      (some (CounterControlPlan.orient growth .right))
      (collision.map (resolve base c)) hat
      (atLogical growth T (destination + 1)) hread hblankPhysical
  have hrun := hfound'.trans hcontinue
  dsimp only [move] at hrun
  rw [orient_eq_orientDirection growth .left,
    orient_eq_orientDirection growth .right] at hrun
  rw [shiftLeft_departRight_atLogical] at hrun
  exact hrun

/-- Solved-search counterpart of the native inward marker-shift theorem. -/
theorem machine_reaches_decrementShift_solved
    (base : Nat) (c : Nat.Partrec.Code) (limit : Nat)
    (hshort : ShortSearches base c limit) (growth : Turing.Dir)
    (counterState searchSlot origin destination distance : Nat)
    (expected : Fin 5) (success : ControlRef)
    (collision : Option ControlRef)
    (hraw : RawCommand.markerShift
      ⟨growth, counterState, searchSlot⟩ expected .right .left success
        (some .right) collision ∈ rawCommands)
    (T : FullTM0.Tape (Symbol numTags))
    (hposition : origin + distance = destination + 1)
    (hdistance : distance < limit)
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary expected).Matches (atLogical growth T origin)
      (OrientedMarkerTape.orientDirection growth .right) distance)
    (hblank : logicalTape growth T destination = blankSymbol) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      ⟨searchState base c ⟨growth, counterState, searchSlot⟩,
        atLogical growth T origin⟩
      ⟨resolve base c success,
        atLogical growth
          (writeLogical growth
            (writeLogical growth T (destination + 1) blankSymbol) destination
              (boundarySymbol expected)) (destination + 1)⟩ := by
  rcases machine_reaches_decrementShift_with base c limit (fun _ => False)
      (solvedSearchRunner base c limit hshort) growth counterState searchSlot
      origin destination distance expected success collision hraw T hposition
      hdistance hgap hblank with hrun | hfailure
  · exact hrun
  · exact hfailure.elim

/-- One internal canonical increment shift, discharged by solved shorter
searches instead of the local-radius bound. -/
theorem machine_reaches_incrementInternal_with
    (base : Nat) (c : Nat.Partrec.Code) (limit : Nat)
    (Failure : FullTM0.Cfg (Symbol numTags) FiniteTM0.State → Prop)
    (runner : CompiledSearchRunner base c limit Failure)
    (counterState searchSlot : Nat)
    (success : ControlRef) (collision : Option ControlRef)
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T) (next : Registers) (i : Fin 4)
    (hpositive : 0 < RegisterLayout.values spec.registers i)
    (hdistance : RegisterLayout.values spec.registers i < limit)
    (hnextCore : layoutEnd next < spec.outerDistance)
    (hsameEnd : layoutEnd next = layoutEnd spec.registers)
    (hmove : MarkerMachine.moveAt .right
        (MarkerTape.canonicalTape spec.registers)
        (MarkerTape.boundaryPosition spec.registers i.castSucc) i.castSucc =
      MarkerTape.canonicalTape next)
    (hraw : RawCommand.markerShift
      ⟨spec.growth, counterState, searchSlot⟩ i.castSucc .left .right
      success (some .left) collision ∈ rawCommands) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨spec.growth, counterState, searchSlot⟩,
          atLogical spec.growth T (lastGapOffset spec.registers i)⟩
        ⟨resolve base c success,
          atLogical spec.growth
            (install next spec.growth spec.returnTag T)
            (boundaryOffset spec.registers i.castSucc)⟩ ∨
      Failure
        ⟨searchState base c ⟨spec.growth, counterState, searchSlot⟩,
          atLogical spec.growth T (lastGapOffset spec.registers i)⟩ := by
  let source := boundaryOffset spec.registers i.castSucc
  let distance := RegisterLayout.values spec.registers i
  let U := writeLogical spec.growth
    (writeLogical spec.growth T source blankSymbol) (source + 1)
      (boundarySymbol i.castSucc)
  have hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary i.castSucc).Matches
      (atLogical spec.growth T (lastGapOffset spec.registers i))
      (OrientedMarkerTape.orientDirection spec.growth .left) distance := by
    change SearchGap (fun symbol => symbol = blankSymbol)
      (fun symbol => symbol = boundarySymbol i.castSucc) _ _ _
    exact h.searchGap_adjacent_left i
  have hstart : lastGapOffset spec.registers i = source + distance := by
    exact lastGapOffset_eq_boundaryOffset_add_value spec.registers i
  have hblank : logicalTape spec.growth T (source + 1) = blankSymbol := by
    have hgapBlank := h.gap_blank i 0 hpositive
    have hcoordinate : source + 1 = firstGapOffset spec.registers i := by
      simp [source, firstGapOffset, boundaryOffset]
    have hcoordinateInt : (source : Int) + 1 =
        firstGapOffset spec.registers i := by
      exact_mod_cast hcoordinate
    rw [hcoordinateInt]
    simpa using hgapBlank
  have hrun := machine_reaches_incrementShift_with base c limit Failure runner
    spec.growth counterState searchSlot source i.castSucc success collision
    hraw T distance hdistance (by simpa [hstart] using hgap) hblank
  rcases hrun with hrun | hhalts
  · left
    have hsourceBound : source ≤ layoutEnd spec.registers := by
      change CounterLayout.boundaryPos
          (RegisterLayout.values spec.registers) i + 1 ≤
        CounterLayout.boundaryPos (RegisterLayout.values spec.registers) 4 + 1
      apply Nat.add_le_add_right
      exact CounterLayout.boundaryPos_mono
        (RegisterLayout.values spec.registers) (show (i : Nat) ≤ 4 by omega)
    have htargetBound : source + 1 ≤ layoutEnd next := by
      rw [hsameEnd]
      have hnext := CounterLayout.boundaryPos_succ
        (RegisterLayout.values spec.registers) i
      change CounterLayout.boundaryPos
          (RegisterLayout.values spec.registers) i + 1 + 1 ≤
        CounterLayout.boundaryPos (RegisterLayout.values spec.registers) 4 + 1
      have hmono := CounterLayout.boundaryPos_mono
        (RegisterLayout.values spec.registers)
        (show (i : Nat) + 1 ≤ 4 by omega)
      omega
    have hrep : Represents (updateSpec spec next hnextCore) U := by
      apply moveRight_represents h next i.castSucc hnextCore
      · omega
      · omega
      · exact hsourceBound
      · exact htargetBound
      · intro hlt
        omega
      · exact hmove
    have hU : U = install next spec.growth spec.returnTag T := by
      apply moveRight_eq_install next i.castSucc hnextCore
      · simp [boundaryOffset]
      · exact hsourceBound.trans (by omega)
      · exact htargetBound
      · exact hrep
    simpa [U, hU, hstart] using hrun
  · right
    simpa [hstart] using hhalts


theorem machine_reaches_incrementInternal_solved
    (base : Nat) (c : Nat.Partrec.Code) (limit : Nat)
    (hshort : ShortSearches base c limit)
    (counterState searchSlot : Nat)
    (success : ControlRef) (collision : Option ControlRef)
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T) (next : Registers) (i : Fin 4)
    (hpositive : 0 < RegisterLayout.values spec.registers i)
    (hdistance : RegisterLayout.values spec.registers i < limit)
    (hnextCore : layoutEnd next < spec.outerDistance)
    (hsameEnd : layoutEnd next = layoutEnd spec.registers)
    (hmove : MarkerMachine.moveAt .right
        (MarkerTape.canonicalTape spec.registers)
        (MarkerTape.boundaryPosition spec.registers i.castSucc) i.castSucc =
      MarkerTape.canonicalTape next)
    (hraw : RawCommand.markerShift
      ⟨spec.growth, counterState, searchSlot⟩ i.castSucc .left .right
      success (some .left) collision ∈ rawCommands) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      ⟨searchState base c ⟨spec.growth, counterState, searchSlot⟩,
        atLogical spec.growth T (lastGapOffset spec.registers i)⟩
      ⟨resolve base c success,
        atLogical spec.growth
          (install next spec.growth spec.returnTag T)
          (boundaryOffset spec.registers i.castSucc)⟩ := by
  rcases machine_reaches_incrementInternal_with base c limit (fun _ => False)
      (solvedSearchRunner base c limit hshort) counterState searchSlot success
      collision h next i hpositive hdistance hnextCore hsameEnd hmove hraw with
    hrun | failure
  · exact hrun
  · exact failure.elim
theorem machine_reaches_decrementCanonical_with
    (base : Nat) (c : Nat.Partrec.Code) (limit : Nat)
    (Failure : FullTM0.Cfg (Symbol numTags) FiniteTM0.State → Prop)
    (runner : CompiledSearchRunner base c limit Failure)
    (counterState searchSlot : Nat)
    (success : ControlRef) (collision : Option ControlRef)
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T) (next : Registers) (label : Fin 5)
    (origin distance : Nat)
    (hsourcePositive : 1 < boundaryOffset spec.registers label)
    (horigin : origin + distance = boundaryOffset spec.registers label)
    (hdistance : distance < limit)
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary label).Matches (atLogical spec.growth T origin)
      (OrientedMarkerTape.orientDirection spec.growth .right) distance)
    (hblank : logicalTape spec.growth T
      ((boundaryOffset spec.registers label - 1 : Nat) : Int) = blankSymbol)
    (hnextCore : layoutEnd next < spec.outerDistance)
    (hlower : layoutEnd next ≤ layoutEnd spec.registers)
    (hupper : layoutEnd spec.registers ≤ layoutEnd next + 1)
    (hsource : boundaryOffset spec.registers label ≤
      layoutEnd spec.registers)
    (hdestination : boundaryOffset spec.registers label - 1 ≤
      layoutEnd next)
    (hshrink : layoutEnd next < layoutEnd spec.registers →
      boundaryOffset spec.registers label = layoutEnd spec.registers)
    (hmove : MarkerMachine.moveAt .left
        (MarkerTape.canonicalTape spec.registers)
        (MarkerTape.boundaryPosition spec.registers label) label =
      MarkerTape.canonicalTape next)
    (hraw : RawCommand.markerShift
      ⟨spec.growth, counterState, searchSlot⟩ label .right .left success
      (some .right) collision ∈ rawCommands) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨spec.growth, counterState, searchSlot⟩,
          atLogical spec.growth T origin⟩
        ⟨resolve base c success,
          atLogical spec.growth
            (install next spec.growth spec.returnTag
              (writeLogical spec.growth T
                (boundaryOffset spec.registers label) blankSymbol))
            (boundaryOffset spec.registers label)⟩ ∨
      Failure
        ⟨searchState base c ⟨spec.growth, counterState, searchSlot⟩,
          atLogical spec.growth T origin⟩ := by
  let source := boundaryOffset spec.registers label
  let destination := source - 1
  let U := writeLogical spec.growth
    (writeLogical spec.growth T source blankSymbol) destination
      (boundarySymbol label)
  have hposition : origin + distance = destination + 1 := by
    simp only [destination]
    omega
  have hsourceEq : destination + 1 = source := by
    simp only [destination]
    omega
  have hrun := machine_reaches_decrementShift_with base c limit Failure runner
    spec.growth counterState searchSlot origin destination distance label
    success collision hraw T hposition hdistance hgap
    (by simpa [source, destination] using hblank)
  rcases hrun with hrun | hhalts
  · left
    have hrep : Represents (updateSpec spec next hnextCore) U := by
      apply moveLeft_represents h next label hnextCore hlower hupper
        hsourcePositive hsource hdestination hshrink hmove
    have hU : U = install next spec.growth spec.returnTag
        (writeLogical spec.growth T source blankSymbol) := by
      apply moveLeft_eq_install_cleared next label hnextCore
      · omega
      · exact hdestination
      · exact hrep
    rw [hsourceEq] at hrun
    change FullTM0.Reaches _ _
      ⟨resolve base c success, atLogical spec.growth U source⟩ at hrun
    rw [hU] at hrun
    exact hrun
  · exact Or.inr hhalts

theorem machine_reaches_decrementCanonical_solved
    (base : Nat) (c : Nat.Partrec.Code) (limit : Nat)
    (hshort : ShortSearches base c limit)
    (counterState searchSlot : Nat)
    (success : ControlRef) (collision : Option ControlRef)
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T) (next : Registers) (label : Fin 5)
    (origin distance : Nat)
    (hsourcePositive : 1 < boundaryOffset spec.registers label)
    (horigin : origin + distance = boundaryOffset spec.registers label)
    (hdistance : distance < limit)
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary label).Matches (atLogical spec.growth T origin)
      (OrientedMarkerTape.orientDirection spec.growth .right) distance)
    (hblank : logicalTape spec.growth T
      ((boundaryOffset spec.registers label - 1 : Nat) : Int) = blankSymbol)
    (hnextCore : layoutEnd next < spec.outerDistance)
    (hlower : layoutEnd next ≤ layoutEnd spec.registers)
    (hupper : layoutEnd spec.registers ≤ layoutEnd next + 1)
    (hsource : boundaryOffset spec.registers label ≤
      layoutEnd spec.registers)
    (hdestination : boundaryOffset spec.registers label - 1 ≤
      layoutEnd next)
    (hshrink : layoutEnd next < layoutEnd spec.registers →
      boundaryOffset spec.registers label = layoutEnd spec.registers)
    (hmove : MarkerMachine.moveAt .left
        (MarkerTape.canonicalTape spec.registers)
        (MarkerTape.boundaryPosition spec.registers label) label =
      MarkerTape.canonicalTape next)
    (hraw : RawCommand.markerShift
      ⟨spec.growth, counterState, searchSlot⟩ label .right .left success
      (some .right) collision ∈ rawCommands) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      ⟨searchState base c ⟨spec.growth, counterState, searchSlot⟩,
        atLogical spec.growth T origin⟩
      ⟨resolve base c success,
        atLogical spec.growth
          (install next spec.growth spec.returnTag
            (writeLogical spec.growth T
              (boundaryOffset spec.registers label) blankSymbol))
          (boundaryOffset spec.registers label)⟩ := by
  rcases machine_reaches_decrementCanonical_with base c limit (fun _ => False)
      (solvedSearchRunner base c limit hshort) counterState searchSlot success collision h next label origin distance
      hsourcePositive horigin hdistance hgap hblank hnextCore hlower hupper
      hsource hdestination hshrink hmove hraw with hrun | failure
  · exact hrun
  · exact failure.elim

/-- The outward boundary-`4` shift with arbitrary generated success and
collision continuations, normalized to the canonical clock-increment tape. -/
theorem machine_reaches_incrementClock_with
    (base : Nat) (c : Nat.Partrec.Code) (limit : Nat)
    (Failure : FullTM0.Cfg (Symbol numTags) FiniteTM0.State → Prop)
    (runner : CompiledSearchRunner base c limit Failure)
    (counterState searchSlot : Nat)
    (success : ControlRef) (collision : Option ControlRef)
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T)
    (hroom : layoutEnd (spec.registers.increment .clock) <
      spec.outerDistance)
    (hlimit : 0 < limit)
    (hraw : RawCommand.markerShift
      ⟨spec.growth, counterState, searchSlot⟩ 4 .left .right
      success (some .left) collision ∈ rawCommands) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨spec.growth, counterState, searchSlot⟩,
          atLogical spec.growth T (layoutEnd spec.registers)⟩
        ⟨resolve base c success,
          atLogical spec.growth (incrementTape spec .clock T)
            (layoutEnd spec.registers)⟩ ∨
      Failure
        ⟨searchState base c ⟨spec.growth, counterState, searchSlot⟩,
          atLogical spec.growth T (layoutEnd spec.registers)⟩ := by
  let next := spec.registers.increment .clock
  let U := writeLogical spec.growth
    (writeLogical spec.growth T (layoutEnd spec.registers) blankSymbol)
    (layoutEnd spec.registers + 1) (boundarySymbol 4)
  have hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary 4).Matches
      (atLogical spec.growth T (layoutEnd spec.registers))
      (OrientedMarkerTape.orientDirection spec.growth .left) 0 := by
    rw [SearchGap.zero]
    change (atLogical spec.growth T (layoutEnd spec.registers)).read =
      boundarySymbol 4
    exact h.read_boundary_four
  have hblank : logicalTape spec.growth T
      (layoutEnd spec.registers + 1) = blankSymbol := by
    simpa [next, layoutEnd_increment] using
      increment_destination_blank h .clock hroom
  have hrun := machine_reaches_incrementShift_with base c limit Failure runner
    spec.growth counterState searchSlot (layoutEnd spec.registers) 4
    success collision hraw T 0 hlimit hgap hblank
  rcases hrun with hrun | hhalts
  · left
    have hmove : MarkerMachine.moveAt .right
        (MarkerTape.canonicalTape spec.registers)
        (MarkerTape.boundaryPosition spec.registers 4) 4 =
        MarkerTape.canonicalTape next := by
      rw [MarkerMachine.moveAt_clock_eq_incrementTape]
      exact MarkerShift.incrementTape_canonical spec.registers .clock
    have hrep : Represents (updateSpec spec next hroom) U := by
      apply moveRight_represents h next 4 hroom
      · dsimp only [next]
        rw [layoutEnd_increment]
        omega
      · dsimp only [next]
        rw [layoutEnd_increment]
      · exact boundaryOffset_four spec.registers |>.le
      · simp only [boundaryOffset_four]
        dsimp only [next]
        rw [layoutEnd_increment]
      · intro _
        simp only [boundaryOffset_four]
        dsimp only [next]
        rw [layoutEnd_increment]
      · exact hmove
    have hU : U = incrementTape spec .clock T := by
      change U = install next spec.growth spec.returnTag T
      apply moveRight_eq_install next 4 hroom
      · simp [boundaryOffset]
      · simp only [boundaryOffset_four]
        dsimp only [next]
        rw [layoutEnd_increment]
        omega
      · simp only [boundaryOffset_four]
        dsimp only [next]
        rw [layoutEnd_increment]
      · exact hrep
    simpa [U, hU] using hrun
  · exact Or.inr hhalts

theorem machine_reaches_incrementClock_solved
    (base : Nat) (c : Nat.Partrec.Code) (limit : Nat)
    (hshort : ShortSearches base c limit) (counterState searchSlot : Nat)
    (success : ControlRef) (collision : Option ControlRef)
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T)
    (hroom : layoutEnd (spec.registers.increment .clock) <
      spec.outerDistance)
    (hlimit : 0 < limit)
    (hraw : RawCommand.markerShift
      ⟨spec.growth, counterState, searchSlot⟩ 4 .left .right
      success (some .left) collision ∈ rawCommands) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      ⟨searchState base c ⟨spec.growth, counterState, searchSlot⟩,
        atLogical spec.growth T (layoutEnd spec.registers)⟩
      ⟨resolve base c success,
        atLogical spec.growth (incrementTape spec .clock T)
          (layoutEnd spec.registers)⟩ := by
  rcases machine_reaches_incrementClock_with base c limit (fun _ => False)
      (solvedSearchRunner base c limit hshort) counterState searchSlot success collision h hroom hlimit hraw with hrun | failure
  · exact hrun
  · exact failure.elim

/-! ## A component-independent nested outcome -/

/-- Some generated bounded search reachable from `start` has crossed the
current radius and installed its exact canonical nested frame. -/
def NestsFrom (base : Nat) (c : Nat.Partrec.Code)
    (start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State) : Prop :=
  ∃ (raw : RawCommand) (hraw : raw ∈ rawCommands)
      (outer : FullTM0.Tape (Symbol numTags)) (distance : Nat)
      (hfar : NestingMachine.bound (CanonicalInitializer.radius c) < distance),
    FullTM0.Reaches (CounterControlNestingBridge.machine base c) start
        (CounterControlNestingBridge.nestedCfg base c
          (rawTag raw hraw) outer) ∧
      Represents
        (frameSpec c (compileRawCommand base c raw hraw) distance hfar)
        (initializeTape c (compileRawCommand base c raw hraw) outer)

private theorem nestsFrom_of_reaches
    {base : Nat} {c : Nat.Partrec.Code}
    {start middle : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (hreach : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c) start middle)
    (hnests : NestsFrom base c middle) :
    NestsFrom base c start := by
  rcases hnests with
    ⟨raw, hraw, outer, distance, hfar, hnested, hframe⟩
  exact ⟨raw, hraw, outer, distance, hfar,
    hreach.trans hnested, hframe⟩

private theorem legExecutesAt_depart
    {growth : Turing.Dir} {T : FullTM0.Tape (Symbol numTags)}
    {leg : MarkerValidation.Leg} {source finish : Nat}
    (h : LegExecutesAt growth T leg source finish) :
    ∃ distance,
      SearchGap (fun symbol => symbol = blankSymbol)
        (Target.boundary leg.target).Matches
        ((atLogical growth T source).move (orient growth leg.direction))
        (orient growth leg.direction) distance ∧
      ((atLogical growth T source).move (orient growth leg.direction)).moveN
          (orient growth leg.direction) distance =
        atLogical growth T finish := by
  cases hdirection : leg.direction with
  | right =>
      rw [LegExecutesAt, hdirection] at h
      rcases h with ⟨distance, hgap, hfinish⟩
      refine ⟨distance, ?_, ?_⟩
      · simpa only [orient_eq_orientDirection,
          atLogical_move_right] using hgap
      · rw [orient_eq_orientDirection, atLogical_move_right,
          atLogical_moveN_right, hfinish]
        apply congrArg (atLogical growth T)
        omega
  | left =>
      rw [LegExecutesAt, hdirection] at h
      rcases h with ⟨distance, hsource, hgap⟩
      refine ⟨distance, ?_, ?_⟩
      · rw [hsource, orient_eq_orientDirection,
          atLogical_move_left]
        exact hgap
      · rw [hsource, orient_eq_orientDirection,
          atLogical_move_left, atLogical_moveN_left]

private theorem legExecutesAt_depart_below
    {growth : Turing.Dir} {T : FullTM0.Tape (Symbol numTags)}
    {leg : MarkerValidation.Leg} {source finish limit : Nat}
    (h : LegExecutesAt growth T leg source finish)
    (hsource : source < limit) (hfinish : finish < limit) :
    ∃ distance,
      distance < limit ∧
      SearchGap (fun symbol => symbol = blankSymbol)
        (Target.boundary leg.target).Matches
        ((atLogical growth T source).move (orient growth leg.direction))
        (orient growth leg.direction) distance ∧
      ((atLogical growth T source).move (orient growth leg.direction)).moveN
          (orient growth leg.direction) distance =
        atLogical growth T finish := by
  cases hdirection : leg.direction with
  | right =>
      rw [LegExecutesAt, hdirection] at h
      rcases h with ⟨distance, hgap, hfinishEq⟩
      refine ⟨distance, by omega, ?_, ?_⟩
      · simpa only [orient_eq_orientDirection,
          atLogical_move_right] using hgap
      · rw [orient_eq_orientDirection, atLogical_move_right,
          atLogical_moveN_right, hfinishEq]
        apply congrArg (atLogical growth T)
        omega
  | left =>
      rw [LegExecutesAt, hdirection] at h
      rcases h with ⟨distance, hsourceEq, hgap⟩
      refine ⟨distance, by omega, ?_, ?_⟩
      · rw [hsourceEq, orient_eq_orientDirection,
          atLogical_move_left]
        exact hgap
      · rw [hsourceEq, orient_eq_orientDirection,
          atLogical_move_left, atLogical_moveN_left]

private theorem legExecutesAt_finish_read
    {growth : Turing.Dir} {T : FullTM0.Tape (Symbol numTags)}
    {leg : MarkerValidation.Leg} {source finish : Nat}
    (h : LegExecutesAt growth T leg source finish) :
    (atLogical growth T finish).read = boundarySymbol leg.target := by
  rcases legExecutesAt_depart h with ⟨distance, hgap, hfinish⟩
  change (Target.boundary leg.target).Matches
    (atLogical growth T finish).read
  rw [← hfinish]
  simpa [FullTM0.Tape.moveN, FullTM0.Tape.read] using hgap.marked

/-! ## A failure-parametric route runner -/

/-- Run all searches after a route's entry rule.  The search primitive may
report any failure predicate that pulls back along successful prefixes. -/
theorem searches_reach_with_failure_at
    (base : Nat) (c : Nat.Partrec.Code) (limit : Nat)
    (Failure : FullTM0.Cfg (Symbol numTags) FiniteTM0.State → Prop)
    (pullback : ∀ {start middle},
      FullTM0.Reaches (CounterControlNestingBridge.machine base c) start middle →
      Failure middle → Failure start)
    (search : ∀ (address : SearchAddress) (expected : Fin 5)
        (direction : Turing.Dir) (success : ControlRef)
        (hraw : RawCommand.boundaryNavigation address expected direction
          success .preserve ∈ rawCommands)
        (outer : FullTM0.Tape (Symbol numTags)) (distance : Nat),
      distance < limit →
      SearchGap (fun symbol => symbol = blankSymbol)
        (Target.boundary expected).Matches outer
        (orient address.growth direction) distance →
      FullTM0.Reaches (CounterControlNestingBridge.machine base c)
          ⟨searchState base c address, outer⟩
          ⟨resolve base c success,
            outer.moveN (orient address.growth direction) distance⟩ ∨
        Failure ⟨searchState base c address, outer⟩)
    (growth : Turing.Dir) (counterState searchSlot directSlot : Nat)
    (after : ControlRef)
    (first : MarkerValidation.Leg) (rest : List MarkerValidation.Leg)
    (T : FullTM0.Tape (Symbol numTags)) (source finish : Nat)
    (hexec : RouteExecutesWithin growth T limit (first :: rest)
      source finish)
    (hcommands : ∀ raw,
      raw ∈ routeCommandsAux growth counterState searchSlot directSlot
          after (first :: rest) →
        raw ∈ rawCommands)
    (hcontinuations : ∀ rule,
      rule ∈ routeContinuationRules growth counterState searchSlot
          directSlot (first :: rest) →
        rule ∈ rawDirectRules) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨growth, counterState, searchSlot⟩,
          (atLogical growth T source).move
            (orient growth first.direction)⟩
        ⟨resolve base c after, atLogical growth T finish⟩ ∨
      Failure
        ⟨searchState base c ⟨growth, counterState, searchSlot⟩,
          (atLogical growth T source).move
            (orient growth first.direction)⟩ := by
  induction rest generalizing first source finish searchSlot directSlot with
  | nil =>
      cases hexec with
      | cons _ _ _ middle _ hsource hfirst hrest =>
        cases hrest with
        | nil _ hmiddle =>
          rcases legExecutesAt_depart_below hfirst hsource hmiddle with
            ⟨distance, hdistance, hgap, hfound⟩
          let raw : RawCommand :=
            .boundaryNavigation ⟨growth, counterState, searchSlot⟩
              first.target first.direction after .preserve
          have hroute : raw ∈ routeCommandsAux growth counterState
              searchSlot directSlot after [first] := by
            simp [raw, routeCommandsAux]
          have hraw : raw ∈ rawCommands := hcommands raw hroute
          have hrun := search ⟨growth, counterState, searchSlot⟩
            first.target first.direction after hraw
            ((atLogical growth T source).move
              (orient growth first.direction)) distance hdistance hgap
          rcases hrun with hsuccess | hfailure
          · left
            rw [hfound] at hsuccess
            exact hsuccess
          · exact Or.inr hfailure
  | cons next tail ih =>
      cases hexec with
      | cons _ _ _ middle _ hsource hfirst hrest =>
        have hmiddle := RouteExecutesWithin.start_lt hrest
        rcases legExecutesAt_depart_below hfirst hsource hmiddle with
          ⟨distance, hdistance, hgap, hfound⟩
        let handoff : ControlRef := directRef growth counterState directSlot
        let raw : RawCommand :=
          .boundaryNavigation ⟨growth, counterState, searchSlot⟩
            first.target first.direction handoff .preserve
        let continuation : RawDirectRule :=
          ⟨growth, handoff, .boundary first.target,
            searchRef growth counterState (searchSlot + 1), next.direction⟩
        have hroute : raw ∈ routeCommandsAux growth counterState
            searchSlot directSlot after (first :: next :: tail) := by
          simp [raw, handoff, routeCommandsAux]
        have hraw : raw ∈ rawCommands := hcommands raw hroute
        have hcontinuationRoute : continuation ∈
            routeContinuationRules growth counterState searchSlot
              directSlot (first :: next :: tail) := by
          simp [continuation, handoff, routeContinuationRules,
            routeContinuationRulesFrom]
        have hcontinuation : continuation ∈ rawDirectRules :=
          hcontinuations continuation hcontinuationRoute
        have hrun := search ⟨growth, counterState, searchSlot⟩
          first.target first.direction handoff hraw
          ((atLogical growth T source).move
            (orient growth first.direction)) distance hdistance hgap
        rcases hrun with hsearch | hfailure
        · have hsearch' : FullTM0.Reaches
              (CounterControlNestingBridge.machine base c)
              ⟨searchState base c ⟨growth, counterState, searchSlot⟩,
                (atLogical growth T source).move
                  (orient growth first.direction)⟩
              ⟨resolve base c handoff, atLogical growth T middle⟩ := by
            rw [hfound] at hsearch
            exact hsearch
          have hread := legExecutesAt_finish_read hfirst
          have hmatch : continuation.read.Matches
              (atLogical growth T middle).read := by
            change (atLogical growth T middle).read =
              boundarySymbol first.target
            exact hread
          have hdirectLocal :=
            CounterControlDirectSemantics.reaches_directRule base c
              continuation hcontinuation (atLogical growth T middle) hmatch
          have hdirect : FullTM0.Reaches
              (CounterControlNestingBridge.machine base c)
              ⟨resolve base c handoff, atLogical growth T middle⟩
              ⟨searchState base c
                  ⟨growth, counterState, searchSlot + 1⟩,
                (atLogical growth T middle).move
                  (orient growth next.direction)⟩ := by
            simpa [CounterControlNestingBridge.machine,
              BoundedMarkerProgram.machine, CounterControlPlan.table,
              continuation, handoff, searchRef,
              CounterControlPlan.resolve] using hdirectLocal
          have hcommandsTail : ∀ command,
              command ∈ routeCommandsAux growth counterState
                  (searchSlot + 1) (directSlot + 1) after (next :: tail) →
                command ∈ rawCommands := by
            intro command hcommand
            apply hcommands command
            exact List.mem_cons_of_mem _ hcommand
          have hcontinuationsTail : ∀ rule,
              rule ∈ routeContinuationRules growth counterState
                  (searchSlot + 1) (directSlot + 1) (next :: tail) →
                rule ∈ rawDirectRules := by
            intro rule hrule
            apply hcontinuations rule
            simp only [routeContinuationRules, routeContinuationRulesFrom,
              List.mem_cons]
            exact Or.inr hrule
          have htail := ih
            (first := next) (source := middle) (finish := finish)
            (searchSlot := searchSlot + 1)
            (directSlot := directSlot + 1) hrest hcommandsTail
            hcontinuationsTail
          have hprefix := hsearch'.trans hdirect
          rcases htail with hsuccess | htailFailure
          · exact Or.inl (hprefix.trans hsuccess)
          · exact Or.inr (pullback hprefix htailFailure)
        · exact Or.inr hfailure

/-- Add a route's direct entry rule to the failure-parametric search runner. -/
theorem route_reaches_with_failure_at
    (base : Nat) (c : Nat.Partrec.Code) (limit : Nat)
    (Failure : FullTM0.Cfg (Symbol numTags) FiniteTM0.State → Prop)
    (pullback : ∀ {start middle},
      FullTM0.Reaches (CounterControlNestingBridge.machine base c) start middle →
      Failure middle → Failure start)
    (search : ∀ (address : SearchAddress) (expected : Fin 5)
        (direction : Turing.Dir) (success : ControlRef)
        (hraw : RawCommand.boundaryNavigation address expected direction
          success .preserve ∈ rawCommands)
        (outer : FullTM0.Tape (Symbol numTags)) (distance : Nat),
      distance < limit →
      SearchGap (fun symbol => symbol = blankSymbol)
        (Target.boundary expected).Matches outer
        (orient address.growth direction) distance →
      FullTM0.Reaches (CounterControlNestingBridge.machine base c)
          ⟨searchState base c address, outer⟩
          ⟨resolve base c success,
            outer.moveN (orient address.growth direction) distance⟩ ∨
        Failure ⟨searchState base c address, outer⟩)
    (growth : Turing.Dir) (counterState searchSlot directSlot : Nat)
    (source after : ControlRef) (sourceBoundary : Fin 5)
    (first : MarkerValidation.Leg) (rest : List MarkerValidation.Leg)
    (T : FullTM0.Tape (Symbol numTags)) (sourcePosition finishPosition : Nat)
    (hsource : (atLogical growth T sourcePosition).read =
      boundarySymbol sourceBoundary)
    (hexec : RouteExecutesWithin growth T limit (first :: rest)
      sourcePosition finishPosition)
    (hcommands : ∀ raw,
      raw ∈ routeCommandsAux growth counterState searchSlot directSlot
          after (first :: rest) → raw ∈ rawCommands)
    (hrules : ∀ rule,
      rule ∈
          routeEntryRules growth counterState source sourceBoundary searchSlot
              (first :: rest) ++
            routeContinuationRules growth counterState searchSlot directSlot
              (first :: rest) → rule ∈ rawDirectRules) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨resolve base c source, atLogical growth T sourcePosition⟩
        ⟨resolve base c after, atLogical growth T finishPosition⟩ ∨
      Failure ⟨resolve base c source, atLogical growth T sourcePosition⟩ := by
  let entry : RawDirectRule :=
    ⟨growth, source, .boundary sourceBoundary,
      searchRef growth counterState searchSlot, first.direction⟩
  have hentryRoute : entry ∈
      routeEntryRules growth counterState source sourceBoundary searchSlot
        (first :: rest) := by
    simp [entry, routeEntryRules]
  have hentry : entry ∈ rawDirectRules := by
    apply hrules entry
    exact List.mem_append_left _ hentryRoute
  have hmatch : entry.read.Matches (atLogical growth T sourcePosition).read := by
    change (atLogical growth T sourcePosition).read =
      boundarySymbol sourceBoundary
    exact hsource
  have hentryLocal := CounterControlDirectSemantics.reaches_directRule
    base c entry hentry (atLogical growth T sourcePosition) hmatch
  have hentryReach : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      ⟨resolve base c source, atLogical growth T sourcePosition⟩
      ⟨searchState base c ⟨growth, counterState, searchSlot⟩,
        (atLogical growth T sourcePosition).move
          (orient growth first.direction)⟩ := by
    simpa [CounterControlNestingBridge.machine, BoundedMarkerProgram.machine,
      CounterControlPlan.table, entry, searchRef,
      CounterControlPlan.resolve] using hentryLocal
  have hcontinuations : ∀ rule,
      rule ∈ routeContinuationRules growth counterState searchSlot
          directSlot (first :: rest) → rule ∈ rawDirectRules := by
    intro rule hrule
    apply hrules rule
    exact List.mem_append_right _ hrule
  have hrun := searches_reach_with_failure_at base c limit Failure pullback
    search growth counterState searchSlot directSlot after first rest T
    sourcePosition finishPosition hexec hcommands hcontinuations
  rcases hrun with hsuccess | hfailure
  · exact Or.inl (hentryReach.trans hsuccess)
  · exact Or.inr (pullback hentryReach hfailure)

/-- Compile a nonempty route directly on an ambient tagged frame. -/
theorem route_reaches_or_nests_at
    (base : Nat) (c : Nat.Partrec.Code) (growth : Turing.Dir)
    (counterState searchSlot directSlot : Nat)
    (source after : ControlRef) (sourceBoundary : Fin 5)
    (first : MarkerValidation.Leg) (rest : List MarkerValidation.Leg)
    (T : FullTM0.Tape (Symbol numTags)) (sourcePosition finishPosition : Nat)
    (hsource : (atLogical growth T sourcePosition).read =
      boundarySymbol sourceBoundary)
    (hexec : RouteExecutesAt growth T (first :: rest)
      sourcePosition finishPosition)
    (hcommands : ∀ raw,
      raw ∈ routeCommandsAux growth counterState searchSlot directSlot
          after (first :: rest) →
        raw ∈ rawCommands)
    (hrules : ∀ rule,
      rule ∈
          routeEntryRules growth counterState source sourceBoundary searchSlot
              (first :: rest) ++
            routeContinuationRules growth counterState searchSlot directSlot
              (first :: rest) →
        rule ∈ rawDirectRules) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨resolve base c source, atLogical growth T sourcePosition⟩
        ⟨resolve base c after, atLogical growth T finishPosition⟩ ∨
      NestsFrom base c
        ⟨resolve base c source, atLogical growth T sourcePosition⟩ := by
  rcases hexec.exists_executesWithin with ⟨limit, hexecWithin⟩
  exact route_reaches_with_failure_at base c limit (NestsFrom base c)
    nestsFrom_of_reaches
    (by
      intro address expected direction success hraw outer distance _ hgap
      have hrun :=
        CounterControlNavigationSemantics.machine_reaches_boundary_preserve_or_nests
          base c address expected direction success hraw outer distance hgap
      rcases hrun with hnear | hfar
      · exact Or.inl hnear
      · rcases hfar with ⟨hfar, hreach, hframe⟩
        exact Or.inr ⟨.boundaryNavigation address expected direction success
          .preserve, hraw, outer, distance, hfar, hreach, hframe⟩)
    growth counterState searchSlot directSlot source after sourceBoundary
    first rest T sourcePosition finishPosition hsource hexecWithin hcommands
    hrules

/-! ## Routes discharged by shorter solved searches -/

private theorem searches_reach_solved_at
    (base : Nat) (c : Nat.Partrec.Code) (limit : Nat)
    (hshort : ShortSearches base c limit) (growth : Turing.Dir)
    (counterState searchSlot directSlot : Nat) (after : ControlRef)
    (first : MarkerValidation.Leg) (rest : List MarkerValidation.Leg)
    (T : FullTM0.Tape (Symbol numTags)) (source finish : Nat)
    (hexec : RouteExecutesWithin growth T limit (first :: rest)
      source finish)
    (hcommands : ∀ raw,
      raw ∈ routeCommandsAux growth counterState searchSlot directSlot
          after (first :: rest) → raw ∈ rawCommands)
    (hcontinuations : ∀ rule,
      rule ∈ routeContinuationRules growth counterState searchSlot
          directSlot (first :: rest) → rule ∈ rawDirectRules) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      ⟨searchState base c ⟨growth, counterState, searchSlot⟩,
        (atLogical growth T source).move (orient growth first.direction)⟩
      ⟨resolve base c after, atLogical growth T finish⟩ := by
  let Failure : FullTM0.Cfg (Symbol numTags) FiniteTM0.State → Prop :=
    fun _ => False
  have hrun := searches_reach_with_failure_at base c limit Failure
    (by intro _ _ _ hfailure; exact hfailure.elim)
    (by
      intro address expected direction success hraw outer distance hdistance
        hgap
      exact Or.inl (machine_reaches_boundary_preserve_solved base c limit
        hshort address expected direction success hraw outer distance
        hdistance hgap))
    growth counterState searchSlot directSlot after first rest T source finish
    hexec hcommands hcontinuations
  rcases hrun with hsuccess | hfailure
  · exact hsuccess
  · exact hfailure.elim

/-- Compile a nonempty native tagged route using the solved-search induction
hypothesis for every internal gap. -/
theorem route_reaches_solved_at
    (base : Nat) (c : Nat.Partrec.Code) (limit : Nat)
    (hshort : ShortSearches base c limit) (growth : Turing.Dir)
    (counterState searchSlot directSlot : Nat)
    (source after : ControlRef) (sourceBoundary : Fin 5)
    (first : MarkerValidation.Leg) (rest : List MarkerValidation.Leg)
    (T : FullTM0.Tape (Symbol numTags)) (sourcePosition finishPosition : Nat)
    (hsource : (atLogical growth T sourcePosition).read =
      boundarySymbol sourceBoundary)
    (hexec : RouteExecutesWithin growth T limit (first :: rest)
      sourcePosition finishPosition)
    (hcommands : ∀ raw,
      raw ∈ routeCommandsAux growth counterState searchSlot directSlot
          after (first :: rest) →
        raw ∈ rawCommands)
    (hrules : ∀ rule,
      rule ∈
          routeEntryRules growth counterState source sourceBoundary searchSlot
              (first :: rest) ++
            routeContinuationRules growth counterState searchSlot directSlot
              (first :: rest) →
        rule ∈ rawDirectRules) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      ⟨resolve base c source, atLogical growth T sourcePosition⟩
      ⟨resolve base c after, atLogical growth T finishPosition⟩ := by
  let Failure : FullTM0.Cfg (Symbol numTags) FiniteTM0.State → Prop :=
    fun _ => False
  have hrun := route_reaches_with_failure_at base c limit Failure
    (by intro _ _ _ hfailure; exact hfailure.elim)
    (by
      intro address expected direction success hraw outer distance hdistance
        hgap
      exact Or.inl (machine_reaches_boundary_preserve_solved base c limit
        hshort address expected direction success hraw outer distance
        hdistance hgap))
    growth counterState searchSlot directSlot source after sourceBoundary
    first rest T sourcePosition finishPosition hsource hexec hcommands hrules
  rcases hrun with hsuccess | hfailure
  · exact hsuccess
  · exact hfailure.elim

/-- Whole-list wrapper for a nonempty solved route. -/
theorem route_reaches_solved_at_of_ne_nil
    (base : Nat) (c : Nat.Partrec.Code) (limit : Nat)
    (hshort : ShortSearches base c limit) (growth : Turing.Dir)
    (counterState searchSlot directSlot : Nat)
    (source after : ControlRef) (sourceBoundary : Fin 5)
    (legs : List MarkerValidation.Leg) (hne : legs ≠ [])
    (T : FullTM0.Tape (Symbol numTags)) (sourcePosition finishPosition : Nat)
    (hsource : (atLogical growth T sourcePosition).read =
      boundarySymbol sourceBoundary)
    (hexec : RouteExecutesWithin growth T limit legs
      sourcePosition finishPosition)
    (hcommands : ∀ raw,
      raw ∈ routeCommandsAux growth counterState searchSlot directSlot
          after legs → raw ∈ rawCommands)
    (hrules : ∀ rule,
      rule ∈ routeEntryRules growth counterState source sourceBoundary
            searchSlot legs ++
          routeContinuationRules growth counterState searchSlot directSlot
            legs →
        rule ∈ rawDirectRules) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      ⟨resolve base c source, atLogical growth T sourcePosition⟩
      ⟨resolve base c after, atLogical growth T finishPosition⟩ := by
  cases legs with
  | nil => exact (hne rfl).elim
  | cons first rest =>
      exact route_reaches_solved_at base c limit hshort growth counterState
        searchSlot directSlot source after sourceBoundary first rest T
        sourcePosition finishPosition hsource hexec hcommands hrules

/-! ## Canonical routes of a represented frame -/

theorem leftLeg_executesAt {spec : Spec numTags}
    {T : FullTM0.Tape (Symbol numTags)} (h : Represents spec T)
    (i : Fin 4) :
    LegExecutesAt spec.growth T ⟨i.castSucc, .left⟩
      (boundaryOffset spec.registers i.succ)
      (boundaryOffset spec.registers i.castSucc) :=
  leftLeg_executesAt_of_core
    (CounterControlCoreFrame.PrefixRepresents.ofFramed h).toCoreRepresents i

theorem rightLeg_executesAt {spec : Spec numTags}
    {T : FullTM0.Tape (Symbol numTags)} (h : Represents spec T)
    (i : Fin 4) :
    LegExecutesAt spec.growth T ⟨i.succ, .right⟩
      (boundaryOffset spec.registers i.castSucc)
      (boundaryOffset spec.registers i.succ) :=
  rightLeg_executesAt_of_core
    (CounterControlCoreFrame.PrefixRepresents.ofFramed h).toCoreRepresents i

theorem boundaryOffset_lt_outerDistance {spec : Spec numTags}
    {T : FullTM0.Tape (Symbol numTags)} (h : Represents spec T)
    (label : Fin 5) :
    boundaryOffset spec.registers label < spec.outerDistance :=
  boundaryOffset_lt_limit_of_core
    (CounterControlCoreFrame.PrefixRepresents.ofFramed h).toCoreRepresents
    spec.core_before_target label

theorem registerValue_lt_outerDistance {spec : Spec numTags}
    {T : FullTM0.Tape (Symbol numTags)} (h : Represents spec T)
    (i : Fin 4) :
    RegisterLayout.values spec.registers i < spec.outerDistance := by
  have hb := boundaryOffset_lt_outerDistance h i.succ
  simp only [boundaryOffset, Fin.val_succ,
    CounterLayout.boundaryPos_succ] at hb
  omega

/-- Bounded form of the validation geometry used with `ShortSearches`. -/
theorem validation_executesWithin {spec : Spec numTags}
    {T : FullTM0.Tape (Symbol numTags)} (h : Represents spec T) :
    RouteExecutesWithin spec.growth T spec.outerDistance
      MarkerValidation.sweep (layoutEnd spec.registers)
      (layoutEnd spec.registers) :=
  validation_executesWithin_of_core
    (CounterControlCoreFrame.PrefixRepresents.ofFramed h).toCoreRepresents
    spec.core_before_target

theorem routeToDecrementStart_executesWithin {spec : Spec numTags}
    {T : FullTM0.Tape (Symbol numTags)} (h : Represents spec T)
    (register : Register) :
    RouteExecutesWithin spec.growth T spec.outerDistance
      (AnchoredCounterGeometry.routeToDecrementStart register)
      (layoutEnd spec.registers)
      (boundaryOffset spec.registers
        (MarkerSchedule.decrementStartBoundary register)) :=
  routeToDecrementStart_executesWithin_of_core
    (CounterControlCoreFrame.PrefixRepresents.ofFramed h).toCoreRepresents
    spec.core_before_target register

theorem routeFromIncrement_executesWithin {spec : Spec numTags}
    {T : FullTM0.Tape (Symbol numTags)} (h : Represents spec T)
    (register : Register) :
    RouteExecutesWithin spec.growth T spec.outerDistance
      (AnchoredCounterGeometry.routeFromIncrement register)
      (boundaryOffset spec.registers
        (MarkerSchedule.decrementStartBoundary register))
      (layoutEnd spec.registers) :=
  routeFromIncrement_executesWithin_of_core
    (CounterControlCoreFrame.PrefixRepresents.ofFramed h).toCoreRepresents
    spec.core_before_target register

theorem routeFromZero_executesWithin {spec : Spec numTags}
    {T : FullTM0.Tape (Symbol numTags)} (h : Represents spec T)
    (register : Register) :
    RouteExecutesWithin spec.growth T spec.outerDistance
      (AnchoredCounterGeometry.routeFromZero register)
      (boundaryOffset spec.registers
        (AnchoredCounterGeometry.registerGap register).castSucc)
      (layoutEnd spec.registers) :=
  routeFromZero_executesWithin_of_core
    (CounterControlCoreFrame.PrefixRepresents.ofFramed h).toCoreRepresents
    spec.core_before_target register
/-! The unbounded canonical-route statements are projections of the stronger
bounded geometry above. -/

/-- The complete validation sweep is executable without changing the
ambient tagged tape. -/
theorem validation_executesAt {spec : Spec numTags}
    {T : FullTM0.Tape (Symbol numTags)} (h : Represents spec T) :
    RouteExecutesAt spec.growth T MarkerValidation.sweep
      (layoutEnd spec.registers) (layoutEnd spec.registers) :=
  (validation_executesWithin h).toExecutesAt

theorem routeToDecrementStart_executesAt {spec : Spec numTags}
    {T : FullTM0.Tape (Symbol numTags)} (h : Represents spec T)
    (register : Register) :
    RouteExecutesAt spec.growth T
      (AnchoredCounterGeometry.routeToDecrementStart register)
      (layoutEnd spec.registers)
      (boundaryOffset spec.registers
        (MarkerSchedule.decrementStartBoundary register)) :=
  (routeToDecrementStart_executesWithin h register).toExecutesAt

theorem routeFromIncrement_executesAt {spec : Spec numTags}
    {T : FullTM0.Tape (Symbol numTags)} (h : Represents spec T)
    (register : Register) :
    RouteExecutesAt spec.growth T
      (AnchoredCounterGeometry.routeFromIncrement register)
      (boundaryOffset spec.registers
        (MarkerSchedule.decrementStartBoundary register))
      (layoutEnd spec.registers) :=
  (routeFromIncrement_executesWithin h register).toExecutesAt

theorem routeFromZero_executesAt {spec : Spec numTags}
    {T : FullTM0.Tape (Symbol numTags)} (h : Represents spec T)
    (register : Register) :
    RouteExecutesAt spec.growth T
      (AnchoredCounterGeometry.routeFromZero register)
      (boundaryOffset spec.registers
        (AnchoredCounterGeometry.registerGap register).castSucc)
      (layoutEnd spec.registers) :=
  (routeFromZero_executesWithin h register).toExecutesAt

/-! ## Validation prefix -/

private abbrev validationCommand_mem :=
  validationCommand_mem_commandsForRule
private abbrev validationRule_mem :=
  validationRule_mem_directRulesForRule

/-- One rule's mandatory eight-leg validation sweep returns to boundary `4`
and enters the instruction body, unless its first long gap launches a nested
frame. -/
theorem machine_reaches_validation_or_nests
    (base : Nat) (c : Nat.Partrec.Code) (growth : Turing.Dir)
    (source : Nat) (instruction : CounterMachine.Instruction)
    (hrule : (source, instruction) ∈ GlobalSourceProgram.program)
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T) (hgrowth : spec.growth = growth) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨logicalState base c growth source,
          atLogical growth T (layoutEnd spec.registers)⟩
        ⟨resolve base c (bodyEntry growth source instruction),
          atLogical growth T (layoutEnd spec.registers)⟩ ∨
      NestsFrom base c
        ⟨logicalState base c growth source,
          atLogical growth T (layoutEnd spec.registers)⟩ := by
  subst growth
  have hcommands : ∀ raw,
      raw ∈ validationCommands spec.growth source instruction →
        raw ∈ rawCommands := by
    intro raw hraw
    exact command_mem_rawCommands_of_rule spec.growth hrule
      (validationCommand_mem spec.growth source instruction hraw)
  have hrules : ∀ raw,
      raw ∈ validationRules spec.growth source →
        raw ∈ rawDirectRules := by
    intro raw hraw
    exact directRule_mem_rawDirectRules_of_rule spec.growth hrule
      (validationRule_mem spec.growth source instruction hraw)
  have hroute := route_reaches_or_nests_at base c spec.growth source
    validationSearchBase validationDirectBase
    (.logical spec.growth source) (bodyEntry spec.growth source instruction)
    4 ⟨3, .left⟩
    [⟨2, .left⟩, ⟨1, .left⟩, ⟨0, .left⟩,
      ⟨1, .right⟩, ⟨2, .right⟩, ⟨3, .right⟩,
      ⟨4, .right⟩]
    T (layoutEnd spec.registers) (layoutEnd spec.registers)
    h.read_boundary_four (by
      simpa only [MarkerValidation.sweep] using validation_executesAt h)
    (by
      intro raw hraw
      exact hcommands raw hraw)
    (by
      intro raw hraw
      exact hrules raw hraw)
  simpa [validationCommands, validationRules, logicalState,
    CounterControlPlan.resolve] using hroute

/-- Solved-search form of the validation prefix.  The strong-induction
hypothesis discharges every canonical gap before the suspended outer target,
so validation deterministically reaches the instruction body. -/
theorem machine_reaches_validation_solved
    (base : Nat) (c : Nat.Partrec.Code) (growth : Turing.Dir)
    (source : Nat) (instruction : CounterMachine.Instruction)
    (hrule : (source, instruction) ∈ GlobalSourceProgram.program)
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T) (hgrowth : spec.growth = growth)
    (hshort : ShortSearches base c spec.outerDistance) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      ⟨logicalState base c growth source,
        atLogical growth T (layoutEnd spec.registers)⟩
      ⟨resolve base c (bodyEntry growth source instruction),
        atLogical growth T (layoutEnd spec.registers)⟩ := by
  subst growth
  have hcommands : ∀ raw,
      raw ∈ validationCommands spec.growth source instruction →
        raw ∈ rawCommands := by
    intro raw hraw
    exact command_mem_rawCommands_of_rule spec.growth hrule
      (validationCommand_mem spec.growth source instruction hraw)
  have hrules : ∀ raw,
      raw ∈ validationRules spec.growth source →
        raw ∈ rawDirectRules := by
    intro raw hraw
    exact directRule_mem_rawDirectRules_of_rule spec.growth hrule
      (validationRule_mem spec.growth source instruction hraw)
  have hroute := route_reaches_solved_at base c spec.outerDistance hshort
    spec.growth source validationSearchBase validationDirectBase
    (.logical spec.growth source) (bodyEntry spec.growth source instruction)
    4 ⟨3, .left⟩
    [⟨2, .left⟩, ⟨1, .left⟩, ⟨0, .left⟩,
      ⟨1, .right⟩, ⟨2, .right⟩, ⟨3, .right⟩,
      ⟨4, .right⟩]
    T (layoutEnd spec.registers) (layoutEnd spec.registers)
    h.read_boundary_four (by
      simpa only [MarkerValidation.sweep] using validation_executesWithin h)
    (by
      intro raw hraw
      exact hcommands raw hraw)
    (by
      intro raw hraw
      exact hrules raw hraw)
  simpa [validationCommands, validationRules, logicalState,
    CounterControlPlan.resolve] using hroute

/-! ## Solved increment schedule -/

/-- Reinstalling any incremented register layout absorbs a previous
increment installation.  All incremented layouts have the same endpoint,
so the later canonical installation covers everything written by the
earlier one. -/
theorem install_incrementTape_eq
    (spec : Spec numTags) (T : FullTM0.Tape (Symbol numTags))
    (earlier later : Register) :
    install (spec.registers.increment later) spec.growth spec.returnTag
        (incrementTape spec earlier T) =
      incrementTape spec later T := by
  change install (spec.registers.increment later) spec.growth spec.returnTag
      (install (spec.registers.increment earlier) spec.growth
        spec.returnTag T) =
    install (spec.registers.increment later) spec.growth spec.returnTag T
  apply install_over_install
  simp only [layoutEnd_increment]
  omega

/- The increment schedule visits boundaries 4, 3, 2, and 1 in order.
These equations isolate its fixed geometry from the execution proof. -/
private theorem incrementSchedule_clock_start (registers : Registers) :
    layoutEnd registers =
      lastGapOffset (registers.increment .clock) 3 := by
  simp [lastGapOffset, CounterLayout.boundaryPos, layoutEnd,
    RegisterLayout.clockBoundary_eq, RegisterLayout.values,
    Registers.increment, Registers.set, Registers.get]
  omega

private theorem incrementSchedule_clock_temp (registers : Registers) :
    boundaryOffset (registers.increment .clock) ((3 : Fin 4).castSucc) =
      lastGapOffset (registers.increment .temp) 2 := by
  simp [lastGapOffset, boundaryOffset, CounterLayout.boundaryPos,
    RegisterLayout.values, Registers.increment, Registers.set, Registers.get]
  omega

private theorem incrementSchedule_temp_right (registers : Registers) :
    boundaryOffset (registers.increment .temp) ((2 : Fin 4).castSucc) =
      lastGapOffset (registers.increment .right) 1 := by
  simp [lastGapOffset, boundaryOffset, CounterLayout.boundaryPos,
    RegisterLayout.values, Registers.increment, Registers.set, Registers.get]
  omega

private theorem incrementSchedule_finish_temp (registers : Registers) :
    boundaryOffset (registers.increment .clock) ((3 : Fin 4).castSucc) =
      boundaryOffset registers 3 := by
  simp [boundaryOffset, CounterLayout.boundaryPos, RegisterLayout.values,
    Registers.increment, Registers.set, Registers.get]

private theorem incrementSchedule_finish_right (registers : Registers) :
    boundaryOffset (registers.increment .temp) ((2 : Fin 4).castSucc) =
      boundaryOffset registers 2 := by
  simp [boundaryOffset, CounterLayout.boundaryPos, RegisterLayout.values,
    Registers.increment, Registers.set, Registers.get]

private theorem incrementSchedule_finish_left (registers : Registers) :
    boundaryOffset (registers.increment .right) ((1 : Fin 4).castSucc) =
      boundaryOffset registers 1 := by
  simp [boundaryOffset, CounterLayout.boundaryPos, RegisterLayout.values,
    Registers.increment, Registers.set, Registers.get]

/-- The two primitive increment shifts needed by the register-independent
schedule.  The successful and halting-aware developments instantiate the
same runner with different shorter-search hypotheses and failure predicates.
-/
structure IncrementScheduleRunner
    (base : Nat) (c : Nat.Partrec.Code)
    (Short : Nat → Prop)
    (Failure : FullTM0.Cfg (Symbol numTags) FiniteTM0.State → Prop) where
  pullback : ∀ {start current},
    FullTM0.Reaches (CounterControlNestingBridge.machine base c) start current →
      Failure current → Failure start
  clock : ∀ (limit : Nat), Short limit →
    ∀ (counterState searchSlot : Nat)
      (success : ControlRef) (collision : Option ControlRef)
      {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)},
      Represents spec T →
      layoutEnd (spec.registers.increment .clock) < spec.outerDistance →
      0 < limit →
      RawCommand.markerShift
        ⟨spec.growth, counterState, searchSlot⟩ 4 .left .right
        success (some .left) collision ∈ rawCommands →
      FullTM0.CompletesOr (CounterControlNestingBridge.machine base c) Failure
        ⟨searchState base c ⟨spec.growth, counterState, searchSlot⟩,
          atLogical spec.growth T (layoutEnd spec.registers)⟩
        ⟨resolve base c success,
          atLogical spec.growth (incrementTape spec .clock T)
            (layoutEnd spec.registers)⟩
  internal : ∀ (limit : Nat), Short limit →
    ∀ (counterState searchSlot : Nat)
      (success : ControlRef) (collision : Option ControlRef)
      {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)},
      Represents spec T → ∀ (next : Registers) (i : Fin 4),
      0 < RegisterLayout.values spec.registers i →
      RegisterLayout.values spec.registers i < limit →
      layoutEnd next < spec.outerDistance →
      layoutEnd next = layoutEnd spec.registers →
      MarkerMachine.moveAt .right
          (MarkerTape.canonicalTape spec.registers)
          (MarkerTape.boundaryPosition spec.registers i.castSucc) i.castSucc =
        MarkerTape.canonicalTape next →
      RawCommand.markerShift
        ⟨spec.growth, counterState, searchSlot⟩ i.castSucc .left .right
        success (some .left) collision ∈ rawCommands →
      FullTM0.CompletesOr (CounterControlNestingBridge.machine base c) Failure
        ⟨searchState base c ⟨spec.growth, counterState, searchSlot⟩,
          atLogical spec.growth T (lastGapOffset spec.registers i)⟩
        ⟨resolve base c success,
          atLogical spec.growth
            (install next spec.growth spec.returnTag T)
            (boundaryOffset spec.registers i.castSucc)⟩

/-- Register-independent increment scheduling, parameterized by the outcome
of each constituent bounded search. -/
theorem machine_reaches_incrementSchedule_with
    (base : Nat) (c : Nat.Partrec.Code)
    (Short : Nat → Prop)
    (Failure : FullTM0.Cfg (Symbol numTags) FiniteTM0.State → Prop)
    (runner : IncrementScheduleRunner base c Short Failure)
    (source : Nat) (register : Register)
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T)
    (hroom : layoutEnd (spec.registers.increment register) <
      spec.outerDistance)
    (hshort : Short spec.outerDistance)
    (hcommands : ∀ raw,
      raw ∈ incrementShiftCommands spec.growth source register →
        raw ∈ rawCommands) :
    FullTM0.CompletesOr (CounterControlNestingBridge.machine base c) Failure
      ⟨searchState base c ⟨spec.growth, source, bodySearchBase⟩,
        atLogical spec.growth T (layoutEnd spec.registers)⟩
      ⟨resolve base c (directRef spec.growth source bodyDirectBase),
        atLogical spec.growth (incrementTape spec register T)
          (boundaryOffset spec.registers
            (MarkerSchedule.decrementStartBoundary register))⟩ := by
  have hlimit : 0 < spec.outerDistance := by
    have := hroom
    omega
  have hclockRoom : layoutEnd (spec.registers.increment .clock) <
      spec.outerDistance := by
    simpa only [layoutEnd_increment] using hroom
  have htempRoom : layoutEnd (spec.registers.increment .temp) <
      spec.outerDistance := by
    simpa only [layoutEnd_increment] using hroom
  have hrightRoom : layoutEnd (spec.registers.increment .right) <
      spec.outerDistance := by
    simpa only [layoutEnd_increment] using hroom
  have hleftRoom : layoutEnd (spec.registers.increment .left) <
      spec.outerDistance := by
    simpa only [layoutEnd_increment] using hroom
  cases register with
  | clock =>
      have hraw : RawCommand.markerShift
          ⟨spec.growth, source, bodySearchBase⟩ 4 .left .right
          (directRef spec.growth source bodyDirectBase) (some .left)
          (some (directRef spec.growth source testDirectSlot)) ∈
            rawCommands := by
        apply hcommands
        simp [incrementShiftCommands, incrementShiftCommandsAux,
          MarkerShift.incrementOrder]
      simpa [MarkerSchedule.decrementStartBoundary] using
        runner.clock spec.outerDistance hshort source bodySearchBase
          (directRef spec.growth source bodyDirectBase)
          (some (directRef spec.growth source testDirectSlot)) h hclockRoom
          hlimit hraw
  | temp =>
      let clockTape := incrementTape spec .clock T
      let clockSpec := incrementSpec spec .clock hclockRoom
      have hclockRep : Represents clockSpec clockTape :=
        incrementTape_represents h .clock hclockRoom
      have hrawFour : RawCommand.markerShift
          ⟨spec.growth, source, bodySearchBase⟩ 4 .left .right
          (searchRef spec.growth source (bodySearchBase + 1)) (some .left)
          (some (directRef spec.growth source testDirectSlot)) ∈
            rawCommands := by
        apply hcommands
        simp [incrementShiftCommands, incrementShiftCommandsAux,
          MarkerShift.incrementOrder]
      have hfour := runner.clock spec.outerDistance hshort source bodySearchBase
        (searchRef spec.growth source (bodySearchBase + 1))
        (some (directRef spec.growth source testDirectSlot)) h hclockRoom
        hlimit hrawFour
      have hrawThree : RawCommand.markerShift
          ⟨clockSpec.growth, source, bodySearchBase + 1⟩ 3 .left .right
          (directRef clockSpec.growth source bodyDirectBase) (some .left)
          none ∈ rawCommands := by
        simpa [clockSpec, incrementSpec, updateSpec] using hcommands
          (.markerShift
            ⟨spec.growth, source, bodySearchBase + 1⟩ 3 .left .right
            (directRef spec.growth source bodyDirectBase) (some .left) none)
          (by simp [incrementShiftCommands, incrementShiftCommandsAux,
            MarkerShift.incrementOrder])
      have hthree := runner.internal spec.outerDistance hshort source (bodySearchBase + 1)
        (directRef clockSpec.growth source bodyDirectBase) none hclockRep
        (spec.registers.increment .temp) (3 : Fin 4)
        (by simp [clockSpec, incrementSpec, updateSpec,
          RegisterLayout.values, Registers.increment, Registers.set,
          Registers.get])
        (by simpa [clockSpec, incrementSpec, updateSpec] using
          registerValue_lt_outerDistance hclockRep (3 : Fin 4))
        (by simpa [clockSpec, incrementSpec, updateSpec] using htempRoom)
        (by simp [clockSpec, incrementSpec, updateSpec, layoutEnd_increment])
        (by simpa [clockSpec, incrementSpec, updateSpec] using
          MarkerSchedule.moveTempBoundary_after_clock spec.registers)
        hrawThree
      have htape : install (spec.registers.increment .temp) spec.growth
          spec.returnTag clockTape = incrementTape spec .temp T := by
        simpa [clockTape] using
          install_incrementTape_eq spec T .clock .temp
      simp only [clockSpec, incrementSpec, updateSpec] at hthree
      rw [htape] at hthree
      rw [← incrementSchedule_clock_start spec.registers,
        incrementSchedule_finish_temp spec.registers] at hthree
      simp only [searchRef, CounterControlPlan.resolve] at hfour hthree
      exact FullTM0.CompletesOr.trans runner.pullback hfour hthree
  | right =>
      let clockTape := incrementTape spec .clock T
      let clockSpec := incrementSpec spec .clock hclockRoom
      let tempTape := incrementTape spec .temp T
      let tempSpec := incrementSpec spec .temp htempRoom
      have hclockRep : Represents clockSpec clockTape :=
        incrementTape_represents h .clock hclockRoom
      have htempRep : Represents tempSpec tempTape :=
        incrementTape_represents h .temp htempRoom
      have hrawFour : RawCommand.markerShift
          ⟨spec.growth, source, bodySearchBase⟩ 4 .left .right
          (searchRef spec.growth source (bodySearchBase + 1)) (some .left)
          (some (directRef spec.growth source testDirectSlot)) ∈
            rawCommands := by
        apply hcommands
        simp [incrementShiftCommands, incrementShiftCommandsAux,
          MarkerShift.incrementOrder]
      have hrawThree : RawCommand.markerShift
          ⟨clockSpec.growth, source, bodySearchBase + 1⟩ 3 .left .right
          (searchRef clockSpec.growth source (bodySearchBase + 2))
          (some .left) none ∈ rawCommands := by
        simpa [clockSpec, incrementSpec, updateSpec] using hcommands
          (.markerShift
            ⟨spec.growth, source, bodySearchBase + 1⟩ 3 .left .right
            (searchRef spec.growth source (bodySearchBase + 2))
            (some .left) none)
          (by simp [incrementShiftCommands, incrementShiftCommandsAux,
            MarkerShift.incrementOrder])
      have hrawTwo : RawCommand.markerShift
          ⟨tempSpec.growth, source, bodySearchBase + 2⟩ 2 .left .right
          (directRef tempSpec.growth source bodyDirectBase) (some .left)
          none ∈ rawCommands := by
        simpa [tempSpec, incrementSpec, updateSpec] using hcommands
          (.markerShift
            ⟨spec.growth, source, bodySearchBase + 2⟩ 2 .left .right
            (directRef spec.growth source bodyDirectBase) (some .left) none)
          (by simp [incrementShiftCommands, incrementShiftCommandsAux,
            MarkerShift.incrementOrder])
      have hfour := runner.clock spec.outerDistance hshort source bodySearchBase
        (searchRef spec.growth source (bodySearchBase + 1))
        (some (directRef spec.growth source testDirectSlot)) h hclockRoom
        hlimit hrawFour
      have hthree := runner.internal spec.outerDistance hshort source (bodySearchBase + 1)
        (searchRef clockSpec.growth source (bodySearchBase + 2)) none
        hclockRep (spec.registers.increment .temp) (3 : Fin 4)
        (by simp [clockSpec, incrementSpec, updateSpec,
          RegisterLayout.values, Registers.increment, Registers.set,
          Registers.get])
        (by simpa [clockSpec, incrementSpec, updateSpec] using
          registerValue_lt_outerDistance hclockRep (3 : Fin 4))
        (by simpa [clockSpec, incrementSpec, updateSpec] using htempRoom)
        (by simp [clockSpec, incrementSpec, updateSpec, layoutEnd_increment])
        (by simpa [clockSpec, incrementSpec, updateSpec] using
          MarkerSchedule.moveTempBoundary_after_clock spec.registers)
        hrawThree
      have htwo := runner.internal spec.outerDistance hshort source (bodySearchBase + 2)
        (directRef tempSpec.growth source bodyDirectBase) none htempRep
        (spec.registers.increment .right) (2 : Fin 4)
        (by simp [tempSpec, incrementSpec, updateSpec,
          RegisterLayout.values, Registers.increment, Registers.set,
          Registers.get])
        (by simpa [tempSpec, incrementSpec, updateSpec] using
          registerValue_lt_outerDistance htempRep (2 : Fin 4))
        (by simpa [tempSpec, incrementSpec, updateSpec] using hrightRoom)
        (by simp [tempSpec, incrementSpec, updateSpec, layoutEnd_increment])
        (by simpa [tempSpec, incrementSpec, updateSpec] using
          MarkerSchedule.moveRightBoundary_after_temp spec.registers)
        hrawTwo
      have htapeThree : install (spec.registers.increment .temp) spec.growth
          spec.returnTag clockTape = tempTape := by
        simpa [clockTape, tempTape] using
          install_incrementTape_eq spec T .clock .temp
      simp only [clockSpec, incrementSpec, updateSpec] at hthree
      rw [htapeThree] at hthree
      have htapeTwo : install (spec.registers.increment .right) spec.growth
          spec.returnTag tempTape = incrementTape spec .right T := by
        simpa [tempTape] using
          install_incrementTape_eq spec T .temp .right
      simp only [tempSpec, incrementSpec, updateSpec] at htwo
      rw [htapeTwo] at htwo
      rw [← incrementSchedule_clock_start spec.registers,
        incrementSchedule_clock_temp spec.registers] at hthree
      rw [incrementSchedule_finish_right spec.registers] at htwo
      simp only [searchRef, CounterControlPlan.resolve] at hfour hthree
      exact FullTM0.CompletesOr.trans runner.pullback hfour
        (FullTM0.CompletesOr.trans runner.pullback hthree htwo)
  | left =>
      let clockTape := incrementTape spec .clock T
      let clockSpec := incrementSpec spec .clock hclockRoom
      let tempTape := incrementTape spec .temp T
      let tempSpec := incrementSpec spec .temp htempRoom
      let rightTape := incrementTape spec .right T
      let rightSpec := incrementSpec spec .right hrightRoom
      have hclockRep : Represents clockSpec clockTape :=
        incrementTape_represents h .clock hclockRoom
      have htempRep : Represents tempSpec tempTape :=
        incrementTape_represents h .temp htempRoom
      have hrightRep : Represents rightSpec rightTape :=
        incrementTape_represents h .right hrightRoom
      have hrawFour : RawCommand.markerShift
          ⟨spec.growth, source, bodySearchBase⟩ 4 .left .right
          (searchRef spec.growth source (bodySearchBase + 1)) (some .left)
          (some (directRef spec.growth source testDirectSlot)) ∈
            rawCommands := by
        apply hcommands
        simp [incrementShiftCommands, incrementShiftCommandsAux,
          MarkerShift.incrementOrder]
      have hrawThree : RawCommand.markerShift
          ⟨clockSpec.growth, source, bodySearchBase + 1⟩ 3 .left .right
          (searchRef clockSpec.growth source (bodySearchBase + 2))
          (some .left) none ∈ rawCommands := by
        simpa [clockSpec, incrementSpec, updateSpec] using hcommands
          (.markerShift
            ⟨spec.growth, source, bodySearchBase + 1⟩ 3 .left .right
            (searchRef spec.growth source (bodySearchBase + 2))
            (some .left) none)
          (by simp [incrementShiftCommands, incrementShiftCommandsAux,
            MarkerShift.incrementOrder])
      have hrawTwo : RawCommand.markerShift
          ⟨tempSpec.growth, source, bodySearchBase + 2⟩ 2 .left .right
          (searchRef tempSpec.growth source (bodySearchBase + 3))
          (some .left) none ∈ rawCommands := by
        simpa [tempSpec, incrementSpec, updateSpec] using hcommands
          (.markerShift
            ⟨spec.growth, source, bodySearchBase + 2⟩ 2 .left .right
            (searchRef spec.growth source (bodySearchBase + 3))
            (some .left) none)
          (by simp [incrementShiftCommands, incrementShiftCommandsAux,
            MarkerShift.incrementOrder])
      have hrawOne : RawCommand.markerShift
          ⟨rightSpec.growth, source, bodySearchBase + 3⟩ 1 .left .right
          (directRef rightSpec.growth source bodyDirectBase) (some .left)
          none ∈ rawCommands := by
        simpa [rightSpec, incrementSpec, updateSpec] using hcommands
          (.markerShift
            ⟨spec.growth, source, bodySearchBase + 3⟩ 1 .left .right
            (directRef spec.growth source bodyDirectBase) (some .left) none)
          (by simp [incrementShiftCommands, incrementShiftCommandsAux,
            MarkerShift.incrementOrder])
      have hfour := runner.clock spec.outerDistance hshort source bodySearchBase
        (searchRef spec.growth source (bodySearchBase + 1))
        (some (directRef spec.growth source testDirectSlot)) h hclockRoom
        hlimit hrawFour
      have hthree := runner.internal spec.outerDistance hshort source (bodySearchBase + 1)
        (searchRef clockSpec.growth source (bodySearchBase + 2)) none
        hclockRep (spec.registers.increment .temp) (3 : Fin 4)
        (by simp [clockSpec, incrementSpec, updateSpec,
          RegisterLayout.values, Registers.increment, Registers.set,
          Registers.get])
        (by simpa [clockSpec, incrementSpec, updateSpec] using
          registerValue_lt_outerDistance hclockRep (3 : Fin 4))
        (by simpa [clockSpec, incrementSpec, updateSpec] using htempRoom)
        (by simp [clockSpec, incrementSpec, updateSpec, layoutEnd_increment])
        (by simpa [clockSpec, incrementSpec, updateSpec] using
          MarkerSchedule.moveTempBoundary_after_clock spec.registers)
        hrawThree
      have htwo := runner.internal spec.outerDistance hshort source (bodySearchBase + 2)
        (searchRef tempSpec.growth source (bodySearchBase + 3)) none
        htempRep (spec.registers.increment .right) (2 : Fin 4)
        (by simp [tempSpec, incrementSpec, updateSpec,
          RegisterLayout.values, Registers.increment, Registers.set,
          Registers.get])
        (by simpa [tempSpec, incrementSpec, updateSpec] using
          registerValue_lt_outerDistance htempRep (2 : Fin 4))
        (by simpa [tempSpec, incrementSpec, updateSpec] using hrightRoom)
        (by simp [tempSpec, incrementSpec, updateSpec, layoutEnd_increment])
        (by simpa [tempSpec, incrementSpec, updateSpec] using
          MarkerSchedule.moveRightBoundary_after_temp spec.registers)
        hrawTwo
      have hone := runner.internal spec.outerDistance hshort source (bodySearchBase + 3)
        (directRef rightSpec.growth source bodyDirectBase) none hrightRep
        (spec.registers.increment .left) (1 : Fin 4)
        (by simp [rightSpec, incrementSpec, updateSpec,
          RegisterLayout.values, Registers.increment, Registers.set,
          Registers.get])
        (by simpa [rightSpec, incrementSpec, updateSpec] using
          registerValue_lt_outerDistance hrightRep (1 : Fin 4))
        (by simpa [rightSpec, incrementSpec, updateSpec] using hleftRoom)
        (by simp [rightSpec, incrementSpec, updateSpec, layoutEnd_increment])
        (by simpa [rightSpec, incrementSpec, updateSpec] using
          MarkerSchedule.moveLeftBoundary_after_right spec.registers)
        hrawOne
      have htapeThree : install (spec.registers.increment .temp) spec.growth
          spec.returnTag clockTape = tempTape := by
        simpa [clockTape, tempTape] using
          install_incrementTape_eq spec T .clock .temp
      simp only [clockSpec, incrementSpec, updateSpec] at hthree
      rw [htapeThree] at hthree
      have htapeTwo : install (spec.registers.increment .right) spec.growth
          spec.returnTag tempTape = rightTape := by
        simpa [tempTape, rightTape] using
          install_incrementTape_eq spec T .temp .right
      simp only [tempSpec, incrementSpec, updateSpec] at htwo
      rw [htapeTwo] at htwo
      have htapeOne : install (spec.registers.increment .left) spec.growth
          spec.returnTag rightTape = incrementTape spec .left T := by
        simpa [rightTape] using
          install_incrementTape_eq spec T .right .left
      simp only [rightSpec, incrementSpec, updateSpec] at hone
      rw [htapeOne] at hone
      rw [← incrementSchedule_clock_start spec.registers,
        incrementSchedule_clock_temp spec.registers] at hthree
      rw [incrementSchedule_temp_right spec.registers] at htwo
      rw [incrementSchedule_finish_left spec.registers] at hone
      simp only [searchRef, CounterControlPlan.resolve] at hfour hthree htwo
      exact FullTM0.CompletesOr.trans runner.pullback hfour
        (FullTM0.CompletesOr.trans runner.pullback hthree
          (FullTM0.CompletesOr.trans runner.pullback htwo hone))

/-- All collision-free shifts of one generated increment execute exactly.
The endpoint is the blank old source cell of the last shifted boundary; the
following direct rule moves right onto the new boundary. -/
theorem machine_reaches_incrementSchedule_solved
    (base : Nat) (c : Nat.Partrec.Code) (source : Nat)
    (register : Register)
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T)
    (hroom : layoutEnd (spec.registers.increment register) <
      spec.outerDistance)
    (hshort : ShortSearches base c spec.outerDistance)
    (hcommands : ∀ raw,
      raw ∈ incrementShiftCommands spec.growth source register →
        raw ∈ rawCommands) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      ⟨searchState base c ⟨spec.growth, source, bodySearchBase⟩,
        atLogical spec.growth T (layoutEnd spec.registers)⟩
      ⟨resolve base c (directRef spec.growth source bodyDirectBase),
        atLogical spec.growth (incrementTape spec register T)
          (boundaryOffset spec.registers
            (MarkerSchedule.decrementStartBoundary register))⟩ := by
  let runner : IncrementScheduleRunner base c (ShortSearches base c)
      (fun _ => False) := {
    pullback := by
      intro _ _ _ failure
      exact failure.elim
    clock := by
      intro limit hshort counterState searchSlot success collision spec T
        h hroom hlimit hraw
      exact Or.inl (machine_reaches_incrementClock_solved base c limit hshort
        counterState searchSlot success collision h hroom hlimit hraw)
    internal := by
      intro limit hshort counterState searchSlot success collision spec T
        h next i hpositive hdistance hnextCore hsameEnd hmove hraw
      exact Or.inl (machine_reaches_incrementInternal_solved base c limit hshort
        counterState searchSlot success collision h next i hpositive hdistance
        hnextCore hsameEnd hmove hraw) }
  rcases machine_reaches_incrementSchedule_with base c (ShortSearches base c)
      (fun _ => False) runner source register h hroom hshort hcommands with
    result | failure
  · exact result
  · exact failure.elim

theorem incrementSchedule_source_blank
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T) (register : Register)
    (hroom : layoutEnd (spec.registers.increment register) <
      spec.outerDistance) :
    logicalTape spec.growth (incrementTape spec register T)
        (boundaryOffset spec.registers
          (MarkerSchedule.decrementStartBoundary register)) =
      blankSymbol := by
  exact (CounterControlCoreFrame.PrefixRepresents.ofFramed
      (incrementTape_represents h register hroom)).toCoreRepresents
    |>.increment_source_blank spec.registers register

/-- Recovery from the blank old source cell to boundary `4` after a complete
increment schedule. -/
theorem machine_reaches_incrementRecovery_solved
    (base : Nat) (c : Nat.Partrec.Code) (source next : Nat)
    (register : Register)
    (hrule : (source, .increment register next) ∈
      GlobalSourceProgram.program)
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T)
    (hshort : ShortSearches base c spec.outerDistance) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      ⟨resolve base c
          (match AnchoredCounterGeometry.routeFromIncrement register with
          | [] => .logical spec.growth next
          | _ :: _ => directRef spec.growth source (bodyDirectBase + 1)),
        atLogical spec.growth T
          (boundaryOffset spec.registers
            (MarkerSchedule.decrementStartBoundary register))⟩
      ⟨logicalState base c spec.growth next,
        atLogical spec.growth T (layoutEnd spec.registers)⟩ := by
  have hcommands : ∀ raw,
      raw ∈ routeCommandsAux spec.growth source secondarySearchBase
          (bodyDirectBase + 2) (.logical spec.growth next)
          (AnchoredCounterGeometry.routeFromIncrement register) →
        raw ∈ rawCommands := by
    intro raw hraw
    apply command_mem_rawCommands_of_rule spec.growth hrule
    simp [commandsForRule, incrementCommands, hraw]
  have hrules : ∀ raw,
      raw ∈ routeEntryRules spec.growth source
            (directRef spec.growth source (bodyDirectBase + 1))
            (MarkerSchedule.decrementStartBoundary register)
            secondarySearchBase
            (AnchoredCounterGeometry.routeFromIncrement register) ++
          routeContinuationRules spec.growth source secondarySearchBase
            (bodyDirectBase + 2)
            (AnchoredCounterGeometry.routeFromIncrement register) →
        raw ∈ rawDirectRules := by
    intro raw hraw
    apply directRule_mem_rawDirectRules_of_rule spec.growth hrule
    change raw ∈ validationRules spec.growth source ++
      incrementRules spec.growth source next register
    apply List.mem_append_right
    rcases List.mem_append.mp hraw with hentry | hcontinuation
    · simp only [incrementRules, List.mem_append]
      exact Or.inl (Or.inl (Or.inr hentry))
    · simp only [incrementRules, List.mem_append]
      exact Or.inl (Or.inr hcontinuation)
  cases register with
  | clock =>
      exact Relation.ReflTransGen.refl
  | temp =>
      have hrun := route_reaches_solved_at_of_ne_nil base c
        spec.outerDistance hshort
        spec.growth source secondarySearchBase (bodyDirectBase + 2)
        (directRef spec.growth source (bodyDirectBase + 1))
        (.logical spec.growth next) 3
        (AnchoredCounterGeometry.routeFromIncrement .temp)
        (by simp [AnchoredCounterGeometry.routeFromIncrement]) T
        (boundaryOffset spec.registers 3) (layoutEnd spec.registers)
        (by rw [atLogical_read]; exact h.boundary 3)
        (routeFromIncrement_executesWithin h .temp)
        (by intro raw hraw; exact hcommands raw hraw)
        (by intro raw hraw; exact hrules raw hraw)
      simpa [AnchoredCounterGeometry.routeFromIncrement, logicalState,
        CounterControlPlan.resolve,
        MarkerSchedule.decrementStartBoundary] using hrun
  | right =>
      have hrun := route_reaches_solved_at_of_ne_nil base c
        spec.outerDistance hshort
        spec.growth source secondarySearchBase (bodyDirectBase + 2)
        (directRef spec.growth source (bodyDirectBase + 1))
        (.logical spec.growth next) 2
        (AnchoredCounterGeometry.routeFromIncrement .right)
        (by simp [AnchoredCounterGeometry.routeFromIncrement]) T
        (boundaryOffset spec.registers 2) (layoutEnd spec.registers)
        (by rw [atLogical_read]; exact h.boundary 2)
        (routeFromIncrement_executesWithin h .right)
        (by intro raw hraw; exact hcommands raw hraw)
        (by intro raw hraw; exact hrules raw hraw)
      simpa [AnchoredCounterGeometry.routeFromIncrement, logicalState,
        CounterControlPlan.resolve,
        MarkerSchedule.decrementStartBoundary] using hrun
  | left =>
      have hrun := route_reaches_solved_at_of_ne_nil base c
        spec.outerDistance hshort
        spec.growth source secondarySearchBase (bodyDirectBase + 2)
        (directRef spec.growth source (bodyDirectBase + 1))
        (.logical spec.growth next) 1
        (AnchoredCounterGeometry.routeFromIncrement .left)
        (by simp [AnchoredCounterGeometry.routeFromIncrement]) T
        (boundaryOffset spec.registers 1) (layoutEnd spec.registers)
        (by rw [atLogical_read]; exact h.boundary 1)
        (routeFromIncrement_executesWithin h .left)
        (by intro raw hraw; exact hcommands raw hraw)
        (by intro raw hraw; exact hrules raw hraw)
      simpa [AnchoredCounterGeometry.routeFromIncrement, logicalState,
        CounterControlPlan.resolve,
        MarkerSchedule.decrementStartBoundary] using hrun

/-- The direct blank rule after the final increment shift moves onto the new
boundary and selects either the recovery route or (for clock) the logical
successor directly. -/
theorem machine_reaches_incrementHandoff
    (base : Nat) (c : Nat.Partrec.Code) (source next : Nat)
    (register : Register)
    (hrule : (source, .increment register next) ∈
      GlobalSourceProgram.program)
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T)
    (hroom : layoutEnd (spec.registers.increment register) <
      spec.outerDistance) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      ⟨resolve base c (directRef spec.growth source bodyDirectBase),
        atLogical spec.growth (incrementTape spec register T)
          (boundaryOffset spec.registers
            (MarkerSchedule.decrementStartBoundary register))⟩
      ⟨resolve base c
          (match AnchoredCounterGeometry.routeFromIncrement register with
          | [] => .logical spec.growth next
          | _ :: _ => directRef spec.growth source (bodyDirectBase + 1)),
        atLogical spec.growth (incrementTape spec register T)
          (boundaryOffset (spec.registers.increment register)
            (MarkerSchedule.decrementStartBoundary register))⟩ := by
  let route := AnchoredCounterGeometry.routeFromIncrement register
  let afterShift : ControlRef := match route with
    | [] => .logical spec.growth next
    | _ :: _ => directRef spec.growth source (bodyDirectBase + 1)
  let raw : RawDirectRule :=
    ⟨spec.growth, directRef spec.growth source bodyDirectBase, .blank,
      afterShift, .right⟩
  have hraw : raw ∈ rawDirectRules := by
    apply directRule_mem_rawDirectRules_of_rule spec.growth hrule
    change raw ∈ validationRules spec.growth source ++
      incrementRules spec.growth source next register
    apply List.mem_append_right
    simp only [incrementRules, List.mem_append]
    apply Or.inl
    apply Or.inl
    apply Or.inl
    simp only [List.mem_singleton]
    exact rfl
  have hblank : raw.read.Matches
      (atLogical spec.growth (incrementTape spec register T)
        (boundaryOffset spec.registers
          (MarkerSchedule.decrementStartBoundary register))).read := by
    change (atLogical spec.growth (incrementTape spec register T)
      (boundaryOffset spec.registers
        (MarkerSchedule.decrementStartBoundary register))).read = blankSymbol
    rw [atLogical_read]
    exact incrementSchedule_source_blank h register hroom
  have hrun := CounterControlDirectSemantics.reaches_directRule base c raw
    hraw (atLogical spec.growth (incrementTape spec register T)
      (boundaryOffset spec.registers
        (MarkerSchedule.decrementStartBoundary register))) hblank
  have hcoord : boundaryOffset spec.registers
        (MarkerSchedule.decrementStartBoundary register) + 1 =
      boundaryOffset (spec.registers.increment register)
        (MarkerSchedule.decrementStartBoundary register) :=
    AnchoredCounterGeometry.incrementStartBoundary_add_one
      spec.registers register
  rw [show orient spec.growth .right =
    OrientedMarkerTape.orientDirection spec.growth .right by
      exact orient_eq_orientDirection spec.growth .right,
    atLogical_move_right, hcoord] at hrun
  change FullTM0.Reaches (CounterControlNestingBridge.machine base c)
    ⟨resolve base c (directRef spec.growth source bodyDirectBase),
      atLogical spec.growth (incrementTape spec register T)
        (boundaryOffset spec.registers
          (MarkerSchedule.decrementStartBoundary register))⟩
    ⟨resolve base c
        (match AnchoredCounterGeometry.routeFromIncrement register with
        | [] => .logical spec.growth next
        | _ :: _ => directRef spec.growth source (bodyDirectBase + 1)),
      atLogical spec.growth (incrementTape spec register T)
        (boundaryOffset (spec.registers.increment register)
          (MarkerSchedule.decrementStartBoundary register))⟩ at hrun
  exact hrun

/-- Exact successful semantics of one compiled increment instruction on a
backed frame. -/
theorem machine_reaches_incrementInstruction_solved
    (base : Nat) (c : Nat.Partrec.Code) (source next : Nat)
    (register : Register)
    (hrule : (source, .increment register next) ∈
      GlobalSourceProgram.program)
    {spec : Spec numTags}
    {T outer : FullTM0.Tape (Symbol numTags)}
    (hback : BackedBy spec T outer)
    (hroom : layoutEnd (spec.registers.increment register) <
      spec.outerDistance)
    (hshort : ShortSearches base c spec.outerDistance) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨logicalState base c spec.growth source,
          atLogical spec.growth T (layoutEnd spec.registers)⟩
        ⟨logicalState base c spec.growth next,
          atLogical spec.growth (incrementTape spec register T)
            (layoutEnd (spec.registers.increment register))⟩ ∧
      BackedBy (incrementSpec spec register hroom)
        (incrementTape spec register T) outer := by
  have h := hback.represents
  have hvalidation := machine_reaches_validation_solved base c spec.growth
    source (.increment register next) hrule h rfl hshort
  have hcommands : ∀ raw,
      raw ∈ incrementShiftCommands spec.growth source register →
        raw ∈ rawCommands := by
    intro raw hraw
    apply command_mem_rawCommands_of_rule spec.growth hrule
    simp [commandsForRule, incrementCommands, hraw]
  have hschedule := machine_reaches_incrementSchedule_solved base c source
    register h hroom hshort hcommands
  have hhandoff := machine_reaches_incrementHandoff base c source next
    register hrule h hroom
  let nextSpec := incrementSpec spec register hroom
  have hnext : Represents nextSpec (incrementTape spec register T) :=
    incrementTape_represents h register hroom
  have hrecovery := machine_reaches_incrementRecovery_solved base c source next
    register hrule hnext (by
      simpa [nextSpec, incrementSpec, updateSpec] using hshort)
  have hvalidation' : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      ⟨logicalState base c spec.growth source,
        atLogical spec.growth T (layoutEnd spec.registers)⟩
      ⟨searchState base c ⟨spec.growth, source, bodySearchBase⟩,
        atLogical spec.growth T (layoutEnd spec.registers)⟩ := by
    simpa [bodyEntry, searchRef, CounterControlPlan.resolve] using hvalidation
  have hrecovery' : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      ⟨resolve base c
          (match AnchoredCounterGeometry.routeFromIncrement register with
          | [] => .logical spec.growth next
          | _ :: _ => directRef spec.growth source (bodyDirectBase + 1)),
        atLogical spec.growth (incrementTape spec register T)
          (boundaryOffset (spec.registers.increment register)
            (MarkerSchedule.decrementStartBoundary register))⟩
      ⟨logicalState base c spec.growth next,
        atLogical spec.growth (incrementTape spec register T)
          (layoutEnd (spec.registers.increment register))⟩ := by
    simpa [nextSpec, incrementSpec, updateSpec] using hrecovery
  constructor
  · exact hvalidation'.trans
      (hschedule.trans (hhandoff.trans hrecovery'))
  · exact incrementTape_backedBy hback register hroom

/-! ## Conditional-decrement routing and branching -/

/-- Navigate from boundary `4` to the boundary which tests the selected
register.  Clock needs no navigation. -/
theorem machine_reaches_decrementToTest_solved
    (base : Nat) (c : Nat.Partrec.Code) (source ifZero ifPositive : Nat)
    (register : Register)
    (hrule : (source, .decrement register ifZero ifPositive) ∈
      GlobalSourceProgram.program)
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T)
    (hshort : ShortSearches base c spec.outerDistance) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      ⟨resolve base c
          (bodyEntry spec.growth source
            (.decrement register ifZero ifPositive)),
        atLogical spec.growth T (layoutEnd spec.registers)⟩
      ⟨resolve base c (directRef spec.growth source testDirectSlot),
        atLogical spec.growth T
          (boundaryOffset spec.registers
            (MarkerSchedule.decrementStartBoundary register))⟩ := by
  let route := AnchoredCounterGeometry.routeToDecrementStart register
  have hcommands : ∀ raw,
      raw ∈ routeCommandsAux spec.growth source bodySearchBase
          (bodyDirectBase + 1) (directRef spec.growth source testDirectSlot)
          route → raw ∈ rawCommands := by
    intro raw hraw
    apply command_mem_rawCommands_of_rule spec.growth hrule
    simp [commandsForRule, decrementCommands, route, hraw]
  have hrules : ∀ raw,
      raw ∈ routeEntryRules spec.growth source
            (directRef spec.growth source bodyDirectBase) 4 bodySearchBase
            route ++
          routeContinuationRules spec.growth source bodySearchBase
            (bodyDirectBase + 1) route →
        raw ∈ rawDirectRules := by
    intro raw hraw
    apply directRule_mem_rawDirectRules_of_rule spec.growth hrule
    change raw ∈ validationRules spec.growth source ++
      decrementRules spec.growth source register ifZero ifPositive
    apply List.mem_append_right
    have hraw' : raw ∈
        routeEntryRules spec.growth source
            (directRef spec.growth source bodyDirectBase) 4 bodySearchBase
            (AnchoredCounterGeometry.routeToDecrementStart register) ++
          routeContinuationRules spec.growth source bodySearchBase
            (bodyDirectBase + 1)
            (AnchoredCounterGeometry.routeToDecrementStart register) := by
      simpa [route] using hraw
    rcases List.mem_append.mp hraw' with hentry | hcontinuation
    · simp only [decrementRules, List.mem_append]
      exact Or.inl (Or.inl (Or.inl hentry))
    · simp only [decrementRules, List.mem_append]
      exact Or.inl (Or.inl (Or.inr hcontinuation))
  cases register with
  | clock => exact Relation.ReflTransGen.refl
  | temp =>
      have hrun := route_reaches_solved_at_of_ne_nil base c
        spec.outerDistance hshort spec.growth source bodySearchBase
        (bodyDirectBase + 1) (directRef spec.growth source bodyDirectBase)
        (directRef spec.growth source testDirectSlot) 4
        (AnchoredCounterGeometry.routeToDecrementStart .temp)
        (by simp [AnchoredCounterGeometry.routeToDecrementStart]) T
        (layoutEnd spec.registers) (boundaryOffset spec.registers 3)
        h.read_boundary_four (routeToDecrementStart_executesWithin h .temp)
        (by intro raw hraw; exact hcommands raw hraw)
        (by intro raw hraw; exact hrules raw hraw)
      change FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨resolve base c
            (bodyEntry spec.growth source
              (.decrement .temp ifZero ifPositive)),
          atLogical spec.growth T (layoutEnd spec.registers)⟩
        ⟨resolve base c (directRef spec.growth source testDirectSlot),
          atLogical spec.growth T (boundaryOffset spec.registers 3)⟩ at hrun
      exact hrun
  | right =>
      have hrun := route_reaches_solved_at_of_ne_nil base c
        spec.outerDistance hshort spec.growth source bodySearchBase
        (bodyDirectBase + 1) (directRef spec.growth source bodyDirectBase)
        (directRef spec.growth source testDirectSlot) 4
        (AnchoredCounterGeometry.routeToDecrementStart .right)
        (by simp [AnchoredCounterGeometry.routeToDecrementStart]) T
        (layoutEnd spec.registers) (boundaryOffset spec.registers 2)
        h.read_boundary_four (routeToDecrementStart_executesWithin h .right)
        (by intro raw hraw; exact hcommands raw hraw)
        (by intro raw hraw; exact hrules raw hraw)
      change FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨resolve base c
            (bodyEntry spec.growth source
              (.decrement .right ifZero ifPositive)),
          atLogical spec.growth T (layoutEnd spec.registers)⟩
        ⟨resolve base c (directRef spec.growth source testDirectSlot),
          atLogical spec.growth T (boundaryOffset spec.registers 2)⟩ at hrun
      exact hrun
  | left =>
      have hrun := route_reaches_solved_at_of_ne_nil base c
        spec.outerDistance hshort spec.growth source bodySearchBase
        (bodyDirectBase + 1) (directRef spec.growth source bodyDirectBase)
        (directRef spec.growth source testDirectSlot) 4
        (AnchoredCounterGeometry.routeToDecrementStart .left)
        (by simp [AnchoredCounterGeometry.routeToDecrementStart]) T
        (layoutEnd spec.registers) (boundaryOffset spec.registers 1)
        h.read_boundary_four (routeToDecrementStart_executesWithin h .left)
        (by intro raw hraw; exact hcommands raw hraw)
        (by intro raw hraw; exact hrules raw hraw)
      change FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨resolve base c
            (bodyEntry spec.growth source
              (.decrement .left ifZero ifPositive)),
          atLogical spec.growth T (layoutEnd spec.registers)⟩
        ⟨resolve base c (directRef spec.growth source testDirectSlot),
          atLogical spec.growth T (boundaryOffset spec.registers 1)⟩ at hrun
      exact hrun

/-- The test rule moves left from the selected right boundary into the tested
gap. -/
theorem machine_reaches_decrementTest
    (base : Nat) (c : Nat.Partrec.Code) (source ifZero ifPositive : Nat)
    (register : Register)
    (hrule : (source, .decrement register ifZero ifPositive) ∈
      GlobalSourceProgram.program)
    {spec : Spec numTags} (T : FullTM0.Tape (Symbol numTags))
    (hread : (atLogical spec.growth T
      (boundaryOffset spec.registers
        (MarkerSchedule.decrementStartBoundary register))).read =
      boundarySymbol (MarkerSchedule.decrementStartBoundary register)) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      ⟨resolve base c (directRef spec.growth source testDirectSlot),
        atLogical spec.growth T
          (boundaryOffset spec.registers
            (MarkerSchedule.decrementStartBoundary register))⟩
      ⟨resolve base c (directRef spec.growth source branchDirectSlot),
        atLogical spec.growth T
          (boundaryOffset spec.registers
            (MarkerSchedule.decrementStartBoundary register) - 1)⟩ := by
  let raw : RawDirectRule :=
    ⟨spec.growth, directRef spec.growth source testDirectSlot,
      .boundary (MarkerSchedule.decrementStartBoundary register),
      directRef spec.growth source branchDirectSlot, .left⟩
  have hraw : raw ∈ rawDirectRules := by
    apply directRule_mem_rawDirectRules_of_rule spec.growth hrule
    change raw ∈ validationRules spec.growth source ++
      decrementRules spec.growth source register ifZero ifPositive
    apply List.mem_append_right
    simp [raw, decrementRules]
  have hmatch : raw.read.Matches
      (atLogical spec.growth T
        (boundaryOffset spec.registers
          (MarkerSchedule.decrementStartBoundary register))).read := by
    simpa [raw, RawRead.Matches] using hread
  have hrun := CounterControlDirectSemantics.reaches_directRule base c raw
    hraw (atLogical spec.growth T
      (boundaryOffset spec.registers
        (MarkerSchedule.decrementStartBoundary register))) hmatch
  have hpositive : 0 < boundaryOffset spec.registers
      (MarkerSchedule.decrementStartBoundary register) := by
    simp [boundaryOffset]
  have hmove : (atLogical spec.growth T
      (boundaryOffset spec.registers
        (MarkerSchedule.decrementStartBoundary register))).move
        (orient spec.growth .left) =
      atLogical spec.growth T
        (boundaryOffset spec.registers
          (MarkerSchedule.decrementStartBoundary register) - 1) := by
    rw [show boundaryOffset spec.registers
        (MarkerSchedule.decrementStartBoundary register) =
          (boundaryOffset spec.registers
            (MarkerSchedule.decrementStartBoundary register) - 1) + 1 by
      omega]
    rw [orient_eq_orientDirection, atLogical_move_left]
    congr 1
  rw [hmove] at hrun
  change FullTM0.Reaches (CounterControlNestingBridge.machine base c)
    ⟨resolve base c (directRef spec.growth source testDirectSlot),
      atLogical spec.growth T
        (boundaryOffset spec.registers
          (MarkerSchedule.decrementStartBoundary register))⟩
    ⟨resolve base c (directRef spec.growth source branchDirectSlot),
      atLogical spec.growth T
        (boundaryOffset spec.registers
          (MarkerSchedule.decrementStartBoundary register) - 1)⟩ at hrun
  exact hrun

/-- A zero tested gap is exactly the adjacent preceding boundary. -/
theorem decrement_zero_predecessor_read
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T) (register : Register)
    (hzero : spec.registers.get register = 0) :
    (atLogical spec.growth T
      (boundaryOffset spec.registers
        (MarkerSchedule.decrementStartBoundary register) - 1)).read =
      boundarySymbol
        (AnchoredCounterGeometry.registerGap register).castSucc := by
  have hcoord : boundaryOffset spec.registers
        (MarkerSchedule.decrementStartBoundary register) - 1 =
      boundaryOffset spec.registers
        (AnchoredCounterGeometry.registerGap register).castSucc :=
    AnchoredCounterGeometry.zeroTest_predecessor
      spec.registers register hzero
  rw [hcoord, atLogical_read]
  exact h.boundary _

/-- From the predecessor boundary of an empty tested gap, the generated zero
route returns to boundary `4` and enters the zero successor. -/
theorem machine_reaches_decrementZeroRecovery_solved
    (base : Nat) (c : Nat.Partrec.Code) (source ifZero ifPositive : Nat)
    (register : Register)
    (hrule : (source, .decrement register ifZero ifPositive) ∈
      GlobalSourceProgram.program)
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T)
    (hzero : spec.registers.get register = 0)
    (hshort : ShortSearches base c spec.outerDistance) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      ⟨resolve base c (directRef spec.growth source branchDirectSlot),
        atLogical spec.growth T
          (boundaryOffset spec.registers
            (MarkerSchedule.decrementStartBoundary register) - 1)⟩
      ⟨logicalState base c spec.growth ifZero,
        atLogical spec.growth T (layoutEnd spec.registers)⟩ := by
  let route := AnchoredCounterGeometry.routeFromZero register
  have hcommands : ∀ raw,
      raw ∈ routeCommandsAux spec.growth source zeroSearchBase zeroDirectBase
          (.logical spec.growth ifZero) route → raw ∈ rawCommands := by
    intro raw hraw
    apply command_mem_rawCommands_of_rule spec.growth hrule
    simp [commandsForRule, decrementCommands, route, hraw]
  have hrules : ∀ raw,
      raw ∈ routeEntryRules spec.growth source
            (directRef spec.growth source branchDirectSlot)
            (AnchoredCounterGeometry.registerGap register).castSucc
            zeroSearchBase route ++
          routeContinuationRules spec.growth source zeroSearchBase
            zeroDirectBase route → raw ∈ rawDirectRules := by
    intro raw hraw
    apply directRule_mem_rawDirectRules_of_rule spec.growth hrule
    change raw ∈ validationRules spec.growth source ++
      decrementRules spec.growth source register ifZero ifPositive
    apply List.mem_append_right
    rcases List.mem_append.mp hraw with hentry | hcontinuation
    · have hentryOriginal : raw ∈ routeEntryRules spec.growth source
          (directRef spec.growth source branchDirectSlot)
          (AnchoredCounterGeometry.registerGap register).castSucc
          zeroSearchBase
          (AnchoredCounterGeometry.routeFromZero register) := by
        simpa [route] using hentry
      have hentryRules : routeEntryRules spec.growth source
          (directRef spec.growth source branchDirectSlot)
          (AnchoredCounterGeometry.registerGap register).castSucc
          zeroSearchBase
          (AnchoredCounterGeometry.routeFromZero register) =
          [⟨spec.growth, directRef spec.growth source branchDirectSlot,
            .boundary
              (AnchoredCounterGeometry.registerGap register).castSucc,
            searchRef spec.growth source zeroSearchBase, .right⟩] := by
        cases register <;> rfl
      rw [hentryRules] at hentryOriginal
      have heq : raw =
          ⟨spec.growth, directRef spec.growth source branchDirectSlot,
            .boundary
              (AnchoredCounterGeometry.registerGap register).castSucc,
            searchRef spec.growth source zeroSearchBase, .right⟩ := by
        simpa using hentryOriginal
      have hfour : raw ∈
          [⟨spec.growth, directRef spec.growth source testDirectSlot,
              .boundary (MarkerSchedule.decrementStartBoundary register),
              directRef spec.growth source branchDirectSlot, .left⟩,
            ⟨spec.growth, directRef spec.growth source branchDirectSlot,
              .blank, searchRef spec.growth source secondarySearchBase,
              .right⟩,
            ⟨spec.growth, directRef spec.growth source branchDirectSlot,
              .boundary
                (AnchoredCounterGeometry.registerGap register).castSucc,
              searchRef spec.growth source zeroSearchBase, .right⟩,
            ⟨spec.growth, directRef spec.growth source finishDirectSlot,
              .blank, .logical spec.growth ifPositive, .left⟩] := by
        simp only [List.mem_cons, List.mem_singleton]
        exact Or.inr (Or.inr (Or.inl heq))
      simp only [decrementRules, List.mem_append]
      exact Or.inl (Or.inr hfour)
    · simp only [decrementRules, List.mem_append]
      exact Or.inr (by simpa [route] using hcontinuation)
  have hsourcePosition : boundaryOffset spec.registers
        (MarkerSchedule.decrementStartBoundary register) - 1 =
      boundaryOffset spec.registers
        (AnchoredCounterGeometry.registerGap register).castSucc :=
    AnchoredCounterGeometry.zeroTest_predecessor
      spec.registers register hzero
  have hrun := route_reaches_solved_at_of_ne_nil base c
    spec.outerDistance hshort spec.growth source zeroSearchBase zeroDirectBase
    (directRef spec.growth source branchDirectSlot)
    (.logical spec.growth ifZero)
    (AnchoredCounterGeometry.registerGap register).castSucc route
    (by simpa [route] using
      AnchoredCounterGeometry.routeFromZero_ne_nil register) T
    (boundaryOffset spec.registers
      (AnchoredCounterGeometry.registerGap register).castSucc)
    (layoutEnd spec.registers)
    (by rw [atLogical_read]; exact h.boundary _)
    (routeFromZero_executesWithin h register)
    (by intro raw hraw; exact hcommands raw hraw)
    (by intro raw hraw; exact hrules raw hraw)
  rw [hsourcePosition]
  simpa [route, logicalState, CounterControlPlan.resolve] using hrun

/-- Exact zero branch of one compiled conditional decrement. -/
theorem machine_reaches_decrementZeroInstruction_solved
    (base : Nat) (c : Nat.Partrec.Code) (source ifZero ifPositive : Nat)
    (register : Register)
    (hrule : (source, .decrement register ifZero ifPositive) ∈
      GlobalSourceProgram.program)
    {spec : Spec numTags}
    {T outer : FullTM0.Tape (Symbol numTags)}
    (hback : BackedBy spec T outer)
    (hzero : spec.registers.get register = 0)
    (hshort : ShortSearches base c spec.outerDistance) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      ⟨logicalState base c spec.growth source,
        atLogical spec.growth T (layoutEnd spec.registers)⟩
      ⟨logicalState base c spec.growth ifZero,
        atLogical spec.growth T (layoutEnd spec.registers)⟩ := by
  have h := hback.represents
  have hvalidation := machine_reaches_validation_solved base c spec.growth
    source (.decrement register ifZero ifPositive) hrule h rfl hshort
  have hroute := machine_reaches_decrementToTest_solved base c source ifZero
    ifPositive register hrule h hshort
  have htest := machine_reaches_decrementTest base c source ifZero ifPositive
    register hrule T (by
      rw [atLogical_read]
      exact h.boundary _)
  have hzeroRoute := machine_reaches_decrementZeroRecovery_solved base c
    source ifZero ifPositive register hrule h hzero hshort
  have hvalidation' : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      ⟨logicalState base c spec.growth source,
        atLogical spec.growth T (layoutEnd spec.registers)⟩
      ⟨resolve base c
          (bodyEntry spec.growth source
            (.decrement register ifZero ifPositive)),
        atLogical spec.growth T (layoutEnd spec.registers)⟩ := hvalidation
  have hpred := decrement_zero_predecessor_read h register hzero
  have hzeroRoute' := hzeroRoute
  exact hvalidation'.trans (hroute.trans (htest.trans (by
    -- The zero-route entry rule reads the predecessor boundary established
    -- by the represented empty gap.
    exact hzeroRoute')))

/-! ## Positive conditional-decrement branch -/

/-- The cell immediately left of the tested boundary is blank when the
selected register is positive. -/
theorem decrement_positive_predecessor_blank
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T) (register : Register)
    (hpositive : 0 < spec.registers.get register) :
    (atLogical spec.growth T
      (boundaryOffset spec.registers
        (MarkerSchedule.decrementStartBoundary register) - 1)).read =
      blankSymbol :=
  (show CounterControlCoreFrame.CoreRepresents
      spec.registers spec.growth T from ⟨h.core⟩)
    |>.positive_predecessor_blank register hpositive

/-- Clearing a source cell which the next canonical core covers preserves
the same exact outer backing. -/
theorem install_clear_inside_backedBy
    {spec : Spec numTags} {T outer : FullTM0.Tape (Symbol numTags)}
    (hback : BackedBy spec T outer) (next : Registers)
    (hnextCore : layoutEnd next < spec.outerDistance) (source : Nat)
    (hsourcePositive : 0 < source) (hsourceCore : source ≤ layoutEnd next)
    (hle : layoutEnd spec.registers ≤ layoutEnd next) :
    BackedBy (updateSpec spec next hnextCore)
      (install next spec.growth spec.returnTag
        (writeLogical spec.growth T source blankSymbol)) outer := by
  constructor
  · rw [install_clear_inside next spec.growth spec.returnTag T source
      hsourcePositive hsourceCore]
    rw [hback.installed]
    exact install_over_install spec.registers next spec.growth
      spec.returnTag outer hle
  · simpa [updateSpec] using hback.searchGap

/-- First positive-decrement shift: the head already sits on the tested
boundary, so its solved search has distance zero. -/
theorem machine_reaches_decrementFirst_with
    (base : Nat) (c : Nat.Partrec.Code) (limit : Nat)
    (Failure : FullTM0.Cfg (Symbol numTags) FiniteTM0.State → Prop)
    (runner : CompiledSearchRunner base c limit Failure)
    (counterState searchSlot : Nat)
    (success : ControlRef) (hlimit : 0 < limit)
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T) (next : Registers) (i : Fin 4)
    (hpositive : 0 < RegisterLayout.values spec.registers i)
    (hnextCore : layoutEnd next < spec.outerDistance)
    (hlower : layoutEnd next ≤ layoutEnd spec.registers)
    (hupper : layoutEnd spec.registers ≤ layoutEnd next + 1)
    (hsource : boundaryOffset spec.registers i.succ ≤
      layoutEnd spec.registers)
    (hdestination : boundaryOffset spec.registers i.succ - 1 ≤
      layoutEnd next)
    (hshrink : layoutEnd next < layoutEnd spec.registers →
      boundaryOffset spec.registers i.succ = layoutEnd spec.registers)
    (hmove : MarkerMachine.moveAt .left
        (MarkerTape.canonicalTape spec.registers)
        (MarkerTape.boundaryPosition spec.registers i.succ) i.succ =
      MarkerTape.canonicalTape next)
    (hraw : RawCommand.markerShift
      ⟨spec.growth, counterState, searchSlot⟩ i.succ .right .left success
      (some .right) none ∈ rawCommands) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨spec.growth, counterState, searchSlot⟩,
          atLogical spec.growth T (boundaryOffset spec.registers i.succ)⟩
        ⟨resolve base c success,
          atLogical spec.growth
            (install next spec.growth spec.returnTag
              (writeLogical spec.growth T
                (boundaryOffset spec.registers i.succ) blankSymbol))
            (boundaryOffset spec.registers i.succ)⟩ ∨
      Failure
        ⟨searchState base c ⟨spec.growth, counterState, searchSlot⟩,
          atLogical spec.growth T (boundaryOffset spec.registers i.succ)⟩ := by
  have hsourcePositive : 1 < boundaryOffset spec.registers i.succ := by
    simp [boundaryOffset]
  have hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary i.succ).Matches
      (atLogical spec.growth T (boundaryOffset spec.registers i.succ))
      (OrientedMarkerTape.orientDirection spec.growth .right) 0 := by
    rw [SearchGap.zero]
    change (atLogical spec.growth T
      (boundaryOffset spec.registers i.succ)).read = boundarySymbol i.succ
    rw [atLogical_read]
    exact h.boundary i.succ
  have hblank : logicalTape spec.growth T
      ((boundaryOffset spec.registers i.succ - 1 : Nat) : Int) =
        blankSymbol := by
    have hb := h.gap_blank i (RegisterLayout.values spec.registers i - 1)
      (by omega)
    have hcoord : (firstGapOffset spec.registers i : Int) +
        (RegisterLayout.values spec.registers i - 1 : Nat) =
        (boundaryOffset spec.registers i.succ - 1 : Nat) := by
      simp [firstGapOffset, boundaryOffset, CounterLayout.boundaryPos_succ]
      omega
    rw [hcoord] at hb
    exact hb
  apply machine_reaches_decrementCanonical_with base c limit Failure runner
    counterState searchSlot success none h next i.succ
    (boundaryOffset spec.registers i.succ) 0 hsourcePositive
    (by simp) hlimit hgap hblank hnextCore hlower hupper hsource hdestination
      hshrink hmove hraw

theorem machine_reaches_decrementFirst_solved
    (base : Nat) (c : Nat.Partrec.Code) (limit : Nat)
    (hshort : ShortSearches base c limit) (counterState searchSlot : Nat)
    (success : ControlRef) (hlimit : 0 < limit)
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T) (next : Registers) (i : Fin 4)
    (hpositive : 0 < RegisterLayout.values spec.registers i)
    (hnextCore : layoutEnd next < spec.outerDistance)
    (hlower : layoutEnd next ≤ layoutEnd spec.registers)
    (hupper : layoutEnd spec.registers ≤ layoutEnd next + 1)
    (hsource : boundaryOffset spec.registers i.succ ≤
      layoutEnd spec.registers)
    (hdestination : boundaryOffset spec.registers i.succ - 1 ≤
      layoutEnd next)
    (hshrink : layoutEnd next < layoutEnd spec.registers →
      boundaryOffset spec.registers i.succ = layoutEnd spec.registers)
    (hmove : MarkerMachine.moveAt .left
        (MarkerTape.canonicalTape spec.registers)
        (MarkerTape.boundaryPosition spec.registers i.succ) i.succ =
      MarkerTape.canonicalTape next)
    (hraw : RawCommand.markerShift
      ⟨spec.growth, counterState, searchSlot⟩ i.succ .right .left success
      (some .right) none ∈ rawCommands) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      ⟨searchState base c ⟨spec.growth, counterState, searchSlot⟩,
        atLogical spec.growth T (boundaryOffset spec.registers i.succ)⟩
      ⟨resolve base c success,
        atLogical spec.growth
          (install next spec.growth spec.returnTag
            (writeLogical spec.growth T
              (boundaryOffset spec.registers i.succ) blankSymbol))
          (boundaryOffset spec.registers i.succ)⟩ := by
  rcases machine_reaches_decrementFirst_with base c limit (fun _ => False)
      (solvedSearchRunner base c limit hshort) counterState searchSlot success hlimit h next i hpositive hnextCore
      hlower hupper hsource hdestination hshrink hmove hraw with hrun | failure
  · exact hrun
  · exact failure.elim

/-- Every later positive-decrement shift searches right across one represented
gap before moving its right boundary left. -/
theorem machine_reaches_decrementFollowing_with
    (base : Nat) (c : Nat.Partrec.Code) (limit : Nat)
    (Failure : FullTM0.Cfg (Symbol numTags) FiniteTM0.State → Prop)
    (runner : CompiledSearchRunner base c limit Failure)
    (counterState searchSlot : Nat)
    (success : ControlRef)
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T) (next : Registers) (i : Fin 4)
    (hpositive : 0 < RegisterLayout.values spec.registers i)
    (hdistance : RegisterLayout.values spec.registers i < limit)
    (hnextCore : layoutEnd next < spec.outerDistance)
    (hlower : layoutEnd next ≤ layoutEnd spec.registers)
    (hupper : layoutEnd spec.registers ≤ layoutEnd next + 1)
    (hsource : boundaryOffset spec.registers i.succ ≤
      layoutEnd spec.registers)
    (hdestination : boundaryOffset spec.registers i.succ - 1 ≤
      layoutEnd next)
    (hshrink : layoutEnd next < layoutEnd spec.registers →
      boundaryOffset spec.registers i.succ = layoutEnd spec.registers)
    (hmove : MarkerMachine.moveAt .left
        (MarkerTape.canonicalTape spec.registers)
        (MarkerTape.boundaryPosition spec.registers i.succ) i.succ =
      MarkerTape.canonicalTape next)
    (hraw : RawCommand.markerShift
      ⟨spec.growth, counterState, searchSlot⟩ i.succ .right .left success
      (some .right) none ∈ rawCommands) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨spec.growth, counterState, searchSlot⟩,
          atLogical spec.growth T (firstGapOffset spec.registers i)⟩
        ⟨resolve base c success,
          atLogical spec.growth
            (install next spec.growth spec.returnTag
              (writeLogical spec.growth T
                (boundaryOffset spec.registers i.succ) blankSymbol))
            (boundaryOffset spec.registers i.succ)⟩ ∨
      Failure
        ⟨searchState base c ⟨spec.growth, counterState, searchSlot⟩,
          atLogical spec.growth T (firstGapOffset spec.registers i)⟩ := by
  have hsourcePositive : 1 < boundaryOffset spec.registers i.succ := by
    simp [boundaryOffset]
  have horigin : firstGapOffset spec.registers i +
      RegisterLayout.values spec.registers i =
      boundaryOffset spec.registers i.succ := by
    simp [firstGapOffset, boundaryOffset, CounterLayout.boundaryPos_succ]
    omega
  have hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary i.succ).Matches
      (atLogical spec.growth T (firstGapOffset spec.registers i))
      (OrientedMarkerTape.orientDirection spec.growth .right)
      (RegisterLayout.values spec.registers i) := by
    change SearchGap (fun symbol => symbol = blankSymbol)
      (fun symbol => symbol = boundarySymbol i.succ) _ _ _
    exact h.searchGap_adjacent_right i
  have hblank : logicalTape spec.growth T
      ((boundaryOffset spec.registers i.succ - 1 : Nat) : Int) =
        blankSymbol := by
    have hb := h.gap_blank i (RegisterLayout.values spec.registers i - 1)
      (by omega)
    have hcoord : (firstGapOffset spec.registers i : Int) +
        (RegisterLayout.values spec.registers i - 1 : Nat) =
        (boundaryOffset spec.registers i.succ - 1 : Nat) := by
      simp [firstGapOffset, boundaryOffset, CounterLayout.boundaryPos_succ]
      omega
    rw [hcoord] at hb
    exact hb
  exact machine_reaches_decrementCanonical_with base c limit Failure runner
    counterState searchSlot success none h next i.succ
    (firstGapOffset spec.registers i)
    (RegisterLayout.values spec.registers i) hsourcePositive horigin
    hdistance hgap hblank hnextCore hlower hupper hsource hdestination
    hshrink hmove hraw

theorem machine_reaches_decrementFollowing_solved
    (base : Nat) (c : Nat.Partrec.Code) (limit : Nat)
    (hshort : ShortSearches base c limit) (counterState searchSlot : Nat)
    (success : ControlRef)
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T) (next : Registers) (i : Fin 4)
    (hpositive : 0 < RegisterLayout.values spec.registers i)
    (hdistance : RegisterLayout.values spec.registers i < limit)
    (hnextCore : layoutEnd next < spec.outerDistance)
    (hlower : layoutEnd next ≤ layoutEnd spec.registers)
    (hupper : layoutEnd spec.registers ≤ layoutEnd next + 1)
    (hsource : boundaryOffset spec.registers i.succ ≤
      layoutEnd spec.registers)
    (hdestination : boundaryOffset spec.registers i.succ - 1 ≤
      layoutEnd next)
    (hshrink : layoutEnd next < layoutEnd spec.registers →
      boundaryOffset spec.registers i.succ = layoutEnd spec.registers)
    (hmove : MarkerMachine.moveAt .left
        (MarkerTape.canonicalTape spec.registers)
        (MarkerTape.boundaryPosition spec.registers i.succ) i.succ =
      MarkerTape.canonicalTape next)
    (hraw : RawCommand.markerShift
      ⟨spec.growth, counterState, searchSlot⟩ i.succ .right .left success
      (some .right) none ∈ rawCommands) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      ⟨searchState base c ⟨spec.growth, counterState, searchSlot⟩,
        atLogical spec.growth T (firstGapOffset spec.registers i)⟩
      ⟨resolve base c success,
        atLogical spec.growth
          (install next spec.growth spec.returnTag
            (writeLogical spec.growth T
              (boundaryOffset spec.registers i.succ) blankSymbol))
          (boundaryOffset spec.registers i.succ)⟩ := by
  rcases machine_reaches_decrementFollowing_with base c limit (fun _ => False)
      (solvedSearchRunner base c limit hshort) counterState searchSlot success h next i hpositive hdistance hnextCore
      hlower hupper hsource hdestination hshrink hmove hraw with hrun | failure
  · exact hrun
  · exact failure.elim

/-- The positive branch reads a blank predecessor cell and moves right onto
the first boundary shifted by the decrement schedule. -/
theorem machine_reaches_decrementPositiveHandoff
    (base : Nat) (c : Nat.Partrec.Code) (source ifZero ifPositive : Nat)
    (register : Register)
    (hrule : (source, .decrement register ifZero ifPositive) ∈
      GlobalSourceProgram.program)
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T)
    (hpositive : 0 < spec.registers.get register) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      ⟨resolve base c (directRef spec.growth source branchDirectSlot),
        atLogical spec.growth T
          (boundaryOffset spec.registers
            (MarkerSchedule.decrementStartBoundary register) - 1)⟩
      ⟨searchState base c ⟨spec.growth, source, secondarySearchBase⟩,
        atLogical spec.growth T
          (boundaryOffset spec.registers
            (MarkerSchedule.decrementStartBoundary register))⟩ := by
  let raw : RawDirectRule :=
    ⟨spec.growth, directRef spec.growth source branchDirectSlot, .blank,
      searchRef spec.growth source secondarySearchBase, .right⟩
  have hraw : raw ∈ rawDirectRules := by
    apply directRule_mem_rawDirectRules_of_rule spec.growth hrule
    change raw ∈ validationRules spec.growth source ++
      decrementRules spec.growth source register ifZero ifPositive
    apply List.mem_append_right
    simp only [decrementRules, List.mem_append]
    apply Or.inl
    apply Or.inr
    simp [raw]
  have hblank : raw.read.Matches
      (atLogical spec.growth T
        (boundaryOffset spec.registers
          (MarkerSchedule.decrementStartBoundary register) - 1)).read := by
    change (atLogical spec.growth T
      (boundaryOffset spec.registers
        (MarkerSchedule.decrementStartBoundary register) - 1)).read =
      blankSymbol
    exact decrement_positive_predecessor_blank h register hpositive
  have hrun := CounterControlDirectSemantics.reaches_directRule base c raw
    hraw (atLogical spec.growth T
      (boundaryOffset spec.registers
        (MarkerSchedule.decrementStartBoundary register) - 1)) hblank
  have hp : 0 < boundaryOffset spec.registers
      (MarkerSchedule.decrementStartBoundary register) := by
    simp [boundaryOffset]
  have hmove : (atLogical spec.growth T
      (boundaryOffset spec.registers
        (MarkerSchedule.decrementStartBoundary register) - 1)).move
        (orient spec.growth .right) =
      atLogical spec.growth T
        (boundaryOffset spec.registers
          (MarkerSchedule.decrementStartBoundary register)) := by
    rw [show boundaryOffset spec.registers
        (MarkerSchedule.decrementStartBoundary register) =
          (boundaryOffset spec.registers
            (MarkerSchedule.decrementStartBoundary register) - 1) + 1 by
      omega]
    rw [orient_eq_orientDirection, atLogical_move_right]
    congr 1
  rw [hmove] at hrun
  change FullTM0.Reaches (CounterControlNestingBridge.machine base c)
    ⟨resolve base c (directRef spec.growth source branchDirectSlot),
      atLogical spec.growth T
        (boundaryOffset spec.registers
          (MarkerSchedule.decrementStartBoundary register) - 1)⟩
    ⟨searchState base c ⟨spec.growth, source, secondarySearchBase⟩,
      atLogical spec.growth T
        (boundaryOffset spec.registers
          (MarkerSchedule.decrementStartBoundary register))⟩ at hrun
  exact hrun

theorem boundaryOffset_le_layoutEnd (registers : Registers)
    (label : Fin 5) : boundaryOffset registers label ≤ layoutEnd registers := by
  change CounterLayout.boundaryPos (RegisterLayout.values registers) label + 1 ≤
    CounterLayout.boundaryPos (RegisterLayout.values registers) 4 + 1
  apply Nat.add_le_add_right
  exact CounterLayout.boundaryPos_mono _ (by omega)

/-- Complete positive-decrement suffix schedule, including exact preservation
of the suspended outer backing. -/
structure DecrementScheduleRunner
    (base : Nat) (c : Nat.Partrec.Code)
    (Short : Nat → Prop)
    (Failure : FullTM0.Cfg (Symbol numTags) FiniteTM0.State → Prop) where
  pullback : ∀ {start current},
    FullTM0.Reaches (CounterControlNestingBridge.machine base c) start current →
      Failure current → Failure start
  first : ∀ (limit : Nat), Short limit →
    ∀ (counterState searchSlot : Nat) (success : ControlRef), 0 < limit →
    ∀ {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)},
      Represents spec T → ∀ (next : Registers) (i : Fin 4),
      0 < RegisterLayout.values spec.registers i →
      layoutEnd next < spec.outerDistance →
      layoutEnd next ≤ layoutEnd spec.registers →
      layoutEnd spec.registers ≤ layoutEnd next + 1 →
      boundaryOffset spec.registers i.succ ≤ layoutEnd spec.registers →
      boundaryOffset spec.registers i.succ - 1 ≤ layoutEnd next →
      (layoutEnd next < layoutEnd spec.registers →
        boundaryOffset spec.registers i.succ = layoutEnd spec.registers) →
      MarkerMachine.moveAt .left
          (MarkerTape.canonicalTape spec.registers)
          (MarkerTape.boundaryPosition spec.registers i.succ) i.succ =
        MarkerTape.canonicalTape next →
      RawCommand.markerShift
        ⟨spec.growth, counterState, searchSlot⟩ i.succ .right .left success
        (some .right) none ∈ rawCommands →
      FullTM0.CompletesOr (CounterControlNestingBridge.machine base c) Failure
        ⟨searchState base c ⟨spec.growth, counterState, searchSlot⟩,
          atLogical spec.growth T (boundaryOffset spec.registers i.succ)⟩
        ⟨resolve base c success,
          atLogical spec.growth
            (install next spec.growth spec.returnTag
              (writeLogical spec.growth T
                (boundaryOffset spec.registers i.succ) blankSymbol))
            (boundaryOffset spec.registers i.succ)⟩
  following : ∀ (limit : Nat), Short limit →
    ∀ (counterState searchSlot : Nat) (success : ControlRef),
    ∀ {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)},
      Represents spec T → ∀ (next : Registers) (i : Fin 4),
      0 < RegisterLayout.values spec.registers i →
      RegisterLayout.values spec.registers i < limit →
      layoutEnd next < spec.outerDistance →
      layoutEnd next ≤ layoutEnd spec.registers →
      layoutEnd spec.registers ≤ layoutEnd next + 1 →
      boundaryOffset spec.registers i.succ ≤ layoutEnd spec.registers →
      boundaryOffset spec.registers i.succ - 1 ≤ layoutEnd next →
      (layoutEnd next < layoutEnd spec.registers →
        boundaryOffset spec.registers i.succ = layoutEnd spec.registers) →
      MarkerMachine.moveAt .left
          (MarkerTape.canonicalTape spec.registers)
          (MarkerTape.boundaryPosition spec.registers i.succ) i.succ =
        MarkerTape.canonicalTape next →
      RawCommand.markerShift
        ⟨spec.growth, counterState, searchSlot⟩ i.succ .right .left success
        (some .right) none ∈ rawCommands →
      FullTM0.CompletesOr (CounterControlNestingBridge.machine base c) Failure
        ⟨searchState base c ⟨spec.growth, counterState, searchSlot⟩,
          atLogical spec.growth T (firstGapOffset spec.registers i)⟩
        ⟨resolve base c success,
          atLogical spec.growth
            (install next spec.growth spec.returnTag
              (writeLogical spec.growth T
                (boundaryOffset spec.registers i.succ) blankSymbol))
            (boundaryOffset spec.registers i.succ)⟩

/-- Register-independent positive-decrement scheduling, parameterized by the
outcome of each constituent bounded search. -/
theorem machine_reaches_decrementSchedule_with
    (base : Nat) (c : Nat.Partrec.Code)
    (Short : Nat → Prop)
    (Failure : FullTM0.Cfg (Symbol numTags) FiniteTM0.State → Prop)
    (runner : DecrementScheduleRunner base c Short Failure)
    (source : Nat)
    (register : Register)
    {spec : Spec numTags} {T outer : FullTM0.Tape (Symbol numTags)}
    (hback : BackedBy spec T outer)
    (hpositive : 0 < spec.registers.get register)
    (hshort : Short spec.outerDistance)
    (hcommands : ∀ raw,
      raw ∈ decrementShiftCommands spec.growth source register →
        raw ∈ rawCommands) :
    (FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨spec.growth, source, secondarySearchBase⟩,
          atLogical spec.growth T
            (boundaryOffset spec.registers
              (MarkerSchedule.decrementStartBoundary register))⟩
        ⟨resolve base c (directRef spec.growth source finishDirectSlot),
          atLogical spec.growth (decrementTape spec register T)
            (layoutEnd spec.registers)⟩ ∧
      BackedBy (decrementSpec spec register hpositive)
        (decrementTape spec register T) outer) ∨
      Failure
        ⟨searchState base c ⟨spec.growth, source, secondarySearchBase⟩,
          atLogical spec.growth T
            (boundaryOffset spec.registers
              (MarkerSchedule.decrementStartBoundary register))⟩ := by
  have h := hback.represents
  have hlimit : 0 < spec.outerDistance := by
    exact Nat.zero_lt_of_lt spec.core_before_target
  have hdesired := decrementTape_backedBy hback register hpositive
  cases register with
  | clock =>
      have hp : 0 < spec.registers.clock := by
        simpa [Registers.get] using hpositive
      let next := spec.registers.decrement .clock
      have hnextCore : layoutEnd next < spec.outerDistance :=
        (layoutEnd_decrement_lt spec.registers .clock hpositive).trans
          spec.core_before_target
      have hend : layoutEnd next + 1 = layoutEnd spec.registers :=
        layoutEnd_decrement_add_one spec.registers .clock hpositive
      have hmove : MarkerMachine.moveAt .left
          (MarkerTape.canonicalTape spec.registers)
          (MarkerTape.boundaryPosition spec.registers 4) 4 =
        MarkerTape.canonicalTape next := by
        have hm := MarkerSchedule.moveClockBoundary_after_increment next
        have hinv := MarkerSchedule.increment_decrement_registers
          spec.registers .clock hpositive
        rw [hinv] at hm
        exact hm
      have hraw : RawCommand.markerShift
          ⟨spec.growth, source, secondarySearchBase⟩ 4 .right .left
          (directRef spec.growth source finishDirectSlot) (some .right)
          none ∈ rawCommands := by
        apply hcommands
        simp [decrementShiftCommands, decrementShiftCommandsAux,
          MarkerShift.decrementOrder]
      have hrun := runner.first spec.outerDistance hshort source secondarySearchBase
        (directRef spec.growth source finishDirectSlot) hlimit h next
        (3 : Fin 4) (by simpa [RegisterLayout.values] using hp)
        hnextCore (by omega) (by omega)
        (boundaryOffset_le_layoutEnd spec.registers 4)
        (by
          change layoutEnd spec.registers - 1 ≤ layoutEnd next
          omega)
        (by intro _; rfl) hmove hraw
      apply FullTM0.CompletesOr.and_right ?_ hdesired
      simpa [next, decrementTape, clearOldLayoutEnd,
        MarkerSchedule.decrementStartBoundary,
        boundaryOffset_four] using hrun
  | temp =>
      have hp : 0 < spec.registers.temp := by
        simpa [Registers.get] using hpositive
      let final := spec.registers.decrement .temp
      have hinv : final.increment .temp = spec.registers := by
        exact MarkerSchedule.increment_decrement_registers
          spec.registers .temp hpositive
      let clockRegs := final.increment .clock
      have hclockEnd : layoutEnd clockRegs = layoutEnd spec.registers := by
        rw [← hinv]
        simp only [clockRegs, layoutEnd_increment]
      have hclockCore : layoutEnd clockRegs < spec.outerDistance := by
        rw [hclockEnd]
        exact spec.core_before_target
      have hmoveThree : MarkerMachine.moveAt .left
          (MarkerTape.canonicalTape spec.registers)
          (MarkerTape.boundaryPosition spec.registers 3) 3 =
        MarkerTape.canonicalTape clockRegs := by
        have hm := MarkerSchedule.moveTempBoundary_before_clock final
        rw [hinv] at hm
        exact hm
      have hrawThree : RawCommand.markerShift
          ⟨spec.growth, source, secondarySearchBase⟩ 3 .right .left
          (searchRef spec.growth source (secondarySearchBase + 1))
          (some .right) none ∈ rawCommands := by
        apply hcommands
        simp [decrementShiftCommands, decrementShiftCommandsAux,
          MarkerShift.decrementOrder]
      have hthree := runner.first spec.outerDistance hshort source secondarySearchBase
        (searchRef spec.growth source (secondarySearchBase + 1)) hlimit h
        clockRegs (2 : Fin 4) (by simpa [RegisterLayout.values] using hp)
        hclockCore (by omega) (by omega)
        (boundaryOffset_le_layoutEnd spec.registers 3)
        (by
          change boundaryOffset spec.registers 3 - 1 ≤ layoutEnd clockRegs
          rw [hclockEnd]
          have hbound := boundaryOffset_le_layoutEnd spec.registers (3 : Fin 5)
          omega)
        (by
          intro hlt
          rw [hclockEnd] at hlt
          omega)
        hmoveThree hrawThree
      let Uclock := install clockRegs spec.growth spec.returnTag
        (writeLogical spec.growth T (boundaryOffset spec.registers 3)
          blankSymbol)
      let clockSpec := updateSpec spec clockRegs hclockCore
      have hclockBack : BackedBy clockSpec Uclock outer := by
        exact install_clear_inside_backedBy hback clockRegs hclockCore
          (boundaryOffset spec.registers 3) (by simp [boundaryOffset])
          (by rw [hclockEnd]; exact boundaryOffset_le_layoutEnd _ 3)
          (by omega)
      have hclockRep := hclockBack.represents
      have hfinalCore : layoutEnd final < clockSpec.outerDistance := by
        have hlt := layoutEnd_decrement_lt spec.registers .temp hpositive
        simpa [clockSpec, updateSpec, final] using
          hlt.trans spec.core_before_target
      have hfinalEnd : layoutEnd final + 1 = layoutEnd clockRegs := by
        rw [hclockEnd]
        exact layoutEnd_decrement_add_one spec.registers .temp hpositive
      have hmoveFour : MarkerMachine.moveAt .left
          (MarkerTape.canonicalTape clockSpec.registers)
          (MarkerTape.boundaryPosition clockSpec.registers 4) 4 =
        MarkerTape.canonicalTape final := by
        simpa [clockSpec, updateSpec, clockRegs] using
          MarkerSchedule.moveClockBoundary_after_increment final
      have hrawFour : RawCommand.markerShift
          ⟨clockSpec.growth, source, secondarySearchBase + 1⟩ 4 .right .left
          (directRef clockSpec.growth source finishDirectSlot) (some .right)
          none ∈ rawCommands := by
        simpa [clockSpec, updateSpec] using hcommands
          (.markerShift
            ⟨spec.growth, source, secondarySearchBase + 1⟩ 4 .right .left
            (directRef spec.growth source finishDirectSlot) (some .right) none)
          (by simp [decrementShiftCommands, decrementShiftCommandsAux,
            MarkerShift.decrementOrder])
      have hfour := runner.following spec.outerDistance (by simpa [clockSpec, updateSpec] using hshort)
        source (secondarySearchBase + 1)
        (directRef clockSpec.growth source finishDirectSlot) hclockRep final
        (3 : Fin 4)
        (by simp [clockSpec, updateSpec, clockRegs, final,
          RegisterLayout.values, Registers.increment, Registers.decrement,
          Registers.set, Registers.get])
        (by simpa [clockSpec, updateSpec] using
          registerValue_lt_outerDistance hclockRep (3 : Fin 4))
        hfinalCore
        (by
          dsimp only [clockSpec, updateSpec]
          rw [hclockEnd]
          omega)
        (by
          dsimp only [clockSpec, updateSpec]
          rw [hclockEnd]
          omega)
        (boundaryOffset_le_layoutEnd clockSpec.registers 4)
        (by
          change layoutEnd clockSpec.registers - 1 ≤ layoutEnd final
          dsimp only [clockSpec, updateSpec]
          rw [hclockEnd]
          omega)
        (by intro _; rfl) hmoveFour hrawFour
      have hhead : boundaryOffset spec.registers (Fin.succ (2 : Fin 4)) =
          firstGapOffset clockSpec.registers 3 := by
        change boundaryOffset spec.registers 3 =
          firstGapOffset clockSpec.registers 3
        simp [clockSpec, updateSpec, clockRegs, final, firstGapOffset,
          boundaryOffset, CounterLayout.boundaryPos,
          RegisterLayout.values, Registers.increment, Registers.decrement,
          Registers.set, Registers.get]
        omega
      have hfourBack := decrementTape_backedBy hclockBack .clock (by
        simp [clockSpec, updateSpec, clockRegs, final, Registers.get,
          Registers.increment, Registers.decrement, Registers.set])
      have hfinalRegs : (decrementSpec clockSpec .clock (by
          simp [clockSpec, updateSpec, clockRegs, final, Registers.get,
            Registers.increment, Registers.decrement, Registers.set])).registers =
          (decrementSpec spec .temp hpositive).registers := by
        simp [decrementSpec, updateSpec, clockSpec, clockRegs, final,
          Registers.increment, Registers.decrement, Registers.set,
          Registers.get]
      have hfinalTape : decrementTape clockSpec .clock Uclock =
          decrementTape spec .temp T := by
        calc
          decrementTape clockSpec .clock Uclock =
              install (decrementSpec clockSpec .clock (by
                simp [clockSpec, updateSpec, clockRegs, final, Registers.get,
                  Registers.increment, Registers.decrement,
                  Registers.set])).registers spec.growth spec.returnTag outer :=
            hfourBack.installed
          _ = install (decrementSpec spec .temp hpositive).registers
              spec.growth spec.returnTag outer := by rw [hfinalRegs]
          _ = decrementTape spec .temp T := hdesired.installed.symm
      have hclockDecrement : clockSpec.registers.decrement .clock = final := by
        simp [clockSpec, updateSpec, clockRegs, final, Registers.decrement,
          Registers.increment, Registers.set, Registers.get]
      have hresultTape :
          install final clockSpec.growth clockSpec.returnTag
              (writeLogical clockSpec.growth Uclock
                (boundaryOffset clockSpec.registers (Fin.succ (3 : Fin 4)))
                blankSymbol) =
            decrementTape clockSpec .clock Uclock := by
        rw [decrementTape, clearOldLayoutEnd, hclockDecrement]
        rw [show boundaryOffset clockSpec.registers
          (Fin.succ (3 : Fin 4)) = layoutEnd clockSpec.registers by rfl]
      rw [hhead] at hthree
      rw [hresultTape, hfinalTape] at hfour
      simp only [clockSpec, updateSpec] at hthree hfour
      have hhead' : boundaryOffset spec.registers (3 : Fin 5) =
          firstGapOffset clockRegs 3 := by
        simpa [clockSpec, updateSpec] using hhead
      have hUclock :
          install clockRegs spec.growth spec.returnTag
              (writeLogical spec.growth T (firstGapOffset clockRegs 3)
                blankSymbol) = Uclock := by
        dsimp only [Uclock]
        rw [← hhead']
      rw [hUclock] at hthree
      rw [show boundaryOffset clockRegs (Fin.succ (3 : Fin 4)) =
        layoutEnd clockRegs by rfl, hclockEnd] at hfour
      simp only [searchRef, CounterControlPlan.resolve] at hthree
      apply FullTM0.CompletesOr.and_right ?_ hdesired
      simpa only [MarkerSchedule.decrementStartBoundary, hhead'] using
        FullTM0.CompletesOr.trans runner.pullback hthree hfour
  | right =>
      have hp : 0 < spec.registers.right := by
        simpa [Registers.get] using hpositive
      let final := spec.registers.decrement .right
      have hinv : final.increment .right = spec.registers :=
        MarkerSchedule.increment_decrement_registers spec.registers .right
          hpositive
      let tempRegs := final.increment .temp
      let clockRegs := final.increment .clock
      have htempEnd : layoutEnd tempRegs = layoutEnd spec.registers := by
        rw [← hinv]
        simp only [tempRegs, layoutEnd_increment]
      have hclockEnd : layoutEnd clockRegs = layoutEnd spec.registers := by
        rw [← hinv]
        simp only [clockRegs, layoutEnd_increment]
      have htempCore : layoutEnd tempRegs < spec.outerDistance := by
        rw [htempEnd]
        exact spec.core_before_target
      have hmoveTwo := MarkerSchedule.moveRightBoundary_before_temp final
      rw [hinv] at hmoveTwo
      have hrawTwo : RawCommand.markerShift
          ⟨spec.growth, source, secondarySearchBase⟩ 2 .right .left
          (searchRef spec.growth source (secondarySearchBase + 1))
          (some .right) none ∈ rawCommands := by
        apply hcommands
        simp [decrementShiftCommands, decrementShiftCommandsAux,
          MarkerShift.decrementOrder]
      have htwo := runner.first spec.outerDistance hshort source secondarySearchBase
        (searchRef spec.growth source (secondarySearchBase + 1)) hlimit h
        tempRegs (1 : Fin 4)
        (by simpa [RegisterLayout.values, Registers.get] using hpositive)
        htempCore (by omega) (by omega)
        (boundaryOffset_le_layoutEnd spec.registers 2)
        (by
          change boundaryOffset spec.registers 2 - 1 ≤ layoutEnd tempRegs
          rw [htempEnd]
          have hbound := boundaryOffset_le_layoutEnd spec.registers (2 : Fin 5)
          omega)
        (by
          intro hlt
          rw [htempEnd] at hlt
          omega)
        hmoveTwo hrawTwo
      let Utemp := install tempRegs spec.growth spec.returnTag
        (writeLogical spec.growth T (boundaryOffset spec.registers 2)
          blankSymbol)
      let tempSpec := updateSpec spec tempRegs htempCore
      have htempBack : BackedBy tempSpec Utemp outer :=
        install_clear_inside_backedBy hback tempRegs htempCore
          (boundaryOffset spec.registers 2) (by simp [boundaryOffset])
          (by rw [htempEnd]; exact boundaryOffset_le_layoutEnd _ 2)
          (by omega)
      have hclockCore : layoutEnd clockRegs < tempSpec.outerDistance := by
        simpa [tempSpec, updateSpec, hclockEnd] using spec.core_before_target
      have hmoveThree : MarkerMachine.moveAt .left
          (MarkerTape.canonicalTape tempSpec.registers)
          (MarkerTape.boundaryPosition tempSpec.registers 3) 3 =
        MarkerTape.canonicalTape clockRegs := by
        simpa [tempSpec, updateSpec, tempRegs, clockRegs] using
          MarkerSchedule.moveTempBoundary_before_clock final
      have hrawThree : RawCommand.markerShift
          ⟨tempSpec.growth, source, secondarySearchBase + 1⟩ 3 .right .left
          (searchRef tempSpec.growth source (secondarySearchBase + 2))
          (some .right) none ∈ rawCommands := by
        simpa [tempSpec, updateSpec] using hcommands
          (.markerShift
            ⟨spec.growth, source, secondarySearchBase + 1⟩ 3 .right .left
            (searchRef spec.growth source (secondarySearchBase + 2))
            (some .right) none)
          (by simp [decrementShiftCommands, decrementShiftCommandsAux,
            MarkerShift.decrementOrder])
      have hthree := runner.following spec.outerDistance (by simpa [tempSpec, updateSpec] using hshort)
        source (secondarySearchBase + 1)
        (searchRef tempSpec.growth source (secondarySearchBase + 2))
        htempBack.represents clockRegs (2 : Fin 4)
        (by simp [tempSpec, updateSpec, tempRegs, final,
          RegisterLayout.values, Registers.increment, Registers.decrement,
          Registers.set, Registers.get])
        (by simpa [tempSpec, updateSpec] using
          registerValue_lt_outerDistance htempBack.represents (2 : Fin 4))
        hclockCore
        (by
          dsimp only [tempSpec, updateSpec]
          rw [hclockEnd, htempEnd])
        (by
          dsimp only [tempSpec, updateSpec]
          rw [hclockEnd, htempEnd]
          omega)
        (boundaryOffset_le_layoutEnd tempSpec.registers 3)
        (by
          dsimp only [tempSpec, updateSpec]
          have hbound := boundaryOffset_le_layoutEnd tempRegs
            (Fin.succ (2 : Fin 4))
          rw [htempEnd] at hbound
          omega)
        (by
          dsimp only [tempSpec, updateSpec]
          intro hlt
          rw [hclockEnd, htempEnd] at hlt
          omega)
        hmoveThree hrawThree
      let Uclock := install clockRegs tempSpec.growth tempSpec.returnTag
        (writeLogical tempSpec.growth Utemp
          (boundaryOffset tempSpec.registers 3) blankSymbol)
      let clockSpec := updateSpec tempSpec clockRegs hclockCore
      have hclockBack : BackedBy clockSpec Uclock outer :=
        install_clear_inside_backedBy htempBack clockRegs hclockCore
          (boundaryOffset tempSpec.registers 3) (by simp [boundaryOffset])
          (by
            dsimp only [tempSpec, updateSpec]
            have hbound := boundaryOffset_le_layoutEnd tempRegs (3 : Fin 5)
            rw [htempEnd] at hbound
            rw [hclockEnd]
            exact hbound)
          (by
            dsimp only [tempSpec, updateSpec]
            rw [hclockEnd, htempEnd])
      have hfinalCore : layoutEnd final < clockSpec.outerDistance := by
        have hlt := layoutEnd_decrement_lt spec.registers .right hpositive
        simpa [clockSpec, tempSpec, updateSpec, final] using
          hlt.trans spec.core_before_target
      have hfinalEnd : layoutEnd final + 1 = layoutEnd spec.registers := by
        exact layoutEnd_decrement_add_one spec.registers .right hpositive
      have hmoveFour : MarkerMachine.moveAt .left
          (MarkerTape.canonicalTape clockSpec.registers)
          (MarkerTape.boundaryPosition clockSpec.registers 4) 4 =
        MarkerTape.canonicalTape final := by
        simpa [clockSpec, tempSpec, updateSpec, clockRegs] using
          MarkerSchedule.moveClockBoundary_after_increment final
      have hrawFour : RawCommand.markerShift
          ⟨clockSpec.growth, source, secondarySearchBase + 2⟩ 4 .right .left
          (directRef clockSpec.growth source finishDirectSlot) (some .right)
          none ∈ rawCommands := by
        simpa [clockSpec, tempSpec, updateSpec] using hcommands
          (.markerShift
            ⟨spec.growth, source, secondarySearchBase + 2⟩ 4 .right .left
            (directRef spec.growth source finishDirectSlot) (some .right) none)
          (by simp [decrementShiftCommands, decrementShiftCommandsAux,
            MarkerShift.decrementOrder])
      have hfour := runner.following spec.outerDistance (by simpa [clockSpec, tempSpec, updateSpec] using hshort)
        source (secondarySearchBase + 2)
        (directRef clockSpec.growth source finishDirectSlot)
        hclockBack.represents final (3 : Fin 4)
        (by simp [clockSpec, tempSpec, updateSpec, clockRegs, final,
          RegisterLayout.values, Registers.increment, Registers.decrement,
          Registers.set, Registers.get])
        (by simpa [clockSpec, tempSpec, updateSpec] using
          registerValue_lt_outerDistance hclockBack.represents (3 : Fin 4))
        hfinalCore
        (by
          dsimp only [clockSpec, tempSpec, updateSpec]
          rw [hclockEnd]
          omega)
        (by
          dsimp only [clockSpec, tempSpec, updateSpec]
          rw [hclockEnd]
          omega)
        (boundaryOffset_le_layoutEnd clockSpec.registers 4)
        (by
          change layoutEnd clockSpec.registers - 1 ≤ layoutEnd final
          dsimp only [clockSpec, tempSpec, updateSpec]
          rw [hclockEnd]
          omega)
        (by intro _; rfl) hmoveFour hrawFour
      have hheadTwo :
          boundaryOffset spec.registers (Fin.succ (1 : Fin 4)) =
          firstGapOffset tempSpec.registers 2 := by
        change boundaryOffset spec.registers 2 =
          firstGapOffset tempSpec.registers 2
        rw [← hinv]
        simp [tempSpec, updateSpec, tempRegs, final, firstGapOffset,
          boundaryOffset, CounterLayout.boundaryPos,
          RegisterLayout.values, Registers.increment, Registers.decrement,
          Registers.set, Registers.get]
        omega
      have hheadThree :
          boundaryOffset tempSpec.registers (Fin.succ (2 : Fin 4)) =
          firstGapOffset clockSpec.registers 3 := by
        change boundaryOffset tempSpec.registers 3 =
          firstGapOffset clockSpec.registers 3
        simp [clockSpec, tempSpec, updateSpec, clockRegs, tempRegs, final,
          firstGapOffset, boundaryOffset, CounterLayout.boundaryPos,
          RegisterLayout.values, Registers.increment, Registers.decrement,
          Registers.set, Registers.get]
        omega
      have hfourBack := decrementTape_backedBy hclockBack .clock (by
        simp [clockSpec, tempSpec, updateSpec, clockRegs, final,
          Registers.get, Registers.increment, Registers.decrement,
          Registers.set])
      have hfinalTape : decrementTape clockSpec .clock Uclock =
          decrementTape spec .right T := by
        calc
          _ = install final spec.growth spec.returnTag outer := by
            simpa [clockSpec, tempSpec, updateSpec, clockRegs, final,
              decrementSpec, Registers.increment, Registers.decrement,
              Registers.set, Registers.get] using hfourBack.installed
          _ = _ := by
            simpa [final, decrementSpec, updateSpec] using hdesired.installed.symm
      have hclockDecrement : clockSpec.registers.decrement .clock = final := by
        simp [clockSpec, tempSpec, updateSpec, clockRegs, final,
          Registers.decrement, Registers.increment, Registers.set,
          Registers.get]
      have hresultTape :
          install final clockSpec.growth clockSpec.returnTag
              (writeLogical clockSpec.growth Uclock
                (boundaryOffset clockSpec.registers (Fin.succ (3 : Fin 4)))
                blankSymbol) =
            decrementTape clockSpec .clock Uclock := by
        rw [decrementTape, clearOldLayoutEnd, hclockDecrement]
        rw [show boundaryOffset clockSpec.registers
          (Fin.succ (3 : Fin 4)) = layoutEnd clockSpec.registers by rfl]
      rw [hresultTape, hfinalTape] at hfour
      have hheadTwo' : boundaryOffset spec.registers (2 : Fin 5) =
          firstGapOffset tempRegs 2 := by
        simpa [tempSpec, updateSpec] using hheadTwo
      have hheadThree' : boundaryOffset tempRegs (3 : Fin 5) =
          firstGapOffset clockRegs 3 := by
        simpa [clockSpec, tempSpec, updateSpec] using hheadThree
      rw [hheadTwo] at htwo
      rw [hheadThree] at hthree
      simp only [tempSpec, clockSpec, updateSpec] at htwo hthree hfour
      have hUtemp :
          install tempRegs spec.growth spec.returnTag
              (writeLogical spec.growth T (firstGapOffset tempRegs 2)
                blankSymbol) = Utemp := by
        dsimp only [Utemp]
        rw [← hheadTwo']
      have hUclock :
          install clockRegs spec.growth spec.returnTag
              (writeLogical spec.growth Utemp (firstGapOffset clockRegs 3)
                blankSymbol) = Uclock := by
        dsimp only [Uclock, tempSpec, updateSpec]
        rw [← hheadThree']
      rw [hUtemp] at htwo
      rw [hUclock] at hthree
      rw [show boundaryOffset clockRegs (Fin.succ (3 : Fin 4)) =
        layoutEnd clockRegs by rfl, hclockEnd] at hfour
      simp only [searchRef, CounterControlPlan.resolve] at htwo hthree
      apply FullTM0.CompletesOr.and_right ?_ hdesired
      simpa only [MarkerSchedule.decrementStartBoundary, hheadTwo'] using
        FullTM0.CompletesOr.trans runner.pullback htwo (FullTM0.CompletesOr.trans runner.pullback hthree hfour)
  | left =>
      have hp : 0 < spec.registers.left := by
        simpa [Registers.get] using hpositive
      let final := spec.registers.decrement .left
      have hinv : final.increment .left = spec.registers :=
        MarkerSchedule.increment_decrement_registers spec.registers .left
          hpositive
      let rightRegs := final.increment .right
      let tempRegs := final.increment .temp
      let clockRegs := final.increment .clock
      have hrightEnd : layoutEnd rightRegs = layoutEnd spec.registers := by
        rw [← hinv]
        simp only [rightRegs, layoutEnd_increment]
      have htempEnd : layoutEnd tempRegs = layoutEnd spec.registers := by
        rw [← hinv]
        simp only [tempRegs, layoutEnd_increment]
      have hclockEnd : layoutEnd clockRegs = layoutEnd spec.registers := by
        rw [← hinv]
        simp only [clockRegs, layoutEnd_increment]
      have hrightCore : layoutEnd rightRegs < spec.outerDistance := by
        rw [hrightEnd]
        exact spec.core_before_target
      have hmoveOne := MarkerSchedule.moveLeftBoundary_before_right final
      rw [hinv] at hmoveOne
      have hrawOne : RawCommand.markerShift
          ⟨spec.growth, source, secondarySearchBase⟩ 1 .right .left
          (searchRef spec.growth source (secondarySearchBase + 1))
          (some .right) none ∈ rawCommands := by
        apply hcommands
        simp [decrementShiftCommands, decrementShiftCommandsAux,
          MarkerShift.decrementOrder]
      have hone := runner.first spec.outerDistance hshort source secondarySearchBase
        (searchRef spec.growth source (secondarySearchBase + 1)) hlimit h
        rightRegs (0 : Fin 4)
        (by simpa [RegisterLayout.values, Registers.get] using hpositive)
        hrightCore (by omega) (by omega)
        (boundaryOffset_le_layoutEnd spec.registers 1)
        (by
          change boundaryOffset spec.registers 1 - 1 ≤ layoutEnd rightRegs
          rw [hrightEnd]
          have hbound := boundaryOffset_le_layoutEnd spec.registers (1 : Fin 5)
          omega)
        (by
          intro hlt
          rw [hrightEnd] at hlt
          omega)
        hmoveOne hrawOne
      let Uright := install rightRegs spec.growth spec.returnTag
        (writeLogical spec.growth T (boundaryOffset spec.registers 1)
          blankSymbol)
      let rightSpec := updateSpec spec rightRegs hrightCore
      have hrightBack : BackedBy rightSpec Uright outer :=
        install_clear_inside_backedBy hback rightRegs hrightCore
          (boundaryOffset spec.registers 1) (by simp [boundaryOffset])
          (by rw [hrightEnd]; exact boundaryOffset_le_layoutEnd _ 1)
          (by omega)
      have htempCore : layoutEnd tempRegs < rightSpec.outerDistance := by
        simpa [rightSpec, updateSpec, htempEnd] using spec.core_before_target
      have hmoveTwo : MarkerMachine.moveAt .left
          (MarkerTape.canonicalTape rightSpec.registers)
          (MarkerTape.boundaryPosition rightSpec.registers 2) 2 =
        MarkerTape.canonicalTape tempRegs := by
        simpa [rightSpec, updateSpec, rightRegs, tempRegs] using
          MarkerSchedule.moveRightBoundary_before_temp final
      have hrawTwo : RawCommand.markerShift
          ⟨rightSpec.growth, source, secondarySearchBase + 1⟩ 2 .right .left
          (searchRef rightSpec.growth source (secondarySearchBase + 2))
          (some .right) none ∈ rawCommands := by
        simpa [rightSpec, updateSpec] using hcommands
          (.markerShift
            ⟨spec.growth, source, secondarySearchBase + 1⟩ 2 .right .left
            (searchRef spec.growth source (secondarySearchBase + 2))
            (some .right) none)
          (by simp [decrementShiftCommands, decrementShiftCommandsAux,
            MarkerShift.decrementOrder])
      have htwo := runner.following spec.outerDistance (by simpa [rightSpec, updateSpec] using hshort)
        source (secondarySearchBase + 1)
        (searchRef rightSpec.growth source (secondarySearchBase + 2))
        hrightBack.represents tempRegs (1 : Fin 4)
        (by simp [rightSpec, updateSpec, rightRegs, final,
          RegisterLayout.values, Registers.increment, Registers.decrement,
          Registers.set, Registers.get])
        (by simpa [rightSpec, updateSpec] using
          registerValue_lt_outerDistance hrightBack.represents (1 : Fin 4))
        htempCore
        (by
          dsimp only [rightSpec, updateSpec]
          rw [htempEnd, hrightEnd])
        (by
          dsimp only [rightSpec, updateSpec]
          rw [htempEnd, hrightEnd]
          omega)
        (boundaryOffset_le_layoutEnd rightSpec.registers 2)
        (by
          dsimp only [rightSpec, updateSpec]
          have hbound := boundaryOffset_le_layoutEnd rightRegs
            (Fin.succ (1 : Fin 4))
          rw [hrightEnd] at hbound
          omega)
        (by
          dsimp only [rightSpec, updateSpec]
          intro hlt
          rw [htempEnd, hrightEnd] at hlt
          omega)
        hmoveTwo hrawTwo
      let Utemp := install tempRegs rightSpec.growth rightSpec.returnTag
        (writeLogical rightSpec.growth Uright
          (boundaryOffset rightSpec.registers 2) blankSymbol)
      let tempSpec := updateSpec rightSpec tempRegs htempCore
      have htempBack : BackedBy tempSpec Utemp outer :=
        install_clear_inside_backedBy hrightBack tempRegs htempCore
          (boundaryOffset rightSpec.registers 2) (by simp [boundaryOffset])
          (by
            dsimp only [rightSpec, updateSpec]
            have hbound := boundaryOffset_le_layoutEnd rightRegs (2 : Fin 5)
            rw [hrightEnd] at hbound
            rw [htempEnd]
            exact hbound)
          (by
            dsimp only [rightSpec, updateSpec]
            rw [htempEnd, hrightEnd])
      have hclockCore : layoutEnd clockRegs < tempSpec.outerDistance := by
        simpa [tempSpec, rightSpec, updateSpec, hclockEnd] using
          spec.core_before_target
      have hmoveThree : MarkerMachine.moveAt .left
          (MarkerTape.canonicalTape tempSpec.registers)
          (MarkerTape.boundaryPosition tempSpec.registers 3) 3 =
        MarkerTape.canonicalTape clockRegs := by
        simpa [tempSpec, rightSpec, updateSpec, tempRegs, clockRegs] using
          MarkerSchedule.moveTempBoundary_before_clock final
      have hrawThree : RawCommand.markerShift
          ⟨tempSpec.growth, source, secondarySearchBase + 2⟩ 3 .right .left
          (searchRef tempSpec.growth source (secondarySearchBase + 3))
          (some .right) none ∈ rawCommands := by
        simpa [tempSpec, rightSpec, updateSpec] using hcommands
          (.markerShift
            ⟨spec.growth, source, secondarySearchBase + 2⟩ 3 .right .left
            (searchRef spec.growth source (secondarySearchBase + 3))
            (some .right) none)
          (by simp [decrementShiftCommands, decrementShiftCommandsAux,
            MarkerShift.decrementOrder])
      have hthree := runner.following spec.outerDistance (by simpa [tempSpec, rightSpec, updateSpec] using hshort)
        source (secondarySearchBase + 2)
        (searchRef tempSpec.growth source (secondarySearchBase + 3))
        htempBack.represents clockRegs (2 : Fin 4)
        (by simp [tempSpec, rightSpec, updateSpec, tempRegs, final,
          RegisterLayout.values, Registers.increment, Registers.decrement,
          Registers.set, Registers.get])
        (by simpa [tempSpec, rightSpec, updateSpec] using
          registerValue_lt_outerDistance htempBack.represents (2 : Fin 4))
        hclockCore
        (by
          dsimp only [tempSpec, rightSpec, updateSpec]
          rw [hclockEnd, htempEnd])
        (by
          dsimp only [tempSpec, rightSpec, updateSpec]
          rw [hclockEnd, htempEnd]
          omega)
        (boundaryOffset_le_layoutEnd tempSpec.registers 3)
        (by
          dsimp only [tempSpec, rightSpec, updateSpec]
          have hbound := boundaryOffset_le_layoutEnd tempRegs
            (Fin.succ (2 : Fin 4))
          rw [htempEnd] at hbound
          omega)
        (by
          dsimp only [tempSpec, rightSpec, updateSpec]
          intro hlt
          rw [hclockEnd, htempEnd] at hlt
          omega)
        hmoveThree hrawThree
      let Uclock := install clockRegs tempSpec.growth tempSpec.returnTag
        (writeLogical tempSpec.growth Utemp
          (boundaryOffset tempSpec.registers 3) blankSymbol)
      let clockSpec := updateSpec tempSpec clockRegs hclockCore
      have hclockBack : BackedBy clockSpec Uclock outer :=
        install_clear_inside_backedBy htempBack clockRegs hclockCore
          (boundaryOffset tempSpec.registers 3) (by simp [boundaryOffset])
          (by
            dsimp only [tempSpec, rightSpec, updateSpec]
            have hbound := boundaryOffset_le_layoutEnd tempRegs (3 : Fin 5)
            rw [htempEnd] at hbound
            rw [hclockEnd]
            exact hbound)
          (by
            dsimp only [tempSpec, rightSpec, updateSpec]
            rw [hclockEnd, htempEnd])
      have hfinalCore : layoutEnd final < clockSpec.outerDistance := by
        have hlt := layoutEnd_decrement_lt spec.registers .left hpositive
        simpa [clockSpec, tempSpec, rightSpec, updateSpec, final] using
          hlt.trans spec.core_before_target
      have hfinalEnd : layoutEnd final + 1 = layoutEnd spec.registers := by
        exact layoutEnd_decrement_add_one spec.registers .left hpositive
      have hmoveFour : MarkerMachine.moveAt .left
          (MarkerTape.canonicalTape clockSpec.registers)
          (MarkerTape.boundaryPosition clockSpec.registers 4) 4 =
        MarkerTape.canonicalTape final := by
        simpa [clockSpec, tempSpec, rightSpec, updateSpec, clockRegs] using
          MarkerSchedule.moveClockBoundary_after_increment final
      have hrawFour : RawCommand.markerShift
          ⟨clockSpec.growth, source, secondarySearchBase + 3⟩ 4 .right .left
          (directRef clockSpec.growth source finishDirectSlot) (some .right)
          none ∈ rawCommands := by
        simpa [clockSpec, tempSpec, rightSpec, updateSpec] using hcommands
          (.markerShift
            ⟨spec.growth, source, secondarySearchBase + 3⟩ 4 .right .left
            (directRef spec.growth source finishDirectSlot) (some .right) none)
          (by simp [decrementShiftCommands, decrementShiftCommandsAux,
            MarkerShift.decrementOrder])
      have hfour := runner.following spec.outerDistance (by simpa [clockSpec, tempSpec, rightSpec, updateSpec] using hshort)
        source (secondarySearchBase + 3)
        (directRef clockSpec.growth source finishDirectSlot)
        hclockBack.represents final (3 : Fin 4)
        (by simp [clockSpec, tempSpec, rightSpec, updateSpec, clockRegs, final,
          RegisterLayout.values, Registers.increment, Registers.decrement,
          Registers.set, Registers.get])
        (by simpa [clockSpec, tempSpec, rightSpec, updateSpec] using
          registerValue_lt_outerDistance hclockBack.represents (3 : Fin 4))
        hfinalCore
        (by
          dsimp only [clockSpec, tempSpec, rightSpec, updateSpec]
          rw [hclockEnd]
          omega)
        (by
          dsimp only [clockSpec, tempSpec, rightSpec, updateSpec]
          rw [hclockEnd]
          omega)
        (boundaryOffset_le_layoutEnd clockSpec.registers 4)
        (by
          change layoutEnd clockSpec.registers - 1 ≤ layoutEnd final
          dsimp only [clockSpec, tempSpec, rightSpec, updateSpec]
          rw [hclockEnd]
          omega)
        (by intro _; rfl) hmoveFour hrawFour
      have hheadOne :
          boundaryOffset spec.registers (Fin.succ (0 : Fin 4)) =
          firstGapOffset rightSpec.registers 1 := by
        change boundaryOffset spec.registers 1 =
          firstGapOffset rightSpec.registers 1
        rw [← hinv]
        simp [rightSpec, updateSpec, rightRegs, final, firstGapOffset,
          boundaryOffset, CounterLayout.boundaryPos, RegisterLayout.values,
          Registers.increment, Registers.decrement, Registers.set,
          Registers.get]
      have hheadTwo :
          boundaryOffset rightSpec.registers (Fin.succ (1 : Fin 4)) =
          firstGapOffset tempSpec.registers 2 := by
        change boundaryOffset rightSpec.registers 2 =
          firstGapOffset tempSpec.registers 2
        simp [tempSpec, rightSpec, updateSpec, tempRegs, rightRegs, final,
          firstGapOffset, boundaryOffset, CounterLayout.boundaryPos,
          RegisterLayout.values, Registers.increment, Registers.decrement,
          Registers.set, Registers.get]
        omega
      have hheadThree :
          boundaryOffset tempSpec.registers (Fin.succ (2 : Fin 4)) =
          firstGapOffset clockSpec.registers 3 := by
        change boundaryOffset tempSpec.registers 3 =
          firstGapOffset clockSpec.registers 3
        simp [clockSpec, tempSpec, rightSpec, updateSpec, clockRegs, tempRegs,
          final, firstGapOffset, boundaryOffset, CounterLayout.boundaryPos,
          RegisterLayout.values, Registers.increment, Registers.decrement,
          Registers.set, Registers.get]
        omega
      have hfourBack := decrementTape_backedBy hclockBack .clock (by
        simp [clockSpec, tempSpec, rightSpec, updateSpec, clockRegs, final,
          Registers.get, Registers.increment, Registers.decrement,
          Registers.set])
      have hfinalTape : decrementTape clockSpec .clock Uclock =
          decrementTape spec .left T := by
        calc
          _ = install final spec.growth spec.returnTag outer := by
            simpa [clockSpec, tempSpec, rightSpec, updateSpec, clockRegs,
              final, decrementSpec, Registers.increment, Registers.decrement,
              Registers.set, Registers.get] using hfourBack.installed
          _ = _ := by
            simpa [final, decrementSpec, updateSpec] using hdesired.installed.symm
      have hclockDecrement : clockSpec.registers.decrement .clock = final := by
        simp [clockSpec, tempSpec, rightSpec, updateSpec, clockRegs, final,
          Registers.decrement, Registers.increment, Registers.set,
          Registers.get]
      have hresultTape :
          install final clockSpec.growth clockSpec.returnTag
              (writeLogical clockSpec.growth Uclock
                (boundaryOffset clockSpec.registers (Fin.succ (3 : Fin 4)))
                blankSymbol) =
            decrementTape clockSpec .clock Uclock := by
        rw [decrementTape, clearOldLayoutEnd, hclockDecrement]
        rw [show boundaryOffset clockSpec.registers
          (Fin.succ (3 : Fin 4)) = layoutEnd clockSpec.registers by rfl]
      rw [hresultTape, hfinalTape] at hfour
      have hheadOne' : boundaryOffset spec.registers (1 : Fin 5) =
          firstGapOffset rightRegs 1 := by
        simpa [rightSpec, updateSpec] using hheadOne
      have hheadTwo' : boundaryOffset rightRegs (2 : Fin 5) =
          firstGapOffset tempRegs 2 := by
        simpa [tempSpec, rightSpec, updateSpec] using hheadTwo
      have hheadThree' : boundaryOffset tempRegs (3 : Fin 5) =
          firstGapOffset clockRegs 3 := by
        simpa [clockSpec, tempSpec, rightSpec, updateSpec] using hheadThree
      rw [hheadOne] at hone
      rw [hheadTwo] at htwo
      rw [hheadThree] at hthree
      simp only [rightSpec, tempSpec, clockSpec, updateSpec] at hone htwo hthree hfour
      have hUright :
          install rightRegs spec.growth spec.returnTag
              (writeLogical spec.growth T (firstGapOffset rightRegs 1)
                blankSymbol) = Uright := by
        dsimp only [Uright]
        rw [← hheadOne']
      have hUtemp :
          install tempRegs spec.growth spec.returnTag
              (writeLogical spec.growth Uright (firstGapOffset tempRegs 2)
                blankSymbol) = Utemp := by
        dsimp only [Utemp, rightSpec, updateSpec]
        rw [← hheadTwo']
      have hUclock :
          install clockRegs spec.growth spec.returnTag
              (writeLogical spec.growth Utemp (firstGapOffset clockRegs 3)
                blankSymbol) = Uclock := by
        dsimp only [Uclock, tempSpec, rightSpec, updateSpec]
        rw [← hheadThree']
      rw [hUright] at hone
      rw [hUtemp] at htwo
      rw [hUclock] at hthree
      rw [show boundaryOffset clockRegs (Fin.succ (3 : Fin 4)) =
        layoutEnd clockRegs by rfl, hclockEnd] at hfour
      simp only [searchRef, CounterControlPlan.resolve] at hone htwo hthree
      apply FullTM0.CompletesOr.and_right ?_ hdesired
      simpa only [MarkerSchedule.decrementStartBoundary, hheadOne'] using
        FullTM0.CompletesOr.trans runner.pullback hone
          (FullTM0.CompletesOr.trans runner.pullback htwo
            (FullTM0.CompletesOr.trans runner.pullback hthree hfour))



/-- Complete positive-decrement suffix schedule, including exact preservation
of the suspended outer backing. -/
theorem machine_reaches_decrementSchedule_solved
    (base : Nat) (c : Nat.Partrec.Code) (source : Nat)
    (register : Register)
    {spec : Spec numTags} {T outer : FullTM0.Tape (Symbol numTags)}
    (hback : BackedBy spec T outer)
    (hpositive : 0 < spec.registers.get register)
    (hshort : ShortSearches base c spec.outerDistance)
    (hcommands : ∀ raw,
      raw ∈ decrementShiftCommands spec.growth source register →
        raw ∈ rawCommands) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨spec.growth, source, secondarySearchBase⟩,
          atLogical spec.growth T
            (boundaryOffset spec.registers
              (MarkerSchedule.decrementStartBoundary register))⟩
        ⟨resolve base c (directRef spec.growth source finishDirectSlot),
          atLogical spec.growth (decrementTape spec register T)
            (layoutEnd spec.registers)⟩ ∧
      BackedBy (decrementSpec spec register hpositive)
        (decrementTape spec register T) outer := by
  let runner : DecrementScheduleRunner base c (ShortSearches base c)
      (fun _ => False) := {
    pullback := by
      intro _ _ _ failure
      exact failure.elim
    first := by
      intro limit hshort counterState searchSlot success hlimit spec T h next i
        hpositive hnextCore hlower hupper hsource hdestination hshrink hmove
        hraw
      exact Or.inl (machine_reaches_decrementFirst_solved base c limit hshort
        counterState searchSlot success hlimit h next i hpositive hnextCore
        hlower hupper hsource hdestination hshrink hmove hraw)
    following := by
      intro limit hshort counterState searchSlot success spec T h next i
        hpositive hdistance hnextCore hlower hupper hsource hdestination
        hshrink hmove hraw
      exact Or.inl (machine_reaches_decrementFollowing_solved base c limit
        hshort counterState searchSlot success h next i hpositive hdistance
        hnextCore hlower hupper hsource hdestination hshrink hmove hraw) }
  rcases machine_reaches_decrementSchedule_with base c (ShortSearches base c)
      (fun _ => False) runner source register hback hpositive hshort hcommands
      with result | failure
  · exact result
  · exact failure.elim

theorem machine_reaches_decrementPositiveFinish
    (base : Nat) (c : Nat.Partrec.Code) (source ifZero ifPositive : Nat)
    (register : Register)
    (hrule : (source, .decrement register ifZero ifPositive) ∈
      GlobalSourceProgram.program)
    {spec : Spec numTags} (T : FullTM0.Tape (Symbol numTags))
    (hpositive : 0 < spec.registers.get register) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨resolve base c (directRef spec.growth source finishDirectSlot),
          atLogical spec.growth (decrementTape spec register T)
            (layoutEnd spec.registers)⟩
        ⟨logicalState base c spec.growth ifPositive,
          atLogical spec.growth (decrementTape spec register T)
            (layoutEnd (spec.registers.decrement register))⟩ := by
  let raw : RawDirectRule :=
    ⟨spec.growth, directRef spec.growth source finishDirectSlot, .blank,
      .logical spec.growth ifPositive, .left⟩
  have hraw : raw ∈ rawDirectRules := by
    apply directRule_mem_rawDirectRules_of_rule spec.growth hrule
    change raw ∈ validationRules spec.growth source ++
      decrementRules spec.growth source register ifZero ifPositive
    apply List.mem_append_right
    simp [raw, decrementRules]
  have hmatch : raw.read.Matches
      (atLogical spec.growth (decrementTape spec register T)
        (layoutEnd spec.registers)).read := by
    change (atLogical spec.growth (decrementTape spec register T)
      (layoutEnd spec.registers)).read = blankSymbol
    rw [atLogical_read]
    exact decrementTape_old_layoutEnd_blank spec register T hpositive
  have hrun := CounterControlDirectSemantics.reaches_directRule base c raw
    hraw (atLogical spec.growth (decrementTape spec register T)
      (layoutEnd spec.registers)) hmatch
  have hend := layoutEnd_decrement_add_one spec.registers register hpositive
  have hmove : (atLogical spec.growth (decrementTape spec register T)
      (layoutEnd spec.registers)).move (orient spec.growth .left) =
      atLogical spec.growth (decrementTape spec register T)
        (layoutEnd (spec.registers.decrement register)) := by
    rw [← hend, orient_eq_orientDirection, atLogical_move_left]
  rw [hmove] at hrun
  change FullTM0.Reaches (CounterControlNestingBridge.machine base c)
    ⟨resolve base c (directRef spec.growth source finishDirectSlot),
      atLogical spec.growth (decrementTape spec register T)
        (layoutEnd spec.registers)⟩
    ⟨logicalState base c spec.growth ifPositive,
      atLogical spec.growth (decrementTape spec register T)
        (layoutEnd (spec.registers.decrement register))⟩ at hrun
  exact hrun

/-- Exact successful semantics of the positive branch of one compiled
conditional decrement, with the updated frame still backed by the same
suspended outer tape. -/
theorem machine_reaches_decrementPositiveInstruction_solved
    (base : Nat) (c : Nat.Partrec.Code) (source ifZero ifPositive : Nat)
    (register : Register)
    (hrule : (source, .decrement register ifZero ifPositive) ∈
      GlobalSourceProgram.program)
    {spec : Spec numTags}
    {T outer : FullTM0.Tape (Symbol numTags)}
    (hback : BackedBy spec T outer)
    (hpositive : 0 < spec.registers.get register)
    (hshort : ShortSearches base c spec.outerDistance) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨logicalState base c spec.growth source,
          atLogical spec.growth T (layoutEnd spec.registers)⟩
        ⟨logicalState base c spec.growth ifPositive,
          atLogical spec.growth (decrementTape spec register T)
            (layoutEnd (spec.registers.decrement register))⟩ ∧
      BackedBy (decrementSpec spec register hpositive)
        (decrementTape spec register T) outer := by
  have h := hback.represents
  have hvalidation := machine_reaches_validation_solved base c spec.growth
    source (.decrement register ifZero ifPositive) hrule h rfl hshort
  have hroute := machine_reaches_decrementToTest_solved base c source ifZero
    ifPositive register hrule h hshort
  have htest := machine_reaches_decrementTest base c source ifZero ifPositive
    register hrule T (by
      rw [atLogical_read]
      exact h.boundary _)
  have hhandoff := machine_reaches_decrementPositiveHandoff base c source
    ifZero ifPositive register hrule h hpositive
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
  constructor
  · exact hvalidation.trans
      (hroute.trans
        (htest.trans
          (hhandoff.trans (hschedule.1.trans hfinish))))
  · exact hschedule.2

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
        let nextSpec := incrementSpec spec register hroom
        have hnextRep : Represents nextSpec
            (incrementTape spec register T) :=
          incrementTape_represents hback.represents register hroom
        have hrecovery := machine_reaches_incrementRecovery_solved base c
          source target register hrule hnextRep (by
            simpa [nextSpec, incrementSpec, updateSpec] using hshort)
        have hrecovery' : FullTM0.Reaches
            (CounterControlNestingBridge.machine base c)
            ⟨resolve base c
                (match AnchoredCounterGeometry.routeFromIncrement register with
                | [] => .logical spec.growth target
                | _ :: _ =>
                    directRef spec.growth source (bodyDirectBase + 1)),
              atLogical spec.growth (incrementTape spec register T)
                (boundaryOffset (spec.registers.increment register)
                  (MarkerSchedule.decrementStartBoundary register))⟩
            ⟨logicalState base c spec.growth target,
              atLogical spec.growth (incrementTape spec register T)
                (layoutEnd (spec.registers.increment register))⟩ := by
          simpa [nextSpec, incrementSpec, updateSpec] using hrecovery
        refine .logical hroom (incrementTape spec register T) first hfirst
          (hvalidation.trans
            (hschedule.trans (hhandoff.trans hrecovery'))) ?_
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
