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
# Search, shift, route, and validation semantics

This module develops the shared bounded-search runners, primitive marker
shifts, preserving routes, and validation prefix used by both instruction
families.  It works directly on represented tagged frames.
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

theorem searches_reach_solved_at
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

abbrev validationCommand_mem :=
  validationCommand_mem_commandsForRule
abbrev validationRule_mem :=
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

end

end CounterControlInstructionSemantics
end Hooper
end Kari
end LeanWang
