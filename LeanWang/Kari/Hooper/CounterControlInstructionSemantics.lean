/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlRouteSemantics
import LeanWang.Kari.Hooper.CounterControlScheduleSemantics
import LeanWang.Kari.Hooper.CounterControlCleanupSemantics
import LeanWang.Kari.Hooper.CounterControlSearchSystem
import LeanWang.Kari.Hooper.CounterControlFrameBacking

/-!
# Semantics of complete counter-controller instructions

This module composes validation, register-update, recovery, and collision
cleanup into instruction-sized executions of the compiled counter controller.
The route layer below works directly on a represented tagged frame.  Unlike
`CounterControlRouteSemantics.route_reaches_or_nests`, it does not require the
entire ambient tape to be the embedding of an untagged marker tape; this is
essential when the return tag and suspended outer target are already present.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlInstructionSemantics

open Turing CounterMachine
open BoundedMarkerProgram FramedMarkerTape FramedCounterGeometry
open CounterControlPlan CounterControlCommandAt CounterControlBridge
open CounterControlScheduleSemantics CounterControlFrameBacking

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
  have hsolve := hshort distance hdistance
    (rawTag raw hraw) outer
  have hgap' : SearchGap
      (CounterControlSearchSystem.searchSystem base c).isBlank
      ((CounterControlSearchSystem.searchSystem base c).isMark
        (rawTag raw hraw)) outer
      ((CounterControlSearchSystem.searchSystem base c).direction
        (rawTag raw hraw)) distance := by
    simpa [CounterControlSearchSystem.searchSystem,
      CounterControlSearchSystem.command, compileRawCommand] using hgap
  have hrun := hsolve hgap'
  change FullTM0.Reaches (CounterControlNestingBridge.machine base c)
    ⟨CounterControlSearchSystem.commandOffset base c (rawTag raw hraw),
      outer⟩
    ⟨foundState (CanonicalInitializer.radius c)
        (CounterControlSearchSystem.commandOffset base c (rawTag raw hraw)),
      outer.moveN
        (CounterControlSearchSystem.command base c
          (rawTag raw hraw)).searchDirection distance⟩ at hrun
  have hoffset : CounterControlSearchSystem.commandOffset base c
      (rawTag raw hraw) = searchState base c raw.address := by
    unfold CounterControlSearchSystem.commandOffset
    rw [rawCommands_get_rawTag]
  have hcommand : CounterControlSearchSystem.command base c
      (rawTag raw hraw) = compileRawCommand base c raw hraw := rfl
  rw [hoffset, hcommand] at hrun
  exact hrun

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
  let raw : RawCommand :=
    .boundaryNavigation address expected direction success .preserve
  have hspec := compileRawCommand_spec base c raw hraw
  have hcompiledGap : SearchGap (fun symbol => symbol = blankSymbol)
      (compileRawCommand base c raw hraw).target.Matches outer
      (compileRawCommand base c raw hraw).searchDirection distance := by
    rw [hspec]
    simpa [raw, compileRawAtTag, Command.target,
      Command.searchDirection, compileNavigationAction] using hgap
  have hfound := rawSearch_reaches_found base c limit hshort raw hraw outer
    distance hdistance hcompiledGap
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
  have hfound := rawSearch_reaches_found base c limit hshort raw hraw
    (atLogical growth T (source + distance)) distance hdistance hcompiledGap
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
  have hfound := rawSearch_reaches_found base c limit hshort raw hraw
    (atLogical growth T origin) distance hdistance hcompiledGap
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

/-- One internal canonical increment shift, discharged by solved shorter
searches instead of the local-radius bound. -/
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
  have hrun := machine_reaches_incrementShift_solved base c limit hshort
    spec.growth counterState searchSlot source i.castSucc success collision
    hraw T distance hdistance (by simpa [hstart] using hgap) hblank
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
      (RegisterLayout.values spec.registers) (show (i : Nat) + 1 ≤ 4 by omega)
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

/-- Generic canonical inward suffix shift using a solved shorter search. -/
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
  have hrun := machine_reaches_decrementShift_solved base c limit hshort
    spec.growth counterState searchSlot origin destination distance label
    success collision hraw T hposition hdistance hgap
    (by simpa [source, destination] using hblank)
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

/-- The outward boundary-`4` shift with arbitrary generated success and
collision continuations, normalized to the canonical clock-increment tape. -/
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
  have hrun := machine_reaches_incrementShift_solved base c limit hshort
    spec.growth counterState searchSlot (layoutEnd spec.registers) 4
    success collision hraw T 0 hlimit hgap hblank
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

/-! ## Routes on a native tagged frame -/

/-- Exact execution geometry of one marker-route leg on a fixed tagged tape.
The two cases retain natural logical coordinates, avoiding any assertion
about cells outside the finite represented frame. -/
def LegExecutesAt {numTags : Nat} (growth : Turing.Dir)
    (T : FullTM0.Tape (Symbol numTags))
    (leg : MarkerValidation.Leg) (source finish : Nat) : Prop :=
  match leg.direction with
  | .right =>
      ∃ distance,
        SearchGap (fun symbol => symbol = blankSymbol)
          (Target.boundary leg.target).Matches
          (atLogical growth T (source + 1))
          (OrientedMarkerTape.orientDirection growth .right) distance ∧
        finish = source + distance + 1
  | .left =>
      ∃ distance,
        source = finish + distance + 1 ∧
        SearchGap (fun symbol => symbol = blankSymbol)
          (Target.boundary leg.target).Matches
          (atLogical growth T (finish + distance))
          (OrientedMarkerTape.orientDirection growth .left) distance

/-- Sequential route geometry on one unchanged tagged tape. -/
inductive RouteExecutesAt {numTags : Nat} (growth : Turing.Dir)
    (T : FullTM0.Tape (Symbol numTags)) :
    List MarkerValidation.Leg → Nat → Nat → Prop
  | nil (position) : RouteExecutesAt growth T [] position position
  | cons (leg legs source middle finish)
      (first : LegExecutesAt growth T leg source middle)
      (rest : RouteExecutesAt growth T legs middle finish) :
      RouteExecutesAt growth T (leg :: legs) source finish

/-- A native tagged route whose every boundary position lies strictly before
the active frame's suspended outer target. -/
inductive RouteExecutesWithin {numTags : Nat} (growth : Turing.Dir)
    (T : FullTM0.Tape (Symbol numTags)) (limit : Nat) :
    List MarkerValidation.Leg → Nat → Nat → Prop
  | nil (position) (hposition : position < limit) :
      RouteExecutesWithin growth T limit [] position position
  | cons (leg legs source middle finish)
      (hsource : source < limit)
      (first : LegExecutesAt growth T leg source middle)
      (rest : RouteExecutesWithin growth T limit legs middle finish) :
      RouteExecutesWithin growth T limit (leg :: legs) source finish

namespace RouteExecutesWithin

theorem start_lt {growth : Turing.Dir}
    {T : FullTM0.Tape (Symbol numTags)} {limit : Nat}
    {legs : List MarkerValidation.Leg} {source finish : Nat}
    (h : RouteExecutesWithin growth T limit legs source finish) :
    source < limit := by
  cases h with
  | nil _ hposition => exact hposition
  | cons _ _ _ _ _ hsource _ _ => exact hsource

theorem toExecutesAt {growth : Turing.Dir}
    {T : FullTM0.Tape (Symbol numTags)} {limit : Nat}
    {legs : List MarkerValidation.Leg} {source finish : Nat}
    (h : RouteExecutesWithin growth T limit legs source finish) :
    RouteExecutesAt growth T legs source finish := by
  induction h with
  | nil position _ => exact RouteExecutesAt.nil position
  | cons leg legs source middle finish _ first _ ih =>
      exact RouteExecutesAt.cons leg legs source middle finish first ih

end RouteExecutesWithin

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

/-- Once the first direct departure has entered a bounded search, an exact
native tagged route reaches its advertised continuation or installs the first
far nested frame. -/
private theorem searches_reach_or_nests_at
    (base : Nat) (c : Nat.Partrec.Code) (growth : Turing.Dir)
    (counterState searchSlot directSlot : Nat) (after : ControlRef)
    (first : MarkerValidation.Leg) (rest : List MarkerValidation.Leg)
    (T : FullTM0.Tape (Symbol numTags)) (source finish : Nat)
    (hexec : RouteExecutesAt growth T (first :: rest) source finish)
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
          (atLogical growth T source).move (orient growth first.direction)⟩
        ⟨resolve base c after, atLogical growth T finish⟩ ∨
      NestsFrom base c
        ⟨searchState base c ⟨growth, counterState, searchSlot⟩,
          (atLogical growth T source).move
            (orient growth first.direction)⟩ := by
  induction rest generalizing first source finish searchSlot directSlot with
  | nil =>
      cases hexec with
      | cons _ _ _ middle _ hfirst hrest =>
        cases hrest
        rcases legExecutesAt_depart hfirst with
          ⟨distance, hgap, hfound⟩
        let raw : RawCommand :=
          .boundaryNavigation ⟨growth, counterState, searchSlot⟩
            first.target first.direction after .preserve
        have hroute : raw ∈ routeCommandsAux growth counterState
            searchSlot directSlot after [first] := by
          simp [raw, routeCommandsAux]
        have hraw : raw ∈ rawCommands := hcommands raw hroute
        have hrun :=
          CounterControlNavigationSemantics.machine_reaches_boundary_preserve_or_nests
            base c ⟨growth, counterState, searchSlot⟩ first.target
            first.direction after hraw
            ((atLogical growth T source).move
              (orient growth first.direction)) distance hgap
        rcases hrun with hnear | hfar
        · left
          rw [hfound] at hnear
          exact hnear
        · right
          rcases hfar with ⟨hfar, hreach, hframe⟩
          exact ⟨raw, hraw,
            (atLogical growth T source).move
              (orient growth first.direction),
            distance, hfar, hreach, hframe⟩
  | cons next tail ih =>
      cases hexec with
      | cons _ _ _ middle _ hfirst hrest =>
        rcases legExecutesAt_depart hfirst with
          ⟨distance, hgap, hfound⟩
        let handoff : ControlRef :=
          directRef growth counterState directSlot
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
        have hrun :=
          CounterControlNavigationSemantics.machine_reaches_boundary_preserve_or_nests
            base c ⟨growth, counterState, searchSlot⟩ first.target
            first.direction handoff hraw
            ((atLogical growth T source).move
              (orient growth first.direction)) distance hgap
        rcases hrun with hnear | hfar
        · have hnear' : FullTM0.Reaches
              (CounterControlNestingBridge.machine base c)
              ⟨searchState base c ⟨growth, counterState, searchSlot⟩,
                (atLogical growth T source).move
                  (orient growth first.direction)⟩
              ⟨resolve base c handoff, atLogical growth T middle⟩ := by
            rw [hfound] at hnear
            exact hnear
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
                  (searchSlot + 1) (directSlot + 1) after
                  (next :: tail) →
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
            simp only [routeContinuationRules,
              routeContinuationRulesFrom, List.mem_cons]
            exact Or.inr hrule
          have htail := ih
            (first := next) (source := middle) (finish := finish)
            (searchSlot := searchSlot + 1)
            (directSlot := directSlot + 1) hrest hcommandsTail
            hcontinuationsTail
          have hprefix := hnear'.trans hdirect
          rcases htail with hsuccess | hnested
          · exact Or.inl (hprefix.trans hsuccess)
          · exact Or.inr (nestsFrom_of_reaches hprefix hnested)
        · right
          rcases hfar with ⟨hfar, hreach, hframe⟩
          exact ⟨raw, hraw,
            (atLogical growth T source).move
              (orient growth first.direction),
            distance, hfar, hreach, hframe⟩

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
          directSlot (first :: rest) →
        rule ∈ rawDirectRules := by
    intro rule hrule
    apply hrules rule
    exact List.mem_append_right _ hrule
  have hsearches := searches_reach_or_nests_at base c growth counterState
    searchSlot directSlot after first rest T sourcePosition finishPosition
    hexec hcommands hcontinuations
  rcases hsearches with hsuccess | hnested
  · exact Or.inl (hentryReach.trans hsuccess)
  · exact Or.inr (nestsFrom_of_reaches hentryReach hnested)

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
          after (first :: rest) →
        raw ∈ rawCommands)
    (hcontinuations : ∀ rule,
      rule ∈ routeContinuationRules growth counterState searchSlot
          directSlot (first :: rest) →
        rule ∈ rawDirectRules) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      ⟨searchState base c ⟨growth, counterState, searchSlot⟩,
        (atLogical growth T source).move (orient growth first.direction)⟩
      ⟨resolve base c after, atLogical growth T finish⟩ := by
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
          have hrun := machine_reaches_boundary_preserve_solved base c limit
            hshort ⟨growth, counterState, searchSlot⟩ first.target
            first.direction after hraw
            ((atLogical growth T source).move
              (orient growth first.direction)) distance hdistance hgap
          rw [hfound] at hrun
          exact hrun
  | cons next tail ih =>
      cases hexec with
      | cons _ _ _ middle _ hsource hfirst hrest =>
        have hmiddle := RouteExecutesWithin.start_lt hrest
        rcases legExecutesAt_depart_below hfirst hsource hmiddle with
          ⟨distance, hdistance, hgap, hfound⟩
        let handoff : ControlRef :=
          directRef growth counterState directSlot
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
        have hsearch := machine_reaches_boundary_preserve_solved base c limit
          hshort ⟨growth, counterState, searchSlot⟩ first.target
          first.direction handoff hraw
          ((atLogical growth T source).move
            (orient growth first.direction)) distance hdistance hgap
        have hsearch' : FullTM0.Reaches
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
        exact hsearch'.trans (hdirect.trans htail)

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
          directSlot (first :: rest) →
        rule ∈ rawDirectRules := by
    intro rule hrule
    apply hrules rule
    exact List.mem_append_right _ hrule
  exact hentryReach.trans
    (searches_reach_solved_at base c limit hshort growth counterState
      searchSlot directSlot after first rest T sourcePosition finishPosition
      hexec hcommands hcontinuations)

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
      (boundaryOffset spec.registers i.castSucc) := by
  rw [LegExecutesAt]
  refine ⟨RegisterLayout.values spec.registers i, ?_, ?_⟩
  · simp only [boundaryOffset, Fin.val_succ, Fin.val_castSucc,
      CounterLayout.boundaryPos_succ]
    omega
  · change SearchGap (fun symbol => symbol = blankSymbol)
      (fun symbol => symbol = boundarySymbol i.castSucc)
      (atLogical spec.growth T
        (boundaryOffset spec.registers i.castSucc +
          RegisterLayout.values spec.registers i))
      (OrientedMarkerTape.orientDirection spec.growth .left)
      (RegisterLayout.values spec.registers i)
    simpa only [boundaryOffset, lastGapOffset, Fin.val_castSucc,
      CounterLayout.boundaryPos_succ, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using h.searchGap_adjacent_left i

theorem rightLeg_executesAt {spec : Spec numTags}
    {T : FullTM0.Tape (Symbol numTags)} (h : Represents spec T)
    (i : Fin 4) :
    LegExecutesAt spec.growth T ⟨i.succ, .right⟩
      (boundaryOffset spec.registers i.castSucc)
      (boundaryOffset spec.registers i.succ) := by
  rw [LegExecutesAt]
  refine ⟨RegisterLayout.values spec.registers i, ?_, ?_⟩
  · change SearchGap (fun symbol => symbol = blankSymbol)
      (fun symbol => symbol = boundarySymbol i.succ)
      (atLogical spec.growth T
        (boundaryOffset spec.registers i.castSucc + 1))
      (OrientedMarkerTape.orientDirection spec.growth .right)
      (RegisterLayout.values spec.registers i)
    simpa only [boundaryOffset, firstGapOffset, Fin.val_castSucc,
      Nat.add_assoc, one_add_one_eq_two] using
        h.searchGap_adjacent_right i
  · simp only [boundaryOffset, Fin.val_succ, Fin.val_castSucc,
      CounterLayout.boundaryPos_succ]
    omega

/-- The complete validation sweep is executable without changing the
ambient tagged tape. -/
theorem validation_executesAt {spec : Spec numTags}
    {T : FullTM0.Tape (Symbol numTags)} (h : Represents spec T) :
    RouteExecutesAt spec.growth T MarkerValidation.sweep
      (layoutEnd spec.registers) (layoutEnd spec.registers) := by
  change RouteExecutesAt spec.growth T _
    (boundaryOffset spec.registers 4) (boundaryOffset spec.registers 4)
  apply RouteExecutesAt.cons _ _ _
    (boundaryOffset spec.registers 3) _ (leftLeg_executesAt h 3)
  apply RouteExecutesAt.cons _ _ _
    (boundaryOffset spec.registers 2) _ (leftLeg_executesAt h 2)
  apply RouteExecutesAt.cons _ _ _
    (boundaryOffset spec.registers 1) _ (leftLeg_executesAt h 1)
  apply RouteExecutesAt.cons _ _ _
    (boundaryOffset spec.registers 0) _ (leftLeg_executesAt h 0)
  apply RouteExecutesAt.cons _ _ _
    (boundaryOffset spec.registers 1) _ (rightLeg_executesAt h 0)
  apply RouteExecutesAt.cons _ _ _
    (boundaryOffset spec.registers 2) _ (rightLeg_executesAt h 1)
  apply RouteExecutesAt.cons _ _ _
    (boundaryOffset spec.registers 3) _ (rightLeg_executesAt h 2)
  apply RouteExecutesAt.cons _ _ _
    (boundaryOffset spec.registers 4) _ (rightLeg_executesAt h 3)
  exact RouteExecutesAt.nil _

theorem routeToDecrementStart_executesAt {spec : Spec numTags}
    {T : FullTM0.Tape (Symbol numTags)} (h : Represents spec T)
    (register : Register) :
    RouteExecutesAt spec.growth T
      (AnchoredCounterGeometry.routeToDecrementStart register)
      (layoutEnd spec.registers)
      (boundaryOffset spec.registers
        (MarkerSchedule.decrementStartBoundary register)) := by
  change RouteExecutesAt spec.growth T _
    (boundaryOffset spec.registers 4) _
  cases register with
  | left =>
      apply RouteExecutesAt.cons _ _ _
        (boundaryOffset spec.registers 3) _ (leftLeg_executesAt h 3)
      apply RouteExecutesAt.cons _ _ _
        (boundaryOffset spec.registers 2) _ (leftLeg_executesAt h 2)
      apply RouteExecutesAt.cons _ _ _
        (boundaryOffset spec.registers 1) _ (leftLeg_executesAt h 1)
      exact RouteExecutesAt.nil _
  | right =>
      apply RouteExecutesAt.cons _ _ _
        (boundaryOffset spec.registers 3) _ (leftLeg_executesAt h 3)
      apply RouteExecutesAt.cons _ _ _
        (boundaryOffset spec.registers 2) _ (leftLeg_executesAt h 2)
      exact RouteExecutesAt.nil _
  | temp =>
      apply RouteExecutesAt.cons _ _ _
        (boundaryOffset spec.registers 3) _ (leftLeg_executesAt h 3)
      exact RouteExecutesAt.nil _
  | clock => exact RouteExecutesAt.nil _

theorem routeFromIncrement_executesAt {spec : Spec numTags}
    {T : FullTM0.Tape (Symbol numTags)} (h : Represents spec T)
    (register : Register) :
    RouteExecutesAt spec.growth T
      (AnchoredCounterGeometry.routeFromIncrement register)
      (boundaryOffset spec.registers
        (MarkerSchedule.decrementStartBoundary register))
      (layoutEnd spec.registers) := by
  change RouteExecutesAt spec.growth T _ _
    (boundaryOffset spec.registers 4)
  cases register with
  | left =>
      apply RouteExecutesAt.cons _ _ _
        (boundaryOffset spec.registers 2) _ (rightLeg_executesAt h 1)
      apply RouteExecutesAt.cons _ _ _
        (boundaryOffset spec.registers 3) _ (rightLeg_executesAt h 2)
      apply RouteExecutesAt.cons _ _ _
        (boundaryOffset spec.registers 4) _ (rightLeg_executesAt h 3)
      exact RouteExecutesAt.nil _
  | right =>
      apply RouteExecutesAt.cons _ _ _
        (boundaryOffset spec.registers 3) _ (rightLeg_executesAt h 2)
      apply RouteExecutesAt.cons _ _ _
        (boundaryOffset spec.registers 4) _ (rightLeg_executesAt h 3)
      exact RouteExecutesAt.nil _
  | temp =>
      apply RouteExecutesAt.cons _ _ _
        (boundaryOffset spec.registers 4) _ (rightLeg_executesAt h 3)
      exact RouteExecutesAt.nil _
  | clock => exact RouteExecutesAt.nil _

theorem routeFromZero_executesAt {spec : Spec numTags}
    {T : FullTM0.Tape (Symbol numTags)} (h : Represents spec T)
    (register : Register) :
    RouteExecutesAt spec.growth T
      (AnchoredCounterGeometry.routeFromZero register)
      (boundaryOffset spec.registers
        (AnchoredCounterGeometry.registerGap register).castSucc)
      (layoutEnd spec.registers) := by
  change RouteExecutesAt spec.growth T _ _
    (boundaryOffset spec.registers 4)
  cases register with
  | left =>
      apply RouteExecutesAt.cons _ _ _
        (boundaryOffset spec.registers 1) _ (rightLeg_executesAt h 0)
      apply RouteExecutesAt.cons _ _ _
        (boundaryOffset spec.registers 2) _ (rightLeg_executesAt h 1)
      apply RouteExecutesAt.cons _ _ _
        (boundaryOffset spec.registers 3) _ (rightLeg_executesAt h 2)
      apply RouteExecutesAt.cons _ _ _
        (boundaryOffset spec.registers 4) _ (rightLeg_executesAt h 3)
      exact RouteExecutesAt.nil _
  | right =>
      apply RouteExecutesAt.cons _ _ _
        (boundaryOffset spec.registers 2) _ (rightLeg_executesAt h 1)
      apply RouteExecutesAt.cons _ _ _
        (boundaryOffset spec.registers 3) _ (rightLeg_executesAt h 2)
      apply RouteExecutesAt.cons _ _ _
        (boundaryOffset spec.registers 4) _ (rightLeg_executesAt h 3)
      exact RouteExecutesAt.nil _
  | temp =>
      apply RouteExecutesAt.cons _ _ _
        (boundaryOffset spec.registers 3) _ (rightLeg_executesAt h 2)
      apply RouteExecutesAt.cons _ _ _
        (boundaryOffset spec.registers 4) _ (rightLeg_executesAt h 3)
      exact RouteExecutesAt.nil _
  | clock =>
      apply RouteExecutesAt.cons _ _ _
        (boundaryOffset spec.registers 4) _ (rightLeg_executesAt h 3)
      exact RouteExecutesAt.nil _

theorem boundaryOffset_lt_outerDistance {spec : Spec numTags}
    {T : FullTM0.Tape (Symbol numTags)} (_h : Represents spec T)
    (label : Fin 5) :
    boundaryOffset spec.registers label < spec.outerDistance := by
  apply lt_of_le_of_lt _ spec.core_before_target
  simp only [boundaryOffset, layoutEnd]
  apply Nat.add_le_add_right
  exact CounterLayout.boundaryPos_mono
    (RegisterLayout.values spec.registers) (by omega)

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
      (layoutEnd spec.registers) := by
  change RouteExecutesWithin spec.growth T spec.outerDistance _
    (boundaryOffset spec.registers 4) (boundaryOffset spec.registers 4)
  apply RouteExecutesWithin.cons _ _ _
    (boundaryOffset spec.registers 3) _
    (boundaryOffset_lt_outerDistance h 4) (leftLeg_executesAt h 3)
  apply RouteExecutesWithin.cons _ _ _
    (boundaryOffset spec.registers 2) _
    (boundaryOffset_lt_outerDistance h 3) (leftLeg_executesAt h 2)
  apply RouteExecutesWithin.cons _ _ _
    (boundaryOffset spec.registers 1) _
    (boundaryOffset_lt_outerDistance h 2) (leftLeg_executesAt h 1)
  apply RouteExecutesWithin.cons _ _ _
    (boundaryOffset spec.registers 0) _
    (boundaryOffset_lt_outerDistance h 1) (leftLeg_executesAt h 0)
  apply RouteExecutesWithin.cons _ _ _
    (boundaryOffset spec.registers 1) _
    (boundaryOffset_lt_outerDistance h 0) (rightLeg_executesAt h 0)
  apply RouteExecutesWithin.cons _ _ _
    (boundaryOffset spec.registers 2) _
    (boundaryOffset_lt_outerDistance h 1) (rightLeg_executesAt h 1)
  apply RouteExecutesWithin.cons _ _ _
    (boundaryOffset spec.registers 3) _
    (boundaryOffset_lt_outerDistance h 2) (rightLeg_executesAt h 2)
  apply RouteExecutesWithin.cons _ _ _
    (boundaryOffset spec.registers 4) _
    (boundaryOffset_lt_outerDistance h 3) (rightLeg_executesAt h 3)
  exact RouteExecutesWithin.nil _ (boundaryOffset_lt_outerDistance h 4)

theorem routeToDecrementStart_executesWithin {spec : Spec numTags}
    {T : FullTM0.Tape (Symbol numTags)} (h : Represents spec T)
    (register : Register) :
    RouteExecutesWithin spec.growth T spec.outerDistance
      (AnchoredCounterGeometry.routeToDecrementStart register)
      (layoutEnd spec.registers)
      (boundaryOffset spec.registers
        (MarkerSchedule.decrementStartBoundary register)) := by
  change RouteExecutesWithin spec.growth T spec.outerDistance _
    (boundaryOffset spec.registers 4) _
  cases register with
  | left =>
      apply RouteExecutesWithin.cons _ _ _
        (boundaryOffset spec.registers 3) _
        (boundaryOffset_lt_outerDistance h 4) (leftLeg_executesAt h 3)
      apply RouteExecutesWithin.cons _ _ _
        (boundaryOffset spec.registers 2) _
        (boundaryOffset_lt_outerDistance h 3) (leftLeg_executesAt h 2)
      apply RouteExecutesWithin.cons _ _ _
        (boundaryOffset spec.registers 1) _
        (boundaryOffset_lt_outerDistance h 2) (leftLeg_executesAt h 1)
      exact RouteExecutesWithin.nil _ (boundaryOffset_lt_outerDistance h 1)
  | right =>
      apply RouteExecutesWithin.cons _ _ _
        (boundaryOffset spec.registers 3) _
        (boundaryOffset_lt_outerDistance h 4) (leftLeg_executesAt h 3)
      apply RouteExecutesWithin.cons _ _ _
        (boundaryOffset spec.registers 2) _
        (boundaryOffset_lt_outerDistance h 3) (leftLeg_executesAt h 2)
      exact RouteExecutesWithin.nil _ (boundaryOffset_lt_outerDistance h 2)
  | temp =>
      apply RouteExecutesWithin.cons _ _ _
        (boundaryOffset spec.registers 3) _
        (boundaryOffset_lt_outerDistance h 4) (leftLeg_executesAt h 3)
      exact RouteExecutesWithin.nil _ (boundaryOffset_lt_outerDistance h 3)
  | clock =>
      exact RouteExecutesWithin.nil _ (boundaryOffset_lt_outerDistance h 4)

theorem routeFromIncrement_executesWithin {spec : Spec numTags}
    {T : FullTM0.Tape (Symbol numTags)} (h : Represents spec T)
    (register : Register) :
    RouteExecutesWithin spec.growth T spec.outerDistance
      (AnchoredCounterGeometry.routeFromIncrement register)
      (boundaryOffset spec.registers
        (MarkerSchedule.decrementStartBoundary register))
      (layoutEnd spec.registers) := by
  change RouteExecutesWithin spec.growth T spec.outerDistance _ _
    (boundaryOffset spec.registers 4)
  cases register with
  | left =>
      apply RouteExecutesWithin.cons _ _ _
        (boundaryOffset spec.registers 2) _
        (boundaryOffset_lt_outerDistance h 1) (rightLeg_executesAt h 1)
      apply RouteExecutesWithin.cons _ _ _
        (boundaryOffset spec.registers 3) _
        (boundaryOffset_lt_outerDistance h 2) (rightLeg_executesAt h 2)
      apply RouteExecutesWithin.cons _ _ _
        (boundaryOffset spec.registers 4) _
        (boundaryOffset_lt_outerDistance h 3) (rightLeg_executesAt h 3)
      exact RouteExecutesWithin.nil _ (boundaryOffset_lt_outerDistance h 4)
  | right =>
      apply RouteExecutesWithin.cons _ _ _
        (boundaryOffset spec.registers 3) _
        (boundaryOffset_lt_outerDistance h 2) (rightLeg_executesAt h 2)
      apply RouteExecutesWithin.cons _ _ _
        (boundaryOffset spec.registers 4) _
        (boundaryOffset_lt_outerDistance h 3) (rightLeg_executesAt h 3)
      exact RouteExecutesWithin.nil _ (boundaryOffset_lt_outerDistance h 4)
  | temp =>
      apply RouteExecutesWithin.cons _ _ _
        (boundaryOffset spec.registers 4) _
        (boundaryOffset_lt_outerDistance h 3) (rightLeg_executesAt h 3)
      exact RouteExecutesWithin.nil _ (boundaryOffset_lt_outerDistance h 4)
  | clock =>
      exact RouteExecutesWithin.nil _ (boundaryOffset_lt_outerDistance h 4)

theorem routeFromZero_executesWithin {spec : Spec numTags}
    {T : FullTM0.Tape (Symbol numTags)} (h : Represents spec T)
    (register : Register) :
    RouteExecutesWithin spec.growth T spec.outerDistance
      (AnchoredCounterGeometry.routeFromZero register)
      (boundaryOffset spec.registers
        (AnchoredCounterGeometry.registerGap register).castSucc)
      (layoutEnd spec.registers) := by
  change RouteExecutesWithin spec.growth T spec.outerDistance _ _
    (boundaryOffset spec.registers 4)
  cases register with
  | left =>
      apply RouteExecutesWithin.cons _ _ _
        (boundaryOffset spec.registers 1) _
        (boundaryOffset_lt_outerDistance h 0) (rightLeg_executesAt h 0)
      apply RouteExecutesWithin.cons _ _ _
        (boundaryOffset spec.registers 2) _
        (boundaryOffset_lt_outerDistance h 1) (rightLeg_executesAt h 1)
      apply RouteExecutesWithin.cons _ _ _
        (boundaryOffset spec.registers 3) _
        (boundaryOffset_lt_outerDistance h 2) (rightLeg_executesAt h 2)
      apply RouteExecutesWithin.cons _ _ _
        (boundaryOffset spec.registers 4) _
        (boundaryOffset_lt_outerDistance h 3) (rightLeg_executesAt h 3)
      exact RouteExecutesWithin.nil _ (boundaryOffset_lt_outerDistance h 4)
  | right =>
      apply RouteExecutesWithin.cons _ _ _
        (boundaryOffset spec.registers 2) _
        (boundaryOffset_lt_outerDistance h 1) (rightLeg_executesAt h 1)
      apply RouteExecutesWithin.cons _ _ _
        (boundaryOffset spec.registers 3) _
        (boundaryOffset_lt_outerDistance h 2) (rightLeg_executesAt h 2)
      apply RouteExecutesWithin.cons _ _ _
        (boundaryOffset spec.registers 4) _
        (boundaryOffset_lt_outerDistance h 3) (rightLeg_executesAt h 3)
      exact RouteExecutesWithin.nil _ (boundaryOffset_lt_outerDistance h 4)
  | temp =>
      apply RouteExecutesWithin.cons _ _ _
        (boundaryOffset spec.registers 3) _
        (boundaryOffset_lt_outerDistance h 2) (rightLeg_executesAt h 2)
      apply RouteExecutesWithin.cons _ _ _
        (boundaryOffset spec.registers 4) _
        (boundaryOffset_lt_outerDistance h 3) (rightLeg_executesAt h 3)
      exact RouteExecutesWithin.nil _ (boundaryOffset_lt_outerDistance h 4)
  | clock =>
      apply RouteExecutesWithin.cons _ _ _
        (boundaryOffset spec.registers 4) _
        (boundaryOffset_lt_outerDistance h 3) (rightLeg_executesAt h 3)
      exact RouteExecutesWithin.nil _ (boundaryOffset_lt_outerDistance h 4)

/-! ## Inclusion of one source rule in the linked controller -/

theorem command_mem_rawCommands_of_rule
    (growth : Turing.Dir) {rule : CounterMachine.Rule}
    (hrule : rule ∈ GlobalSourceProgram.program) {raw : RawCommand}
    (hraw : raw ∈ commandsForRule growth rule) :
    raw ∈ rawCommands := by
  have horiented : raw ∈ rawCommandsFor growth := by
    rw [rawCommandsFor, List.mem_flatMap]
    exact ⟨rule, hrule, hraw⟩
  cases growth with
  | right => exact List.mem_append_left _ horiented
  | left => exact List.mem_append_right _ horiented

theorem directRule_mem_rawDirectRules_of_rule
    (growth : Turing.Dir) {rule : CounterMachine.Rule}
    (hrule : rule ∈ GlobalSourceProgram.program) {raw : RawDirectRule}
    (hraw : raw ∈ directRulesForRule growth rule) :
    raw ∈ rawDirectRules := by
  have horiented : raw ∈ rawDirectRulesFor growth := by
    rw [rawDirectRulesFor, List.mem_flatMap]
    exact ⟨rule, hrule, hraw⟩
  cases growth with
  | right => exact List.mem_append_left _ horiented
  | left => exact List.mem_append_right _ horiented

private theorem validationCommand_mem
    (growth : Turing.Dir) (source : Nat)
    (instruction : CounterMachine.Instruction) {raw : RawCommand}
    (hraw : raw ∈ validationCommands growth source instruction) :
    raw ∈ commandsForRule growth (source, instruction) := by
  cases instruction <;> simp [commandsForRule, hraw]

private theorem validationRule_mem
    (growth : Turing.Dir) (source : Nat)
    (instruction : CounterMachine.Instruction) {raw : RawDirectRule}
    (hraw : raw ∈ validationRules growth source) :
    raw ∈ directRulesForRule growth (source, instruction) := by
  cases instruction <;> simp [directRulesForRule, hraw]

/-! ## Validation prefix -/

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
        machine_reaches_incrementClock_solved base c spec.outerDistance
          hshort source bodySearchBase
          (directRef spec.growth source bodyDirectBase)
          (some (directRef spec.growth source testDirectSlot)) h hclockRoom
          hlimit hraw
  | temp =>
      let clockTape := incrementTape spec .clock T
      let clockSpec := incrementSpec spec .clock hclockRoom
      have hclockRep : Represents clockSpec clockTape := by
        exact incrementTape_represents h .clock hclockRoom
      have hrawFour : RawCommand.markerShift
          ⟨spec.growth, source, bodySearchBase⟩ 4 .left .right
          (searchRef spec.growth source (bodySearchBase + 1)) (some .left)
          (some (directRef spec.growth source testDirectSlot)) ∈
            rawCommands := by
        apply hcommands
        simp [incrementShiftCommands, incrementShiftCommandsAux,
          MarkerShift.incrementOrder]
      have hfour := machine_reaches_incrementClock_solved base c
        spec.outerDistance hshort source bodySearchBase
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
      have hthree := machine_reaches_incrementInternal_solved base c
        spec.outerDistance hshort source (bodySearchBase + 1)
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
      have hhead : layoutEnd spec.registers =
          lastGapOffset (spec.registers.increment .clock) 3 := by
        simp [lastGapOffset, boundaryOffset, CounterLayout.boundaryPos,
          layoutEnd, RegisterLayout.clockBoundary_eq, RegisterLayout.values,
          Registers.increment, Registers.set, Registers.get] <;> omega
      have htape : install (spec.registers.increment .temp) spec.growth
          spec.returnTag clockTape = incrementTape spec .temp T := by
        change install (spec.registers.increment .temp) spec.growth
            spec.returnTag
            (install (spec.registers.increment .clock) spec.growth
              spec.returnTag T) =
          install (spec.registers.increment .temp) spec.growth
            spec.returnTag T
        apply install_over_install
        simp only [layoutEnd_increment]
        omega
      simp only [clockSpec, incrementSpec, updateSpec] at hthree
      rw [htape] at hthree
      have hfinish : boundaryOffset (spec.registers.increment .clock)
          ((3 : Fin 4).castSucc) = boundaryOffset spec.registers 3 := by
        simp [boundaryOffset, CounterLayout.boundaryPos,
          RegisterLayout.values, Registers.increment, Registers.set,
          Registers.get] <;> omega
      rw [← hhead, hfinish] at hthree
      simp only [searchRef, CounterControlPlan.resolve] at hfour hthree
      exact hfour.trans hthree
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
      have hfour := machine_reaches_incrementClock_solved base c
        spec.outerDistance hshort source bodySearchBase
        (searchRef spec.growth source (bodySearchBase + 1))
        (some (directRef spec.growth source testDirectSlot)) h hclockRoom
        hlimit hrawFour
      have hthree := machine_reaches_incrementInternal_solved base c
        spec.outerDistance hshort source (bodySearchBase + 1)
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
      have htwo := machine_reaches_incrementInternal_solved base c
        spec.outerDistance hshort source (bodySearchBase + 2)
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
      have hheadFour : layoutEnd spec.registers =
          lastGapOffset (spec.registers.increment .clock) 3 := by
        simp [lastGapOffset, boundaryOffset, CounterLayout.boundaryPos,
          layoutEnd, RegisterLayout.clockBoundary_eq, RegisterLayout.values,
          Registers.increment, Registers.set, Registers.get] <;> omega
      have hheadThree : boundaryOffset (spec.registers.increment .clock) 3 =
          lastGapOffset (spec.registers.increment .temp) 2 := by
        simp [lastGapOffset, boundaryOffset, CounterLayout.boundaryPos,
          RegisterLayout.values, Registers.increment, Registers.set,
          Registers.get] <;> omega
      have htapeThree : install (spec.registers.increment .temp) spec.growth
          spec.returnTag clockTape = tempTape := by
        change install (spec.registers.increment .temp) spec.growth
            spec.returnTag
            (install (spec.registers.increment .clock) spec.growth
              spec.returnTag T) =
          install (spec.registers.increment .temp) spec.growth
            spec.returnTag T
        apply install_over_install
        simp only [layoutEnd_increment]
        omega
      simp only [clockSpec, incrementSpec, updateSpec] at hthree
      rw [htapeThree] at hthree
      have htapeTwo : install (spec.registers.increment .right) spec.growth
          spec.returnTag tempTape = incrementTape spec .right T := by
        change install (spec.registers.increment .right) spec.growth
            spec.returnTag
            (install (spec.registers.increment .temp) spec.growth
              spec.returnTag T) =
          install (spec.registers.increment .right) spec.growth
            spec.returnTag T
        apply install_over_install
        simp only [layoutEnd_increment]
        omega
      simp only [tempSpec, incrementSpec, updateSpec] at htwo
      rw [htapeTwo] at htwo
      have hhandoffThree :
          boundaryOffset (spec.registers.increment .clock)
              ((3 : Fin 4).castSucc) =
            lastGapOffset (spec.registers.increment .temp) 2 := by
        simpa using hheadThree
      have hfinish : boundaryOffset (spec.registers.increment .temp)
          ((2 : Fin 4).castSucc) = boundaryOffset spec.registers 2 := by
        simp [boundaryOffset, CounterLayout.boundaryPos,
          RegisterLayout.values, Registers.increment, Registers.set,
          Registers.get] <;> omega
      rw [← hheadFour, hhandoffThree] at hthree
      rw [hfinish] at htwo
      simp only [searchRef, CounterControlPlan.resolve] at hfour hthree
      exact hfour.trans (hthree.trans htwo)
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
      have hfour := machine_reaches_incrementClock_solved base c
        spec.outerDistance hshort source bodySearchBase
        (searchRef spec.growth source (bodySearchBase + 1))
        (some (directRef spec.growth source testDirectSlot)) h hclockRoom
        hlimit hrawFour
      have hthree := machine_reaches_incrementInternal_solved base c
        spec.outerDistance hshort source (bodySearchBase + 1)
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
      have htwo := machine_reaches_incrementInternal_solved base c
        spec.outerDistance hshort source (bodySearchBase + 2)
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
      have hone := machine_reaches_incrementInternal_solved base c
        spec.outerDistance hshort source (bodySearchBase + 3)
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
      have hheadFour : layoutEnd spec.registers =
          lastGapOffset (spec.registers.increment .clock) 3 := by
        simp [lastGapOffset, boundaryOffset, CounterLayout.boundaryPos,
          layoutEnd, RegisterLayout.clockBoundary_eq, RegisterLayout.values,
          Registers.increment, Registers.set, Registers.get] <;> omega
      have hheadThree : boundaryOffset (spec.registers.increment .clock) 3 =
          lastGapOffset (spec.registers.increment .temp) 2 := by
        simp [lastGapOffset, boundaryOffset, CounterLayout.boundaryPos,
          RegisterLayout.values, Registers.increment, Registers.set,
          Registers.get] <;> omega
      have hheadTwo : boundaryOffset (spec.registers.increment .temp) 2 =
          lastGapOffset (spec.registers.increment .right) 1 := by
        simp [lastGapOffset, boundaryOffset, CounterLayout.boundaryPos,
          RegisterLayout.values, Registers.increment, Registers.set,
          Registers.get] <;> omega
      have htapeThree : install (spec.registers.increment .temp) spec.growth
          spec.returnTag clockTape = tempTape := by
        change install (spec.registers.increment .temp) spec.growth
            spec.returnTag
            (install (spec.registers.increment .clock) spec.growth
              spec.returnTag T) =
          install (spec.registers.increment .temp) spec.growth
            spec.returnTag T
        apply install_over_install
        simp only [layoutEnd_increment]
        omega
      simp only [clockSpec, incrementSpec, updateSpec] at hthree
      rw [htapeThree] at hthree
      have htapeTwo : install (spec.registers.increment .right) spec.growth
          spec.returnTag tempTape = rightTape := by
        change install (spec.registers.increment .right) spec.growth
            spec.returnTag
            (install (spec.registers.increment .temp) spec.growth
              spec.returnTag T) =
          install (spec.registers.increment .right) spec.growth
            spec.returnTag T
        apply install_over_install
        simp only [layoutEnd_increment]
        omega
      simp only [tempSpec, incrementSpec, updateSpec] at htwo
      rw [htapeTwo] at htwo
      have htapeOne : install (spec.registers.increment .left) spec.growth
          spec.returnTag rightTape = incrementTape spec .left T := by
        change install (spec.registers.increment .left) spec.growth
            spec.returnTag
            (install (spec.registers.increment .right) spec.growth
              spec.returnTag T) =
          install (spec.registers.increment .left) spec.growth
            spec.returnTag T
        apply install_over_install
        simp only [layoutEnd_increment]
        omega
      simp only [rightSpec, incrementSpec, updateSpec] at hone
      rw [htapeOne] at hone
      have hhandoffThree :
          boundaryOffset (spec.registers.increment .clock)
              ((3 : Fin 4).castSucc) =
            lastGapOffset (spec.registers.increment .temp) 2 := by
        simpa using hheadThree
      have hhandoffTwo :
          boundaryOffset (spec.registers.increment .temp)
              ((2 : Fin 4).castSucc) =
            lastGapOffset (spec.registers.increment .right) 1 := by
        simpa using hheadTwo
      have hfinish : boundaryOffset (spec.registers.increment .right)
          ((1 : Fin 4).castSucc) = boundaryOffset spec.registers 1 := by
        simp [boundaryOffset, CounterLayout.boundaryPos,
          RegisterLayout.values, Registers.increment, Registers.set,
          Registers.get] <;> omega
      rw [← hheadFour, hhandoffThree] at hthree
      rw [hhandoffTwo] at htwo
      rw [hfinish] at hone
      simp only [searchRef, CounterControlPlan.resolve] at hfour hthree htwo
      exact hfour.trans (hthree.trans (htwo.trans hone))

/-- The cell vacated by the last boundary of an increment schedule is blank
in the exact canonical increment tape. -/
theorem incrementSchedule_source_blank
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T) (register : Register)
    (hroom : layoutEnd (spec.registers.increment register) <
      spec.outerDistance) :
    logicalTape spec.growth (incrementTape spec register T)
        (boundaryOffset spec.registers
          (MarkerSchedule.decrementStartBoundary register)) =
      blankSymbol := by
  have hnext := incrementTape_represents h register hroom
  cases register with
  | left =>
      have hb := hnext.gap_blank (0 : Fin 4) spec.registers.left (by
        simp [incrementSpec, updateSpec, RegisterLayout.values,
          Registers.increment, Registers.set, Registers.get])
      change logicalTape spec.growth (incrementTape spec .left T)
        (firstGapOffset (spec.registers.increment .left) 0 +
          spec.registers.left) = blankSymbol at hb
      have hcoord : firstGapOffset (spec.registers.increment .left) 0 +
          spec.registers.left = boundaryOffset spec.registers 1 := by
        simp [firstGapOffset, boundaryOffset, CounterLayout.boundaryPos,
          RegisterLayout.values, Registers.increment, Registers.set,
          Registers.get] <;> omega
      have hcoordInt : (firstGapOffset
          (spec.registers.increment .left) 0 : Int) + spec.registers.left =
          boundaryOffset spec.registers 1 := by
        exact_mod_cast hcoord
      rw [hcoordInt] at hb
      simpa [MarkerSchedule.decrementStartBoundary] using hb
  | right =>
      have hb := hnext.gap_blank (1 : Fin 4) spec.registers.right (by
        simp [incrementSpec, updateSpec, RegisterLayout.values,
          Registers.increment, Registers.set, Registers.get])
      change logicalTape spec.growth (incrementTape spec .right T)
        (firstGapOffset (spec.registers.increment .right) 1 +
          spec.registers.right) = blankSymbol at hb
      have hcoord : firstGapOffset (spec.registers.increment .right) 1 +
          spec.registers.right = boundaryOffset spec.registers 2 := by
        simp [firstGapOffset, boundaryOffset, CounterLayout.boundaryPos,
          RegisterLayout.values, Registers.increment, Registers.set,
          Registers.get] <;> omega
      have hcoordInt : (firstGapOffset
          (spec.registers.increment .right) 1 : Int) + spec.registers.right =
          boundaryOffset spec.registers 2 := by
        exact_mod_cast hcoord
      rw [hcoordInt] at hb
      simpa [MarkerSchedule.decrementStartBoundary] using hb
  | temp =>
      have hb := hnext.gap_blank (2 : Fin 4) spec.registers.temp (by
        simp [incrementSpec, updateSpec, RegisterLayout.values,
          Registers.increment, Registers.set, Registers.get])
      change logicalTape spec.growth (incrementTape spec .temp T)
        (firstGapOffset (spec.registers.increment .temp) 2 +
          spec.registers.temp) = blankSymbol at hb
      have hcoord : firstGapOffset (spec.registers.increment .temp) 2 +
          spec.registers.temp = boundaryOffset spec.registers 3 := by
        simp [firstGapOffset, boundaryOffset, CounterLayout.boundaryPos,
          RegisterLayout.values, Registers.increment, Registers.set,
          Registers.get] <;> omega
      have hcoordInt : (firstGapOffset
          (spec.registers.increment .temp) 2 : Int) + spec.registers.temp =
          boundaryOffset spec.registers 3 := by
        exact_mod_cast hcoord
      rw [hcoordInt] at hb
      simpa [MarkerSchedule.decrementStartBoundary] using hb
  | clock =>
      have hb := hnext.gap_blank (3 : Fin 4) spec.registers.clock (by
        simp [incrementSpec, updateSpec, RegisterLayout.values,
          Registers.increment, Registers.set, Registers.get])
      change logicalTape spec.growth (incrementTape spec .clock T)
        (firstGapOffset (spec.registers.increment .clock) 3 +
          spec.registers.clock) = blankSymbol at hb
      have hcoord : firstGapOffset (spec.registers.increment .clock) 3 +
          spec.registers.clock = boundaryOffset spec.registers 4 := by
        simp [firstGapOffset, boundaryOffset, CounterLayout.boundaryPos,
          RegisterLayout.values, Registers.increment, Registers.set,
          Registers.get] <;> omega
      have hcoordInt : (firstGapOffset
          (spec.registers.increment .clock) 3 : Int) + spec.registers.clock =
          boundaryOffset spec.registers 4 := by
        exact_mod_cast hcoord
      rw [hcoordInt] at hb
      simpa [MarkerSchedule.decrementStartBoundary] using hb

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
        (MarkerSchedule.decrementStartBoundary register) := by
    cases register <;>
      simp [MarkerSchedule.decrementStartBoundary, boundaryOffset,
        CounterLayout.boundaryPos, RegisterLayout.values,
        Registers.increment, Registers.set, Registers.get] <;> omega
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

/-! ## The outward-collision branch of increment -/

/-- The first (boundary-`4`) increment shift detects an occupied outward
destination exactly when the current frame touches its suspended target. -/
theorem machine_reaches_incrementCollision
    (base : Nat) (c : Nat.Partrec.Code) (source : Nat)
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T)
    (hcollision : layoutEnd spec.registers + 1 = spec.outerDistance)
    (hraw : RawCommand.markerShift
      ⟨spec.growth, source, bodySearchBase⟩ 4 .left .right
      (directRef spec.growth source bodyDirectBase) (some .left)
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
      (directRef spec.growth source bodyDirectBase) (some .left)
      (some (directRef spec.growth source testDirectSlot))
  let move : MarkerProgram.Move :=
    ⟨4, orient spec.growth .left, orient spec.growth .right⟩
  have hatRaw := CommandAt.compileRawCommand base c raw hraw
  have hspec := compileRawCommand_spec base c raw hraw
  have hat : CommandAt (CanonicalInitializer.radius c) base
      (searchState base c ⟨spec.growth, source, bodySearchBase⟩)
      (.markerShift move
        (resolve base c (directRef spec.growth source bodyDirectBase))
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
    (resolve base c (directRef spec.growth source bodyDirectBase))
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

end

end CounterControlInstructionSemantics
end Hooper
end Kari
end LeanWang
