/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlSearchResolution
import LeanWang.Kari.Hooper.CounterControlStepGeometry
import LeanWang.Kari.Hooper.CounterControlTraceSimulation

/-!
# Converse semantics of compiled counter instructions

This file is the halting-aware counterpart of the solved-search instruction
semantics.  A shorter compiled search is only assumed to resolve: it either
finds its marker and continues, or the complete finite controller halts.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlInstructionResolution

open Turing CounterMachine
open BoundedMarkerProgram FramedMarkerTape FramedCounterGeometry
open CounterControlPlan CounterControlCommandAt CounterControlBridge
open CounterControlScheduleSemantics CounterControlFrameBacking
open CounterControlInstructionSemantics CounterControlSearchResolution
  CounterControlCoreRoutes

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-! ## Resolving cleanup navigation -/

/-- Resolving-search form of an erasing boundary command.  The exact erase
continuation runs only after the search has found its target. -/
theorem machine_reaches_boundary_erase_or_halts
    (base : Nat) (c : Nat.Partrec.Code) (limit : Nat)
    (hshort : ShortResolves base c limit)
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
                blankSymbol).move (orient address.growth departure)⟩ ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨searchState base c address, outer⟩ := by
  exact machine_reaches_boundary_erase_with base c limit
    (FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c))
    (resolvingSearchRunner base c limit hshort) address expected direction
    success departure hraw outer distance hdistance hgap

/-- Resolving searches instantiate the shared four-command cleanup runner. -/
def resolvingCleanupRunner
    (base : Nat) (c : Nat.Partrec.Code) (limit source : Nat)
    (growth : Turing.Dir) (hshort : ShortResolves base c limit) :
    CounterControlCleanupSemantics.CleanupRunner base c limit growth source
      (FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)) where
  pullback := by
    intro start current hreach hhalts
    exact FullTM0.HaltsFrom.of_reaches hreach hhalts
  erase := by
    intro address expected success _ hraw outer distance hdistance hgap
    exact machine_reaches_boundary_erase_or_halts base c limit hshort address
      expected .left success (some .left) hraw outer distance hdistance hgap

/-- Resolving-search form of the cleanup tag command. -/
theorem machine_reaches_tag_or_halts
    (base : Nat) (c : Nat.Partrec.Code) (limit : Nat)
    (hshort : ShortResolves base c limit)
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
          outer.moveN (orient address.growth direction) distance⟩ ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨searchState base c address, outer⟩ := by
  exact machine_reaches_tag_with base c limit
    (FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c))
    (resolvingSearchRunner base c limit hshort) address direction success hraw
    outer distance hdistance hgap

/-- The four erasing boundary searches either reach the directional return
dispatcher or halt from the cleanup entry.  The last erase lands directly on
the saved tag; no unbounded tag search is needed. -/
theorem machine_reaches_cleanup_return_or_halts
    (base : Nat) (c : Nat.Partrec.Code) (limit source : Nat)
    (hshort : ShortResolves base c limit)
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T)
    (hlimit : spec.outerDistance = limit)
    (hcommands : ∀ raw, raw ∈ cleanupCommands spec.growth source →
      raw ∈ rawCommands) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨spec.growth, source, cleanupSearchBase⟩,
          atLogical spec.growth (CounterControlCleanupSemantics.afterFour spec T)
            (layoutEnd spec.registers)⟩
        ⟨controllerReturn base c spec.growth,
          atLogical spec.growth
            (CounterControlCleanupSemantics.afterZero spec T) 0⟩ ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨spec.growth, source, cleanupSearchBase⟩,
          atLogical spec.growth (CounterControlCleanupSemantics.afterFour spec T)
            (layoutEnd spec.registers)⟩ := by
  have hthree : RegisterLayout.values spec.registers 3 + 1 < limit := by
    rw [← hlimit]
    have hcore := spec.core_before_target
    rw [layoutEnd_eq] at hcore
    simp [RegisterLayout.values]
    omega
  exact CounterControlCleanupSemantics.machine_reaches_cleanup_return_with
    base c limit source
    (FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c))
    (resolvingCleanupRunner base c limit source spec.growth hshort)
    hthree
    (by rw [← hlimit]; exact registerValue_lt_outerDistance h 2)
    (by rw [← hlimit]; exact registerValue_lt_outerDistance h 1)
    (by rw [← hlimit]; exact registerValue_lt_outerDistance h 0)
    (by simpa [orient_eq_orientDirection] using
      CounterControlCleanupSemantics.cleanupGap_three h)
    (by simpa [orient_eq_orientDirection] using
      CounterControlCleanupSemantics.cleanupGap_two h)
    (by simpa [orient_eq_orientDirection] using
      CounterControlCleanupSemantics.cleanupGap_one h)
    (by simpa [orient_eq_orientDirection] using
      CounterControlCleanupSemantics.cleanupGap_zero h)
    hcommands

/-- Resolving cleanup through the shared return dispatcher. -/
theorem machine_reaches_cleanup_resume_or_halts
    (base : Nat) (c : Nat.Partrec.Code) (source : Nat)
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T)
    (hreturnDirection :
      (compileCommand base c spec.returnTag).searchDirection = spec.growth)
    (hshort : ShortResolves base c spec.outerDistance)
    (hcommands : ∀ raw, raw ∈ cleanupCommands spec.growth source →
      raw ∈ rawCommands) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨spec.growth, source, cleanupSearchBase⟩,
          atLogical spec.growth (CounterControlCleanupSemantics.afterFour spec T)
            (layoutEnd spec.registers)⟩
        ⟨resumeState (CanonicalInitializer.radius c)
            (searchState base c
              (rawCommands.get spec.returnTag).address),
          atLogical spec.growth
            (CounterControlCleanupSemantics.afterTag spec T) 0⟩ ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨spec.growth, source, cleanupSearchBase⟩,
          atLogical spec.growth (CounterControlCleanupSemantics.afterFour spec T)
            (layoutEnd spec.registers)⟩ := by
  have hreturn := machine_reaches_cleanup_return_or_halts base c
    spec.outerDistance source hshort h rfl hcommands
  have hread :
      (atLogical spec.growth
        (CounterControlCleanupSemantics.afterZero spec T) 0).read =
        tagSymbol spec.returnTag :=
    CounterControlCleanupSemantics.afterZero_read_tag h
  have hdispatch :=
    CounterControlCleanupSemantics.machine_sharedReturn_reaches_resume
      base c spec.returnTag
      (atLogical spec.growth
        (CounterControlCleanupSemantics.afterZero spec T) 0) hread
  have hdispatch' : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      ⟨controllerReturn base c spec.growth,
        atLogical spec.growth
          (CounterControlCleanupSemantics.afterZero spec T) 0⟩
      ⟨resumeState (CanonicalInitializer.radius c)
          (searchState base c (rawCommands.get spec.returnTag).address),
        atLogical spec.growth
          (CounterControlCleanupSemantics.afterTag spec T) 0⟩ := by
    simpa [hreturnDirection, CounterControlCleanupSemantics.afterTag,
      atLogical_write] using hdispatch
  exact FullTM0.ResolvesTo.trans hreturn (Or.inl hdispatch')

/-- Backed-frame form of resolving cleanup: successful erasure restores the
suspended outer tape exactly. -/
theorem machine_reaches_cleanup_outer_or_halts
    (base : Nat) (c : Nat.Partrec.Code) (source : Nat)
    {spec : Spec numTags}
    {T outer : FullTM0.Tape (Symbol numTags)}
    (hback : BackedBy spec T outer)
    (hreturnDirection :
      (compileCommand base c spec.returnTag).searchDirection = spec.growth)
    (hshort : ShortResolves base c spec.outerDistance)
    (hcommands : ∀ raw, raw ∈ cleanupCommands spec.growth source →
      raw ∈ rawCommands) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨spec.growth, source, cleanupSearchBase⟩,
          atLogical spec.growth (CounterControlCleanupSemantics.afterFour spec T)
            (layoutEnd spec.registers)⟩
        ⟨resumeState (CanonicalInitializer.radius c)
            (searchState base c
              (rawCommands.get spec.returnTag).address), outer⟩ ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨spec.growth, source, cleanupSearchBase⟩,
          atLogical spec.growth (CounterControlCleanupSemantics.afterFour spec T)
            (layoutEnd spec.registers)⟩ := by
  have hrun := machine_reaches_cleanup_resume_or_halts base c source
    hback.represents hreturnDirection hshort hcommands
  rw [afterTag_eq_outer hback] at hrun
  simpa [atLogical] using hrun

/-- From the exact outward-collision endpoint, resolving cleanup either
restores the suspended outer configuration or halts. -/
theorem machine_reaches_collisionCleanup_or_halts
    (base : Nat) (c : Nat.Partrec.Code) (source : Nat)
    {spec : Spec numTags}
    {T outer : FullTM0.Tape (Symbol numTags)}
    (hback : BackedBy spec T outer)
    (hreturnDirection :
      (compileCommand base c spec.returnTag).searchDirection = spec.growth)
    (hcollision : layoutEnd spec.registers + 1 = spec.outerDistance)
    (hshort : ShortResolves base c spec.outerDistance)
    (hentry : CounterControlCleanupSemantics.cleanupEntryRule
      spec.growth source ∈ rawDirectRules)
    (hcommands : ∀ raw, raw ∈ cleanupCommands spec.growth source →
      raw ∈ rawCommands) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨resolve base c (directRef spec.growth source testDirectSlot),
          atLogical spec.growth
            (CounterControlCleanupSemantics.afterFour spec T)
            spec.outerDistance⟩
        ⟨resumeState (CanonicalInitializer.radius c)
            (searchState base c
              (rawCommands.get spec.returnTag).address), outer⟩ ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨resolve base c (directRef spec.growth source testDirectSlot),
          atLogical spec.growth
            (CounterControlCleanupSemantics.afterFour spec T)
            spec.outerDistance⟩ := by
  have hentryRun :=
    CounterControlCleanupSemantics.machine_reaches_cleanupEntry base c source
      hback.represents hcollision hentry
  exact FullTM0.ResolvesTo.trans_reaches hentryRun
    (machine_reaches_cleanup_outer_or_halts base c source hback
      hreturnDirection hshort hcommands)

/-! ## Validation -/

/-- Whole-list wrapper for a nonempty resolving route. -/
private abbrev validationCommand_mem :=
  validationCommand_mem_commandsForRule
private abbrev validationRule_mem :=
  validationRule_mem_directRulesForRule

theorem route_reaches_or_halts_at_of_ne_nil
    (base : Nat) (c : Nat.Partrec.Code) (limit : Nat)
    (hshort : ShortResolves base c limit) (growth : Turing.Dir)
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
        ⟨resolve base c after, atLogical growth T finishPosition⟩ ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨resolve base c source, atLogical growth T sourcePosition⟩ := by
  cases legs with
  | nil => exact (hne rfl).elim
  | cons first rest =>
      exact route_reaches_or_halts_at base c limit hshort growth counterState
        searchSlot directSlot source after sourceBoundary first rest T
        sourcePosition finishPosition hsource hexec hcommands hrules

/-- The mandatory validation sweep reaches the selected instruction body, or
one of its shorter searches makes the complete controller halt. -/
theorem machine_reaches_validation_or_halts
    (base : Nat) (c : Nat.Partrec.Code) (growth : Turing.Dir)
    (source : Nat) (instruction : CounterMachine.Instruction)
    (hrule : (source, instruction) ∈ GlobalSourceProgram.program)
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T) (hgrowth : spec.growth = growth)
    (hshort : ShortResolves base c spec.outerDistance) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨logicalState base c growth source,
          atLogical growth T (layoutEnd spec.registers)⟩
        ⟨resolve base c (bodyEntry growth source instruction),
          atLogical growth T (layoutEnd spec.registers)⟩ ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
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
  have hroute := route_reaches_or_halts_at base c spec.outerDistance hshort
    spec.growth source validationSearchBase validationDirectBase
    (.logical spec.growth source) (bodyEntry spec.growth source instruction)
    4 ⟨3, .left⟩
    [⟨2, .left⟩, ⟨1, .left⟩, ⟨0, .left⟩,
      ⟨1, .right⟩, ⟨2, .right⟩, ⟨3, .right⟩,
      ⟨4, .right⟩]
    T (layoutEnd spec.registers) (layoutEnd spec.registers)
    h.read_boundary_four (by
      simpa only [MarkerValidation.sweep] using validation_executesWithin h)
    (by intro raw hraw; exact hcommands raw hraw)
    (by intro raw hraw; exact hrules raw hraw)
  simpa [validationCommands, validationRules, logicalState,
    CounterControlPlan.resolve] using hroute

/-! ## Halting-aware marker shifts -/

/-- Resolving-search counterpart of the native outward marker shift. -/
theorem machine_reaches_incrementShift_or_halts
    (base : Nat) (c : Nat.Partrec.Code) (limit : Nat)
    (hshort : ShortResolves base c limit) (growth : Turing.Dir)
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
                (boundarySymbol expected)) source⟩ ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨growth, counterState, searchSlot⟩,
          atLogical growth T (source + distance)⟩ := by
  exact machine_reaches_incrementShift_with base c limit
    (FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c))
    (resolvingSearchRunner base c limit hshort) growth counterState searchSlot
    source expected success collision hraw T distance hdistance hgap hblank

/-- Resolving-search counterpart of the native inward marker shift. -/
theorem machine_reaches_decrementShift_or_halts
    (base : Nat) (c : Nat.Partrec.Code) (limit : Nat)
    (hshort : ShortResolves base c limit) (growth : Turing.Dir)
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
              (writeLogical growth T (destination + 1) blankSymbol)
                destination (boundarySymbol expected)) (destination + 1)⟩ ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨growth, counterState, searchSlot⟩,
          atLogical growth T origin⟩ := by
  exact machine_reaches_decrementShift_with base c limit
    (FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c))
    (resolvingSearchRunner base c limit hshort) growth counterState searchSlot
    origin destination distance expected success collision hraw T hposition
    hdistance hgap hblank

/-! ## Canonical shift normalization -/

/-- One internal canonical outward shift resolves to its exact installed
frame update, or halts at the shift's search entry. -/
theorem machine_reaches_incrementInternal_or_halts
    (base : Nat) (c : Nat.Partrec.Code) (limit : Nat)
    (hshort : ShortResolves base c limit)
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
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
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
  have hrun := machine_reaches_incrementShift_or_halts base c limit hshort
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

/-- One canonical inward shift resolves to the normalized installed frame, or
halts at the shift's search entry. -/
theorem machine_reaches_decrementCanonical_or_halts
    (base : Nat) (c : Nat.Partrec.Code) (limit : Nat)
    (hshort : ShortResolves base c limit)
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
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
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
  have hrun := machine_reaches_decrementShift_or_halts base c limit hshort
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

/-- The outward clock shift resolves to the exact incremented tape, or halts
at its search entry. -/
theorem machine_reaches_incrementClock_or_halts
    (base : Nat) (c : Nat.Partrec.Code) (limit : Nat)
    (hshort : ShortResolves base c limit) (counterState searchSlot : Nat)
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
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
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
  have hrun := machine_reaches_incrementShift_or_halts base c limit hshort
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

/-! ## Collision-free increment schedule -/

/-- All collision-free shifts of one generated increment resolve to the
blank old source cell of the final shifted boundary, or a constituent search
halts the complete controller. -/
theorem machine_reaches_incrementSchedule_or_halts
    (base : Nat) (c : Nat.Partrec.Code) (source : Nat)
    (register : Register)
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T)
    (hroom : layoutEnd (spec.registers.increment register) <
      spec.outerDistance)
    (hshort : ShortResolves base c spec.outerDistance)
    (hcommands : ∀ raw,
      raw ∈ incrementShiftCommands spec.growth source register →
        raw ∈ rawCommands) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨spec.growth, source, bodySearchBase⟩,
          atLogical spec.growth T (layoutEnd spec.registers)⟩
        ⟨resolve base c (directRef spec.growth source bodyDirectBase),
          atLogical spec.growth (incrementTape spec register T)
            (boundaryOffset spec.registers
              (MarkerSchedule.decrementStartBoundary register))⟩ ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨spec.growth, source, bodySearchBase⟩,
          atLogical spec.growth T (layoutEnd spec.registers)⟩ := by
  let runner : IncrementScheduleRunner base c (ShortResolves base c)
      (FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)) := {
    pullback := FullTM0.HaltsFrom.of_reaches
    clock := by
      intro limit hshort counterState searchSlot success collision spec T
        h hroom hlimit hraw
      exact machine_reaches_incrementClock_or_halts base c limit hshort
        counterState searchSlot success collision h hroom hlimit hraw
    internal := by
      intro limit hshort counterState searchSlot success collision spec T
        h next i hpositive hdistance hnextCore hsameEnd hmove hraw
      exact machine_reaches_incrementInternal_or_halts base c limit hshort
        counterState searchSlot success collision h next i hpositive hdistance
        hnextCore hsameEnd hmove hraw }
  exact machine_reaches_incrementSchedule_with base c (ShortResolves base c)
    (FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)) runner
    source register h hroom hshort hcommands

theorem machine_reaches_incrementRecovery_or_halts
    (base : Nat) (c : Nat.Partrec.Code) (source next : Nat)
    (register : Register)
    (hrule : (source, .increment register next) ∈
      GlobalSourceProgram.program)
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T)
    (hshort : ShortResolves base c spec.outerDistance) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨resolve base c
            (match AnchoredCounterGeometry.routeFromIncrement register with
            | [] => .logical spec.growth next
            | _ :: _ => directRef spec.growth source (bodyDirectBase + 1)),
          atLogical spec.growth T
            (boundaryOffset spec.registers
              (MarkerSchedule.decrementStartBoundary register))⟩
        ⟨logicalState base c spec.growth next,
          atLogical spec.growth T (layoutEnd spec.registers)⟩ ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨resolve base c
            (match AnchoredCounterGeometry.routeFromIncrement register with
            | [] => .logical spec.growth next
            | _ :: _ => directRef spec.growth source (bodyDirectBase + 1)),
          atLogical spec.growth T
            (boundaryOffset spec.registers
              (MarkerSchedule.decrementStartBoundary register))⟩ := by
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
  | clock => exact Or.inl Relation.ReflTransGen.refl
  | temp =>
      have hrun := route_reaches_or_halts_at_of_ne_nil base c
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
      have hrun := route_reaches_or_halts_at_of_ne_nil base c
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
      have hrun := route_reaches_or_halts_at_of_ne_nil base c
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

/-- Exact collision-free increment semantics on a backed frame: either the
logical successor frame is reached and remains backed by the same outer tape,
or the complete controller halts from the instruction's logical entry. -/
theorem machine_reaches_incrementInstruction_or_halts
    (base : Nat) (c : Nat.Partrec.Code) (source next : Nat)
    (register : Register)
    (hrule : (source, .increment register next) ∈
      GlobalSourceProgram.program)
    {spec : Spec numTags}
    {T outer : FullTM0.Tape (Symbol numTags)}
    (hback : BackedBy spec T outer)
    (hroom : layoutEnd (spec.registers.increment register) <
      spec.outerDistance)
    (hshort : ShortResolves base c spec.outerDistance) :
    (FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨logicalState base c spec.growth source,
          atLogical spec.growth T (layoutEnd spec.registers)⟩
        ⟨logicalState base c spec.growth next,
          atLogical spec.growth (incrementTape spec register T)
            (layoutEnd (spec.registers.increment register))⟩ ∧
      BackedBy (incrementSpec spec register hroom)
        (incrementTape spec register T) outer) ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨logicalState base c spec.growth source,
          atLogical spec.growth T (layoutEnd spec.registers)⟩ := by
  have h := hback.represents
  have hvalidation := machine_reaches_validation_or_halts base c spec.growth
    source (.increment register next) hrule h rfl hshort
  have hcommands : ∀ raw,
      raw ∈ incrementShiftCommands spec.growth source register →
        raw ∈ rawCommands := by
    intro raw hraw
    apply command_mem_rawCommands_of_rule spec.growth hrule
    simp [commandsForRule, incrementCommands, hraw]
  have hschedule := machine_reaches_incrementSchedule_or_halts base c source
    register h hroom hshort hcommands
  have hhandoff := machine_reaches_incrementHandoff base c source next
    register hrule h hroom
  let nextSpec := incrementSpec spec register hroom
  have hnext : Represents nextSpec (incrementTape spec register T) :=
    incrementTape_represents h register hroom
  have hrecovery := machine_reaches_incrementRecovery_or_halts base c
    source next register hrule hnext (by
      simpa [nextSpec, incrementSpec, updateSpec] using hshort)
  have hvalidation' :
      FullTM0.Reaches (CounterControlNestingBridge.machine base c)
          ⟨logicalState base c spec.growth source,
            atLogical spec.growth T (layoutEnd spec.registers)⟩
          ⟨searchState base c ⟨spec.growth, source, bodySearchBase⟩,
            atLogical spec.growth T (layoutEnd spec.registers)⟩ ∨
        FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
          ⟨logicalState base c spec.growth source,
            atLogical spec.growth T (layoutEnd spec.registers)⟩ := by
    simpa [bodyEntry, searchRef, CounterControlPlan.resolve] using hvalidation
  have hrecovery' :
      FullTM0.Reaches (CounterControlNestingBridge.machine base c)
          ⟨resolve base c
              (match AnchoredCounterGeometry.routeFromIncrement register with
              | [] => .logical spec.growth next
              | _ :: _ => directRef spec.growth source
                  (bodyDirectBase + 1)),
            atLogical spec.growth (incrementTape spec register T)
              (boundaryOffset (spec.registers.increment register)
                (MarkerSchedule.decrementStartBoundary register))⟩
          ⟨logicalState base c spec.growth next,
            atLogical spec.growth (incrementTape spec register T)
              (layoutEnd (spec.registers.increment register))⟩ ∨
        FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
          ⟨resolve base c
              (match AnchoredCounterGeometry.routeFromIncrement register with
              | [] => .logical spec.growth next
              | _ :: _ => directRef spec.growth source
                  (bodyDirectBase + 1)),
            atLogical spec.growth (incrementTape spec register T)
              (boundaryOffset (spec.registers.increment register)
                (MarkerSchedule.decrementStartBoundary register))⟩ := by
    simpa [nextSpec, incrementSpec, updateSpec] using hrecovery
  have hrun := FullTM0.ResolvesTo.trans hvalidation'
    (FullTM0.ResolvesTo.trans hschedule
      (FullTM0.ResolvesTo.trans (Or.inl hhandoff) hrecovery'))
  rcases hrun with hrun | hhalts
  · exact Or.inl ⟨hrun, incrementTape_backedBy hback register hroom⟩
  · exact Or.inr hhalts

/-- If the outward increment destination is the suspended target cell, the
instruction reaches the generated collision-cleanup entry, unless validation
has already halted the complete controller. -/
theorem machine_reaches_incrementCollisionInstruction_or_halts
    (base : Nat) (c : Nat.Partrec.Code) (source next : Nat)
    (register : Register)
    (hrule : (source, .increment register next) ∈
      GlobalSourceProgram.program)
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T)
    (hcollision : layoutEnd spec.registers + 1 = spec.outerDistance)
    (hshort : ShortResolves base c spec.outerDistance) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨logicalState base c spec.growth source,
          atLogical spec.growth T (layoutEnd spec.registers)⟩
        ⟨resolve base c (directRef spec.growth source testDirectSlot),
          atLogical spec.growth
            (CounterControlCleanupSemantics.afterFour spec T)
            spec.outerDistance⟩ ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨logicalState base c spec.growth source,
          atLogical spec.growth T (layoutEnd spec.registers)⟩ := by
  have hvalidation := machine_reaches_validation_or_halts base c spec.growth
    source (.increment register next) hrule h rfl hshort
  let success : ControlRef := match register with
    | .clock => directRef spec.growth source bodyDirectBase
    | _ => searchRef spec.growth source (bodySearchBase + 1)
  have hraw : RawCommand.markerShift
      ⟨spec.growth, source, bodySearchBase⟩ 4 .left .right
      success (some .left)
      (some (directRef spec.growth source testDirectSlot)) ∈ rawCommands := by
    apply command_mem_rawCommands_of_rule spec.growth hrule
    cases register <;>
      simp [success, commandsForRule, incrementCommands, incrementShiftCommands,
        incrementShiftCommandsAux, MarkerShift.incrementOrder]
  have hcollisionReach := machine_reaches_incrementCollision base c source
    success h hcollision hraw
  have hvalidation' :
      FullTM0.Reaches (CounterControlNestingBridge.machine base c)
          ⟨logicalState base c spec.growth source,
            atLogical spec.growth T (layoutEnd spec.registers)⟩
          ⟨searchState base c ⟨spec.growth, source, bodySearchBase⟩,
            atLogical spec.growth T (layoutEnd spec.registers)⟩ ∨
        FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
          ⟨logicalState base c spec.growth source,
            atLogical spec.growth T (layoutEnd spec.registers)⟩ := by
    simpa [bodyEntry, searchRef, CounterControlPlan.resolve] using hvalidation
  exact FullTM0.ResolvesTo.trans hvalidation' (Or.inl hcollisionReach)

/-- Complete collision branch of an increment instruction.  Successful
cleanup restores the suspended outer tape at its exact resume state; any
failed validation or cleanup search is propagated back to the logical
instruction entry. -/
theorem machine_reaches_incrementCollisionCleanup_or_halts
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
    (hshort : ShortResolves base c spec.outerDistance) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨logicalState base c spec.growth source,
          atLogical spec.growth T (layoutEnd spec.registers)⟩
        ⟨resumeState (CanonicalInitializer.radius c)
            (searchState base c
              (rawCommands.get spec.returnTag).address), outer⟩ ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨logicalState base c spec.growth source,
          atLogical spec.growth T (layoutEnd spec.registers)⟩ := by
  have hcollisionEntry :=
    machine_reaches_incrementCollisionInstruction_or_halts base c source next
      register hrule hback.represents hcollision hshort
  have hentry : CounterControlCleanupSemantics.cleanupEntryRule
      spec.growth source ∈ rawDirectRules := by
    apply directRule_mem_rawDirectRules_of_rule spec.growth hrule
    change CounterControlCleanupSemantics.cleanupEntryRule spec.growth source ∈
      validationRules spec.growth source ++
        incrementRules spec.growth source next register
    apply List.mem_append_right
    simp [CounterControlCleanupSemantics.cleanupEntryRule, incrementRules]
  have hcleanupCommands : ∀ raw,
      raw ∈ cleanupCommands spec.growth source → raw ∈ rawCommands := by
    intro raw hraw
    apply command_mem_rawCommands_of_rule spec.growth hrule
    simp [commandsForRule, incrementCommands, hraw]
  have hcleanup := machine_reaches_collisionCleanup_or_halts base c source
    hback hreturnDirection hcollision hshort hentry hcleanupCommands
  exact FullTM0.ResolvesTo.trans hcollisionEntry hcleanup

/-! ## Conditional-decrement routing and zero branch -/

/-- Navigate from boundary `4` to the selected register test, or halt in a
shorter route search.  Clock requires no navigation. -/
theorem machine_reaches_decrementToTest_or_halts
    (base : Nat) (c : Nat.Partrec.Code) (source ifZero ifPositive : Nat)
    (register : Register)
    (hrule : (source, .decrement register ifZero ifPositive) ∈
      GlobalSourceProgram.program)
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T)
    (hshort : ShortResolves base c spec.outerDistance) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨resolve base c
            (bodyEntry spec.growth source
              (.decrement register ifZero ifPositive)),
          atLogical spec.growth T (layoutEnd spec.registers)⟩
        ⟨resolve base c (directRef spec.growth source testDirectSlot),
          atLogical spec.growth T
            (boundaryOffset spec.registers
              (MarkerSchedule.decrementStartBoundary register))⟩ ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨resolve base c
            (bodyEntry spec.growth source
              (.decrement register ifZero ifPositive)),
          atLogical spec.growth T (layoutEnd spec.registers)⟩ := by
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
  | clock => exact Or.inl Relation.ReflTransGen.refl
  | temp =>
      have hrun := route_reaches_or_halts_at_of_ne_nil base c
        spec.outerDistance hshort spec.growth source bodySearchBase
        (bodyDirectBase + 1) (directRef spec.growth source bodyDirectBase)
        (directRef spec.growth source testDirectSlot) 4
        (AnchoredCounterGeometry.routeToDecrementStart .temp)
        (by simp [AnchoredCounterGeometry.routeToDecrementStart]) T
        (layoutEnd spec.registers) (boundaryOffset spec.registers 3)
        h.read_boundary_four (routeToDecrementStart_executesWithin h .temp)
        (by intro raw hraw; exact hcommands raw hraw)
        (by intro raw hraw; exact hrules raw hraw)
      change (FullTM0.Reaches (CounterControlNestingBridge.machine base c)
          ⟨resolve base c
              (bodyEntry spec.growth source
                (.decrement .temp ifZero ifPositive)),
            atLogical spec.growth T (layoutEnd spec.registers)⟩
          ⟨resolve base c (directRef spec.growth source testDirectSlot),
            atLogical spec.growth T (boundaryOffset spec.registers 3)⟩ ∨
        FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
          ⟨resolve base c
              (bodyEntry spec.growth source
                (.decrement .temp ifZero ifPositive)),
            atLogical spec.growth T (layoutEnd spec.registers)⟩) at hrun
      exact hrun
  | right =>
      have hrun := route_reaches_or_halts_at_of_ne_nil base c
        spec.outerDistance hshort spec.growth source bodySearchBase
        (bodyDirectBase + 1) (directRef spec.growth source bodyDirectBase)
        (directRef spec.growth source testDirectSlot) 4
        (AnchoredCounterGeometry.routeToDecrementStart .right)
        (by simp [AnchoredCounterGeometry.routeToDecrementStart]) T
        (layoutEnd spec.registers) (boundaryOffset spec.registers 2)
        h.read_boundary_four (routeToDecrementStart_executesWithin h .right)
        (by intro raw hraw; exact hcommands raw hraw)
        (by intro raw hraw; exact hrules raw hraw)
      change (FullTM0.Reaches (CounterControlNestingBridge.machine base c)
          ⟨resolve base c
              (bodyEntry spec.growth source
                (.decrement .right ifZero ifPositive)),
            atLogical spec.growth T (layoutEnd spec.registers)⟩
          ⟨resolve base c (directRef spec.growth source testDirectSlot),
            atLogical spec.growth T (boundaryOffset spec.registers 2)⟩ ∨
        FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
          ⟨resolve base c
              (bodyEntry spec.growth source
                (.decrement .right ifZero ifPositive)),
            atLogical spec.growth T (layoutEnd spec.registers)⟩) at hrun
      exact hrun
  | left =>
      have hrun := route_reaches_or_halts_at_of_ne_nil base c
        spec.outerDistance hshort spec.growth source bodySearchBase
        (bodyDirectBase + 1) (directRef spec.growth source bodyDirectBase)
        (directRef spec.growth source testDirectSlot) 4
        (AnchoredCounterGeometry.routeToDecrementStart .left)
        (by simp [AnchoredCounterGeometry.routeToDecrementStart]) T
        (layoutEnd spec.registers) (boundaryOffset spec.registers 1)
        h.read_boundary_four (routeToDecrementStart_executesWithin h .left)
        (by intro raw hraw; exact hcommands raw hraw)
        (by intro raw hraw; exact hrules raw hraw)
      change (FullTM0.Reaches (CounterControlNestingBridge.machine base c)
          ⟨resolve base c
              (bodyEntry spec.growth source
                (.decrement .left ifZero ifPositive)),
            atLogical spec.growth T (layoutEnd spec.registers)⟩
          ⟨resolve base c (directRef spec.growth source testDirectSlot),
            atLogical spec.growth T (boundaryOffset spec.registers 1)⟩ ∨
        FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
          ⟨resolve base c
              (bodyEntry spec.growth source
                (.decrement .left ifZero ifPositive)),
            atLogical spec.growth T (layoutEnd spec.registers)⟩) at hrun
      exact hrun

/-- From the predecessor boundary of an empty tested gap, the generated zero
route reaches the zero successor, or a route search halts. -/
theorem machine_reaches_decrementZeroRecovery_or_halts
    (base : Nat) (c : Nat.Partrec.Code) (source ifZero ifPositive : Nat)
    (register : Register)
    (hrule : (source, .decrement register ifZero ifPositive) ∈
      GlobalSourceProgram.program)
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T)
    (hzero : spec.registers.get register = 0)
    (hshort : ShortResolves base c spec.outerDistance) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨resolve base c (directRef spec.growth source branchDirectSlot),
          atLogical spec.growth T
            (boundaryOffset spec.registers
              (MarkerSchedule.decrementStartBoundary register) - 1)⟩
        ⟨logicalState base c spec.growth ifZero,
          atLogical spec.growth T (layoutEnd spec.registers)⟩ ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨resolve base c (directRef spec.growth source branchDirectSlot),
          atLogical spec.growth T
            (boundaryOffset spec.registers
              (MarkerSchedule.decrementStartBoundary register) - 1)⟩ := by
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
        simp only [List.mem_cons]
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
  have hrun := route_reaches_or_halts_at_of_ne_nil base c
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

/-- Exact zero branch of one compiled conditional decrement, with the
unchanged backed-frame invariant returned in the successful branch. -/
theorem machine_reaches_decrementZeroInstruction_or_halts
    (base : Nat) (c : Nat.Partrec.Code) (source ifZero ifPositive : Nat)
    (register : Register)
    (hrule : (source, .decrement register ifZero ifPositive) ∈
      GlobalSourceProgram.program)
    {spec : Spec numTags}
    {T outer : FullTM0.Tape (Symbol numTags)}
    (hback : BackedBy spec T outer)
    (hzero : spec.registers.get register = 0)
    (hshort : ShortResolves base c spec.outerDistance) :
    (FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨logicalState base c spec.growth source,
          atLogical spec.growth T (layoutEnd spec.registers)⟩
        ⟨logicalState base c spec.growth ifZero,
          atLogical spec.growth T (layoutEnd spec.registers)⟩ ∧
      BackedBy spec T outer) ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨logicalState base c spec.growth source,
          atLogical spec.growth T (layoutEnd spec.registers)⟩ := by
  have h := hback.represents
  have hvalidation := machine_reaches_validation_or_halts base c spec.growth
    source (.decrement register ifZero ifPositive) hrule h rfl hshort
  have hroute := machine_reaches_decrementToTest_or_halts base c source
    ifZero ifPositive register hrule h hshort
  have htest := machine_reaches_decrementTest base c source ifZero ifPositive
    register hrule T (by rw [atLogical_read]; exact h.boundary _)
  have hzeroRoute := machine_reaches_decrementZeroRecovery_or_halts base c
    source ifZero ifPositive register hrule h hzero hshort
  have hrun := FullTM0.ResolvesTo.trans hvalidation
    (FullTM0.ResolvesTo.trans hroute
      (FullTM0.ResolvesTo.trans (Or.inl htest) hzeroRoute))
  rcases hrun with hrun | hhalts
  · exact Or.inl ⟨hrun, hback⟩
  · exact Or.inr hhalts

/-! ## Positive conditional-decrement shifts -/

/-- The first positive-decrement shift has search distance zero and either
installs its exact next canonical core or halts. -/
theorem machine_reaches_decrementFirst_or_halts
    (base : Nat) (c : Nat.Partrec.Code) (limit : Nat)
    (hshort : ShortResolves base c limit) (counterState searchSlot : Nat)
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
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
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
  apply machine_reaches_decrementCanonical_or_halts base c limit hshort
    counterState searchSlot success none h next i.succ
    (boundaryOffset spec.registers i.succ) 0 hsourcePositive
    (by simp) hlimit hgap hblank hnextCore hlower hupper hsource hdestination
      hshrink hmove hraw

/-- Every later positive-decrement shift searches one represented gap before
installing its exact next canonical core, or halts. -/
theorem machine_reaches_decrementFollowing_or_halts
    (base : Nat) (c : Nat.Partrec.Code) (limit : Nat)
    (hshort : ShortResolves base c limit) (counterState searchSlot : Nat)
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
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
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
  exact machine_reaches_decrementCanonical_or_halts base c limit hshort
    counterState searchSlot success none h next i.succ
    (firstGapOffset spec.registers i)
    (RegisterLayout.values spec.registers i) hsourcePositive horigin
    hdistance hgap hblank hnextCore hlower hupper hsource hdestination
    hshrink hmove hraw

/-! ## Positive conditional-decrement schedule -/

/-- Every shift in a positive-decrement suffix resolves.  A successful
suffix returns the exact decremented tape together with its unchanged outer
backing; a failed constituent search halts the complete controller from the
schedule entry. -/
theorem machine_reaches_decrementSchedule_or_halts
    (base : Nat) (c : Nat.Partrec.Code) (source : Nat)
    (register : Register)
    {spec : Spec numTags} {T outer : FullTM0.Tape (Symbol numTags)}
    (hback : BackedBy spec T outer)
    (hpositive : 0 < spec.registers.get register)
    (hshort : ShortResolves base c spec.outerDistance)
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
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨spec.growth, source, secondarySearchBase⟩,
          atLogical spec.growth T
            (boundaryOffset spec.registers
              (MarkerSchedule.decrementStartBoundary register))⟩ := by
  let runner : DecrementScheduleRunner base c (ShortResolves base c)
      (FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)) := {
    pullback := FullTM0.HaltsFrom.of_reaches
    first := by
      intro limit hshort counterState searchSlot success hlimit spec T h next i
        hpositive hnextCore hlower hupper hsource hdestination hshrink hmove
        hraw
      exact machine_reaches_decrementFirst_or_halts base c limit hshort
        counterState searchSlot success hlimit h next i hpositive hnextCore
        hlower hupper hsource hdestination hshrink hmove hraw
    following := by
      intro limit hshort counterState searchSlot success spec T h next i
        hpositive hdistance hnextCore hlower hupper hsource hdestination
        hshrink hmove hraw
      exact machine_reaches_decrementFollowing_or_halts base c limit hshort
        counterState searchSlot success h next i hpositive hdistance hnextCore
        hlower hupper hsource hdestination hshrink hmove hraw }
  exact machine_reaches_decrementSchedule_with base c (ShortResolves base c)
    (FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)) runner
    source register hback hpositive hshort hcommands

/-- Exact positive branch of a compiled conditional decrement.  Every
shorter search either completes the decremented logical frame or exposes a
halt from the instruction entry. -/
theorem machine_reaches_decrementPositiveInstruction_or_halts
    (base : Nat) (c : Nat.Partrec.Code) (source ifZero ifPositive : Nat)
    (register : Register)
    (hrule : (source, .decrement register ifZero ifPositive) ∈
      GlobalSourceProgram.program)
    {spec : Spec numTags}
    {T outer : FullTM0.Tape (Symbol numTags)}
    (hback : BackedBy spec T outer)
    (hpositive : 0 < spec.registers.get register)
    (hshort : ShortResolves base c spec.outerDistance) :
    (FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨logicalState base c spec.growth source,
          atLogical spec.growth T (layoutEnd spec.registers)⟩
        ⟨logicalState base c spec.growth ifPositive,
          atLogical spec.growth (decrementTape spec register T)
            (layoutEnd (spec.registers.decrement register))⟩ ∧
      BackedBy (decrementSpec spec register hpositive)
        (decrementTape spec register T) outer) ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨logicalState base c spec.growth source,
          atLogical spec.growth T (layoutEnd spec.registers)⟩ := by
  have h := hback.represents
  have hvalidation := machine_reaches_validation_or_halts base c spec.growth
    source (.decrement register ifZero ifPositive) hrule h rfl hshort
  have hroute := machine_reaches_decrementToTest_or_halts base c source
    ifZero ifPositive register hrule h hshort
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
  have hschedule := machine_reaches_decrementSchedule_or_halts base c source
    register hback hpositive hshort hcommands
  have hfinish := machine_reaches_decrementPositiveFinish base c source
    ifZero ifPositive register hrule T hpositive
  have hscheduleFinish :
      FullTM0.Reaches (CounterControlNestingBridge.machine base c)
          ⟨searchState base c
              ⟨spec.growth, source, secondarySearchBase⟩,
            atLogical spec.growth T
              (boundaryOffset spec.registers
                (MarkerSchedule.decrementStartBoundary register))⟩
          ⟨logicalState base c spec.growth ifPositive,
            atLogical spec.growth (decrementTape spec register T)
              (layoutEnd (spec.registers.decrement register))⟩ ∨
        FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
          ⟨searchState base c
              ⟨spec.growth, source, secondarySearchBase⟩,
            atLogical spec.growth T
              (boundaryOffset spec.registers
                (MarkerSchedule.decrementStartBoundary register))⟩ := by
    rcases hschedule with hschedule | hhalts
    · exact Or.inl (hschedule.1.trans hfinish)
    · exact Or.inr hhalts
  have hrun := FullTM0.ResolvesTo.trans hvalidation
    (FullTM0.ResolvesTo.trans hroute
      (FullTM0.ResolvesTo.trans (Or.inl htest)
        (FullTM0.ResolvesTo.trans (Or.inl hhandoff) hscheduleFinish)))
  exact FullTM0.ResolvesTo.and_right hrun
    (decrementTape_backedBy hback register hpositive)

/-! ## Abstract-step interface -/

/-- Successful concrete realization of an abstract counter configuration.
The existential core bound packages exactly the updated frame specification
needed by the next simultaneous-induction step. -/
def LogicalStepReached
    (base : Nat) (c : Nat.Partrec.Code)
    (source : Nat) (next : CounterMachine.Cfg)
    (spec : Spec numTags) (T outer : FullTM0.Tape (Symbol numTags)) : Prop :=
  ∃ (hcore : layoutEnd next.registers < spec.outerDistance)
      (nextTape : FullTM0.Tape (Symbol numTags)),
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨logicalState base c spec.growth source,
          atLogical spec.growth T (layoutEnd spec.registers)⟩
        ⟨logicalState base c spec.growth next.state,
          atLogical spec.growth nextTape (layoutEnd next.registers)⟩ ∧
      BackedBy (updateSpec spec next.registers hcore) nextTape outer

/-- Concrete boundary exposed when a requested increment collides with the
suspended outer target instead of producing a larger logical frame. -/
def IncrementCollisionReached
    (base : Nat) (c : Nat.Partrec.Code) (source : Nat)
    (spec : Spec numTags) (T : FullTM0.Tape (Symbol numTags)) : Prop :=
  ∃ (register : Register) (next : Nat),
    (source, .increment register next) ∈ GlobalSourceProgram.program ∧
      layoutEnd spec.registers + 1 = spec.outerDistance ∧
      FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨logicalState base c spec.growth source,
          atLogical spec.growth T (layoutEnd spec.registers)⟩
        ⟨resolve base c (directRef spec.growth source testDirectSlot),
          atLogical spec.growth
            (CounterControlCleanupSemantics.afterFour spec T)
            spec.outerDistance⟩

/-- Uniform instruction-case API below the framed trace layer.  A defined
abstract step either reaches its exact backed successor, exposes the unique
increment-collision cleanup endpoint, or halts from the original logical
configuration. -/
theorem machine_resolves_counterStep
    (base : Nat) (c : Nat.Partrec.Code)
    (cfg nextCfg : CounterMachine.Cfg)
    {spec : Spec numTags}
    {T outer : FullTM0.Tape (Symbol numTags)}
    (hback : BackedBy spec T outer)
    (hregisters : cfg.registers = spec.registers)
    (hstep : CounterMachine.step GlobalSourceProgram.program cfg =
      some nextCfg)
    (hshort : ShortResolves base c spec.outerDistance) :
    LogicalStepReached base c cfg.state nextCfg spec T outer ∨
      IncrementCollisionReached base c cfg.state spec T ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨logicalState base c spec.growth cfg.state,
          atLogical spec.growth T (layoutEnd spec.registers)⟩ := by
  rcases cfg with ⟨source, registers⟩
  change registers = spec.registers at hregisters
  subst registers
  have hcase := CounterControlStepGeometry.stepCase_of_step_eq_some hstep
  cases hcase with
  | increment register target hlookup hnext =>
      subst nextCfg
      have hrule := CounterProgram.rule_mem_of_lookupInstruction_eq_some
        hlookup
      rcases increment_has_room_or_collision spec register with
        hroom | hcollision
      · have hrun := machine_reaches_incrementInstruction_or_halts base c
          source target register hrule hback hroom hshort
        rcases hrun with hsuccess | hhalts
        · left
          refine ⟨hroom, incrementTape spec register T, hsuccess.1, ?_⟩
          simpa [incrementSpec] using hsuccess.2
        · exact Or.inr (Or.inr hhalts)
      · have hcollision' :
            layoutEnd spec.registers + 1 = spec.outerDistance :=
          (increment_collision_iff spec register).1 hcollision
        have hrun := machine_reaches_incrementCollisionInstruction_or_halts
          base c source target register hrule hback.represents hcollision'
          hshort
        rcases hrun with hsuccess | hhalts
        · exact Or.inr (Or.inl
            ⟨register, target, hrule, hcollision', hsuccess⟩)
        · exact Or.inr (Or.inr hhalts)
  | decrementZero register ifZero ifPositive hlookup hzero hnext =>
      subst nextCfg
      have hrule := CounterProgram.rule_mem_of_lookupInstruction_eq_some
        hlookup
      have hrun := machine_reaches_decrementZeroInstruction_or_halts base c
        source ifZero ifPositive register hrule hback hzero hshort
      rcases hrun with hsuccess | hhalts
      · left
        refine ⟨spec.core_before_target, T, hsuccess.1, ?_⟩
        simpa [updateSpec] using hsuccess.2
      · exact Or.inr (Or.inr hhalts)
  | decrementPositive register ifZero ifPositive hlookup hpositive hnext =>
      subst nextCfg
      have hrule := CounterProgram.rule_mem_of_lookupInstruction_eq_some
        hlookup
      have hrun := machine_reaches_decrementPositiveInstruction_or_halts
        base c source ifZero ifPositive register hrule hback hpositive hshort
      rcases hrun with hsuccess | hhalts
      · left
        let hcore := CounterControlStepGeometry.decrement_has_room spec
          register hpositive
        refine ⟨hcore, decrementTape spec register T, hsuccess.1, ?_⟩
        simpa [decrementSpec] using hsuccess.2
      · exact Or.inr (Or.inr hhalts)

/-- The complete compiled counter controller resolves one abstract step in
every represented nested frame.  The three outcomes are exactly those used
by the generic trace lifting layer: a backed logical successor, restoration
of the suspended search boundary, or concrete halting. -/
theorem oneStepResolves
    (base : Nat) (c : Nat.Partrec.Code)
    (frame : Frame (Symbol numTags) CounterControlSearchSystem.Search)
    (hshort : ShortResolves base c frame.distance) :
    CounterControlTraceSimulation.OneStepResolves base c frame := by
  intro current next concrete hstep hlogical
  rcases hlogical with
    ⟨hcore, T, hback, rfl, _hstate, hframe⟩
  let spec := CounterControlFrameSimulation.activeSpec base c frame
    current.registers hcore
  change BackedBy spec T frame.outer at hback
  have hrun := machine_resolves_counterStep base c current next
    (spec := spec) hback
    (by simp [spec]) hstep
    (by simpa [spec] using hshort)
  rcases hrun with hnext | hcollision | hhalts
  · rcases hnext with ⟨hnextCore, nextTape, hreach, hnextBack⟩
    have hnextCore' : layoutEnd next.registers < frame.distance := by
      simpa [spec] using hnextCore
    have hnextBack' : BackedBy
        (CounterControlFrameSimulation.activeSpec base c frame
          next.registers hnextCore') nextTape frame.outer := by
      simpa [spec, CounterControlFrameSimulation.activeSpec, updateSpec] using
        hnextBack
    let nextConcrete := CounterControlFrameSimulation.logicalCfg base c frame
      next nextTape
    have hnextFrame : CounterControlFrameSimulation.LogicalFrame base c frame
        next nextConcrete := by
      exact ⟨hnextCore', nextTape, hnextBack', rfl,
        CounterControlAbstractTrace.state_lt_logicalSpan_of_step hstep,
        hframe⟩
    left
    refine ⟨nextConcrete, ?_, hnextFrame⟩
    simpa [nextConcrete, CounterControlFrameSimulation.logicalCfg, spec,
      CounterControlFrameSimulation.activeSpec] using hreach
  · rcases hcollision with
      ⟨register, target, hrule, hcollision, hcollisionReach⟩
    have hentry : CounterControlCleanupSemantics.cleanupEntryRule
        spec.growth current.state ∈ rawDirectRules := by
      apply directRule_mem_rawDirectRules_of_rule spec.growth hrule
      change CounterControlCleanupSemantics.cleanupEntryRule
          spec.growth current.state ∈
        validationRules spec.growth current.state ++
          incrementRules spec.growth current.state target register
      apply List.mem_append_right
      simp [CounterControlCleanupSemantics.cleanupEntryRule, incrementRules]
    have hcleanupCommands : ∀ raw,
        raw ∈ cleanupCommands spec.growth current.state →
          raw ∈ rawCommands := by
      intro raw hraw
      apply command_mem_rawCommands_of_rule spec.growth hrule
      simp [commandsForRule, incrementCommands, hraw]
    have hreturnDirection :
        (compileCommand base c spec.returnTag).searchDirection =
          spec.growth := by
      simp [spec, CounterControlFrameSimulation.activeSpec,
        CounterControlFrameSimulation.frameGrowth,
        CounterControlSearchSystem.command]
    have hcleanup := machine_reaches_collisionCleanup_or_halts base c
      current.state hback hreturnDirection hcollision
      (by simpa [spec] using hshort) hentry hcleanupCommands
    have hcombined := FullTM0.ResolvesTo.trans (Or.inl hcollisionReach)
      hcleanup
    rcases hcombined with hboundaryReach | hhalts
    · let boundary : FullTM0.Cfg (Symbol numTags) FiniteTM0.State :=
        ⟨resumeState (CanonicalInitializer.radius c)
            (CounterControlSearchSystem.commandOffset base c frame.saved),
          frame.outer⟩
      have hboundary : CounterControlSearchSystem.BoundaryAt base c frame
          boundary := ⟨hframe, rfl⟩
      right
      left
      refine ⟨boundary, ?_, hboundary⟩
      simpa [boundary, CounterControlFrameSimulation.logicalCfg, spec,
        CounterControlFrameSimulation.activeSpec,
        CounterControlSearchSystem.command,
        CounterControlSearchSystem.commandOffset] using hboundaryReach
    · right
      right
      simpa [CounterControlFrameSimulation.logicalCfg, spec,
        CounterControlFrameSimulation.activeSpec] using hhalts
  · right
    right
    simpa [CounterControlFrameSimulation.logicalCfg, spec,
      CounterControlFrameSimulation.activeSpec] using hhalts

end

end CounterControlInstructionResolution
end Hooper
end Kari
end LeanWang
