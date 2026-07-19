/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlCanonicalOpenMortality
import LeanWang.Kari.Hooper.CounterControlInstructionResolution

/-!
# Resolving validation and increments on a target-free open counter core

The finite-frame instruction theorems use `FramedMarkerTape.Represents`,
whose far matching target is needed for the outer Hooper induction.  A
logical instruction on the top-level open core should never inspect such a
target: each of its bounded searches is between two of the five represented
counter boundaries, while an outward increment writes into the infinite
blank runway.

This file develops the target-free validation sweep and increment branch.  It
rebuilds the route geometry from `CoreRepresents` alone and feeds the genuine
internal search gaps to the resolving Basic Lemma.  Thus every validation
search either reaches its represented boundary or exposes a concrete halt;
no finite outer target and no locality limit argument is used.  Decrement
resolution continues in `CounterControlOpenDecrementResolution`.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlOpenInstructionResolution

open Turing CounterMachine
open BoundedMarkerProgram FramedMarkerTape FramedCounterGeometry
open CounterControlPlan CounterControlCoreFrame
open CounterControlCoreRoutes
open CounterControlTagFreeOpen
open CounterControlInstructionSemantics
open CounterControlInstructionResolution
open CounterControlSearchResolution
open CounterControlScheduleSemantics
open CounterControlBridge

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-- A bookkeeping specification one cell beyond an open core.  Its target
and tag are never asserted to occur on the tape; it is used only to
instantiate local theorems whose statements carry a `Spec` for coordinates. -/
def openSpec (registers : Registers) (growth : Turing.Dir) : Spec numTags where
  growth := growth
  returnTag := CounterControlOpenSimulation.rootSearch
  registers := registers
  outerDistance := layoutEnd registers + 1
  outerTarget := .anyTag
  core_before_target := by omega

/-! ## Target-free primitive boundary updates -/

/-- Moving one represented boundary right has a core-only proof independent
of whether its blank runway is finite or infinite. -/
theorem moveRight_core
    {current next : Registers} {growth : Turing.Dir}
    {T : FullTM0.Tape (Symbol numTags)}
    (h : CoreRepresents current growth T) (label : Fin 5)
    (hlower : layoutEnd current ≤ layoutEnd next)
    (hupper : layoutEnd next ≤ layoutEnd current + 1)
    (hsource : boundaryOffset current label ≤ layoutEnd current)
    (htarget : boundaryOffset current label + 1 ≤ layoutEnd next)
    (hextend : layoutEnd current < layoutEnd next →
      boundaryOffset current label + 1 = layoutEnd next)
    (hmove : MarkerMachine.moveAt .right
        (MarkerTape.canonicalTape current)
        (MarkerTape.boundaryPosition current label) label =
      MarkerTape.canonicalTape next) :
    let U := writeLogical growth
      (writeLogical growth T (boundaryOffset current label) blankSymbol)
      (boundaryOffset current label + 1) (boundarySymbol label)
    U = installCore next growth T ∧ CoreRepresents next growth U := by
  let source := boundaryOffset current label
  let U := writeLogical growth
    (writeLogical growth T source blankSymbol)
    (source + 1) (boundarySymbol label)
  have hsourcePositive : 0 < source := by
    simp [source, boundaryOffset]
  have hU (position : Int) :
      logicalTape growth U position =
        if position = source + 1 then boundarySymbol label
        else if position = source then blankSymbol
        else logicalTape growth T position := by
    simpa only [U, logicalTape_writeLogical_apply, Nat.cast_add, Nat.cast_one]
  have hrep : CoreRepresents next growth U := by
    constructor
    intro position hposition
    change logicalTape growth U (position + 1) = coreSymbol next position
    rw [hU, coreSymbol_of_moveAt_right current next label hmove]
    have hsourcePosition :
        (position : Int) + 1 = (source : Nat) ↔
          position = CounterLayout.boundaryPos
            (RegisterLayout.values current) label := by
      simp only [source, boundaryOffset]
      constructor <;> intro heq <;> exact_mod_cast (by omega : _)
    have htargetPosition :
        (position : Int) + 1 = (source : Int) + 1 ↔
          position = CounterLayout.boundaryPos
            (RegisterLayout.values current) label + 1 := by
      simp only [source, boundaryOffset]
      constructor <;> intro heq <;> exact_mod_cast (by omega : _)
    simp only [htargetPosition, hsourcePosition]
    by_cases htargetMarker : position = CounterLayout.boundaryPos
        (RegisterLayout.values current) label + 1
    · simp [htargetMarker]
    by_cases hsourceMarker : position = CounterLayout.boundaryPos
        (RegisterLayout.values current) label
    · simp [hsourceMarker, htargetMarker]
    · simp only [htargetMarker, hsourceMarker, ↓reduceIte]
      apply h.core position
      by_contra hold
      have hpast : RegisterLayout.clockBoundary current < position :=
        Nat.lt_of_not_ge hold
      have hstrictEnds : layoutEnd current < layoutEnd next := by
        simp only [layoutEnd] at hposition hpast ⊢
        omega
      have hnextEnd : layoutEnd next = layoutEnd current + 1 := by omega
      have hpositionEnd : position + 1 = layoutEnd next := by
        simp only [layoutEnd] at hposition hpast hnextEnd ⊢
        omega
      have hsourceEnd := hextend hstrictEnds
      apply htargetMarker
      simp only [source, boundaryOffset] at hsourceEnd
      omega
  have houtside : ∀ position : Int,
      ¬(1 ≤ position ∧ position ≤ layoutEnd next) →
        logicalTape growth T position = logicalTape growth U position := by
    intro position houtside
    rw [hU]
    have hsourceNe : position ≠ (source : Int) := by
      intro heq
      apply houtside
      rw [heq]
      constructor
      · exact_mod_cast hsourcePositive
      · exact_mod_cast hsource.trans hlower
    have htargetNe : position ≠ (source : Int) + 1 := by
      intro heq
      apply houtside
      rw [heq]
      constructor
      · omega
      · exact_mod_cast htarget
    simp [hsourceNe, htargetNe]
  have hinstall := installCore_congr_of_outside next growth T U houtside
  have hself : installCore next growth U = U :=
    installCore_eq_self_of_coreRepresents hrep
  exact ⟨hself.symm.trans hinstall.symm, hrep⟩

/-- Moving one represented boundary right and rewriting its old and new
cells produces exactly the core-only installation of the supplied next
register tuple.  The proof uses the infinite runway instead of a finite
outer target. -/
theorem moveRight_coreOpen
    {current next : Registers} {growth : Turing.Dir}
    {T : FullTM0.Tape (Symbol numTags)}
    (h : CoreOpenRepresents current growth T) (label : Fin 5)
    (hlower : layoutEnd current ≤ layoutEnd next)
    (hupper : layoutEnd next ≤ layoutEnd current + 1)
    (hsource : boundaryOffset current label ≤ layoutEnd current)
    (htarget : boundaryOffset current label + 1 ≤ layoutEnd next)
    (hextend : layoutEnd current < layoutEnd next →
      boundaryOffset current label + 1 = layoutEnd next)
    (hmove : MarkerMachine.moveAt .right
        (MarkerTape.canonicalTape current)
        (MarkerTape.boundaryPosition current label) label =
      MarkerTape.canonicalTape next) :
    let U := writeLogical growth
      (writeLogical growth T (boundaryOffset current label) blankSymbol)
      (boundaryOffset current label + 1) (boundarySymbol label)
    U = installCore next growth T ∧
      CoreOpenRepresents next growth U := by
  let source := boundaryOffset current label
  let U := writeLogical growth
    (writeLogical growth T source blankSymbol)
    (source + 1) (boundarySymbol label)
  rcases moveRight_core h.toCoreRepresents label hlower hupper hsource
      htarget hextend hmove with ⟨hinstall, hcore⟩
  refine ⟨hinstall, hcore, ?_⟩
  intro position hpast
  change logicalTape growth U position = blankSymbol
  simp only [U, logicalTape_writeLogical_apply, Nat.cast_add, Nat.cast_one]
  have hneTarget : (position : Int) ≠ (source : Int) + 1 := by
    intro heq
    have heqNat : position = source + 1 := by exact_mod_cast heq
    omega
  have hneSource : (position : Int) ≠ (source : Nat) := by
    intro heq
    have heqNat : position = source := by exact_mod_cast heq
    omega
  simp only [hneTarget, hneSource, ↓reduceIte]
  exact h.runway position (hlower.trans_lt hpast)

/-- Moving one represented boundary left has a core-only proof independent
of whether its blank runway is finite or infinite. -/
theorem moveLeft_core
    {current next : Registers} {growth : Turing.Dir}
    {T : FullTM0.Tape (Symbol numTags)}
    (h : CoreRepresents current growth T) (label : Fin 5)
    (hlower : layoutEnd next ≤ layoutEnd current)
    (hsourcePositive : 1 < boundaryOffset current label)
    (hdestination : boundaryOffset current label - 1 ≤ layoutEnd next)
    (hmove : MarkerMachine.moveAt .left
        (MarkerTape.canonicalTape current)
        (MarkerTape.boundaryPosition current label) label =
      MarkerTape.canonicalTape next) :
    let source := boundaryOffset current label
    let cleared := writeLogical growth T source blankSymbol
    let U := writeLogical growth cleared (source - 1) (boundarySymbol label)
    U = installCore next growth cleared ∧ CoreRepresents next growth U := by
  let source := boundaryOffset current label
  let destination := source - 1
  let cleared := writeLogical growth T source blankSymbol
  let U := writeLogical growth cleared destination (boundarySymbol label)
  have hdestinationPositive : 0 < destination := by
    simp only [destination]
    omega
  have hmarkerPositive : 0 < CounterLayout.boundaryPos
      (RegisterLayout.values current) label := by
    simp only [source, boundaryOffset] at hsourcePositive
    omega
  have hU (position : Int) :
      logicalTape growth U position =
        if position = destination then boundarySymbol label
        else if position = source then blankSymbol
        else logicalTape growth T position := by
    simpa only [U, cleared, logicalTape_writeLogical_apply]
  have hrep : CoreRepresents next growth U := by
    constructor
    intro position hposition
    change logicalTape growth U (position + 1) = coreSymbol next position
    rw [hU, coreSymbol_of_moveAt_left current next label
      hmarkerPositive hmove]
    have hsourcePosition :
        (position : Int) + 1 = (source : Int) ↔
          position = CounterLayout.boundaryPos
            (RegisterLayout.values current) label := by
      simp only [source, boundaryOffset]
      constructor <;> intro heq <;> exact_mod_cast (by omega : _)
    have hdestinationPosition :
        (position : Int) + 1 = (destination : Int) ↔
          position + 1 = CounterLayout.boundaryPos
            (RegisterLayout.values current) label := by
      simp only [destination, source, boundaryOffset]
      constructor
      · intro heq
        have hcast : (position : Int) + 1 =
            CounterLayout.boundaryPos
              (RegisterLayout.values current) label := by
          push_cast at heq
          omega
        exact_mod_cast hcast
      · intro heq
        have hcast : (position : Int) + 1 =
            CounterLayout.boundaryPos
              (RegisterLayout.values current) label := by
          exact_mod_cast heq
        push_cast
        omega
    simp only [hdestinationPosition, hsourcePosition]
    by_cases hdestinationMarker : position + 1 =
        CounterLayout.boundaryPos (RegisterLayout.values current) label
    · simp [hdestinationMarker]
    by_cases hsourceMarker : position =
        CounterLayout.boundaryPos (RegisterLayout.values current) label
    · simp [hsourceMarker, hdestinationMarker]
    · simp only [hdestinationMarker, hsourceMarker, ↓reduceIte]
      apply h.core position
      simp only [layoutEnd] at hlower hposition
      omega
  have houtside : ∀ position : Int,
      ¬(1 ≤ position ∧ position ≤ layoutEnd next) →
        logicalTape growth cleared position = logicalTape growth U position := by
    intro position houtside
    simp only [U, logicalTape_writeLogical_apply]
    have hdestinationNe : position ≠ (destination : Int) := by
      intro heq
      apply houtside
      rw [heq]
      constructor
      · exact_mod_cast hdestinationPositive
      · exact_mod_cast hdestination
    simp [hdestinationNe]
  have hinstall := installCore_congr_of_outside next growth cleared U houtside
  have hself : installCore next growth U = U :=
    installCore_eq_self_of_coreRepresents hrep
  exact ⟨hself.symm.trans hinstall.symm, hrep⟩

/-- Moving a represented boundary left and clearing its old cell produces the
exact core-only installation over that cleared backing tape.  This also
covers the final boundary-`4` move, whose old cell becomes the first runway
blank. -/
theorem moveLeft_coreOpen
    {current next : Registers} {growth : Turing.Dir}
    {T : FullTM0.Tape (Symbol numTags)}
    (h : CoreOpenRepresents current growth T) (label : Fin 5)
    (hlower : layoutEnd next ≤ layoutEnd current)
    (hupper : layoutEnd current ≤ layoutEnd next + 1)
    (hsourcePositive : 1 < boundaryOffset current label)
    (hsource : boundaryOffset current label ≤ layoutEnd current)
    (hdestination : boundaryOffset current label - 1 ≤ layoutEnd next)
    (hshrink : layoutEnd next < layoutEnd current →
      boundaryOffset current label = layoutEnd current)
    (hmove : MarkerMachine.moveAt .left
        (MarkerTape.canonicalTape current)
        (MarkerTape.boundaryPosition current label) label =
      MarkerTape.canonicalTape next) :
    let source := boundaryOffset current label
    let cleared := writeLogical growth T source blankSymbol
    let U := writeLogical growth cleared (source - 1) (boundarySymbol label)
    U = installCore next growth cleared ∧ CoreOpenRepresents next growth U := by
  let source := boundaryOffset current label
  let destination := source - 1
  let cleared := writeLogical growth T source blankSymbol
  let U := writeLogical growth cleared destination (boundarySymbol label)
  rcases moveLeft_core h.toCoreRepresents label hlower hsourcePositive
      hdestination hmove with ⟨hinstall, hcore⟩
  refine ⟨hinstall, hcore, ?_⟩
  intro position hpast
  change logicalTape growth U position = blankSymbol
  simp only [U, cleared, logicalTape_writeLogical_apply]
  by_cases hsourcePosition : position = source
  · have hsourceInt : (position : Int) = (source : Int) := by
      exact_mod_cast hsourcePosition
    have hdestinationInt : (position : Int) ≠ (destination : Int) := by
      intro heq
      have : source = destination := by
        exact_mod_cast hsourceInt.symm.trans heq
      omega
    rw [if_neg hdestinationInt, if_pos hsourceInt]
  · have hdestinationNe : (position : Int) ≠ (destination : Int) := by
      intro heq
      have heqNat : position = destination := by exact_mod_cast heq
      omega
    have hsourceNe : (position : Int) ≠ (source : Int) := by
      exact_mod_cast hsourcePosition
    simp only [hdestinationNe, hsourceNe, ↓reduceIte]
    apply h.runway position
    by_contra hold
    have hpositionLe : position ≤ layoutEnd current :=
      Nat.le_of_not_gt hold
    have hstrict : layoutEnd next < layoutEnd current := by omega
    have hsourceEnd := hshrink hstrict
    apply hsourcePosition
    omega

/-! ## Internal routes from the tag-free core -/

/-- The converse Basic Lemma resolves every finite compiled search distance,
so it supplies `ShortResolves` at any chosen geometric limit. -/
theorem shortResolves_all (base : Nat) (c : Nat.Partrec.Code)
    (limit : Nat) :
    ShortResolves base c limit := by
  intro distance _hdistance
  exact CounterControlFiniteConverse.resolves_all base c distance
/-! ## Target-free validation resolution -/

/-- The mandatory validation sweep of any compiled instruction reaches its
body or a genuine finite internal search exposes a halt.  In particular, a
well-formed open logical entry cannot enter a no-target launch during
validation. -/
theorem machine_reaches_validation_or_halts_of_core
    (base : Nat) (c : Nat.Partrec.Code) (growth : Turing.Dir)
    (source : Nat) (instruction : CounterMachine.Instruction)
    (hrule : (source, instruction) ∈ GlobalSourceProgram.program)
    {registers : Registers} {T : FullTM0.Tape (Symbol numTags)}
    (h : CoreRepresents registers growth T) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨logicalState base c growth source,
          atLogical growth T (layoutEnd registers)⟩
        ⟨resolve base c (bodyEntry growth source instruction),
          atLogical growth T (layoutEnd registers)⟩ ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨logicalState base c growth source,
          atLogical growth T (layoutEnd registers)⟩ := by
  let limit := layoutEnd registers + 1
  have hlimit : layoutEnd registers < limit := by
    simp [limit]
  have hcommands : ∀ raw,
      raw ∈ validationCommands growth source instruction →
        raw ∈ rawCommands := by
    intro raw hraw
    apply command_mem_rawCommands_of_rule growth hrule
    cases instruction <;> simp [commandsForRule, hraw]
  have hrules : ∀ raw,
      raw ∈ validationRules growth source →
        raw ∈ rawDirectRules := by
    intro raw hraw
    apply directRule_mem_rawDirectRules_of_rule growth hrule
    cases instruction <;> simp [directRulesForRule, hraw]
  have hroute := route_reaches_or_halts_at_of_ne_nil base c limit
    (shortResolves_all base c limit)
    growth source validationSearchBase validationDirectBase
    (.logical growth source) (bodyEntry growth source instruction)
    4 MarkerValidation.sweep (by simp [MarkerValidation.sweep]) T
    (layoutEnd registers) (layoutEnd registers)
    h.read_boundary_four
    (validation_executesWithin_of_core h hlimit)
    (by intro raw hraw; exact hcommands raw (by
      simpa [validationCommands, MarkerValidation.sweep] using hraw))
    (by intro raw hraw; exact hrules raw (by
      simpa [validationRules, MarkerValidation.sweep] using hraw))
  simpa [validationCommands, validationRules, logicalState,
    CounterControlPlan.resolve] using hroute

/-! ## Target-free outward shifts -/

/-- Shift boundary `4` one cell into the infinite blank runway. -/
theorem machine_reaches_incrementClock_or_halts_of_open
    (base : Nat) (c : Nat.Partrec.Code) (source searchSlot : Nat)
    (success : ControlRef) (collision : Option ControlRef)
    {registers : Registers} {growth : Turing.Dir}
    {T : FullTM0.Tape (Symbol numTags)}
    (h : CoreOpenRepresents registers growth T)
    (hraw : RawCommand.markerShift
      ⟨growth, source, searchSlot⟩ 4 .left .right success
      (some .left) collision ∈ rawCommands) :
    (FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨growth, source, searchSlot⟩,
          atLogical growth T (layoutEnd registers)⟩
        ⟨resolve base c success,
          atLogical growth
            (incrementCoreTape registers growth .clock T)
            (layoutEnd registers)⟩ ∧
      CoreOpenRepresents (registers.increment .clock) growth
        (incrementCoreTape registers growth .clock T)) ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨growth, source, searchSlot⟩,
          atLogical growth T (layoutEnd registers)⟩ := by
  let next := registers.increment .clock
  let limit := layoutEnd next + 1
  let U := writeLogical growth
    (writeLogical growth T (layoutEnd registers) blankSymbol)
    (layoutEnd registers + 1) (boundarySymbol 4)
  have hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary 4).Matches
      (atLogical growth T (layoutEnd registers))
      (OrientedMarkerTape.orientDirection growth .left) 0 := by
    rw [SearchGap.zero]
    exact h.read_boundary_four
  have hblank : logicalTape growth T (layoutEnd registers + 1) =
      blankSymbol :=
    h.runway (layoutEnd registers + 1) (Nat.lt_succ_self _)
  have hrun := machine_reaches_incrementShift_or_halts base c limit
    (shortResolves_all base c limit) growth source searchSlot
    (layoutEnd registers) 4 success collision hraw T 0
    (by simp [limit]) hgap hblank
  rcases hrun with hrun | hhalts
  · left
    have hmove : MarkerMachine.moveAt .right
        (MarkerTape.canonicalTape registers)
        (MarkerTape.boundaryPosition registers 4) 4 =
        MarkerTape.canonicalTape next := by
      rw [MarkerMachine.moveAt_clock_eq_incrementTape]
      exact MarkerShift.incrementTape_canonical registers .clock
    have hnormalized := moveRight_coreOpen h 4
      (next := next)
      (by simp [next, layoutEnd_increment])
      (by simp [next, layoutEnd_increment])
      (boundaryOffset_four registers |>.le)
      (by simp [next, boundaryOffset_four, layoutEnd_increment])
      (by intro _; simp [next, boundaryOffset_four, layoutEnd_increment])
      hmove
    have hU : U = incrementCoreTape registers growth .clock T := by
      simpa [U, next, incrementCoreTape] using hnormalized.1
    refine ⟨?_, ?_⟩
    · simpa [U, hU] using hrun
    · rw [← hU]
      exact hnormalized.2
  · exact Or.inr hhalts

/-- Shift an internal represented boundary right.  The search is a genuine
adjacent-boundary gap and the endpoint is the exact core-only installation
of `next` over the input tape. -/
theorem machine_reaches_incrementInternal_or_halts_of_open
    (base : Nat) (c : Nat.Partrec.Code) (limit : Nat)
    (counterState searchSlot : Nat)
    (success : ControlRef) (collision : Option ControlRef)
    {current next : Registers} {growth : Turing.Dir}
    {T : FullTM0.Tape (Symbol numTags)}
    (h : CoreOpenRepresents current growth T) (i : Fin 4)
    (hpositive : 0 < RegisterLayout.values current i)
    (hdistance : RegisterLayout.values current i < limit)
    (hlower : layoutEnd current ≤ layoutEnd next)
    (hupper : layoutEnd next ≤ layoutEnd current + 1)
    (hsameEnd : layoutEnd next = layoutEnd current)
    (hmove : MarkerMachine.moveAt .right
        (MarkerTape.canonicalTape current)
        (MarkerTape.boundaryPosition current i.castSucc) i.castSucc =
      MarkerTape.canonicalTape next)
    (hraw : RawCommand.markerShift
      ⟨growth, counterState, searchSlot⟩ i.castSucc .left .right
      success (some .left) collision ∈ rawCommands) :
    (FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨growth, counterState, searchSlot⟩,
          atLogical growth T (lastGapOffset current i)⟩
        ⟨resolve base c success,
          atLogical growth (installCore next growth T)
            (boundaryOffset current i.castSucc)⟩ ∧
      CoreOpenRepresents next growth (installCore next growth T)) ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨growth, counterState, searchSlot⟩,
          atLogical growth T (lastGapOffset current i)⟩ := by
  let shiftSource := boundaryOffset current i.castSucc
  let distance := RegisterLayout.values current i
  let U := writeLogical growth
    (writeLogical growth T shiftSource blankSymbol) (shiftSource + 1)
      (boundarySymbol i.castSucc)
  have hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary i.castSucc).Matches
      (atLogical growth T (lastGapOffset current i))
      (OrientedMarkerTape.orientDirection growth .left) distance := by
    change SearchGap (fun symbol => symbol = blankSymbol)
      (fun symbol => symbol = boundarySymbol i.castSucc) _ _ _
    exact h.searchGap_adjacent_left i
  have hstart : lastGapOffset current i = shiftSource + distance :=
    lastGapOffset_eq_boundaryOffset_add_value current i
  have hblank : logicalTape growth T (shiftSource + 1) = blankSymbol := by
    have hgapBlank := h.gap_blank i 0 hpositive
    have hcoordinate : shiftSource + 1 = firstGapOffset current i := by
      simp [shiftSource, firstGapOffset, boundaryOffset]
    have hcoordinateInt : (shiftSource : Int) + 1 =
        firstGapOffset current i := by
      exact_mod_cast hcoordinate
    rw [hcoordinateInt]
    simpa using hgapBlank
  have hrun := machine_reaches_incrementShift_or_halts base c limit
    (shortResolves_all base c limit) growth counterState searchSlot
    shiftSource i.castSucc success collision hraw T distance hdistance
    (by simpa [hstart] using hgap) hblank
  rcases hrun with hrun | hhalts
  · left
    have hsourceBound : shiftSource ≤ layoutEnd current := by
      change CounterLayout.boundaryPos
          (RegisterLayout.values current) i + 1 ≤
        CounterLayout.boundaryPos (RegisterLayout.values current) 4 + 1
      apply Nat.add_le_add_right
      exact CounterLayout.boundaryPos_mono
        (RegisterLayout.values current) (by omega)
    have htargetBound : shiftSource + 1 ≤ layoutEnd next := by
      rw [hsameEnd]
      have hnext := CounterLayout.boundaryPos_succ
        (RegisterLayout.values current) i
      change CounterLayout.boundaryPos
          (RegisterLayout.values current) i + 1 + 1 ≤
        CounterLayout.boundaryPos (RegisterLayout.values current) 4 + 1
      have hmono := CounterLayout.boundaryPos_mono
        (RegisterLayout.values current) (by omega : (i : Nat) + 1 ≤ 4)
      omega
    have hnormalized := moveRight_coreOpen h i.castSucc
      (next := next) hlower hupper hsourceBound htargetBound
      (by intro hlt; omega) hmove
    have hU : U = installCore next growth T := by
      simpa [U, shiftSource] using hnormalized.1
    refine ⟨?_, ?_⟩
    · simpa [U, hU, hstart] using hrun
    · rw [← hU]
      exact hnormalized.2
  · right
    simpa [hstart] using hhalts

/-! ## The target-free increment schedule -/

/-- Operational interface shared by open and finite-prefix increment
schedules.  Both representations supply the same clock and internal shifts;
only their runway invariant differs. -/
structure IncrementEnvelope (growth : Turing.Dir) (limit : Nat) where
  Represents : Registers → FullTM0.Tape (Symbol numTags) → Prop
  core_before_limit : ∀ {registers T}, Represents registers T →
    layoutEnd registers < limit
  increment : ∀ {registers T} (register : Register),
    Represents registers T → layoutEnd (registers.increment register) < limit →
      Represents (registers.increment register)
        (incrementCoreTape registers growth register T)
  clock : ∀ (base : Nat) (c : Nat.Partrec.Code)
      (source searchSlot : Nat) (success : ControlRef)
      (collision : Option ControlRef)
      {registers : Registers} {T : FullTM0.Tape (Symbol numTags)},
      Represents registers T →
      layoutEnd (registers.increment .clock) < limit →
      RawCommand.markerShift
        ⟨growth, source, searchSlot⟩ 4 .left .right success
        (some .left) collision ∈ rawCommands →
      (FullTM0.Reaches (CounterControlNestingBridge.machine base c)
          ⟨searchState base c ⟨growth, source, searchSlot⟩,
            atLogical growth T (layoutEnd registers)⟩
          ⟨resolve base c success,
            atLogical growth
              (incrementCoreTape registers growth .clock T)
              (layoutEnd registers)⟩ ∧
        Represents (registers.increment .clock)
          (incrementCoreTape registers growth .clock T)) ∨
        FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
          ⟨searchState base c ⟨growth, source, searchSlot⟩,
            atLogical growth T (layoutEnd registers)⟩
  internal : ∀ (base : Nat) (c : Nat.Partrec.Code)
      (counterState searchSlot : Nat) (success : ControlRef)
      (collision : Option ControlRef)
      {current next : Registers} {T : FullTM0.Tape (Symbol numTags)},
      Represents current T → ∀ (i : Fin 4),
      0 < RegisterLayout.values current i →
      RegisterLayout.values current i < limit →
      layoutEnd current ≤ layoutEnd next →
      layoutEnd next ≤ layoutEnd current + 1 →
      layoutEnd next = layoutEnd current →
      MarkerMachine.moveAt .right
          (MarkerTape.canonicalTape current)
          (MarkerTape.boundaryPosition current i.castSucc) i.castSucc =
        MarkerTape.canonicalTape next →
      RawCommand.markerShift
        ⟨growth, counterState, searchSlot⟩ i.castSucc .left .right
        success (some .left) collision ∈ rawCommands →
      (FullTM0.Reaches (CounterControlNestingBridge.machine base c)
          ⟨searchState base c ⟨growth, counterState, searchSlot⟩,
            atLogical growth T (lastGapOffset current i)⟩
          ⟨resolve base c success,
            atLogical growth (installCore next growth T)
              (boundaryOffset current i.castSucc)⟩ ∧
        Represents next (installCore next growth T)) ∨
        FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
          ⟨searchState base c ⟨growth, counterState, searchSlot⟩,
            atLogical growth T (lastGapOffset current i)⟩

/-- Every collision-free increment schedule has the same controller trace
under any increment envelope. -/
theorem machine_reaches_incrementSchedule_or_halts_of_envelope
    (base : Nat) (c : Nat.Partrec.Code) (source : Nat)
    (register : Register)
    {registers : Registers} {growth : Turing.Dir} {limit : Nat}
    {T : FullTM0.Tape (Symbol numTags)}
    (E : IncrementEnvelope growth limit) (h : E.Represents registers T)
    (hroom : layoutEnd (registers.increment register) < limit)
    (hcommands : ∀ raw,
      raw ∈ incrementShiftCommands growth source register →
        raw ∈ rawCommands) :
    (FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨growth, source, bodySearchBase⟩,
          atLogical growth T (layoutEnd registers)⟩
        ⟨resolve base c (directRef growth source bodyDirectBase),
          atLogical growth (incrementCoreTape registers growth register T)
            (boundaryOffset registers
              (MarkerSchedule.decrementStartBoundary register))⟩ ∧
      E.Represents (registers.increment register)
        (incrementCoreTape registers growth register T)) ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨growth, source, bodySearchBase⟩,
          atLogical growth T (layoutEnd registers)⟩ := by
  have hfinal (r : Register) :
      E.Represents (registers.increment r)
        (incrementCoreTape registers growth r T) :=
    E.increment r h (by simpa [layoutEnd_increment] using hroom)
  cases register with
  | clock =>
      have hraw : RawCommand.markerShift
          ⟨growth, source, bodySearchBase⟩ 4 .left .right
          (directRef growth source bodyDirectBase) (some .left)
          (some (directRef growth source testDirectSlot)) ∈ rawCommands := by
        apply hcommands
        simp [incrementShiftCommands, incrementShiftCommandsAux,
          MarkerShift.incrementOrder]
      simpa [MarkerSchedule.decrementStartBoundary] using
        E.clock base c source
          bodySearchBase (directRef growth source bodyDirectBase)
          (some (directRef growth source testDirectSlot)) h (by simpa [layoutEnd_increment] using hroom) hraw
  | temp =>
      let clockRegisters := registers.increment .clock
      let tempRegisters := registers.increment .temp
      let clockTape := incrementCoreTape registers growth .clock T
      let tempTape := incrementCoreTape registers growth .temp T
      have hclockPrefix :
          E.Represents clockRegisters clockTape := by
        simpa [clockRegisters, clockTape] using hfinal .clock
      have hrawFour : RawCommand.markerShift
          ⟨growth, source, bodySearchBase⟩ 4 .left .right
          (searchRef growth source (bodySearchBase + 1)) (some .left)
          (some (directRef growth source testDirectSlot)) ∈ rawCommands := by
        apply hcommands
        simp [incrementShiftCommands, incrementShiftCommandsAux,
          MarkerShift.incrementOrder]
      have hrawThree : RawCommand.markerShift
          ⟨growth, source, bodySearchBase + 1⟩ 3 .left .right
          (directRef growth source bodyDirectBase) (some .left) none ∈
            rawCommands := by
        apply hcommands
        simp [incrementShiftCommands, incrementShiftCommandsAux,
          MarkerShift.incrementOrder]
      have hfour := E.clock base c
        source bodySearchBase (searchRef growth source (bodySearchBase + 1))
        (some (directRef growth source testDirectSlot)) h (by simpa [layoutEnd_increment] using hroom) hrawFour
      have hthree := E.internal
        (next := tempRegisters) base c
        source (bodySearchBase + 1)
        (directRef growth source bodyDirectBase) none hclockPrefix (3 : Fin 4)
        (by simp [clockRegisters, RegisterLayout.values, Registers.increment,
          Registers.set, Registers.get])
        (by
          have hbound := E.core_before_limit h
          simp [clockRegisters, layoutEnd, CounterLayout.boundaryPos,
            RegisterLayout.clockBoundary_eq, RegisterLayout.values,
            Registers.increment, Registers.set, Registers.get] at hbound ⊢
          omega)
        (by simp [clockRegisters, tempRegisters, layoutEnd_increment])
        (by simp [clockRegisters, tempRegisters, layoutEnd_increment])
        (by simp [clockRegisters, tempRegisters, layoutEnd_increment])
        (by simpa [clockRegisters, tempRegisters] using
          MarkerSchedule.moveTempBoundary_after_clock registers)
        hrawThree
      have hhead : layoutEnd registers = lastGapOffset clockRegisters 3 := by
        simp [clockRegisters, lastGapOffset, boundaryOffset,
          CounterLayout.boundaryPos, layoutEnd,
          RegisterLayout.clockBoundary_eq, RegisterLayout.values,
          Registers.increment, Registers.set, Registers.get] <;> omega
      have htape : installCore tempRegisters growth clockTape = tempTape := by
        simpa [clockRegisters, tempRegisters, clockTape, tempTape] using
          installCore_incrementCoreTape_eq registers growth .clock .temp T
      rw [htape] at hthree
      have hfinish : boundaryOffset clockRegisters ((3 : Fin 4).castSucc) =
          boundaryOffset registers 3 := by
        simp [clockRegisters, boundaryOffset, CounterLayout.boundaryPos,
          RegisterLayout.values, Registers.increment, Registers.set,
          Registers.get] <;> omega
      rw [← hhead, hfinish] at hthree
      simp only [searchRef, CounterControlPlan.resolve] at hfour hthree
      have hrun := FullTM0.ResolvesTo.trans
        (hfour.imp (fun hsuccess => hsuccess.1) id)
        (hthree.imp (fun hsuccess => hsuccess.1) id)
      rcases hrun with hrun | hhalts
      · exact Or.inl ⟨hrun, hfinal .temp⟩
      · exact Or.inr hhalts
  | right =>
      let clockRegisters := registers.increment .clock
      let tempRegisters := registers.increment .temp
      let rightRegisters := registers.increment .right
      let clockTape := incrementCoreTape registers growth .clock T
      let tempTape := incrementCoreTape registers growth .temp T
      let rightTape := incrementCoreTape registers growth .right T
      have hclockPrefix :
          E.Represents clockRegisters clockTape := by
        simpa [clockRegisters, clockTape] using hfinal .clock
      have htempPrefix :
          E.Represents tempRegisters tempTape := by
        simpa [tempRegisters, tempTape] using hfinal .temp
      have hrawFour : RawCommand.markerShift
          ⟨growth, source, bodySearchBase⟩ 4 .left .right
          (searchRef growth source (bodySearchBase + 1)) (some .left)
          (some (directRef growth source testDirectSlot)) ∈ rawCommands := by
        apply hcommands
        simp [incrementShiftCommands, incrementShiftCommandsAux,
          MarkerShift.incrementOrder]
      have hrawThree : RawCommand.markerShift
          ⟨growth, source, bodySearchBase + 1⟩ 3 .left .right
          (searchRef growth source (bodySearchBase + 2)) (some .left) none ∈
            rawCommands := by
        apply hcommands
        simp [incrementShiftCommands, incrementShiftCommandsAux,
          MarkerShift.incrementOrder]
      have hrawTwo : RawCommand.markerShift
          ⟨growth, source, bodySearchBase + 2⟩ 2 .left .right
          (directRef growth source bodyDirectBase) (some .left) none ∈
            rawCommands := by
        apply hcommands
        simp [incrementShiftCommands, incrementShiftCommandsAux,
          MarkerShift.incrementOrder]
      have hfour := E.clock base c
        source bodySearchBase (searchRef growth source (bodySearchBase + 1))
        (some (directRef growth source testDirectSlot)) h (by simpa [layoutEnd_increment] using hroom) hrawFour
      have hthree := E.internal
        (next := tempRegisters) base c
        source (bodySearchBase + 1)
        (searchRef growth source (bodySearchBase + 2)) none hclockPrefix
        (3 : Fin 4)
        (by simp [clockRegisters, RegisterLayout.values, Registers.increment,
          Registers.set, Registers.get])
        (by
          have hbound := E.core_before_limit h
          simp [clockRegisters, layoutEnd, CounterLayout.boundaryPos,
            RegisterLayout.clockBoundary_eq, RegisterLayout.values,
            Registers.increment, Registers.set, Registers.get] at hbound ⊢
          omega)
        (by simp [clockRegisters, tempRegisters, layoutEnd_increment])
        (by simp [clockRegisters, tempRegisters, layoutEnd_increment])
        (by simp [clockRegisters, tempRegisters, layoutEnd_increment])
        (by simpa [clockRegisters, tempRegisters] using
          MarkerSchedule.moveTempBoundary_after_clock registers)
        hrawThree
      have htwo := E.internal
        (next := rightRegisters) base c
        source (bodySearchBase + 2)
        (directRef growth source bodyDirectBase) none htempPrefix (2 : Fin 4)
        (by simp [tempRegisters, RegisterLayout.values, Registers.increment,
          Registers.set, Registers.get])
        (by
          have hbound := E.core_before_limit h
          simp [tempRegisters, layoutEnd, CounterLayout.boundaryPos,
            RegisterLayout.clockBoundary_eq, RegisterLayout.values,
            Registers.increment, Registers.set, Registers.get] at hbound ⊢
          omega)
        (by simp [tempRegisters, rightRegisters, layoutEnd_increment])
        (by simp [tempRegisters, rightRegisters, layoutEnd_increment])
        (by simp [tempRegisters, rightRegisters, layoutEnd_increment])
        (by simpa [tempRegisters, rightRegisters] using
          MarkerSchedule.moveRightBoundary_after_temp registers)
        hrawTwo
      have hheadFour : layoutEnd registers =
          lastGapOffset clockRegisters 3 := by
        simp [clockRegisters, lastGapOffset, boundaryOffset,
          CounterLayout.boundaryPos, layoutEnd,
          RegisterLayout.clockBoundary_eq, RegisterLayout.values,
          Registers.increment, Registers.set, Registers.get] <;> omega
      have hheadThree : boundaryOffset clockRegisters 3 =
          lastGapOffset tempRegisters 2 := by
        simp [clockRegisters, tempRegisters, lastGapOffset, boundaryOffset,
          CounterLayout.boundaryPos, RegisterLayout.values,
          Registers.increment, Registers.set, Registers.get] <;> omega
      have htapeThree : installCore tempRegisters growth clockTape =
          tempTape := by
        simpa [clockRegisters, tempRegisters, clockTape, tempTape] using
          installCore_incrementCoreTape_eq registers growth .clock .temp T
      rw [htapeThree] at hthree
      have htapeTwo : installCore rightRegisters growth tempTape =
          rightTape := by
        simpa [tempRegisters, rightRegisters, tempTape, rightTape] using
          installCore_incrementCoreTape_eq registers growth .temp .right T
      rw [htapeTwo] at htwo
      have hhandoffThree :
          boundaryOffset clockRegisters ((3 : Fin 4).castSucc) =
            lastGapOffset tempRegisters 2 := by
        simpa using hheadThree
      have hfinish :
          boundaryOffset tempRegisters ((2 : Fin 4).castSucc) =
            boundaryOffset registers 2 := by
        simp [tempRegisters, boundaryOffset, CounterLayout.boundaryPos,
          RegisterLayout.values, Registers.increment, Registers.set,
          Registers.get] <;> omega
      rw [← hheadFour, hhandoffThree] at hthree
      rw [hfinish] at htwo
      simp only [searchRef, CounterControlPlan.resolve] at hfour hthree
      have hrun := FullTM0.ResolvesTo.trans
        (hfour.imp (fun hsuccess => hsuccess.1) id)
        (FullTM0.ResolvesTo.trans
          (hthree.imp (fun hsuccess => hsuccess.1) id)
          (htwo.imp (fun hsuccess => hsuccess.1) id))
      rcases hrun with hrun | hhalts
      · exact Or.inl ⟨hrun, hfinal .right⟩
      · exact Or.inr hhalts
  | left =>
      let clockRegisters := registers.increment .clock
      let tempRegisters := registers.increment .temp
      let rightRegisters := registers.increment .right
      let leftRegisters := registers.increment .left
      let clockTape := incrementCoreTape registers growth .clock T
      let tempTape := incrementCoreTape registers growth .temp T
      let rightTape := incrementCoreTape registers growth .right T
      let leftTape := incrementCoreTape registers growth .left T
      have hclockPrefix :
          E.Represents clockRegisters clockTape := by
        simpa [clockRegisters, clockTape] using hfinal .clock
      have htempPrefix :
          E.Represents tempRegisters tempTape := by
        simpa [tempRegisters, tempTape] using hfinal .temp
      have hrightPrefix :
          E.Represents rightRegisters rightTape := by
        simpa [rightRegisters, rightTape] using hfinal .right
      have hrawFour : RawCommand.markerShift
          ⟨growth, source, bodySearchBase⟩ 4 .left .right
          (searchRef growth source (bodySearchBase + 1)) (some .left)
          (some (directRef growth source testDirectSlot)) ∈ rawCommands := by
        apply hcommands
        simp [incrementShiftCommands, incrementShiftCommandsAux,
          MarkerShift.incrementOrder]
      have hrawThree : RawCommand.markerShift
          ⟨growth, source, bodySearchBase + 1⟩ 3 .left .right
          (searchRef growth source (bodySearchBase + 2)) (some .left) none ∈
            rawCommands := by
        apply hcommands
        simp [incrementShiftCommands, incrementShiftCommandsAux,
          MarkerShift.incrementOrder]
      have hrawTwo : RawCommand.markerShift
          ⟨growth, source, bodySearchBase + 2⟩ 2 .left .right
          (searchRef growth source (bodySearchBase + 3)) (some .left) none ∈
            rawCommands := by
        apply hcommands
        simp [incrementShiftCommands, incrementShiftCommandsAux,
          MarkerShift.incrementOrder]
      have hrawOne : RawCommand.markerShift
          ⟨growth, source, bodySearchBase + 3⟩ 1 .left .right
          (directRef growth source bodyDirectBase) (some .left) none ∈
            rawCommands := by
        apply hcommands
        simp [incrementShiftCommands, incrementShiftCommandsAux,
          MarkerShift.incrementOrder]
      have hfour := E.clock base c
        source bodySearchBase (searchRef growth source (bodySearchBase + 1))
        (some (directRef growth source testDirectSlot)) h (by simpa [layoutEnd_increment] using hroom) hrawFour
      have hthree := E.internal
        (next := tempRegisters) base c
        source (bodySearchBase + 1)
        (searchRef growth source (bodySearchBase + 2)) none hclockPrefix
        (3 : Fin 4)
        (by simp [clockRegisters, RegisterLayout.values, Registers.increment,
          Registers.set, Registers.get])
        (by
          have hbound := E.core_before_limit h
          simp [clockRegisters, layoutEnd, CounterLayout.boundaryPos,
            RegisterLayout.clockBoundary_eq, RegisterLayout.values,
            Registers.increment, Registers.set, Registers.get] at hbound ⊢
          omega)
        (by simp [clockRegisters, tempRegisters, layoutEnd_increment])
        (by simp [clockRegisters, tempRegisters, layoutEnd_increment])
        (by simp [clockRegisters, tempRegisters, layoutEnd_increment])
        (by simpa [clockRegisters, tempRegisters] using
          MarkerSchedule.moveTempBoundary_after_clock registers)
        hrawThree
      have htwo := E.internal
        (next := rightRegisters) base c
        source (bodySearchBase + 2)
        (searchRef growth source (bodySearchBase + 3)) none htempPrefix
        (2 : Fin 4)
        (by simp [tempRegisters, RegisterLayout.values, Registers.increment,
          Registers.set, Registers.get])
        (by
          have hbound := E.core_before_limit h
          simp [tempRegisters, layoutEnd, CounterLayout.boundaryPos,
            RegisterLayout.clockBoundary_eq, RegisterLayout.values,
            Registers.increment, Registers.set, Registers.get] at hbound ⊢
          omega)
        (by simp [tempRegisters, rightRegisters, layoutEnd_increment])
        (by simp [tempRegisters, rightRegisters, layoutEnd_increment])
        (by simp [tempRegisters, rightRegisters, layoutEnd_increment])
        (by simpa [tempRegisters, rightRegisters] using
          MarkerSchedule.moveRightBoundary_after_temp registers)
        hrawTwo
      have hone := E.internal
        (next := leftRegisters) base c
        source (bodySearchBase + 3)
        (directRef growth source bodyDirectBase) none hrightPrefix (1 : Fin 4)
        (by simp [rightRegisters, RegisterLayout.values, Registers.increment,
          Registers.set, Registers.get])
        (by
          have hbound := E.core_before_limit h
          simp [rightRegisters, layoutEnd, CounterLayout.boundaryPos,
            RegisterLayout.clockBoundary_eq, RegisterLayout.values,
            Registers.increment, Registers.set, Registers.get] at hbound ⊢
          omega)
        (by simp [rightRegisters, leftRegisters, layoutEnd_increment])
        (by simp [rightRegisters, leftRegisters, layoutEnd_increment])
        (by simp [rightRegisters, leftRegisters, layoutEnd_increment])
        (by simpa [rightRegisters, leftRegisters] using
          MarkerSchedule.moveLeftBoundary_after_right registers)
        hrawOne
      have hheadFour : layoutEnd registers =
          lastGapOffset clockRegisters 3 := by
        simp [clockRegisters, lastGapOffset, boundaryOffset,
          CounterLayout.boundaryPos, layoutEnd,
          RegisterLayout.clockBoundary_eq, RegisterLayout.values,
          Registers.increment, Registers.set, Registers.get] <;> omega
      have hheadThree : boundaryOffset clockRegisters 3 =
          lastGapOffset tempRegisters 2 := by
        simp [clockRegisters, tempRegisters, lastGapOffset, boundaryOffset,
          CounterLayout.boundaryPos, RegisterLayout.values,
          Registers.increment, Registers.set, Registers.get] <;> omega
      have hheadTwo : boundaryOffset tempRegisters 2 =
          lastGapOffset rightRegisters 1 := by
        simp [tempRegisters, rightRegisters, lastGapOffset, boundaryOffset,
          CounterLayout.boundaryPos, RegisterLayout.values,
          Registers.increment, Registers.set, Registers.get] <;> omega
      have htapeThree : installCore tempRegisters growth clockTape =
          tempTape := by
        simpa [clockRegisters, tempRegisters, clockTape, tempTape] using
          installCore_incrementCoreTape_eq registers growth .clock .temp T
      rw [htapeThree] at hthree
      have htapeTwo : installCore rightRegisters growth tempTape =
          rightTape := by
        simpa [tempRegisters, rightRegisters, tempTape, rightTape] using
          installCore_incrementCoreTape_eq registers growth .temp .right T
      rw [htapeTwo] at htwo
      have htapeOne : installCore leftRegisters growth rightTape =
          leftTape := by
        simpa [rightRegisters, leftRegisters, rightTape, leftTape] using
          installCore_incrementCoreTape_eq registers growth .right .left T
      rw [htapeOne] at hone
      have hhandoffThree :
          boundaryOffset clockRegisters ((3 : Fin 4).castSucc) =
            lastGapOffset tempRegisters 2 := by
        simpa using hheadThree
      have hhandoffTwo :
          boundaryOffset tempRegisters ((2 : Fin 4).castSucc) =
            lastGapOffset rightRegisters 1 := by
        simpa using hheadTwo
      have hfinish :
          boundaryOffset rightRegisters ((1 : Fin 4).castSucc) =
            boundaryOffset registers 1 := by
        simp [rightRegisters, boundaryOffset, CounterLayout.boundaryPos,
          RegisterLayout.values, Registers.increment, Registers.set,
          Registers.get] <;> omega
      rw [← hheadFour, hhandoffThree] at hthree
      rw [hhandoffTwo] at htwo
      rw [hfinish] at hone
      simp only [searchRef, CounterControlPlan.resolve] at hfour hthree htwo
      have hrun := FullTM0.ResolvesTo.trans
        (hfour.imp (fun hsuccess => hsuccess.1) id)
        (FullTM0.ResolvesTo.trans
          (hthree.imp (fun hsuccess => hsuccess.1) id)
          (FullTM0.ResolvesTo.trans
            (htwo.imp (fun hsuccess => hsuccess.1) id)
            (hone.imp (fun hsuccess => hsuccess.1) id)))
      rcases hrun with hrun | hhalts
      · exact Or.inl ⟨hrun, hfinal .left⟩
      · exact Or.inr hhalts


/-- Every shift in a collision-free increment schedule resolves on an open
core.  The arbitrary finite `limit` used by the converse Basic Lemma is chosen
past the updated core; it is not asserted to contain a target. -/
theorem machine_reaches_incrementSchedule_or_halts_of_open
    (base : Nat) (c : Nat.Partrec.Code) (source : Nat)
    (register : Register)
    {registers : Registers} {growth : Turing.Dir}
    {T : FullTM0.Tape (Symbol numTags)}
    (h : CoreOpenRepresents registers growth T)
    (hcommands : ∀ raw,
      raw ∈ incrementShiftCommands growth source register →
        raw ∈ rawCommands) :
    (FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨growth, source, bodySearchBase⟩,
          atLogical growth T (layoutEnd registers)⟩
        ⟨resolve base c (directRef growth source bodyDirectBase),
          atLogical growth (incrementCoreTape registers growth register T)
            (boundaryOffset registers
              (MarkerSchedule.decrementStartBoundary register))⟩ ∧
      CoreOpenRepresents (registers.increment register) growth
        (incrementCoreTape registers growth register T)) ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨growth, source, bodySearchBase⟩,
          atLogical growth T (layoutEnd registers)⟩ := by
  let limit := layoutEnd registers + 2
  let E : IncrementEnvelope growth limit := {
    Represents := fun current U =>
      CoreOpenRepresents current growth U ∧ layoutEnd current < limit
    core_before_limit := fun h => h.2
    increment := by
      intro current U r h hroom
      exact ⟨incrementCoreTape_preserves_open h.1 r, hroom⟩
    clock := by
      intro base c source searchSlot success collision current U h hroom hraw
      exact (machine_reaches_incrementClock_or_halts_of_open base c source
        searchSlot success collision h.1 hraw).imp
          (fun result => ⟨result.1, result.2, hroom⟩) id
    internal := by
      intro base c counterState searchSlot success collision current next U h i
        hpositive hdistance hlower hupper hsameEnd hmove hraw
      have hbound : layoutEnd next < limit := by
        rw [hsameEnd]
        exact h.2
      exact (machine_reaches_incrementInternal_or_halts_of_open base c limit
        counterState searchSlot success collision h.1 i hpositive hdistance
        hlower hupper hsameEnd hmove hraw).imp
          (fun result => ⟨result.1, result.2, hbound⟩) id }
  have hE : E.Represents registers T := by
    exact ⟨h, by simp [E, limit]⟩
  have hroom : layoutEnd (registers.increment register) < limit := by
    simp [limit, layoutEnd_increment]
  exact (machine_reaches_incrementSchedule_or_halts_of_envelope base c source
    register E hE hroom hcommands).imp
      (fun result => ⟨result.1, result.2.1⟩) id

/-- The direct blank rule following the increment schedule moves onto the
shifted boundary and chooses the recovery route (or the logical successor for
the clock register). -/
theorem machine_reaches_incrementHandoff_of_source_blank
    (base : Nat) (c : Nat.Partrec.Code) (source next : Nat)
    (register : Register)
    (hrule : (source, .increment register next) ∈
      GlobalSourceProgram.program)
    {registers : Registers} {growth : Turing.Dir}
    {T : FullTM0.Tape (Symbol numTags)}
    (hsource : logicalTape growth T
      (boundaryOffset registers
        (MarkerSchedule.decrementStartBoundary register)) = blankSymbol) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      ⟨resolve base c (directRef growth source bodyDirectBase),
        atLogical growth T
          (boundaryOffset registers
            (MarkerSchedule.decrementStartBoundary register))⟩
      ⟨resolve base c
          (match AnchoredCounterGeometry.routeFromIncrement register with
          | [] => .logical growth next
          | _ :: _ => directRef growth source (bodyDirectBase + 1)),
        atLogical growth T
          (boundaryOffset (registers.increment register)
            (MarkerSchedule.decrementStartBoundary register))⟩ := by
  let route := AnchoredCounterGeometry.routeFromIncrement register
  let afterShift : ControlRef := match route with
    | [] => .logical growth next
    | _ :: _ => directRef growth source (bodyDirectBase + 1)
  let raw : RawDirectRule :=
    ⟨growth, directRef growth source bodyDirectBase, .blank,
      afterShift, .right⟩
  have hraw : raw ∈ rawDirectRules := by
    apply directRule_mem_rawDirectRules_of_rule growth hrule
    change raw ∈ validationRules growth source ++
      incrementRules growth source next register
    apply List.mem_append_right
    simp only [incrementRules, List.mem_append]
    apply Or.inl
    apply Or.inl
    apply Or.inl
    simp only [List.mem_singleton]
    exact rfl
  have hblank : raw.read.Matches
      (atLogical growth T
        (boundaryOffset registers
          (MarkerSchedule.decrementStartBoundary register))).read := by
    change (atLogical growth T
      (boundaryOffset registers
        (MarkerSchedule.decrementStartBoundary register))).read = blankSymbol
    rw [atLogical_read]
    exact hsource
  have hrun := CounterControlDirectSemantics.reaches_directRule base c raw
    hraw (atLogical growth T
      (boundaryOffset registers
        (MarkerSchedule.decrementStartBoundary register))) hblank
  have hcoord : boundaryOffset registers
        (MarkerSchedule.decrementStartBoundary register) + 1 =
      boundaryOffset (registers.increment register)
        (MarkerSchedule.decrementStartBoundary register) :=
    AnchoredCounterGeometry.incrementStartBoundary_add_one registers register
  rw [show orient growth .right =
    OrientedMarkerTape.orientDirection growth .right by
      exact orient_eq_orientDirection growth .right,
    atLogical_move_right, hcoord] at hrun
  change FullTM0.Reaches (CounterControlNestingBridge.machine base c)
    ⟨resolve base c (directRef growth source bodyDirectBase),
      atLogical growth T
        (boundaryOffset registers
          (MarkerSchedule.decrementStartBoundary register))⟩
    ⟨resolve base c
        (match AnchoredCounterGeometry.routeFromIncrement register with
        | [] => .logical growth next
        | _ :: _ => directRef growth source (bodyDirectBase + 1)),
      atLogical growth T
        (boundaryOffset (registers.increment register)
          (MarkerSchedule.decrementStartBoundary register))⟩ at hrun
  exact hrun

/-- Open-core specialization of the representation-independent increment
handoff. -/
theorem machine_reaches_incrementHandoff_of_open
    (base : Nat) (c : Nat.Partrec.Code) (source next : Nat)
    (register : Register)
    (hrule : (source, .increment register next) ∈
      GlobalSourceProgram.program)
    {registers : Registers} {growth : Turing.Dir}
    {T : FullTM0.Tape (Symbol numTags)}
    (h : CoreOpenRepresents registers growth T) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      ⟨resolve base c (directRef growth source bodyDirectBase),
        atLogical growth (incrementCoreTape registers growth register T)
          (boundaryOffset registers
            (MarkerSchedule.decrementStartBoundary register))⟩
      ⟨resolve base c
          (match AnchoredCounterGeometry.routeFromIncrement register with
          | [] => .logical growth next
          | _ :: _ => directRef growth source (bodyDirectBase + 1)),
        atLogical growth (incrementCoreTape registers growth register T)
          (boundaryOffset (registers.increment register)
            (MarkerSchedule.decrementStartBoundary register))⟩ := by
  apply machine_reaches_incrementHandoff_of_source_blank base c source next
    register hrule
  exact (incrementCoreTape_preserves_open h register).toCoreRepresents
    |>.increment_source_blank registers register

/-- The post-increment recovery route reaches boundary `4`, or a constituent
internal search halts. -/
theorem machine_reaches_incrementRecovery_or_halts_of_core
    (base : Nat) (c : Nat.Partrec.Code) (source next : Nat)
    (register : Register)
    (hrule : (source, .increment register next) ∈
      GlobalSourceProgram.program)
    {registers : Registers} {growth : Turing.Dir}
    {T : FullTM0.Tape (Symbol numTags)}
    (h : CoreRepresents registers growth T) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨resolve base c
            (match AnchoredCounterGeometry.routeFromIncrement register with
            | [] => .logical growth next
            | _ :: _ => directRef growth source (bodyDirectBase + 1)),
          atLogical growth T
            (boundaryOffset registers
              (MarkerSchedule.decrementStartBoundary register))⟩
        ⟨logicalState base c growth next,
          atLogical growth T (layoutEnd registers)⟩ ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨resolve base c
            (match AnchoredCounterGeometry.routeFromIncrement register with
            | [] => .logical growth next
            | _ :: _ => directRef growth source (bodyDirectBase + 1)),
          atLogical growth T
            (boundaryOffset registers
              (MarkerSchedule.decrementStartBoundary register))⟩ := by
  let limit := layoutEnd registers + 1
  have hlimit : layoutEnd registers < limit := by simp [limit]
  have hcommands : ∀ raw,
      raw ∈ routeCommandsAux growth source secondarySearchBase
          (bodyDirectBase + 2) (.logical growth next)
          (AnchoredCounterGeometry.routeFromIncrement register) →
        raw ∈ rawCommands := by
    intro raw hraw
    apply command_mem_rawCommands_of_rule growth hrule
    simp [commandsForRule, incrementCommands, hraw]
  have hrules : ∀ raw,
      raw ∈ routeEntryRules growth source
            (directRef growth source (bodyDirectBase + 1))
            (MarkerSchedule.decrementStartBoundary register)
            secondarySearchBase
            (AnchoredCounterGeometry.routeFromIncrement register) ++
          routeContinuationRules growth source secondarySearchBase
            (bodyDirectBase + 2)
            (AnchoredCounterGeometry.routeFromIncrement register) →
        raw ∈ rawDirectRules := by
    intro raw hraw
    apply directRule_mem_rawDirectRules_of_rule growth hrule
    change raw ∈ validationRules growth source ++
      incrementRules growth source next register
    apply List.mem_append_right
    rcases List.mem_append.mp hraw with hentry | hcontinuation
    · simp only [incrementRules, List.mem_append]
      exact Or.inl (Or.inl (Or.inr hentry))
    · simp only [incrementRules, List.mem_append]
      exact Or.inl (Or.inr hcontinuation)
  cases register with
  | clock => exact Or.inl Relation.ReflTransGen.refl
  | temp =>
      have hrun := route_reaches_or_halts_at_of_ne_nil base c limit
        (shortResolves_all base c limit)
        growth source secondarySearchBase (bodyDirectBase + 2)
        (directRef growth source (bodyDirectBase + 1))
        (.logical growth next) 3
        (AnchoredCounterGeometry.routeFromIncrement .temp)
        (by simp [AnchoredCounterGeometry.routeFromIncrement]) T
        (boundaryOffset registers 3) (layoutEnd registers)
        (by rw [atLogical_read]; exact h.boundary 3)
        (routeFromIncrement_executesWithin_of_core h hlimit .temp)
        (by intro raw hraw; exact hcommands raw hraw)
        (by intro raw hraw; exact hrules raw hraw)
      simpa [AnchoredCounterGeometry.routeFromIncrement, logicalState,
        CounterControlPlan.resolve,
        MarkerSchedule.decrementStartBoundary] using hrun
  | right =>
      have hrun := route_reaches_or_halts_at_of_ne_nil base c limit
        (shortResolves_all base c limit)
        growth source secondarySearchBase (bodyDirectBase + 2)
        (directRef growth source (bodyDirectBase + 1))
        (.logical growth next) 2
        (AnchoredCounterGeometry.routeFromIncrement .right)
        (by simp [AnchoredCounterGeometry.routeFromIncrement]) T
        (boundaryOffset registers 2) (layoutEnd registers)
        (by rw [atLogical_read]; exact h.boundary 2)
        (routeFromIncrement_executesWithin_of_core h hlimit .right)
        (by intro raw hraw; exact hcommands raw hraw)
        (by intro raw hraw; exact hrules raw hraw)
      simpa [AnchoredCounterGeometry.routeFromIncrement, logicalState,
        CounterControlPlan.resolve,
        MarkerSchedule.decrementStartBoundary] using hrun
  | left =>
      have hrun := route_reaches_or_halts_at_of_ne_nil base c limit
        (shortResolves_all base c limit)
        growth source secondarySearchBase (bodyDirectBase + 2)
        (directRef growth source (bodyDirectBase + 1))
        (.logical growth next) 1
        (AnchoredCounterGeometry.routeFromIncrement .left)
        (by simp [AnchoredCounterGeometry.routeFromIncrement]) T
        (boundaryOffset registers 1) (layoutEnd registers)
        (by rw [atLogical_read]; exact h.boundary 1)
        (routeFromIncrement_executesWithin_of_core h hlimit .left)
        (by intro raw hraw; exact hcommands raw hraw)
        (by intro raw hraw; exact hrules raw hraw)
      simpa [AnchoredCounterGeometry.routeFromIncrement, logicalState,
        CounterControlPlan.resolve,
        MarkerSchedule.decrementStartBoundary] using hrun

/-- Exact target-free semantics of a collision-free increment instruction. -/
theorem machine_reaches_incrementInstruction_or_halts_of_open
    (base : Nat) (c : Nat.Partrec.Code) (source next : Nat)
    (register : Register)
    (hrule : (source, .increment register next) ∈
      GlobalSourceProgram.program)
    {registers : Registers} {growth : Turing.Dir}
    {T : FullTM0.Tape (Symbol numTags)}
    (h : CoreOpenRepresents registers growth T) :
    (FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨logicalState base c growth source,
          atLogical growth T (layoutEnd registers)⟩
        ⟨logicalState base c growth next,
          atLogical growth (incrementCoreTape registers growth register T)
            (layoutEnd (registers.increment register))⟩ ∧
      CoreOpenRepresents (registers.increment register) growth
        (incrementCoreTape registers growth register T)) ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨logicalState base c growth source,
          atLogical growth T (layoutEnd registers)⟩ := by
  have hvalidation := machine_reaches_validation_or_halts_of_core base c growth
    source (.increment register next) hrule h.toCoreRepresents
  have hcommands : ∀ raw,
      raw ∈ incrementShiftCommands growth source register →
        raw ∈ rawCommands := by
    intro raw hraw
    apply command_mem_rawCommands_of_rule growth hrule
    simp [commandsForRule, incrementCommands, hraw]
  have hschedule := machine_reaches_incrementSchedule_or_halts_of_open base c
    source register h hcommands
  have hhandoff := machine_reaches_incrementHandoff_of_open base c source next
    register hrule h
  have hnext := incrementCoreTape_preserves_open h register
  have hrecovery := machine_reaches_incrementRecovery_or_halts_of_core base c
    source next register hrule hnext.toCoreRepresents
  have hvalidation' :
      FullTM0.Reaches (CounterControlNestingBridge.machine base c)
          ⟨logicalState base c growth source,
            atLogical growth T (layoutEnd registers)⟩
          ⟨searchState base c ⟨growth, source, bodySearchBase⟩,
            atLogical growth T (layoutEnd registers)⟩ ∨
        FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
          ⟨logicalState base c growth source,
            atLogical growth T (layoutEnd registers)⟩ := by
    simpa [bodyEntry, searchRef, CounterControlPlan.resolve] using hvalidation
  have hschedule' := hschedule.imp (fun hsuccess => hsuccess.1) id
  have hrun := FullTM0.ResolvesTo.trans hvalidation'
    (FullTM0.ResolvesTo.trans hschedule'
      (FullTM0.ResolvesTo.trans (Or.inl hhandoff) hrecovery))
  rcases hrun with hrun | hhalts
  · exact Or.inl ⟨hrun, hnext⟩
  · exact Or.inr hhalts

end

end CounterControlOpenInstructionResolution
end Hooper
end Kari
end LeanWang
