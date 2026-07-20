/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlOpenIncrementResolution
import LeanWang.Kari.Hooper.CounterControlDecrementSchedule

/-!
# Resolving decrements on a target-free open counter core

This module continues the open-core instruction semantics with the positive
and zero conditional-decrement branches and packages their abstract one-step
resolution laws.  It builds on the common validation and increment layer in
`CounterControlOpenIncrementResolution`.
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
/-! ## Target-free positive-decrement shifts -/

/-- One canonical inward shift resolves to an exact core-only installation
over the tape with its old source cell cleared, or the constituent search
halts. -/
theorem machine_reaches_decrementCanonical_or_halts_of_open
    (base : Nat) (c : Nat.Partrec.Code) (limit : Nat)
    (counterState searchSlot : Nat)
    (success : ControlRef) (collision : Option ControlRef)
    {current next : Registers} {growth : Turing.Dir}
    {T : FullTM0.Tape (Symbol numTags)}
    (h : CoreOpenRepresents current growth T) (label : Fin 5)
    (origin distance : Nat)
    (hsourcePositive : 1 < boundaryOffset current label)
    (horigin : origin + distance = boundaryOffset current label)
    (hdistance : distance < limit)
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary label).Matches (atLogical growth T origin)
      (OrientedMarkerTape.orientDirection growth .right) distance)
    (hblank : logicalTape growth T
      ((boundaryOffset current label - 1 : Nat) : Int) = blankSymbol)
    (hlower : layoutEnd next ≤ layoutEnd current)
    (hupper : layoutEnd current ≤ layoutEnd next + 1)
    (hsource : boundaryOffset current label ≤ layoutEnd current)
    (hdestination : boundaryOffset current label - 1 ≤ layoutEnd next)
    (hshrink : layoutEnd next < layoutEnd current →
      boundaryOffset current label = layoutEnd current)
    (hmove : MarkerMachine.moveAt .left
        (MarkerTape.canonicalTape current)
        (MarkerTape.boundaryPosition current label) label =
      MarkerTape.canonicalTape next)
    (hraw : RawCommand.markerShift
      ⟨growth, counterState, searchSlot⟩ label .right .left success
      (some .right) collision ∈ rawCommands) :
    (FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨growth, counterState, searchSlot⟩,
          atLogical growth T origin⟩
        ⟨resolve base c success,
          atLogical growth
            (installCore next growth
              (writeLogical growth T
                (boundaryOffset current label) blankSymbol))
            (boundaryOffset current label)⟩ ∧
      CoreOpenRepresents next growth
        (installCore next growth
          (writeLogical growth T
            (boundaryOffset current label) blankSymbol))) ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨growth, counterState, searchSlot⟩,
          atLogical growth T origin⟩ := by
  let source := boundaryOffset current label
  let destination := source - 1
  let cleared := writeLogical growth T source blankSymbol
  let U := writeLogical growth cleared destination (boundarySymbol label)
  have hposition : origin + distance = destination + 1 := by
    simp only [destination]
    omega
  have hsourceEq : destination + 1 = source := by
    simp only [destination]
    omega
  have hrun := machine_reaches_decrementShift_or_halts base c limit
    (shortResolves_all base c limit) growth counterState searchSlot origin
    destination distance label success collision hraw T hposition hdistance
    hgap (by simpa [source, destination] using hblank)
  rcases hrun with hrun | hhalts
  · left
    have hnormalized := moveLeft_coreOpen h label hlower hupper
      hsourcePositive hsource hdestination hshrink hmove
    have hU : U = installCore next growth cleared := by
      simpa [U, cleared, source, destination] using hnormalized.1
    rw [hsourceEq] at hrun
    change FullTM0.Reaches _ _
      ⟨resolve base c success, atLogical growth U source⟩ at hrun
    rw [hU] at hrun
    refine ⟨hrun, ?_⟩
    rw [← hU]
    exact hnormalized.2
  · exact Or.inr hhalts

/-- The first positive-decrement shift has search distance zero. -/
theorem machine_reaches_decrementFirst_or_halts_of_open
    (base : Nat) (c : Nat.Partrec.Code) (limit : Nat)
    (counterState searchSlot : Nat) (success : ControlRef)
    (hlimit : 0 < limit)
    {current next : Registers} {growth : Turing.Dir}
    {T : FullTM0.Tape (Symbol numTags)}
    (h : CoreOpenRepresents current growth T) (i : Fin 4)
    (hpositive : 0 < RegisterLayout.values current i)
    (hlower : layoutEnd next ≤ layoutEnd current)
    (hupper : layoutEnd current ≤ layoutEnd next + 1)
    (hsource : boundaryOffset current i.succ ≤ layoutEnd current)
    (hdestination : boundaryOffset current i.succ - 1 ≤ layoutEnd next)
    (hshrink : layoutEnd next < layoutEnd current →
      boundaryOffset current i.succ = layoutEnd current)
    (hmove : MarkerMachine.moveAt .left
        (MarkerTape.canonicalTape current)
        (MarkerTape.boundaryPosition current i.succ) i.succ =
      MarkerTape.canonicalTape next)
    (hraw : RawCommand.markerShift
      ⟨growth, counterState, searchSlot⟩ i.succ .right .left success
      (some .right) none ∈ rawCommands) :
    (FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨growth, counterState, searchSlot⟩,
          atLogical growth T (boundaryOffset current i.succ)⟩
        ⟨resolve base c success,
          atLogical growth
            (installCore next growth
              (writeLogical growth T
                (boundaryOffset current i.succ) blankSymbol))
            (boundaryOffset current i.succ)⟩ ∧
      CoreOpenRepresents next growth
        (installCore next growth
          (writeLogical growth T
            (boundaryOffset current i.succ) blankSymbol))) ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨growth, counterState, searchSlot⟩,
          atLogical growth T (boundaryOffset current i.succ)⟩ := by
  have hsourcePositive : 1 < boundaryOffset current i.succ := by
    simp [boundaryOffset]
  have hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary i.succ).Matches
      (atLogical growth T (boundaryOffset current i.succ))
      (OrientedMarkerTape.orientDirection growth .right) 0 := by
    rw [SearchGap.zero]
    change (atLogical growth T (boundaryOffset current i.succ)).read =
      boundarySymbol i.succ
    rw [atLogical_read]
    exact h.boundary i.succ
  have hblank : logicalTape growth T
      ((boundaryOffset current i.succ - 1 : Nat) : Int) = blankSymbol := by
    have hb := h.gap_blank i (RegisterLayout.values current i - 1) (by omega)
    have hcoord : (firstGapOffset current i : Int) +
        (RegisterLayout.values current i - 1 : Nat) =
        (boundaryOffset current i.succ - 1 : Nat) := by
      simp [firstGapOffset, boundaryOffset, CounterLayout.boundaryPos_succ]
      omega
    rw [hcoord] at hb
    exact hb
  apply machine_reaches_decrementCanonical_or_halts_of_open base c limit
    counterState searchSlot success none h i.succ
    (boundaryOffset current i.succ) 0 hsourcePositive
    (by simp) hlimit hgap hblank hlower hupper hsource hdestination hshrink
    hmove hraw

/-- Every later positive-decrement shift searches one represented gap. -/
theorem machine_reaches_decrementFollowing_or_halts_of_open
    (base : Nat) (c : Nat.Partrec.Code) (limit : Nat)
    (counterState searchSlot : Nat) (success : ControlRef)
    {current next : Registers} {growth : Turing.Dir}
    {T : FullTM0.Tape (Symbol numTags)}
    (h : CoreOpenRepresents current growth T) (i : Fin 4)
    (hpositive : 0 < RegisterLayout.values current i)
    (hdistance : RegisterLayout.values current i < limit)
    (hlower : layoutEnd next ≤ layoutEnd current)
    (hupper : layoutEnd current ≤ layoutEnd next + 1)
    (hsource : boundaryOffset current i.succ ≤ layoutEnd current)
    (hdestination : boundaryOffset current i.succ - 1 ≤ layoutEnd next)
    (hshrink : layoutEnd next < layoutEnd current →
      boundaryOffset current i.succ = layoutEnd current)
    (hmove : MarkerMachine.moveAt .left
        (MarkerTape.canonicalTape current)
        (MarkerTape.boundaryPosition current i.succ) i.succ =
      MarkerTape.canonicalTape next)
    (hraw : RawCommand.markerShift
      ⟨growth, counterState, searchSlot⟩ i.succ .right .left success
      (some .right) none ∈ rawCommands) :
    (FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨growth, counterState, searchSlot⟩,
          atLogical growth T (firstGapOffset current i)⟩
        ⟨resolve base c success,
          atLogical growth
            (installCore next growth
              (writeLogical growth T
                (boundaryOffset current i.succ) blankSymbol))
            (boundaryOffset current i.succ)⟩ ∧
      CoreOpenRepresents next growth
        (installCore next growth
          (writeLogical growth T
            (boundaryOffset current i.succ) blankSymbol))) ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨growth, counterState, searchSlot⟩,
          atLogical growth T (firstGapOffset current i)⟩ := by
  have hsourcePositive : 1 < boundaryOffset current i.succ := by
    simp [boundaryOffset]
  have horigin : firstGapOffset current i +
      RegisterLayout.values current i = boundaryOffset current i.succ := by
    simp [firstGapOffset, boundaryOffset, CounterLayout.boundaryPos_succ]
    omega
  have hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary i.succ).Matches
      (atLogical growth T (firstGapOffset current i))
      (OrientedMarkerTape.orientDirection growth .right)
      (RegisterLayout.values current i) := by
    change SearchGap (fun symbol => symbol = blankSymbol)
      (fun symbol => symbol = boundarySymbol i.succ) _ _ _
    exact h.searchGap_adjacent_right i
  have hblank : logicalTape growth T
      ((boundaryOffset current i.succ - 1 : Nat) : Int) = blankSymbol := by
    have hb := h.gap_blank i (RegisterLayout.values current i - 1) (by omega)
    have hcoord : (firstGapOffset current i : Int) +
        (RegisterLayout.values current i - 1 : Nat) =
        (boundaryOffset current i.succ - 1 : Nat) := by
      simp [firstGapOffset, boundaryOffset, CounterLayout.boundaryPos_succ]
      omega
    rw [hcoord] at hb
    exact hb
  exact machine_reaches_decrementCanonical_or_halts_of_open base c limit
    counterState searchSlot success none h i.succ
    (firstGapOffset current i) (RegisterLayout.values current i)
    hsourcePositive horigin hdistance hgap hblank hlower hupper hsource
    hdestination hshrink hmove hraw

/-- A cleared cell already covered by the new core is hidden by core-only
installation. -/
theorem installCore_write_inside
    (registers : Registers) (growth : Turing.Dir)
    (T : FullTM0.Tape (Symbol numTags)) (source : Nat)
    (hpositive : 0 < source) (hcore : source ≤ layoutEnd registers) :
    installCore registers growth
        (writeLogical growth T source blankSymbol) =
      installCore registers growth T := by
  apply installCore_congr_of_outside
  intro position houtside
  rw [logicalTape_writeLogical_apply]
  have hne : position ≠ (source : Int) := by
    intro heq
    apply houtside
    rw [heq]
    constructor
    · exact_mod_cast hpositive
    · exact_mod_cast hcore
  simp [hne]

/-- An internal left shift over an already installed core collapses to a
single installation over the original backing tape. -/
theorem installCore_after_internal_left
    (current next : Registers) (growth : Turing.Dir)
    (T : FullTM0.Tape (Symbol numTags)) (source : Nat)
    (hcurrent : layoutEnd current ≤ layoutEnd next)
    (hpositive : 0 < source) (hsource : source ≤ layoutEnd next) :
    installCore next growth
        (writeLogical growth (installCore current growth T) source blankSymbol) =
      installCore next growth T := by
  rw [installCore_write_inside next growth (installCore current growth T)
    source hpositive hsource]
  exact installCore_over_installCore current next growth T hcurrent

/-- Clearing the unique cell lost when the far boundary moves left commutes
with discarding the old core overlay. -/
theorem installCore_clear_old_overlay
    (current next : Registers) (growth : Turing.Dir)
    (T : FullTM0.Tape (Symbol numTags))
    (hend : layoutEnd next + 1 = layoutEnd current) :
    installCore next growth
        (writeLogical growth (installCore current growth T)
          (layoutEnd current) blankSymbol) =
      installCore next growth
        (writeLogical growth T (layoutEnd current) blankSymbol) := by
  apply installCore_congr_of_outside
  intro position houtside
  simp only [logicalTape_writeLogical_apply]
  by_cases hposition : position = (layoutEnd current : Int)
  · simp [hposition]
  · simp only [hposition, ↓reduceIte, logicalTape_installCore]
    unfold logicalCoreOverlay
    rw [if_neg]
    intro hcurrentCore
    apply houtside
    constructor
    · exact hcurrentCore.1
    · exact_mod_cast (by omega : (position : Int) ≤ layoutEnd next)

/-- Installing any core at least as long as an open represented core preserves
the infinite blank runway. -/
theorem installCore_open_of_extension
    {current next : Registers} {growth : Turing.Dir}
    {T : FullTM0.Tape (Symbol numTags)}
    (h : CoreOpenRepresents current growth T)
    (hle : layoutEnd current ≤ layoutEnd next) :
    CoreOpenRepresents next growth (installCore next growth T) := by
  constructor
  · constructor
    intro position hposition
    exact installCore_core next growth T position hposition
  · intro position hpast
    rw [installCore_of_layoutEnd_lt next growth T hpast]
    exact h.runway position (hle.trans_lt hpast)

/-! ## A common envelope interface for positive-decrement schedules -/

/-- The operational content needed by the four positive-decrement schedules.
The open and finite-prefix representations differ only in how their blank
runway is bounded; the controller trace itself is identical. -/
structure DecrementEnvelope (growth : Turing.Dir) (limit : Nat) where
  Represents : Registers → FullTM0.Tape (Symbol numTags) → Prop
  first : ∀ (base : Nat) (c : Nat.Partrec.Code)
      (counterState searchSlot : Nat) (success : ControlRef)
      {current next : Registers} {T : FullTM0.Tape (Symbol numTags)}
      (hlimit : 0 < limit) (h : Represents current T) (i : Fin 4)
      (hpositive : 0 < RegisterLayout.values current i)
      (hlower : layoutEnd next ≤ layoutEnd current)
      (hupper : layoutEnd current ≤ layoutEnd next + 1)
      (hsource : boundaryOffset current i.succ ≤ layoutEnd current)
      (hdestination : boundaryOffset current i.succ - 1 ≤ layoutEnd next)
      (hshrink : layoutEnd next < layoutEnd current →
        boundaryOffset current i.succ = layoutEnd current)
      (hmove : MarkerMachine.moveAt .left
        (MarkerTape.canonicalTape current)
        (MarkerTape.boundaryPosition current i.succ) i.succ =
          MarkerTape.canonicalTape next)
      (hraw : RawCommand.markerShift
        ⟨growth, counterState, searchSlot⟩ i.succ .right .left success
        (some .right) none ∈ rawCommands),
    (FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨growth, counterState, searchSlot⟩,
          atLogical growth T (boundaryOffset current i.succ)⟩
        ⟨resolve base c success,
          atLogical growth
            (installCore next growth
              (writeLogical growth T
                (boundaryOffset current i.succ) blankSymbol))
            (boundaryOffset current i.succ)⟩ ∧
      Represents next
        (installCore next growth
          (writeLogical growth T
            (boundaryOffset current i.succ) blankSymbol))) ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨growth, counterState, searchSlot⟩,
          atLogical growth T (boundaryOffset current i.succ)⟩
  following : ∀ (base : Nat) (c : Nat.Partrec.Code)
      (counterState searchSlot : Nat) (success : ControlRef)
      {current next : Registers} {T : FullTM0.Tape (Symbol numTags)}
      (h : Represents current T) (i : Fin 4)
      (hpositive : 0 < RegisterLayout.values current i)
      (hdistance : RegisterLayout.values current i < limit)
      (hlower : layoutEnd next ≤ layoutEnd current)
      (hupper : layoutEnd current ≤ layoutEnd next + 1)
      (hsource : boundaryOffset current i.succ ≤ layoutEnd current)
      (hdestination : boundaryOffset current i.succ - 1 ≤ layoutEnd next)
      (hshrink : layoutEnd next < layoutEnd current →
        boundaryOffset current i.succ = layoutEnd current)
      (hmove : MarkerMachine.moveAt .left
        (MarkerTape.canonicalTape current)
        (MarkerTape.boundaryPosition current i.succ) i.succ =
          MarkerTape.canonicalTape next)
      (hraw : RawCommand.markerShift
        ⟨growth, counterState, searchSlot⟩ i.succ .right .left success
        (some .right) none ∈ rawCommands),
    (FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨growth, counterState, searchSlot⟩,
          atLogical growth T (firstGapOffset current i)⟩
        ⟨resolve base c success,
          atLogical growth
            (installCore next growth
              (writeLogical growth T
                (boundaryOffset current i.succ) blankSymbol))
            (boundaryOffset current i.succ)⟩ ∧
      Represents next
        (installCore next growth
          (writeLogical growth T
            (boundaryOffset current i.succ) blankSymbol))) ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨growth, counterState, searchSlot⟩,
          atLogical growth T (firstGapOffset current i)⟩
  install_equal_length : ∀ {current next : Registers}
      {T : FullTM0.Tape (Symbol numTags)},
    Represents current T → layoutEnd next = layoutEnd current →
      Represents next (installCore next growth T)
  registerValue_lt : ∀ {registers : Registers}
      {T : FullTM0.Tape (Symbol numTags)},
    Represents registers T → ∀ i : Fin 4,
      RegisterLayout.values registers i < limit
  limit_positive : ∀ {registers : Registers}
      {T : FullTM0.Tape (Symbol numTags)},
    Represents registers T → 0 < limit
  decrement : ∀ {registers : Registers}
      {T : FullTM0.Tape (Symbol numTags)} (register : Register),
    Represents registers T → 0 < registers.get register →
      Represents (registers.decrement register)
        (decrementCoreTape registers growth register T)

/-- A positive-decrement schedule depends only on the common envelope
operations, not on whether its blank runway is finite or infinite. -/
theorem machine_reaches_decrementSchedule_or_halts_of_envelope
    (base : Nat) (c : Nat.Partrec.Code) (source : Nat)
    (register : Register)
    {registers : Registers} {growth : Turing.Dir} {limit : Nat}
    {T : FullTM0.Tape (Symbol numTags)}
    (E : DecrementEnvelope growth limit) (h : E.Represents registers T)
    (hpositive : 0 < registers.get register)
    (hcommands : ∀ raw,
      raw ∈ decrementShiftCommands growth source register →
        raw ∈ rawCommands) :
    (FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨growth, source, secondarySearchBase⟩,
          atLogical growth T
            (boundaryOffset registers
              (MarkerSchedule.decrementStartBoundary register))⟩
        ⟨resolve base c (directRef growth source finishDirectSlot),
          atLogical growth
            (decrementCoreTape registers growth register T)
            (layoutEnd registers)⟩ ∧
      E.Represents (registers.decrement register)
        (decrementCoreTape registers growth register T)) ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨growth, source, secondarySearchBase⟩,
          atLogical growth T
            (boundaryOffset registers
              (MarkerSchedule.decrementStartBoundary register))⟩ := by
  let final := registers.decrement register
  have hregisters : registers =
      decrementStageRegisters final register := by
    symm
    exact MarkerSchedule.increment_decrement_registers
      registers register hpositive
  have hend : layoutEnd final + 1 = layoutEnd registers :=
    layoutEnd_decrement_add_one registers register hpositive
  have hdesired : installCore final growth
      (writeLogical growth T (layoutEnd registers) blankSymbol) =
      decrementCoreTape registers growth register T := by
    rfl
  have hstageRep (stage : Register) :
      E.Represents (decrementStageRegisters final stage)
        (installCore (decrementStageRegisters final stage) growth T) := by
    apply E.install_equal_length h
    rw [decrementStage_layoutEnd, hend]
  let suffixRunner : DecrementSuffixRunner base c
      (FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c))
      growth registers final register T
      (decrementCoreTape registers growth register T) := {
    stageTape := fun stage =>
      installCore (decrementStageRegisters final stage) growth T
    aligned := hregisters
    pullback := FullTM0.HaltsFrom.of_reaches
    firstStep := by
      intro counterState searchSlot success current next hcurrent hnext hraw
      subst current
      let nextRegisters := decrementStageRegisters final next
      let geometry := decrementStepGeometry (final := final) hnext
      have hrun := E.first base c counterState searchSlot success
        (E.limit_positive h) h (decrementStageIndex register)
        (by simpa [hregisters] using geometry.positive)
        (by simpa [hregisters, nextRegisters] using
          geometry.next_le_current)
        (by simpa [hregisters, nextRegisters] using
          geometry.current_le_next_succ)
        (by simpa [hregisters] using geometry.source_le)
        (by simpa [hregisters, nextRegisters] using
          geometry.destination_le)
        (by
          intro hlt
          simpa [hregisters, nextRegisters] using
            geometry.shrink_source_eq_end (by
              simpa [hregisters, nextRegisters] using hlt))
        (by simpa [hregisters, nextRegisters] using geometry.move)
        hraw
      have htapeNext : installCore nextRegisters growth
          (writeLogical growth T
            (boundaryOffset registers
              (decrementStageIndex register).succ) blankSymbol) =
          installCore nextRegisters growth T := by
        apply installCore_write_inside
        · simp [boundaryOffset]
        · simpa [hregisters, nextRegisters] using
            geometry.source_le_next
      rw [htapeNext] at hrun
      rcases hrun with hrun | hhalts
      · exact Or.inl hrun.1
      · exact Or.inr hhalts
    followingStep := by
      intro counterState searchSlot success current next hnext hraw
      let currentRegisters := decrementStageRegisters final current
      let nextRegisters := decrementStageRegisters final next
      let currentTape := installCore currentRegisters growth T
      have hcurrent : E.Represents currentRegisters currentTape := by
        simpa [currentRegisters, currentTape] using hstageRep current
      let geometry := decrementStepGeometry (final := final) hnext
      have hrun := E.following base c counterState searchSlot success hcurrent
        (decrementStageIndex current)
        (by simpa [currentRegisters] using geometry.positive)
        (E.registerValue_lt hcurrent (decrementStageIndex current))
        (by simpa [currentRegisters, nextRegisters] using
          geometry.next_le_current)
        (by simpa [currentRegisters, nextRegisters] using
          geometry.current_le_next_succ)
        (by simpa [currentRegisters] using geometry.source_le)
        (by simpa [currentRegisters, nextRegisters] using
          geometry.destination_le)
        (by
          intro hlt
          simpa [currentRegisters, nextRegisters] using
            geometry.shrink_source_eq_end (by
              simpa [currentRegisters, nextRegisters] using hlt))
        (by simpa [currentRegisters, nextRegisters] using
          geometry.move)
        hraw
      have htapeNext : installCore nextRegisters growth
          (writeLogical growth currentTape
            (boundaryOffset currentRegisters
              (decrementStageIndex current).succ) blankSymbol) =
          installCore nextRegisters growth T := by
        apply installCore_after_internal_left
        · simpa [currentRegisters, nextRegisters] using
            geometry.current_le_next
        · simp [boundaryOffset]
        · simpa [currentRegisters, nextRegisters] using
            geometry.source_le_next
      rw [htapeNext] at hrun
      rcases hrun with hrun | hhalts
      · exact Or.inl hrun.1
      · exact Or.inr hhalts
    firstFinish := by
      intro counterState searchSlot hstart hraw
      subst register
      have hclockPositive :
          0 < RegisterLayout.values registers (3 : Fin 4) := by
        rw [hregisters]
        exact decrementStage_positive final .clock
      have hmove : MarkerMachine.moveAt .left
          (MarkerTape.canonicalTape registers)
          (MarkerTape.boundaryPosition registers 4) 4 =
          MarkerTape.canonicalTape final := by
        rw [hregisters]
        exact MarkerSchedule.moveClockBoundary_after_increment final
      have hrun := E.first base c counterState searchSlot
        (directRef growth counterState finishDirectSlot)
        (E.limit_positive h) h (3 : Fin 4) hclockPositive
        (by omega) (by omega) (boundaryOffset_le_layoutEnd registers 4)
        (by change layoutEnd registers - 1 ≤ layoutEnd final; omega)
        (by intro _; exact boundaryOffset_four registers) hmove hraw
      rcases hrun with hrun | hhalts
      · left
        simpa [boundaryOffset_four, hend, hdesired] using hrun.1
      · exact Or.inr hhalts
    followingFinish := by
      intro counterState searchSlot hraw
      let current := decrementStageRegisters final .clock
      let currentTape := installCore current growth T
      have hcurrent : E.Represents current currentTape := by
        simpa [current, currentTape] using hstageRep .clock
      have hcurrentEnd : layoutEnd current = layoutEnd registers := by
        simp [current, decrementStage_layoutEnd, hend]
      have hclockPositive :
          0 < RegisterLayout.values current (3 : Fin 4) := by
        simpa only [current, decrementStageRegisters,
          decrementStageIndex] using decrementStage_positive final .clock
      have hmove : MarkerMachine.moveAt .left
          (MarkerTape.canonicalTape current)
          (MarkerTape.boundaryPosition current 4) 4 =
          MarkerTape.canonicalTape final := by
        simpa only [current, decrementStageRegisters] using
          MarkerSchedule.moveClockBoundary_after_increment final
      have hrun := E.following base c counterState searchSlot
        (directRef growth counterState finishDirectSlot) hcurrent (3 : Fin 4)
        hclockPositive (E.registerValue_lt hcurrent (3 : Fin 4))
        (by rw [hcurrentEnd, ← hend]; omega)
        (by rw [hcurrentEnd, ← hend])
        (boundaryOffset_le_layoutEnd current 4)
        (by
          change layoutEnd current - 1 ≤ layoutEnd final
          rw [hcurrentEnd, ← hend]
          omega)
        (by intro _; exact boundaryOffset_four current) hmove hraw
      have hfinalTape : installCore final growth
          (writeLogical growth currentTape
            (boundaryOffset current 4) blankSymbol) =
          decrementCoreTape registers growth register T := by
        change installCore final growth
          (writeLogical growth (installCore current growth T)
            (layoutEnd current) blankSymbol) =
          decrementCoreTape registers growth register T
        rw [installCore_clear_old_overlay current final growth T]
        · rw [hcurrentEnd]
          exact hdesired
        · rw [hcurrentEnd]
          exact hend
      have hfinalTape' : installCore final growth
          (writeLogical growth currentTape
            (layoutEnd registers) blankSymbol) =
          decrementCoreTape registers growth register T := by
        rw [← hcurrentEnd]
        simpa [boundaryOffset_four] using hfinalTape
      have hfinish : boundaryOffset current (3 : Fin 4).succ =
          layoutEnd registers := by
        change layoutEnd current = layoutEnd registers
        exact hcurrentEnd
      rw [hfinish] at hrun
      rw [hfinalTape'] at hrun
      rcases hrun with hrun | hhalts
      · exact Or.inl hrun.1
      · exact Or.inr hhalts }
  have hrun := machine_reaches_decrementSuffix_with base c
    (FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c))
    suffixRunner source hcommands
  have hfinal := E.decrement register h hpositive
  exact hrun.imp (fun hs => ⟨hs, hfinal⟩) id
/-- An open runway equipped with a finite search bound.  The extra bound is
proof-only and is preserved because every intermediate decrement layout has
the same length as the input layout. -/
def openDecrementEnvelope (growth : Turing.Dir) (limit : Nat) :
    DecrementEnvelope growth limit where
  Represents registers T :=
    CoreOpenRepresents registers growth T ∧ layoutEnd registers < limit
  first := by
    intro base c counterState searchSlot success current next T hlimit h i
      hpositive hlower hupper hsource hdestination hshrink hmove hraw
    have hrun := machine_reaches_decrementFirst_or_halts_of_open
      base c limit counterState searchSlot success hlimit h.1 i hpositive
      hlower hupper hsource hdestination hshrink hmove hraw
    exact hrun.imp (fun hs => ⟨hs.1, hs.2, hlower.trans_lt h.2⟩) id
  following := by
    intro base c counterState searchSlot success current next T h i hpositive
      hdistance hlower hupper hsource hdestination hshrink hmove hraw
    have hrun := machine_reaches_decrementFollowing_or_halts_of_open
      base c limit counterState searchSlot success h.1 i hpositive hdistance
      hlower hupper hsource hdestination hshrink hmove hraw
    exact hrun.imp (fun hs => ⟨hs.1, hs.2, hlower.trans_lt h.2⟩) id
  install_equal_length := by
    intro current next T h heq
    exact ⟨installCore_open_of_extension h.1 (heq.ge), by simpa [heq] using h.2⟩
  registerValue_lt := by
    intro registers T h i
    exact AnchoredCounterGeometry.registerValue_lt_of_layoutEnd_lt
      registers i h.2
  limit_positive := by
    intro registers T h
    exact AnchoredCounterGeometry.limit_positive_of_layoutEnd_lt registers h.2
  decrement := by
    intro registers T register h hpositive
    exact ⟨decrementCoreTape_preserves_open h.1 register hpositive,
      (layoutEnd_decrement_lt registers register hpositive).trans h.2⟩

/-- Uniform target-free positive-decrement schedule. -/
theorem machine_reaches_decrementSchedule_or_halts_of_open
    (base : Nat) (c : Nat.Partrec.Code) (source : Nat)
    (register : Register)
    {registers : Registers} {growth : Turing.Dir}
    {T : FullTM0.Tape (Symbol numTags)}
    (h : CoreOpenRepresents registers growth T)
    (hpositive : 0 < registers.get register)
    (hcommands : ∀ raw,
      raw ∈ decrementShiftCommands growth source register →
        raw ∈ rawCommands) :
    (FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨growth, source, secondarySearchBase⟩,
          atLogical growth T
            (boundaryOffset registers
              (MarkerSchedule.decrementStartBoundary register))⟩
        ⟨resolve base c (directRef growth source finishDirectSlot),
          atLogical growth
            (decrementCoreTape registers growth register T)
            (layoutEnd registers)⟩ ∧
      CoreOpenRepresents (registers.decrement register) growth
        (decrementCoreTape registers growth register T)) ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨growth, source, secondarySearchBase⟩,
          atLogical growth T
            (boundaryOffset registers
              (MarkerSchedule.decrementStartBoundary register))⟩ := by
  let limit := layoutEnd registers + 1
  let E := openDecrementEnvelope growth limit
  have hE : E.Represents registers T := ⟨h, by simp [limit]⟩
  have hrun := machine_reaches_decrementSchedule_or_halts_of_envelope
    base c source register E hE hpositive hcommands
  exact hrun.imp (fun hs => ⟨hs.1, hs.2.1⟩) id

/-! ## Target-free positive-decrement handoff and finish -/

/-- The cell immediately left of the tested boundary is blank when the
selected represented register is positive. -/
theorem decrement_positive_predecessor_blank_of_core
    {registers : Registers} {growth : Turing.Dir}
    {T : FullTM0.Tape (Symbol numTags)}
    (h : CoreRepresents registers growth T) (register : Register)
    (hpositive : 0 < registers.get register) :
    (atLogical growth T
      (boundaryOffset registers
        (MarkerSchedule.decrementStartBoundary register) - 1)).read =
      blankSymbol :=
  h.positive_predecessor_blank register hpositive

/-- The positive branch reads that blank predecessor and moves right onto the
first boundary of the decrement schedule. -/
theorem machine_reaches_decrementPositiveHandoff_of_core
    (base : Nat) (c : Nat.Partrec.Code) (source ifZero ifPositive : Nat)
    (register : Register)
    (hrule : (source, .decrement register ifZero ifPositive) ∈
      GlobalSourceProgram.program)
    {registers : Registers} {growth : Turing.Dir}
    {T : FullTM0.Tape (Symbol numTags)}
    (h : CoreRepresents registers growth T)
    (hpositive : 0 < registers.get register) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      ⟨resolve base c (directRef growth source branchDirectSlot),
        atLogical growth T
          (boundaryOffset registers
            (MarkerSchedule.decrementStartBoundary register) - 1)⟩
      ⟨searchState base c ⟨growth, source, secondarySearchBase⟩,
        atLogical growth T
          (boundaryOffset registers
            (MarkerSchedule.decrementStartBoundary register))⟩ := by
  let raw : RawDirectRule :=
    ⟨growth, directRef growth source branchDirectSlot, .blank,
      searchRef growth source secondarySearchBase, .right⟩
  have hraw : raw ∈ rawDirectRules := by
    apply directRule_mem_rawDirectRules_of_rule growth hrule
    change raw ∈ validationRules growth source ++
      decrementRules growth source register ifZero ifPositive
    apply List.mem_append_right
    simp only [decrementRules, List.mem_append]
    apply Or.inl
    apply Or.inr
    simp [raw]
  have hblank : raw.read.Matches
      (atLogical growth T
        (boundaryOffset registers
          (MarkerSchedule.decrementStartBoundary register) - 1)).read := by
    exact decrement_positive_predecessor_blank_of_core h register hpositive
  have hrun := CounterControlDirectSemantics.reaches_directRule base c raw
    hraw (atLogical growth T
      (boundaryOffset registers
        (MarkerSchedule.decrementStartBoundary register) - 1)) hblank
  have hp : 0 < boundaryOffset registers
      (MarkerSchedule.decrementStartBoundary register) := by
    simp [boundaryOffset]
  have hmove : (atLogical growth T
      (boundaryOffset registers
        (MarkerSchedule.decrementStartBoundary register) - 1)).move
        (orient growth .right) =
      atLogical growth T
        (boundaryOffset registers
          (MarkerSchedule.decrementStartBoundary register)) := by
    rw [show boundaryOffset registers
        (MarkerSchedule.decrementStartBoundary register) =
          (boundaryOffset registers
            (MarkerSchedule.decrementStartBoundary register) - 1) + 1 by
      omega]
    rw [orient_eq_orientDirection, atLogical_move_right]
    congr 1
  rw [hmove] at hrun
  change FullTM0.Reaches (CounterControlNestingBridge.machine base c)
    ⟨resolve base c (directRef growth source branchDirectSlot),
      atLogical growth T
        (boundaryOffset registers
          (MarkerSchedule.decrementStartBoundary register) - 1)⟩
    ⟨searchState base c ⟨growth, source, secondarySearchBase⟩,
      atLogical growth T
        (boundaryOffset registers
          (MarkerSchedule.decrementStartBoundary register))⟩ at hrun
  exact hrun

/-- The old far boundary cell is blank in the core-only decrement tape. -/
theorem decrementCoreTape_old_layoutEnd_blank
    (registers : Registers) (growth : Turing.Dir) (register : Register)
    (T : FullTM0.Tape (Symbol numTags))
    (hpositive : 0 < registers.get register) :
    logicalTape growth (decrementCoreTape registers growth register T)
      (layoutEnd registers) = blankSymbol := by
  change logicalTape growth
    (installCore (registers.decrement register) growth
      (clearOldCoreEnd registers growth T)) (layoutEnd registers) = blankSymbol
  rw [installCore_of_layoutEnd_lt]
  · exact writeLogical_at growth T (layoutEnd registers) blankSymbol
  · have hend := layoutEnd_decrement_add_one registers register hpositive
    omega

/-- The final blank rule leaves the vacated old boundary cell and moves left
onto boundary `4` of the decremented open core. -/
theorem machine_reaches_decrementPositiveFinish_of_core
    (base : Nat) (c : Nat.Partrec.Code) (source ifZero ifPositive : Nat)
    (register : Register)
    (hrule : (source, .decrement register ifZero ifPositive) ∈
      GlobalSourceProgram.program)
    {registers : Registers} (growth : Turing.Dir)
    (T : FullTM0.Tape (Symbol numTags))
    (hpositive : 0 < registers.get register) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨resolve base c (directRef growth source finishDirectSlot),
          atLogical growth (decrementCoreTape registers growth register T)
            (layoutEnd registers)⟩
        ⟨logicalState base c growth ifPositive,
          atLogical growth (decrementCoreTape registers growth register T)
            (layoutEnd (registers.decrement register))⟩ := by
  let raw : RawDirectRule :=
    ⟨growth, directRef growth source finishDirectSlot, .blank,
      .logical growth ifPositive, .left⟩
  have hraw : raw ∈ rawDirectRules := by
    apply directRule_mem_rawDirectRules_of_rule growth hrule
    change raw ∈ validationRules growth source ++
      decrementRules growth source register ifZero ifPositive
    apply List.mem_append_right
    simp [raw, decrementRules]
  have hmatch : raw.read.Matches
      (atLogical growth (decrementCoreTape registers growth register T)
        (layoutEnd registers)).read := by
    change (atLogical growth (decrementCoreTape registers growth register T)
      (layoutEnd registers)).read = blankSymbol
    rw [atLogical_read]
    exact decrementCoreTape_old_layoutEnd_blank registers growth register T
      hpositive
  have hrun := CounterControlDirectSemantics.reaches_directRule base c raw
    hraw (atLogical growth (decrementCoreTape registers growth register T)
      (layoutEnd registers)) hmatch
  have hend := layoutEnd_decrement_add_one registers register hpositive
  have hmove : (atLogical growth
      (decrementCoreTape registers growth register T)
      (layoutEnd registers)).move (orient growth .left) =
      atLogical growth (decrementCoreTape registers growth register T)
        (layoutEnd (registers.decrement register)) := by
    rw [← hend, orient_eq_orientDirection, atLogical_move_left]
  rw [hmove] at hrun
  change FullTM0.Reaches (CounterControlNestingBridge.machine base c)
    ⟨resolve base c (directRef growth source finishDirectSlot),
      atLogical growth (decrementCoreTape registers growth register T)
        (layoutEnd registers)⟩
    ⟨logicalState base c growth ifPositive,
      atLogical growth (decrementCoreTape registers growth register T)
        (layoutEnd (registers.decrement register))⟩ at hrun
  exact hrun

/-! ## The target-free zero-decrement branch -/

/-- Navigate from the instruction body to the selected decrement test using
only the represented core, or halt in one of those genuine internal
searches. -/
theorem machine_reaches_decrementToTest_or_halts_of_core
    (base : Nat) (c : Nat.Partrec.Code) (growth : Turing.Dir)
    (source ifZero ifPositive : Nat) (register : Register)
    (hrule : (source, .decrement register ifZero ifPositive) ∈
      GlobalSourceProgram.program)
    {registers : Registers} {T : FullTM0.Tape (Symbol numTags)}
    (h : CoreRepresents registers growth T) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨resolve base c
            (bodyEntry growth source
              (.decrement register ifZero ifPositive)),
          atLogical growth T (layoutEnd registers)⟩
        ⟨resolve base c (directRef growth source testDirectSlot),
          atLogical growth T
            (boundaryOffset registers
              (MarkerSchedule.decrementStartBoundary register))⟩ ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨resolve base c
            (bodyEntry growth source
              (.decrement register ifZero ifPositive)),
          atLogical growth T (layoutEnd registers)⟩ := by
  let limit := layoutEnd registers + 1
  have hlimit : layoutEnd registers < limit := by simp [limit]
  let route := AnchoredCounterGeometry.routeToDecrementStart register
  have hcommands : ∀ raw,
      raw ∈ routeCommandsAux growth source bodySearchBase
          (bodyDirectBase + 1) (directRef growth source testDirectSlot)
          route → raw ∈ rawCommands := by
    intro raw hraw
    apply command_mem_rawCommands_of_rule growth hrule
    simp [commandsForRule, decrementCommands, route, hraw]
  have hrules : ∀ raw,
      raw ∈ routeEntryRules growth source
            (bodyEntry growth source
              (.decrement register ifZero ifPositive)) 4 bodySearchBase
            route ++
          routeContinuationRules growth source bodySearchBase
            (bodyDirectBase + 1) route →
        raw ∈ rawDirectRules := by
    intro raw hraw
    apply directRule_mem_rawDirectRules_of_rule growth hrule
    change raw ∈ validationRules growth source ++
      decrementRules growth source register ifZero ifPositive
    apply List.mem_append_right
    have hraw' : raw ∈
        routeEntryRules growth source
            (directRef growth source bodyDirectBase) 4 bodySearchBase
            (AnchoredCounterGeometry.routeToDecrementStart register) ++
          routeContinuationRules growth source bodySearchBase
            (bodyDirectBase + 1)
            (AnchoredCounterGeometry.routeToDecrementStart register) := by
      simp only [bodyEntry] at hraw
      cases hlegs : AnchoredCounterGeometry.routeToDecrementStart register with
      | nil =>
          simp [route, hlegs, routeEntryRules, routeContinuationRules] at hraw
      | cons first rest => simpa [route, hlegs] using hraw
    rcases List.mem_append.mp hraw' with hentry | hcontinuation
    · simp only [decrementRules, List.mem_append]
      exact Or.inl (Or.inl (Or.inl hentry))
    · simp only [decrementRules, List.mem_append]
      exact Or.inl (Or.inl (Or.inr hcontinuation))
  exact route_reaches_or_halts_at_maybe_empty base c limit
    (shortResolves_all base c limit) growth source bodySearchBase
    (bodyDirectBase + 1)
    (bodyEntry growth source (.decrement register ifZero ifPositive))
    (directRef growth source testDirectSlot) 4 route
    (by
      intro hnil
      simp [route, bodyEntry, hnil])
    T (layoutEnd registers)
    (boundaryOffset registers
      (MarkerSchedule.decrementStartBoundary register))
    h.read_boundary_four
    (routeToDecrementStart_executesWithin_of_core h hlimit register)
    hcommands hrules

/-- From the predecessor boundary of an empty selected gap, return to the
zero successor using only core-internal searches, or expose a halt. -/
theorem machine_reaches_decrementZeroRecovery_or_halts_of_core
    (base : Nat) (c : Nat.Partrec.Code) (growth : Turing.Dir)
    (source ifZero ifPositive : Nat) (register : Register)
    (hrule : (source, .decrement register ifZero ifPositive) ∈
      GlobalSourceProgram.program)
    {registers : Registers} {T : FullTM0.Tape (Symbol numTags)}
    (h : CoreRepresents registers growth T)
    (hzero : registers.get register = 0) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨resolve base c (directRef growth source branchDirectSlot),
          atLogical growth T
            (boundaryOffset registers
              (MarkerSchedule.decrementStartBoundary register) - 1)⟩
        ⟨logicalState base c growth ifZero,
          atLogical growth T (layoutEnd registers)⟩ ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨resolve base c (directRef growth source branchDirectSlot),
          atLogical growth T
            (boundaryOffset registers
              (MarkerSchedule.decrementStartBoundary register) - 1)⟩ := by
  let limit := layoutEnd registers + 1
  have hlimit : layoutEnd registers < limit := by simp [limit]
  let route := AnchoredCounterGeometry.routeFromZero register
  have hcommands : ∀ raw,
      raw ∈ routeCommandsAux growth source zeroSearchBase zeroDirectBase
          (.logical growth ifZero) route → raw ∈ rawCommands := by
    intro raw hraw
    apply command_mem_rawCommands_of_rule growth hrule
    simp [commandsForRule, decrementCommands, route, hraw]
  have hrules : ∀ raw,
      raw ∈ routeEntryRules growth source
            (directRef growth source branchDirectSlot)
            (AnchoredCounterGeometry.registerGap register).castSucc
            zeroSearchBase route ++
          routeContinuationRules growth source zeroSearchBase
            zeroDirectBase route → raw ∈ rawDirectRules := by
    intro raw hraw
    apply directRule_mem_rawDirectRules_of_rule growth hrule
    change raw ∈ validationRules growth source ++
      decrementRules growth source register ifZero ifPositive
    apply List.mem_append_right
    rcases List.mem_append.mp hraw with hentry | hcontinuation
    · have hentryOriginal : raw ∈ routeEntryRules growth source
          (directRef growth source branchDirectSlot)
          (AnchoredCounterGeometry.registerGap register).castSucc
          zeroSearchBase
          (AnchoredCounterGeometry.routeFromZero register) := by
        simpa [route] using hentry
      have hentryRules : routeEntryRules growth source
          (directRef growth source branchDirectSlot)
          (AnchoredCounterGeometry.registerGap register).castSucc
          zeroSearchBase
          (AnchoredCounterGeometry.routeFromZero register) =
          [⟨growth, directRef growth source branchDirectSlot,
            .boundary
              (AnchoredCounterGeometry.registerGap register).castSucc,
            searchRef growth source zeroSearchBase, .right⟩] := by
        cases register <;> rfl
      rw [hentryRules] at hentryOriginal
      have heq : raw =
          ⟨growth, directRef growth source branchDirectSlot,
            .boundary
              (AnchoredCounterGeometry.registerGap register).castSucc,
            searchRef growth source zeroSearchBase, .right⟩ := by
        simpa using hentryOriginal
      have hfour : raw ∈
          [⟨growth, directRef growth source testDirectSlot,
              .boundary (MarkerSchedule.decrementStartBoundary register),
              directRef growth source branchDirectSlot, .left⟩,
            ⟨growth, directRef growth source branchDirectSlot,
              .blank, searchRef growth source secondarySearchBase,
              .right⟩,
            ⟨growth, directRef growth source branchDirectSlot,
              .boundary
                (AnchoredCounterGeometry.registerGap register).castSucc,
              searchRef growth source zeroSearchBase, .right⟩,
            ⟨growth, directRef growth source finishDirectSlot,
              .blank, .logical growth ifPositive, .left⟩] := by
        simp only [List.mem_cons]
        exact Or.inr (Or.inr (Or.inl heq))
      simp only [decrementRules, List.mem_append]
      exact Or.inl (Or.inr hfour)
    · simp only [decrementRules, List.mem_append]
      exact Or.inr (by simpa [route] using hcontinuation)
  have hsourcePosition : boundaryOffset registers
        (MarkerSchedule.decrementStartBoundary register) - 1 =
      boundaryOffset registers
        (AnchoredCounterGeometry.registerGap register).castSucc :=
    AnchoredCounterGeometry.zeroTest_predecessor registers register hzero
  have hrun := route_reaches_or_halts_at_of_ne_nil base c limit
    (shortResolves_all base c limit) growth source zeroSearchBase
    zeroDirectBase (directRef growth source branchDirectSlot)
    (.logical growth ifZero)
    (AnchoredCounterGeometry.registerGap register).castSucc route
    (by simpa [route] using
      AnchoredCounterGeometry.routeFromZero_ne_nil register) T
    (boundaryOffset registers
      (AnchoredCounterGeometry.registerGap register).castSucc)
    (layoutEnd registers)
    (by rw [atLogical_read]; exact h.boundary _)
    (routeFromZero_executesWithin_of_core h hlimit register)
    (by intro raw hraw; exact hcommands raw hraw)
    (by intro raw hraw; exact hrules raw hraw)
  rw [hsourcePosition]
  simpa [route, logicalState, CounterControlPlan.resolve] using hrun

/-- Complete target-free zero branch of a compiled conditional decrement.
The tape and open-core invariant are unchanged in the successful branch. -/
theorem machine_reaches_decrementZeroInstruction_or_halts_of_core
    (base : Nat) (c : Nat.Partrec.Code) (growth : Turing.Dir)
    (source ifZero ifPositive : Nat) (register : Register)
    (hrule : (source, .decrement register ifZero ifPositive) ∈
      GlobalSourceProgram.program)
    {registers : Registers} {T : FullTM0.Tape (Symbol numTags)}
    (h : CoreRepresents registers growth T)
    (hzero : registers.get register = 0) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨logicalState base c growth source,
          atLogical growth T (layoutEnd registers)⟩
        ⟨logicalState base c growth ifZero,
          atLogical growth T (layoutEnd registers)⟩ ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨logicalState base c growth source,
          atLogical growth T (layoutEnd registers)⟩ := by
  have hvalidation := machine_reaches_validation_or_halts_of_core
    base c growth source (.decrement register ifZero ifPositive) hrule h
  have hroute := machine_reaches_decrementToTest_or_halts_of_core
    base c growth source ifZero ifPositive register hrule h
  have htest := CounterControlInstructionSemantics.machine_reaches_decrementTest
    base c source ifZero ifPositive register hrule
    (spec := openSpec registers growth) T (by
      change (atLogical growth T
        (boundaryOffset registers
          (MarkerSchedule.decrementStartBoundary register))).read = _
      rw [atLogical_read]
      exact h.boundary _)
  have htest' : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      ⟨resolve base c (directRef growth source testDirectSlot),
        atLogical growth T
          (boundaryOffset registers
            (MarkerSchedule.decrementStartBoundary register))⟩
      ⟨resolve base c (directRef growth source branchDirectSlot),
        atLogical growth T
          (boundaryOffset registers
            (MarkerSchedule.decrementStartBoundary register) - 1)⟩ := by
    simpa [openSpec] using htest
  have hzeroRoute :=
    machine_reaches_decrementZeroRecovery_or_halts_of_core
      base c growth source ifZero ifPositive register hrule h hzero
  exact FullTM0.ResolvesTo.trans hvalidation
    (FullTM0.ResolvesTo.trans hroute
      (FullTM0.ResolvesTo.trans (Or.inl htest') hzeroRoute))

/-- Exact target-free positive branch of a compiled conditional decrement. -/
theorem machine_reaches_decrementPositiveInstruction_or_halts_of_open
    (base : Nat) (c : Nat.Partrec.Code) (source ifZero ifPositive : Nat)
    (register : Register)
    (hrule : (source, .decrement register ifZero ifPositive) ∈
      GlobalSourceProgram.program)
    {registers : Registers} {growth : Turing.Dir}
    {T : FullTM0.Tape (Symbol numTags)}
    (h : CoreOpenRepresents registers growth T)
    (hpositive : 0 < registers.get register) :
    (FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨logicalState base c growth source,
          atLogical growth T (layoutEnd registers)⟩
        ⟨logicalState base c growth ifPositive,
          atLogical growth (decrementCoreTape registers growth register T)
            (layoutEnd (registers.decrement register))⟩ ∧
      CoreOpenRepresents (registers.decrement register) growth
        (decrementCoreTape registers growth register T)) ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨logicalState base c growth source,
          atLogical growth T (layoutEnd registers)⟩ := by
  have hvalidation := machine_reaches_validation_or_halts_of_core base c growth
    source (.decrement register ifZero ifPositive) hrule h.toCoreRepresents
  have hroute := machine_reaches_decrementToTest_or_halts_of_core base c growth
    source ifZero ifPositive register hrule h.toCoreRepresents
  have htest := CounterControlInstructionSemantics.machine_reaches_decrementTest
    base c source ifZero ifPositive register hrule
    (spec := openSpec registers growth) T (by
      change (atLogical growth T
        (boundaryOffset registers
          (MarkerSchedule.decrementStartBoundary register))).read = _
      rw [atLogical_read]
      exact h.boundary _)
  have htest' : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      ⟨resolve base c (directRef growth source testDirectSlot),
        atLogical growth T
          (boundaryOffset registers
            (MarkerSchedule.decrementStartBoundary register))⟩
      ⟨resolve base c (directRef growth source branchDirectSlot),
        atLogical growth T
          (boundaryOffset registers
            (MarkerSchedule.decrementStartBoundary register) - 1)⟩ := by
    simpa [openSpec] using htest
  have hhandoff := machine_reaches_decrementPositiveHandoff_of_core base c
    source ifZero ifPositive register hrule h.toCoreRepresents hpositive
  have hcommands : ∀ raw,
      raw ∈ decrementShiftCommands growth source register →
        raw ∈ rawCommands := by
    intro raw hraw
    apply command_mem_rawCommands_of_rule growth hrule
    simp [commandsForRule, decrementCommands, hraw]
  have hschedule := machine_reaches_decrementSchedule_or_halts_of_open base c
    source register h hpositive hcommands
  have hfinish := machine_reaches_decrementPositiveFinish_of_core base c source
    ifZero ifPositive register hrule growth T hpositive
  have hscheduleFinish :
      FullTM0.Reaches (CounterControlNestingBridge.machine base c)
          ⟨searchState base c ⟨growth, source, secondarySearchBase⟩,
            atLogical growth T
              (boundaryOffset registers
                (MarkerSchedule.decrementStartBoundary register))⟩
          ⟨logicalState base c growth ifPositive,
            atLogical growth (decrementCoreTape registers growth register T)
              (layoutEnd (registers.decrement register))⟩ ∨
        FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
          ⟨searchState base c ⟨growth, source, secondarySearchBase⟩,
            atLogical growth T
              (boundaryOffset registers
                (MarkerSchedule.decrementStartBoundary register))⟩ := by
    rcases hschedule with hschedule | hhalts
    · exact Or.inl (hschedule.1.trans hfinish)
    · exact Or.inr hhalts
  have hrun := FullTM0.ResolvesTo.trans hvalidation
    (FullTM0.ResolvesTo.trans hroute
      (FullTM0.ResolvesTo.trans (Or.inl htest')
        (FullTM0.ResolvesTo.trans (Or.inl hhandoff) hscheduleFinish)))
  rcases hrun with hrun | hhalts
  · exact Or.inl ⟨hrun,
      decrementCoreTape_preserves_open h register hpositive⟩
  · exact Or.inr hhalts

/-- `OpenStepContinuesOrHalts` for an increment step. -/
theorem openStepContinuesOrHalts_of_increment
    (base : Nat) (c : Nat.Partrec.Code)
    {growth : Turing.Dir} {current next : CounterMachine.Cfg}
    {concrete : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (hstep : CounterMachine.step GlobalSourceProgram.program current =
      some next)
    (register : Register) (target : Nat)
    (hlookup : CounterMachine.lookupInstruction
      GlobalSourceProgram.program current.state =
        some (.increment register target))
    (hnext : next = ⟨target, current.registers.increment register⟩)
    (hlogical :
      CounterControlCanonicalOpenMortality.OpenLogical
        base c growth current concrete) :
    (∃ nextConcrete,
      FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        concrete nextConcrete ∧
      CounterControlCanonicalOpenMortality.OpenLogical
        base c growth next nextConcrete) ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        concrete := by
  rcases hlogical with ⟨T, hopen, rfl, hstate⟩
  have hrule : (current.state, .increment register target) ∈
      GlobalSourceProgram.program :=
    CounterProgram.rule_mem_of_lookupInstruction_eq_some hlookup
  have hrun := machine_reaches_incrementInstruction_or_halts_of_open base c
    current.state target register hrule hopen
  rcases hrun with hrun | hhalts
  · subst next
    left
    refine ⟨⟨logicalState base c growth target,
        atLogical growth
          (incrementCoreTape current.registers growth register T)
          (layoutEnd (current.registers.increment register))⟩,
      hrun.1, ?_⟩
    exact ⟨incrementCoreTape current.registers growth register T,
      hrun.2, rfl,
      CounterControlAbstractTrace.state_lt_logicalSpan_of_step hstep⟩
  · exact Or.inr hhalts

/-- `OpenStepContinuesOrHalts` for a positive decrement step. -/
theorem openStepContinuesOrHalts_of_decrementPositive
    (base : Nat) (c : Nat.Partrec.Code)
    {growth : Turing.Dir} {current next : CounterMachine.Cfg}
    {concrete : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (hstep : CounterMachine.step GlobalSourceProgram.program current =
      some next)
    (register : Register) (ifZero ifPositive : Nat)
    (hlookup : CounterMachine.lookupInstruction
      GlobalSourceProgram.program current.state =
        some (.decrement register ifZero ifPositive))
    (hpositive : 0 < current.registers.get register)
    (hnext : next =
      ⟨ifPositive, current.registers.decrement register⟩)
    (hlogical :
      CounterControlCanonicalOpenMortality.OpenLogical
        base c growth current concrete) :
    (∃ nextConcrete,
      FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        concrete nextConcrete ∧
      CounterControlCanonicalOpenMortality.OpenLogical
        base c growth next nextConcrete) ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        concrete := by
  rcases hlogical with ⟨T, hopen, rfl, hstate⟩
  have hrule : (current.state,
      .decrement register ifZero ifPositive) ∈
        GlobalSourceProgram.program :=
    CounterProgram.rule_mem_of_lookupInstruction_eq_some hlookup
  have hrun := machine_reaches_decrementPositiveInstruction_or_halts_of_open
    base c current.state ifZero ifPositive register hrule hopen hpositive
  rcases hrun with hrun | hhalts
  · subst next
    left
    refine ⟨⟨logicalState base c growth ifPositive,
        atLogical growth
          (decrementCoreTape current.registers growth register T)
          (layoutEnd (current.registers.decrement register))⟩,
      hrun.1, ?_⟩
    exact ⟨decrementCoreTape current.registers growth register T,
      hrun.2, rfl,
      CounterControlAbstractTrace.state_lt_logicalSpan_of_step hstep⟩
  · exact Or.inr hhalts

/-- `OpenStepContinuesOrHalts` for the complete zero-decrement case.  This is
the first full branch of the target-free one-instruction endpoint. -/
theorem openStepContinuesOrHalts_of_decrementZero
    (base : Nat) (c : Nat.Partrec.Code)
    {growth : Turing.Dir} {current next : CounterMachine.Cfg}
    {concrete : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (hstep : CounterMachine.step GlobalSourceProgram.program current =
      some next)
    (register : Register) (ifZero ifPositive : Nat)
    (hlookup : CounterMachine.lookupInstruction
      GlobalSourceProgram.program current.state =
        some (.decrement register ifZero ifPositive))
    (hzero : current.registers.get register = 0)
    (hnext : next = ⟨ifZero, current.registers⟩)
    (hlogical :
      CounterControlCanonicalOpenMortality.OpenLogical
        base c growth current concrete) :
    (∃ nextConcrete,
      FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        concrete nextConcrete ∧
      CounterControlCanonicalOpenMortality.OpenLogical
        base c growth next nextConcrete) ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        concrete := by
  rcases hlogical with ⟨T, hopen, rfl, hstate⟩
  have hrule : (current.state,
      .decrement register ifZero ifPositive) ∈
        GlobalSourceProgram.program :=
    CounterProgram.rule_mem_of_lookupInstruction_eq_some hlookup
  have hrun := machine_reaches_decrementZeroInstruction_or_halts_of_core
    base c growth current.state ifZero ifPositive register hrule
    hopen.toCoreRepresents hzero
  rcases hrun with hrun | hhalts
  · subst next
    left
    refine ⟨⟨logicalState base c growth ifZero,
        atLogical growth T (layoutEnd current.registers)⟩,
      hrun, ?_⟩
    exact ⟨T, hopen, rfl,
      CounterControlAbstractTrace.state_lt_logicalSpan_of_step hstep⟩
  · exact Or.inr hhalts

end

end CounterControlOpenInstructionResolution
end Hooper
end Kari
end LeanWang
