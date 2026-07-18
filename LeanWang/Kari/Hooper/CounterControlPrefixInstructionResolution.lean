/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlOpenInstructionResolution
import LeanWang.Kari.Hooper.CounterControlLooseEnvelopeTotal

/-!
# Resolving instructions on finite tag-free counter prefixes

Validation of an arbitrary controller entry reconstructs the five-boundary
counter core without establishing that logical coordinate `0` is a saved
return tag.  This module supplies the missing operational layer.  A finite
tag-free core with a blank runway and a nonblank target executes defined
counter instructions normally while the updated core fits; an outward
increment at the target erases the core and reaches the shared directional
return state.  No claim about dispatching that return is made here.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlPrefixInstructionResolution

open Turing CounterMachine
open BoundedMarkerProgram FramedMarkerTape FramedCounterGeometry
open OrientedMarkerTape
open CounterControlPlan CounterControlCoreFrame
open CounterControlTagFreeOpen
open CounterControlCommandAt
open CounterControlInstructionSemantics
open CounterControlInstructionResolution
open CounterControlOpenInstructionResolution
open CounterControlSearchResolution
open CounterControlScheduleSemantics
open CounterControlCleanupSemantics
open CounterControlBridge

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-- A target attached to a tag-free finite prefix.  The target is required
to be genuinely nonblank; logical coordinate `0` remains unconstrained. -/
structure CoreTargetRepresents (registers : Registers)
    (growth : Turing.Dir) (limit : Nat) (target : Target numTags)
    (T : FullTM0.Tape (Symbol numTags)) : Prop extends
    CorePrefixRepresents registers growth limit T where
  target_matches : target.Matches (logicalTape growth T limit)

namespace CoreTargetRepresents

variable {registers : Registers} {growth : Turing.Dir} {limit : Nat}
variable {target : Target numTags} {T : FullTM0.Tape (Symbol numTags)}

theorem target_ne_blank
    (h : CoreTargetRepresents registers growth limit target T) :
    logicalTape growth T limit ≠ blankSymbol := by
  intro hblank
  exact target_not_blank target (hblank ▸ h.target_matches)

/-- A collision-free increment preserves the same finite target. -/
theorem increment
    (h : CoreTargetRepresents registers growth limit target T)
    (register : Register)
    (hroom : layoutEnd (registers.increment register) < limit) :
    CoreTargetRepresents (registers.increment register) growth limit target
      (incrementCoreTape registers growth register T) := by
  refine ⟨incrementCoreTape_preserves_prefix h.toCorePrefixRepresents
      register hroom, ?_⟩
  change target.Matches
    (logicalTape growth
      (installCore (registers.increment register) growth T) limit)
  rw [installCore_of_layoutEnd_lt
    (registers.increment register) growth T hroom]
  exact h.target_matches

/-- A positive decrement preserves the same finite target. -/
theorem decrement
    (h : CoreTargetRepresents registers growth limit target T)
    (register : Register) (hpositive : 0 < registers.get register) :
    CoreTargetRepresents (registers.decrement register) growth limit target
      (decrementCoreTape registers growth register T) := by
  have hnext := decrementCoreTape_preserves_prefix
    h.toCorePrefixRepresents register hpositive
  refine ⟨hnext, ?_⟩
  change target.Matches
    (logicalTape growth
      (installCore (registers.decrement register) growth
        (clearOldCoreEnd registers growth T)) limit)
  rw [installCore_of_layoutEnd_lt (registers.decrement register) growth
    (clearOldCoreEnd registers growth T) hnext.core_before_limit]
  have hne : limit ≠ layoutEnd registers :=
    Nat.ne_of_gt h.core_before_limit
  rw [show logicalTape growth (clearOldCoreEnd registers growth T) limit =
      logicalTape growth T limit by
    simpa [clearOldCoreEnd] using
      writeLogical_of_ne growth T (layoutEnd registers) limit blankSymbol hne]
  exact h.target_matches

end CoreTargetRepresents

theorem registerValue_lt_limit_of_prefix
    {registers : Registers} {growth : Turing.Dir} {limit : Nat}
    {T : FullTM0.Tape (Symbol numTags)}
    (h : CorePrefixRepresents registers growth limit T) (i : Fin 4) :
    RegisterLayout.values registers i < limit := by
  have hend := h.core_before_limit
  fin_cases i <;>
    simp [RegisterLayout.values, layoutEnd_eq] at hend ⊢ <;> omega

/-- The specification used only to name cleanup tapes and coordinates.
Its dummy return tag is never asserted to occur on the represented tape. -/
def prefixSpec (registers : Registers) (growth : Turing.Dir)
    (limit : Nat) (target : Target numTags)
    (hcore : layoutEnd registers < limit) : Spec numTags where
  growth := growth
  returnTag := CounterControlOpenSimulation.rootSearch
  registers := registers
  outerDistance := limit
  outerTarget := target
  core_before_target := hcore

/-! ## Target-free primitive boundary updates -/

/-- Moving one represented boundary right and rewriting its old and new
cells produces exactly the core-only installation of the supplied next
register tuple.  The proof uses the finite runway instead of a finite
outer target. -/
theorem moveRight_corePrefix
    {current next : Registers} {growth : Turing.Dir} {limit : Nat}
    {T : FullTM0.Tape (Symbol numTags)}
    (h : CorePrefixRepresents current growth limit T) (label : Fin 5)
    (hnextCore : layoutEnd next < limit)
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
      CorePrefixRepresents next growth limit U := by
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
  have hrep : CorePrefixRepresents next growth limit U := by
    constructor
    · constructor
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
    · exact hnextCore
    · intro position hpast hpositionLimit
      change logicalTape growth U position = blankSymbol
      rw [hU]
      have hneTarget : (position : Int) ≠ (source : Int) + 1 := by
        intro heq
        have heqNat : position = source + 1 := by exact_mod_cast heq
        omega
      have hneSource : (position : Int) ≠ (source : Nat) := by
        intro heq
        have heqNat : position = source := by exact_mod_cast heq
        omega
      simp only [hneTarget, hneSource, ↓reduceIte]
      exact h.runway position (hlower.trans_lt hpast) hpositionLimit
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
    installCore_eq_self_of_coreRepresents hrep.toCoreRepresents
  exact ⟨hself.symm.trans hinstall.symm, hrep⟩

/-- Moving a represented boundary left and clearing its old cell produces the
exact core-only installation over that cleared backing tape.  This also
covers the final boundary-`4` move, whose old cell becomes the first runway
blank. -/
theorem moveLeft_corePrefix
    {current next : Registers} {growth : Turing.Dir} {limit : Nat}
    {T : FullTM0.Tape (Symbol numTags)}
    (h : CorePrefixRepresents current growth limit T) (label : Fin 5)
    (hnextCore : layoutEnd next < limit)
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
    U = installCore next growth cleared ∧
      CorePrefixRepresents next growth limit U := by
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
  have hrep : CorePrefixRepresents next growth limit U := by
    constructor
    · constructor
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
    · exact hnextCore
    · intro position hpast hpositionLimit
      change logicalTape growth U position = blankSymbol
      rw [hU]
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
        · by_contra hold
          have hpositionLe : position ≤ layoutEnd current :=
            Nat.le_of_not_gt hold
          have hstrict : layoutEnd next < layoutEnd current := by omega
          have hsourceEnd := hshrink hstrict
          apply hsourcePosition
          omega
        · exact hpositionLimit
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
    installCore_eq_self_of_coreRepresents hrep.toCoreRepresents
  exact ⟨hself.symm.trans hinstall.symm, hrep⟩

/-! ## Target-free outward shifts -/

/-- Shift boundary `4` one cell into the finite blank runway. -/
theorem machine_reaches_incrementClock_or_halts_of_prefix
    (base : Nat) (c : Nat.Partrec.Code) (source searchSlot : Nat)
    (success : ControlRef) (collision : Option ControlRef)
    {registers : Registers} {growth : Turing.Dir} {limit : Nat}
    {T : FullTM0.Tape (Symbol numTags)}
    (h : CorePrefixRepresents registers growth limit T)
    (hroom : layoutEnd (registers.increment .clock) < limit)
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
      CorePrefixRepresents (registers.increment .clock) growth limit
        (incrementCoreTape registers growth .clock T)) ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨growth, source, searchSlot⟩,
          atLogical growth T (layoutEnd registers)⟩ := by
  let next := registers.increment .clock
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
    h.runway (layoutEnd registers + 1) (Nat.lt_succ_self _) (by
      simpa [next, layoutEnd_increment] using hroom)
  have hrun := machine_reaches_incrementShift_or_halts base c limit
    (shortResolves_all base c limit) growth source searchSlot
    (layoutEnd registers) 4 success collision hraw T 0
    (by omega) hgap hblank
  rcases hrun with hrun | hhalts
  · left
    have hmove : MarkerMachine.moveAt .right
        (MarkerTape.canonicalTape registers)
        (MarkerTape.boundaryPosition registers 4) 4 =
        MarkerTape.canonicalTape next := by
      rw [MarkerMachine.moveAt_clock_eq_incrementTape]
      exact MarkerShift.incrementTape_canonical registers .clock
    have hnormalized := moveRight_corePrefix h 4
      (next := next) hroom
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
theorem machine_reaches_incrementInternal_or_halts_of_prefix
    (base : Nat) (c : Nat.Partrec.Code) (limit : Nat)
    (counterState searchSlot : Nat)
    (success : ControlRef) (collision : Option ControlRef)
    {current next : Registers} {growth : Turing.Dir}
    {T : FullTM0.Tape (Symbol numTags)}
    (h : CorePrefixRepresents current growth limit T) (i : Fin 4)
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
      CorePrefixRepresents next growth limit (installCore next growth T)) ∨
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
    have hnextCore : layoutEnd next < limit := by
      rw [hsameEnd]
      exact h.core_before_limit
    have hnormalized := moveRight_corePrefix h i.castSucc
      (next := next) hnextCore hlower hupper hsourceBound htargetBound
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

/-- Every shift in a collision-free increment schedule resolves on an open
core.  The arbitrary finite `limit` used by the converse Basic Lemma is chosen
past the updated core; it is not asserted to contain a target. -/


theorem machine_reaches_incrementSchedule_or_halts_of_prefix
    (base : Nat) (c : Nat.Partrec.Code) (source : Nat)
    (register : Register)
    {registers : Registers} {growth : Turing.Dir} {limit : Nat}
    {T : FullTM0.Tape (Symbol numTags)}
    (h : CorePrefixRepresents registers growth limit T)
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
      CorePrefixRepresents (registers.increment register) growth limit
        (incrementCoreTape registers growth register T)) ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨growth, source, bodySearchBase⟩,
          atLogical growth T (layoutEnd registers)⟩ := by
  have hfinal (r : Register) :
      CorePrefixRepresents (registers.increment r) growth limit
        (incrementCoreTape registers growth r T) := by
    apply incrementCoreTape_preserves_prefix h r
    simpa [layoutEnd_increment] using hroom
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
        machine_reaches_incrementClock_or_halts_of_prefix base c source
          bodySearchBase (directRef growth source bodyDirectBase)
          (some (directRef growth source testDirectSlot)) h (by simpa [layoutEnd_increment] using hroom) hraw
  | temp =>
      let clockRegisters := registers.increment .clock
      let tempRegisters := registers.increment .temp
      let clockTape := incrementCoreTape registers growth .clock T
      let tempTape := incrementCoreTape registers growth .temp T
      have hclockPrefix :
          CorePrefixRepresents clockRegisters growth limit clockTape := by
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
      have hfour := machine_reaches_incrementClock_or_halts_of_prefix base c
        source bodySearchBase (searchRef growth source (bodySearchBase + 1))
        (some (directRef growth source testDirectSlot)) h (by simpa [layoutEnd_increment] using hroom) hrawFour
      have hthree := machine_reaches_incrementInternal_or_halts_of_prefix
        (next := tempRegisters) base c
        limit source (bodySearchBase + 1)
        (directRef growth source bodyDirectBase) none hclockPrefix (3 : Fin 4)
        (by simp [clockRegisters, RegisterLayout.values, Registers.increment,
          Registers.set, Registers.get])
        (by
          have hbound := h.core_before_limit
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
        simp only [clockTape, tempTape, incrementCoreTape]
        apply installCore_over_installCore
        simp [clockRegisters, tempRegisters, layoutEnd_increment]
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
          CorePrefixRepresents clockRegisters growth limit clockTape := by
        simpa [clockRegisters, clockTape] using hfinal .clock
      have htempPrefix :
          CorePrefixRepresents tempRegisters growth limit tempTape := by
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
      have hfour := machine_reaches_incrementClock_or_halts_of_prefix base c
        source bodySearchBase (searchRef growth source (bodySearchBase + 1))
        (some (directRef growth source testDirectSlot)) h (by simpa [layoutEnd_increment] using hroom) hrawFour
      have hthree := machine_reaches_incrementInternal_or_halts_of_prefix
        (next := tempRegisters) base c
        limit source (bodySearchBase + 1)
        (searchRef growth source (bodySearchBase + 2)) none hclockPrefix
        (3 : Fin 4)
        (by simp [clockRegisters, RegisterLayout.values, Registers.increment,
          Registers.set, Registers.get])
        (by
          have hbound := h.core_before_limit
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
      have htwo := machine_reaches_incrementInternal_or_halts_of_prefix
        (next := rightRegisters) base c
        limit source (bodySearchBase + 2)
        (directRef growth source bodyDirectBase) none htempPrefix (2 : Fin 4)
        (by simp [tempRegisters, RegisterLayout.values, Registers.increment,
          Registers.set, Registers.get])
        (by
          have hbound := h.core_before_limit
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
        simp only [clockTape, tempTape, incrementCoreTape]
        apply installCore_over_installCore
        simp [clockRegisters, tempRegisters, layoutEnd_increment]
      rw [htapeThree] at hthree
      have htapeTwo : installCore rightRegisters growth tempTape =
          rightTape := by
        simp only [tempTape, rightTape, incrementCoreTape]
        apply installCore_over_installCore
        simp [tempRegisters, rightRegisters, layoutEnd_increment]
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
          CorePrefixRepresents clockRegisters growth limit clockTape := by
        simpa [clockRegisters, clockTape] using hfinal .clock
      have htempPrefix :
          CorePrefixRepresents tempRegisters growth limit tempTape := by
        simpa [tempRegisters, tempTape] using hfinal .temp
      have hrightPrefix :
          CorePrefixRepresents rightRegisters growth limit rightTape := by
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
      have hfour := machine_reaches_incrementClock_or_halts_of_prefix base c
        source bodySearchBase (searchRef growth source (bodySearchBase + 1))
        (some (directRef growth source testDirectSlot)) h (by simpa [layoutEnd_increment] using hroom) hrawFour
      have hthree := machine_reaches_incrementInternal_or_halts_of_prefix
        (next := tempRegisters) base c
        limit source (bodySearchBase + 1)
        (searchRef growth source (bodySearchBase + 2)) none hclockPrefix
        (3 : Fin 4)
        (by simp [clockRegisters, RegisterLayout.values, Registers.increment,
          Registers.set, Registers.get])
        (by
          have hbound := h.core_before_limit
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
      have htwo := machine_reaches_incrementInternal_or_halts_of_prefix
        (next := rightRegisters) base c
        limit source (bodySearchBase + 2)
        (searchRef growth source (bodySearchBase + 3)) none htempPrefix
        (2 : Fin 4)
        (by simp [tempRegisters, RegisterLayout.values, Registers.increment,
          Registers.set, Registers.get])
        (by
          have hbound := h.core_before_limit
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
      have hone := machine_reaches_incrementInternal_or_halts_of_prefix
        (next := leftRegisters) base c
        limit source (bodySearchBase + 3)
        (directRef growth source bodyDirectBase) none hrightPrefix (1 : Fin 4)
        (by simp [rightRegisters, RegisterLayout.values, Registers.increment,
          Registers.set, Registers.get])
        (by
          have hbound := h.core_before_limit
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
        simp only [clockTape, tempTape, incrementCoreTape]
        apply installCore_over_installCore
        simp [clockRegisters, tempRegisters, layoutEnd_increment]
      rw [htapeThree] at hthree
      have htapeTwo : installCore rightRegisters growth tempTape =
          rightTape := by
        simp only [tempTape, rightTape, incrementCoreTape]
        apply installCore_over_installCore
        simp [tempRegisters, rightRegisters, layoutEnd_increment]
      rw [htapeTwo] at htwo
      have htapeOne : installCore leftRegisters growth rightTape =
          leftTape := by
        simp only [rightTape, leftTape, incrementCoreTape]
        apply installCore_over_installCore
        simp [rightRegisters, leftRegisters, layoutEnd_increment]
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

/-! ## Target-free increment handoff and recovery -/

/-- The cell vacated by the last boundary shift is blank in the exact
core-only increment tape. -/


theorem incrementCoreSchedule_source_blank
    {registers : Registers} {growth : Turing.Dir} {limit : Nat}
    {T : FullTM0.Tape (Symbol numTags)}
    (h : CorePrefixRepresents registers growth limit T) (register : Register)
    (hroom : layoutEnd (registers.increment register) < limit) :
    logicalTape growth (incrementCoreTape registers growth register T)
        (boundaryOffset registers
          (MarkerSchedule.decrementStartBoundary register)) =
      blankSymbol := by
  have hnext := incrementCoreTape_preserves_prefix h register hroom
  cases register with
  | left =>
      have hb := hnext.gap_blank (0 : Fin 4) registers.left (by
        simp [RegisterLayout.values, Registers.increment, Registers.set,
          Registers.get])
      change logicalTape growth (incrementCoreTape registers growth .left T)
        (firstGapOffset (registers.increment .left) 0 + registers.left) =
          blankSymbol at hb
      have hcoord : firstGapOffset (registers.increment .left) 0 +
          registers.left = boundaryOffset registers 1 := by
        simp [firstGapOffset, boundaryOffset, CounterLayout.boundaryPos,
          RegisterLayout.values, Registers.increment, Registers.set,
          Registers.get] <;> omega
      have hcoordInt : (firstGapOffset
          (registers.increment .left) 0 : Int) + registers.left =
          boundaryOffset registers 1 := by
        exact_mod_cast hcoord
      rw [hcoordInt] at hb
      simpa [MarkerSchedule.decrementStartBoundary] using hb
  | right =>
      have hb := hnext.gap_blank (1 : Fin 4) registers.right (by
        simp [RegisterLayout.values, Registers.increment, Registers.set,
          Registers.get])
      change logicalTape growth (incrementCoreTape registers growth .right T)
        (firstGapOffset (registers.increment .right) 1 + registers.right) =
          blankSymbol at hb
      have hcoord : firstGapOffset (registers.increment .right) 1 +
          registers.right = boundaryOffset registers 2 := by
        simp [firstGapOffset, boundaryOffset, CounterLayout.boundaryPos,
          RegisterLayout.values, Registers.increment, Registers.set,
          Registers.get] <;> omega
      have hcoordInt : (firstGapOffset
          (registers.increment .right) 1 : Int) + registers.right =
          boundaryOffset registers 2 := by
        exact_mod_cast hcoord
      rw [hcoordInt] at hb
      simpa [MarkerSchedule.decrementStartBoundary] using hb
  | temp =>
      have hb := hnext.gap_blank (2 : Fin 4) registers.temp (by
        simp [RegisterLayout.values, Registers.increment, Registers.set,
          Registers.get])
      change logicalTape growth (incrementCoreTape registers growth .temp T)
        (firstGapOffset (registers.increment .temp) 2 + registers.temp) =
          blankSymbol at hb
      have hcoord : firstGapOffset (registers.increment .temp) 2 +
          registers.temp = boundaryOffset registers 3 := by
        simp [firstGapOffset, boundaryOffset, CounterLayout.boundaryPos,
          RegisterLayout.values, Registers.increment, Registers.set,
          Registers.get] <;> omega
      have hcoordInt : (firstGapOffset
          (registers.increment .temp) 2 : Int) + registers.temp =
          boundaryOffset registers 3 := by
        exact_mod_cast hcoord
      rw [hcoordInt] at hb
      simpa [MarkerSchedule.decrementStartBoundary] using hb
  | clock =>
      have hb := hnext.gap_blank (3 : Fin 4) registers.clock (by
        simp [RegisterLayout.values, Registers.increment, Registers.set,
          Registers.get])
      change logicalTape growth (incrementCoreTape registers growth .clock T)
        (firstGapOffset (registers.increment .clock) 3 + registers.clock) =
          blankSymbol at hb
      have hcoord : firstGapOffset (registers.increment .clock) 3 +
          registers.clock = boundaryOffset registers 4 := by
        simp [firstGapOffset, boundaryOffset, CounterLayout.boundaryPos,
          RegisterLayout.values, Registers.increment, Registers.set,
          Registers.get] <;> omega
      have hcoordInt : (firstGapOffset
          (registers.increment .clock) 3 : Int) + registers.clock =
          boundaryOffset registers 4 := by
        exact_mod_cast hcoord
      rw [hcoordInt] at hb
      simpa [MarkerSchedule.decrementStartBoundary] using hb

/-- The direct blank rule following the increment schedule moves onto the
shifted boundary and chooses the recovery route (or the logical successor for
the clock register). -/
theorem machine_reaches_incrementHandoff_of_prefix
    (base : Nat) (c : Nat.Partrec.Code) (source next : Nat)
    (register : Register)
    (hrule : (source, .increment register next) ∈
      GlobalSourceProgram.program)
    {registers : Registers} {growth : Turing.Dir} {limit : Nat}
    {T : FullTM0.Tape (Symbol numTags)}
    (h : CorePrefixRepresents registers growth limit T)
    (hroom : layoutEnd (registers.increment register) < limit) :
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
      (atLogical growth (incrementCoreTape registers growth register T)
        (boundaryOffset registers
          (MarkerSchedule.decrementStartBoundary register))).read := by
    change (atLogical growth (incrementCoreTape registers growth register T)
      (boundaryOffset registers
        (MarkerSchedule.decrementStartBoundary register))).read = blankSymbol
    rw [atLogical_read]
    exact incrementCoreSchedule_source_blank h register hroom
  have hrun := CounterControlDirectSemantics.reaches_directRule base c raw
    hraw (atLogical growth (incrementCoreTape registers growth register T)
      (boundaryOffset registers
        (MarkerSchedule.decrementStartBoundary register))) hblank
  have hcoord : boundaryOffset registers
        (MarkerSchedule.decrementStartBoundary register) + 1 =
      boundaryOffset (registers.increment register)
        (MarkerSchedule.decrementStartBoundary register) := by
    cases register <;>
      simp [MarkerSchedule.decrementStartBoundary, boundaryOffset,
        CounterLayout.boundaryPos, RegisterLayout.values,
        Registers.increment, Registers.set, Registers.get] <;> omega
  rw [show orient growth .right =
    OrientedMarkerTape.orientDirection growth .right by
      exact orient_eq_orientDirection growth .right,
    atLogical_move_right, hcoord] at hrun
  change FullTM0.Reaches (CounterControlNestingBridge.machine base c)
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
          (MarkerSchedule.decrementStartBoundary register))⟩ at hrun
  exact hrun

/-- A collision-free increment resolves directly from its validated body
entry and preserves the same finite tag-free prefix. -/
theorem machine_reaches_incrementBody_or_halts_of_prefix
    (base : Nat) (c : Nat.Partrec.Code) (source next : Nat)
    (register : Register)
    (hrule : (source, .increment register next) ∈
      GlobalSourceProgram.program)
    {registers : Registers} {growth : Turing.Dir} {limit : Nat}
    {T : FullTM0.Tape (Symbol numTags)}
    (h : CorePrefixRepresents registers growth limit T)
    (hroom : layoutEnd (registers.increment register) < limit) :
    (FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨resolve base c (bodyEntry growth source (.increment register next)),
          atLogical growth T (layoutEnd registers)⟩
        ⟨logicalState base c growth next,
          atLogical growth (incrementCoreTape registers growth register T)
            (layoutEnd (registers.increment register))⟩ ∧
      CorePrefixRepresents (registers.increment register) growth limit
        (incrementCoreTape registers growth register T)) ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨resolve base c (bodyEntry growth source (.increment register next)),
          atLogical growth T (layoutEnd registers)⟩ := by
  have hcommands : ∀ raw,
      raw ∈ incrementShiftCommands growth source register →
        raw ∈ rawCommands := by
    intro raw hraw
    apply command_mem_rawCommands_of_rule growth hrule
    simp [commandsForRule, incrementCommands, hraw]
  have hschedule := machine_reaches_incrementSchedule_or_halts_of_prefix
    base c source register h hroom hcommands
  have hschedule' :
      FullTM0.Reaches (CounterControlNestingBridge.machine base c)
          ⟨resolve base c
              (bodyEntry growth source (.increment register next)),
            atLogical growth T (layoutEnd registers)⟩
          ⟨resolve base c (directRef growth source bodyDirectBase),
            atLogical growth (incrementCoreTape registers growth register T)
              (boundaryOffset registers
                (MarkerSchedule.decrementStartBoundary register))⟩ ∨
        FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
          ⟨resolve base c
              (bodyEntry growth source (.increment register next)),
            atLogical growth T (layoutEnd registers)⟩ := by
    simpa [bodyEntry, searchRef, CounterControlPlan.resolve] using
      hschedule.imp (fun hsuccess => hsuccess.1) id
  have hhandoff := machine_reaches_incrementHandoff_of_prefix base c
    source next register hrule h hroom
  have hnext := incrementCoreTape_preserves_prefix h register hroom
  have hrecovery := machine_reaches_incrementRecovery_or_halts_of_core
    base c source next register hrule hnext.toCoreRepresents
  have hrun := FullTM0.ResolvesTo.trans hschedule'
    (FullTM0.ResolvesTo.trans (Or.inl hhandoff) hrecovery)
  rcases hrun with hrun | hhalts
  · exact Or.inl ⟨hrun, hnext⟩
  · exact Or.inr hhalts

/-! ## Outward collision on a tag-free prefix -/

/-- The first outward shift takes its generated collision exit when the
finite prefix ends immediately after boundary `4`. -/
theorem machine_reaches_incrementCollision_of_prefix
    (base : Nat) (c : Nat.Partrec.Code) (source : Nat)
    (success : ControlRef)
    {registers : Registers} {growth : Turing.Dir} {limit : Nat}
    {target : Target numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : CoreTargetRepresents registers growth limit target T)
    (hcollision : layoutEnd registers + 1 = limit)
    (hraw : RawCommand.markerShift
      ⟨growth, source, bodySearchBase⟩ 4 .left .right
      success (some .left)
      (some (directRef growth source testDirectSlot)) ∈ rawCommands) :
    let spec := prefixSpec registers growth limit target
      h.core_before_limit
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      ⟨searchState base c ⟨growth, source, bodySearchBase⟩,
        atLogical growth T (layoutEnd registers)⟩
      ⟨resolve base c (directRef growth source testDirectSlot),
        atLogical growth
          (CounterControlCleanupSemantics.afterFour spec T) limit⟩ := by
  let spec := prefixSpec registers growth limit target h.core_before_limit
  let raw : RawCommand :=
    .markerShift ⟨growth, source, bodySearchBase⟩ 4 .left .right
      success (some .left)
      (some (directRef growth source testDirectSlot))
  let move : MarkerProgram.Move :=
    ⟨4, orient growth .left, orient growth .right⟩
  have hatRaw := CommandAt.compileRawCommand base c raw hraw
  have hspec := compileRawCommand_spec base c raw hraw
  have hat : CommandAt (CanonicalInitializer.radius c) base
      (searchState base c ⟨growth, source, bodySearchBase⟩)
      (.markerShift move (resolve base c success) (rawTag raw hraw)
        (some (orient growth .left))
        (some (resolve base c (directRef growth source testDirectSlot))))
      (commands base c) := by
    rw [hspec] at hatRaw
    simpa [raw, move, compileRawAtTag, RawCommand.address] using hatRaw
  have hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary 4).Matches
      (atLogical growth T (layoutEnd registers))
      (orient growth .left) 0 := by
    rw [SearchGap.zero]
    exact h.read_boundary_four
  have htargetNonblank : logicalTape growth T
      (layoutEnd registers + 1) ≠ blankSymbol := by
    have hcollisionZ : (layoutEnd registers : Int) + 1 = limit := by
      exact_mod_cast hcollision
    rw [hcollisionZ]
    exact h.target_ne_blank
  have hnonblank :
      (((((atLogical growth T (layoutEnd registers)).moveN
        move.searchDirection 0).write blankSymbol).move
          move.shiftDirection).read ≠ blankSymbol) := by
    rw [FullTM0.Tape.moveN_zero]
    change (((atLogical growth T (layoutEnd registers)).write
      blankSymbol).move (orient growth .right)).read ≠ blankSymbol
    rw [atLogical_write, orient_eq_orientDirection,
      atLogical_move_right, atLogical_read]
    rw [writeLogical_of_ne growth T (layoutEnd registers)
      (layoutEnd registers + 1) blankSymbol (by omega)]
    exact htargetNonblank
  have hrun := CounterControlBridge.machine_reaches_shift_collision
    (coreTable base c) move (resolve base c success)
    (resolve base c (directRef growth source testDirectSlot))
    (rawTag raw hraw) (some (orient growth .left)) hat
    (atLogical growth T (layoutEnd registers)) 0 hgap (by simp) hnonblank
  have htape :
      (atLogical growth
          (writeLogical growth T (layoutEnd registers) blankSymbol)
          (layoutEnd registers)).move growth =
        atLogical growth
          (writeLogical growth T (layoutEnd registers) blankSymbol)
          limit := by
    have hmove := atLogical_move_right growth
      (writeLogical growth T (layoutEnd registers) blankSymbol)
      (layoutEnd registers)
    rw [OrientedMarkerTape.orientDirection_growth_right, hcollision] at hmove
    exact hmove
  simp only [move, FullTM0.Tape.moveN_zero, atLogical_write,
    orient_eq_orientDirection,
    OrientedMarkerTape.orientDirection_growth_right, htape] at hrun
  simpa [spec, prefixSpec, CounterControlNestingBridge.machine,
    BoundedMarkerProgram.entryState,
    CounterControlCleanupSemantics.afterFour,
    CounterControlCleanupSemantics.clearBoundary,
    boundaryOffset_four] using hrun

/-! ## Cleanup from a core without a saved-tag hypothesis -/

private theorem atLogical_write_above_apply_left_of_core
    (growth : Turing.Dir) (T : FullTM0.Tape (Symbol numTags))
    (written origin k : Nat) (symbol : Symbol numTags)
    (habove : origin < written) :
    atLogical growth (writeLogical growth T written symbol) origin
        (FullTM0.Tape.offset
          (OrientedMarkerTape.orientDirection growth .left) k) =
      atLogical growth T origin
        (FullTM0.Tape.offset
          (OrientedMarkerTape.orientDirection growth .left) k) := by
  rw [atLogical_apply_offset, atLogical_apply_offset]
  cases growth <;>
    simp [logicalTape, OrientedMarkerTape.orientTape, writeLogical,
      physicalCoord, Function.update, FullTM0.Tape.offset] <;> omega

private theorem searchGap_write_above_left_of_core
    {IsMark : Symbol numTags → Prop} (growth : Turing.Dir)
    (T : FullTM0.Tape (Symbol numTags)) (written origin distance : Nat)
    (symbol : Symbol numTags) (habove : origin < written)
    (hgap : SearchGap (fun a => a = blankSymbol) IsMark
      (atLogical growth T origin)
      (OrientedMarkerTape.orientDirection growth .left) distance) :
    SearchGap (fun a => a = blankSymbol) IsMark
      (atLogical growth (writeLogical growth T written symbol) origin)
      (OrientedMarkerTape.orientDirection growth .left) distance := by
  constructor
  · intro k hk
    rw [atLogical_write_above_apply_left_of_core growth T written origin k
      symbol habove]
    exact hgap.blank hk
  · rw [atLogical_write_above_apply_left_of_core growth T written origin
      distance symbol habove]
    exact hgap.marked

private theorem written_boundary_above_lastGap_of_core
    (registers : Registers) (i : Fin 4) (label : Fin 5)
    (hlabel : (i : Nat) < label) :
    lastGapOffset registers i < boundaryOffset registers label := by
  simp only [lastGapOffset, boundaryOffset]
  have hle : (i : Nat) + 1 ≤ label := by omega
  have hmono := CounterLayout.boundaryPos_mono
    (RegisterLayout.values registers) hle
  omega

private theorem cleanup_boundary_three_eq_lastGap_two_add_one_of_core
    (registers : Registers) :
    boundaryOffset registers 3 = lastGapOffset registers 2 + 1 := by
  simp [boundaryOffset, lastGapOffset]

private theorem cleanup_boundary_two_eq_lastGap_one_add_one_of_core
    (registers : Registers) :
    boundaryOffset registers 2 = lastGapOffset registers 1 + 1 := by
  simp [boundaryOffset, lastGapOffset]

private theorem cleanup_boundary_one_eq_lastGap_zero_add_one_of_core
    (registers : Registers) :
    boundaryOffset registers 1 = lastGapOffset registers 0 + 1 := by
  simp [boundaryOffset, lastGapOffset]

/-- The first cleanup gap depends only on the five-boundary core. -/
theorem cleanupGap_three_of_core {spec : Spec numTags}
    {T : FullTM0.Tape (Symbol numTags)}
    (h : CoreRepresents spec.registers spec.growth T) :
    SearchGap (fun a => a = blankSymbol)
      (Target.boundary 3).Matches
      (atLogical spec.growth (afterFour spec T)
        (boundaryOffset spec.registers 4))
      (orient spec.growth .left)
      (RegisterLayout.values spec.registers 3 + 1) := by
  have hbase : SearchGap (fun a => a = blankSymbol)
      (Target.boundary 3).Matches
      (atLogical spec.growth T (lastGapOffset spec.registers 3))
      (orient spec.growth .left)
      (RegisterLayout.values spec.registers 3) := by
    change SearchGap (fun a => a = blankSymbol)
      (fun symbol => symbol = boundarySymbol 3) _ _ _
    exact h.searchGap_adjacent_left (3 : Fin 4)
  have htail := searchGap_write_above_left_of_core spec.growth T
    (boundaryOffset spec.registers 4) (lastGapOffset spec.registers 3)
    (RegisterLayout.values spec.registers 3) blankSymbol
    (written_boundary_above_lastGap_of_core spec.registers 3 4 (by decide))
    hbase
  apply searchGap_erased_right_boundary (spec := spec) (i := (3 : Fin 4))
  · simpa [afterFour, clearBoundary] using htail
  · change logicalTape spec.growth
      (writeLogical spec.growth T (boundaryOffset spec.registers 4)
        blankSymbol) (boundaryOffset spec.registers 4) = blankSymbol
    exact writeLogical_at spec.growth T
      (boundaryOffset spec.registers 4) blankSymbol

/-- The second cleanup gap depends only on the five-boundary core. -/
theorem cleanupGap_two_of_core {spec : Spec numTags}
    {T : FullTM0.Tape (Symbol numTags)}
    (h : CoreRepresents spec.registers spec.growth T) :
    SearchGap (fun a => a = blankSymbol)
      (Target.boundary 2).Matches
      (atLogical spec.growth (afterThree spec T)
        (lastGapOffset spec.registers 2))
      (orient spec.growth .left)
      (RegisterLayout.values spec.registers 2) := by
  have hbase : SearchGap (fun a => a = blankSymbol)
      (Target.boundary 2).Matches
      (atLogical spec.growth T (lastGapOffset spec.registers 2))
      (orient spec.growth .left)
      (RegisterLayout.values spec.registers 2) := by
    change SearchGap (fun a => a = blankSymbol)
      (fun symbol => symbol = boundarySymbol 2) _ _ _
    exact h.searchGap_adjacent_left (2 : Fin 4)
  have hfour := searchGap_write_above_left_of_core spec.growth T
    (boundaryOffset spec.registers 4) (lastGapOffset spec.registers 2)
    (RegisterLayout.values spec.registers 2) blankSymbol
    (written_boundary_above_lastGap_of_core spec.registers 2 4 (by decide))
    hbase
  have hthree := searchGap_write_above_left_of_core spec.growth
    (afterFour spec T)
    (boundaryOffset spec.registers 3) (lastGapOffset spec.registers 2)
    (RegisterLayout.values spec.registers 2) blankSymbol
    (written_boundary_above_lastGap_of_core spec.registers 2 3 (by decide))
    (by simpa [afterFour, clearBoundary] using hfour)
  simpa [afterThree, clearBoundary] using hthree

/-- The third cleanup gap depends only on the five-boundary core. -/
theorem cleanupGap_one_of_core {spec : Spec numTags}
    {T : FullTM0.Tape (Symbol numTags)}
    (h : CoreRepresents spec.registers spec.growth T) :
    SearchGap (fun a => a = blankSymbol)
      (Target.boundary 1).Matches
      (atLogical spec.growth (afterTwo spec T)
        (lastGapOffset spec.registers 1))
      (orient spec.growth .left)
      (RegisterLayout.values spec.registers 1) := by
  have hbase : SearchGap (fun a => a = blankSymbol)
      (Target.boundary 1).Matches
      (atLogical spec.growth T (lastGapOffset spec.registers 1))
      (orient spec.growth .left)
      (RegisterLayout.values spec.registers 1) := by
    change SearchGap (fun a => a = blankSymbol)
      (fun symbol => symbol = boundarySymbol 1) _ _ _
    exact h.searchGap_adjacent_left (1 : Fin 4)
  have hfour := searchGap_write_above_left_of_core spec.growth T
    (boundaryOffset spec.registers 4) (lastGapOffset spec.registers 1)
    (RegisterLayout.values spec.registers 1) blankSymbol
    (written_boundary_above_lastGap_of_core spec.registers 1 4 (by decide))
    hbase
  have hthree := searchGap_write_above_left_of_core spec.growth
    (afterFour spec T)
    (boundaryOffset spec.registers 3) (lastGapOffset spec.registers 1)
    (RegisterLayout.values spec.registers 1) blankSymbol
    (written_boundary_above_lastGap_of_core spec.registers 1 3 (by decide))
    (by simpa [afterFour, clearBoundary] using hfour)
  have htwo := searchGap_write_above_left_of_core spec.growth
    (afterThree spec T)
    (boundaryOffset spec.registers 2) (lastGapOffset spec.registers 1)
    (RegisterLayout.values spec.registers 1) blankSymbol
    (written_boundary_above_lastGap_of_core spec.registers 1 2 (by decide))
    (by simpa [afterThree, clearBoundary] using hthree)
  simpa [afterTwo, clearBoundary] using htwo

/-- The fourth cleanup gap depends only on the five-boundary core. -/
theorem cleanupGap_zero_of_core {spec : Spec numTags}
    {T : FullTM0.Tape (Symbol numTags)}
    (h : CoreRepresents spec.registers spec.growth T) :
    SearchGap (fun a => a = blankSymbol)
      (Target.boundary 0).Matches
      (atLogical spec.growth (afterOne spec T)
        (lastGapOffset spec.registers 0))
      (orient spec.growth .left)
      (RegisterLayout.values spec.registers 0) := by
  have hbase : SearchGap (fun a => a = blankSymbol)
      (Target.boundary 0).Matches
      (atLogical spec.growth T (lastGapOffset spec.registers 0))
      (orient spec.growth .left)
      (RegisterLayout.values spec.registers 0) := by
    change SearchGap (fun a => a = blankSymbol)
      (fun symbol => symbol = boundarySymbol 0) _ _ _
    exact h.searchGap_adjacent_left (0 : Fin 4)
  have hfour := searchGap_write_above_left_of_core spec.growth T
    (boundaryOffset spec.registers 4) (lastGapOffset spec.registers 0)
    (RegisterLayout.values spec.registers 0) blankSymbol
    (written_boundary_above_lastGap_of_core spec.registers 0 4 (by decide))
    hbase
  have hthree := searchGap_write_above_left_of_core spec.growth
    (afterFour spec T)
    (boundaryOffset spec.registers 3) (lastGapOffset spec.registers 0)
    (RegisterLayout.values spec.registers 0) blankSymbol
    (written_boundary_above_lastGap_of_core spec.registers 0 3 (by decide))
    (by simpa [afterFour, clearBoundary] using hfour)
  have htwo := searchGap_write_above_left_of_core spec.growth
    (afterThree spec T)
    (boundaryOffset spec.registers 2) (lastGapOffset spec.registers 0)
    (RegisterLayout.values spec.registers 0) blankSymbol
    (written_boundary_above_lastGap_of_core spec.registers 0 2 (by decide))
    (by simpa [afterThree, clearBoundary] using hthree)
  have hone := searchGap_write_above_left_of_core spec.growth
    (afterTwo spec T)
    (boundaryOffset spec.registers 1) (lastGapOffset spec.registers 0)
    (RegisterLayout.values spec.registers 0) blankSymbol
    (written_boundary_above_lastGap_of_core spec.registers 0 1 (by decide))
    (by simpa [afterTwo, clearBoundary] using htwo)
  simpa [afterOne, clearBoundary] using hone


theorem machine_reaches_decrementCanonical_or_halts_of_prefix
    (base : Nat) (c : Nat.Partrec.Code) (limit : Nat)
    (counterState searchSlot : Nat)
    (success : ControlRef) (collision : Option ControlRef)
    {current next : Registers} {growth : Turing.Dir}
    {T : FullTM0.Tape (Symbol numTags)}
    (h : CorePrefixRepresents current growth limit T) (label : Fin 5)
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
      CorePrefixRepresents next growth limit
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
    have hnextCore : layoutEnd next < limit :=
      hlower.trans_lt h.core_before_limit
    have hnormalized := moveLeft_corePrefix h label hnextCore hlower hupper
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
theorem machine_reaches_decrementFirst_or_halts_of_prefix
    (base : Nat) (c : Nat.Partrec.Code) (limit : Nat)
    (counterState searchSlot : Nat) (success : ControlRef)
    (hlimit : 0 < limit)
    {current next : Registers} {growth : Turing.Dir}
    {T : FullTM0.Tape (Symbol numTags)}
    (h : CorePrefixRepresents current growth limit T) (i : Fin 4)
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
      CorePrefixRepresents next growth limit
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
  apply machine_reaches_decrementCanonical_or_halts_of_prefix base c limit
    counterState searchSlot success none h i.succ
    (boundaryOffset current i.succ) 0 hsourcePositive
    (by simp) hlimit hgap hblank hlower hupper hsource hdestination hshrink
    hmove hraw

/-- Every later positive-decrement shift searches one represented gap. -/
theorem machine_reaches_decrementFollowing_or_halts_of_prefix
    (base : Nat) (c : Nat.Partrec.Code) (limit : Nat)
    (counterState searchSlot : Nat) (success : ControlRef)
    {current next : Registers} {growth : Turing.Dir}
    {T : FullTM0.Tape (Symbol numTags)}
    (h : CorePrefixRepresents current growth limit T) (i : Fin 4)
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
      CorePrefixRepresents next growth limit
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
  exact machine_reaches_decrementCanonical_or_halts_of_prefix base c limit
    counterState searchSlot success none h i.succ
    (firstGapOffset current i) (RegisterLayout.values current i)
    hsourcePositive horigin hdistance hgap hblank hlower hupper hsource
    hdestination hshrink hmove hraw

/-- Installing a core at least as long as a represented finite prefix
preserves its runway when the new core still lies before the same limit. -/
theorem installCore_prefix_of_extension
    {current next : Registers} {growth : Turing.Dir} {limit : Nat}
    {T : FullTM0.Tape (Symbol numTags)}
    (h : CorePrefixRepresents current growth limit T)
    (hle : layoutEnd current ≤ layoutEnd next)
    (hnext : layoutEnd next < limit) :
    CorePrefixRepresents next growth limit (installCore next growth T) := by
  constructor
  · constructor
    intro position hposition
    exact installCore_core next growth T position hposition
  · exact hnext
  · intro position hpast hlimit
    rw [installCore_of_layoutEnd_lt next growth T hpast]
    exact h.runway position (hle.trans_lt hpast) hlimit

/-- A finite blank runway as an instance of the common decrement-schedule
interface. -/
def prefixDecrementEnvelope (growth : Turing.Dir) (limit : Nat) :
    DecrementEnvelope growth limit where
  Represents registers T := CorePrefixRepresents registers growth limit T
  first := by
    intro base c counterState searchSlot success current next T hlimit h i
      hpositive hlower hupper hsource hdestination hshrink hmove hraw
    exact machine_reaches_decrementFirst_or_halts_of_prefix
      base c limit counterState searchSlot success hlimit h i hpositive
      hlower hupper hsource hdestination hshrink hmove hraw
  following := by
    intro base c counterState searchSlot success current next T h i hpositive
      hdistance hlower hupper hsource hdestination hshrink hmove hraw
    exact machine_reaches_decrementFollowing_or_halts_of_prefix
      base c limit counterState searchSlot success h i hpositive hdistance
      hlower hupper hsource hdestination hshrink hmove hraw
  install_equal_length := by
    intro current next T h heq
    exact installCore_prefix_of_extension h heq.ge (by simpa [heq] using
      h.core_before_limit)
  registerValue_lt := by
    intro registers T h i
    exact registerValue_lt_of_layoutEnd_lt registers i h.core_before_limit
  limit_positive := by
    intro registers T h
    exact limit_positive_of_layoutEnd_lt registers h.core_before_limit
  decrement := by
    intro registers T register h hpositive
    exact decrementCoreTape_preserves_prefix h register hpositive

/-- Uniform positive-decrement schedule inside a finite tag-free prefix. -/
theorem machine_reaches_decrementSchedule_or_halts_of_prefix
    (base : Nat) (c : Nat.Partrec.Code) (source : Nat)
    (register : Register)
    {registers : Registers} {growth : Turing.Dir} {limit : Nat}
    {T : FullTM0.Tape (Symbol numTags)}
    (h : CorePrefixRepresents registers growth limit T)
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
      CorePrefixRepresents (registers.decrement register) growth limit
        (decrementCoreTape registers growth register T)) ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨growth, source, secondarySearchBase⟩,
          atLogical growth T
            (boundaryOffset registers
              (MarkerSchedule.decrementStartBoundary register))⟩ := by
  exact machine_reaches_decrementSchedule_or_halts_of_envelope
    base c source register (prefixDecrementEnvelope growth limit) h
      hpositive hcommands



theorem machine_reaches_decrementZeroBody_or_halts_of_prefix
    (base : Nat) (c : Nat.Partrec.Code) (growth : Turing.Dir)
    (source ifZero ifPositive : Nat) (register : Register)
    (hrule : (source, .decrement register ifZero ifPositive) ∈
      GlobalSourceProgram.program)
    {registers : Registers} {limit : Nat}
    {T : FullTM0.Tape (Symbol numTags)}
    (h : CorePrefixRepresents registers growth limit T)
    (hzero : registers.get register = 0) :
    (FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨resolve base c
            (bodyEntry growth source
              (.decrement register ifZero ifPositive)),
          atLogical growth T (layoutEnd registers)⟩
        ⟨logicalState base c growth ifZero,
          atLogical growth T (layoutEnd registers)⟩ ∧
      CorePrefixRepresents registers growth limit T) ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨resolve base c
            (bodyEntry growth source
              (.decrement register ifZero ifPositive)),
          atLogical growth T (layoutEnd registers)⟩ := by
  have hroute := machine_reaches_decrementToTest_or_halts_of_core
    base c growth source ifZero ifPositive register hrule
    h.toCoreRepresents
  have htest := CounterControlInstructionSemantics.machine_reaches_decrementTest
    base c source ifZero ifPositive register hrule
    (spec := CounterControlOpenInstructionResolution.openSpec registers growth)
    T (by
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
    simpa [CounterControlOpenInstructionResolution.openSpec] using htest
  have hzeroRoute :=
    machine_reaches_decrementZeroRecovery_or_halts_of_core
      base c growth source ifZero ifPositive register hrule
      h.toCoreRepresents hzero
  have hrun := FullTM0.ResolvesTo.trans hroute
    (FullTM0.ResolvesTo.trans (Or.inl htest') hzeroRoute)
  rcases hrun with hrun | hhalts
  · exact Or.inl ⟨hrun, h⟩
  · exact Or.inr hhalts

/-- The positive branch resolves from the validated body entry and preserves
the finite tag-free prefix while shrinking the core by one cell. -/
theorem machine_reaches_decrementPositiveBody_or_halts_of_prefix
    (base : Nat) (c : Nat.Partrec.Code)
    (source ifZero ifPositive : Nat) (register : Register)
    (hrule : (source, .decrement register ifZero ifPositive) ∈
      GlobalSourceProgram.program)
    {registers : Registers} {growth : Turing.Dir} {limit : Nat}
    {T : FullTM0.Tape (Symbol numTags)}
    (h : CorePrefixRepresents registers growth limit T)
    (hpositive : 0 < registers.get register) :
    (FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨resolve base c
            (bodyEntry growth source
              (.decrement register ifZero ifPositive)),
          atLogical growth T (layoutEnd registers)⟩
        ⟨logicalState base c growth ifPositive,
          atLogical growth (decrementCoreTape registers growth register T)
            (layoutEnd (registers.decrement register))⟩ ∧
      CorePrefixRepresents (registers.decrement register) growth limit
        (decrementCoreTape registers growth register T)) ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨resolve base c
            (bodyEntry growth source
              (.decrement register ifZero ifPositive)),
          atLogical growth T (layoutEnd registers)⟩ := by
  have hroute := machine_reaches_decrementToTest_or_halts_of_core
    base c growth source ifZero ifPositive register hrule
    h.toCoreRepresents
  have htest := CounterControlInstructionSemantics.machine_reaches_decrementTest
    base c source ifZero ifPositive register hrule
    (spec := CounterControlOpenInstructionResolution.openSpec registers growth)
    T (by
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
    simpa [CounterControlOpenInstructionResolution.openSpec] using htest
  have hhandoff := machine_reaches_decrementPositiveHandoff_of_core base c
    source ifZero ifPositive register hrule h.toCoreRepresents hpositive
  have hcommands : ∀ raw,
      raw ∈ decrementShiftCommands growth source register →
        raw ∈ rawCommands := by
    intro raw hraw
    apply command_mem_rawCommands_of_rule growth hrule
    simp [commandsForRule, decrementCommands, hraw]
  have hschedule := machine_reaches_decrementSchedule_or_halts_of_prefix
    base c source register h hpositive hcommands
  have hfinish := machine_reaches_decrementPositiveFinish_of_core base c
    source ifZero ifPositive register hrule growth T hpositive
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
  have hrun := FullTM0.ResolvesTo.trans hroute
    (FullTM0.ResolvesTo.trans (Or.inl htest')
      (FullTM0.ResolvesTo.trans (Or.inl hhandoff) hscheduleFinish))
  rcases hrun with hrun | hhalts
  · exact Or.inl ⟨hrun,
      decrementCoreTape_preserves_prefix h register hpositive⟩
  · exact Or.inr hhalts

/-! ## Exact tag-free cleanup -/

/-- Cleanup never reads logical coordinate `0`: the four boundary erasures
therefore reach the shared directional return state from a core prefix even
when the adjacent cell is not a saved tag. -/
theorem machine_reaches_cleanup_return_or_halts_of_prefix
    (base : Nat) (c : Nat.Partrec.Code) (source : Nat)
    {registers : Registers} {growth : Turing.Dir} {limit : Nat}
    {target : Target numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : CorePrefixRepresents registers growth limit T)
    (hcommands : ∀ raw, raw ∈ cleanupCommands growth source →
      raw ∈ rawCommands) :
    let spec := prefixSpec registers growth limit target h.core_before_limit
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨growth, source, cleanupSearchBase⟩,
          atLogical growth (afterFour spec T) (layoutEnd registers)⟩
        ⟨controllerReturn base c growth,
          atLogical growth (afterZero spec T) 0⟩ ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨growth, source, cleanupSearchBase⟩,
          atLogical growth (afterFour spec T) (layoutEnd registers)⟩ := by
  let spec := prefixSpec registers growth limit target h.core_before_limit
  let rawThree : RawCommand :=
    .boundaryNavigation ⟨growth, source, cleanupSearchBase⟩ 3 .left
      (searchRef growth source (cleanupSearchBase + 1))
      (.erase (some .left))
  let rawTwo : RawCommand :=
    .boundaryNavigation ⟨growth, source, cleanupSearchBase + 1⟩ 2 .left
      (searchRef growth source (cleanupSearchBase + 2))
      (.erase (some .left))
  let rawOne : RawCommand :=
    .boundaryNavigation ⟨growth, source, cleanupSearchBase + 2⟩ 1 .left
      (searchRef growth source (cleanupSearchBase + 3))
      (.erase (some .left))
  let rawZero : RawCommand :=
    .boundaryNavigation ⟨growth, source, cleanupSearchBase + 3⟩ 0 .left
      (.sharedReturn growth) (.erase (some .left))
  have hrawThree : rawThree ∈ rawCommands := hcommands rawThree (by
    simp [rawThree, cleanupCommands])
  have hrawTwo : rawTwo ∈ rawCommands := hcommands rawTwo (by
    simp [rawTwo, cleanupCommands])
  have hrawOne : rawOne ∈ rawCommands := hcommands rawOne (by
    simp [rawOne, cleanupCommands])
  have hrawZero : rawZero ∈ rawCommands := hcommands rawZero (by
    simp [rawZero, cleanupCommands])
  have hshort : ShortResolves base c limit :=
    CounterControlLooseFrameMortality.shortResolves_all base c limit
  have hdistanceThree : RegisterLayout.values registers 3 + 1 < limit := by
    have hcore := h.core_before_limit
    rw [layoutEnd_eq] at hcore
    simp [RegisterLayout.values] at hcore ⊢
    omega
  have hdistanceTwo : RegisterLayout.values registers 2 < limit :=
    registerValue_lt_limit_of_prefix h (2 : Fin 4)
  have hdistanceOne : RegisterLayout.values registers 1 < limit :=
    registerValue_lt_limit_of_prefix h (1 : Fin 4)
  have hdistanceZero : RegisterLayout.values registers 0 < limit :=
    registerValue_lt_limit_of_prefix h (0 : Fin 4)
  have hgapThree := cleanupGap_three_of_core
    (spec := spec) h.toCoreRepresents
  have hrunThree := machine_reaches_boundary_erase_or_halts base c limit
    hshort ⟨growth, source, cleanupSearchBase⟩ 3 .left
    (searchRef growth source (cleanupSearchBase + 1)) (some .left)
    hrawThree
    (atLogical growth (afterFour spec T) (boundaryOffset registers 4))
    (RegisterLayout.values registers 3 + 1) hdistanceThree
    (by simpa [spec, prefixSpec] using hgapThree)
  have hthree :
      FullTM0.Reaches (CounterControlNestingBridge.machine base c)
          ⟨searchState base c ⟨growth, source, cleanupSearchBase⟩,
            atLogical growth (afterFour spec T) (layoutEnd registers)⟩
          ⟨searchState base c
              ⟨growth, source, cleanupSearchBase + 1⟩,
            atLogical growth (afterThree spec T)
              (lastGapOffset registers 2)⟩ ∨
        FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
          ⟨searchState base c ⟨growth, source, cleanupSearchBase⟩,
            atLogical growth (afterFour spec T)
              (layoutEnd registers)⟩ := by
    rcases hrunThree with hrun | hhalts
    · left
      have hstart : boundaryOffset registers 4 =
          boundaryOffset registers 3 +
            (RegisterLayout.values registers 3 + 1) := by
        simp [boundaryOffset, CounterLayout.boundaryPos]
        omega
      have hfound :
          (atLogical growth (afterFour spec T)
              (boundaryOffset registers 4)).moveN
              (orient growth .left)
              (RegisterLayout.values registers 3 + 1) =
            atLogical growth (afterFour spec T)
              (boundaryOffset registers 3) := by
        rw [hstart, orient_eq_orientDirection, atLogical_moveN_left]
      simp only at hrun
      rw [hfound, orient_eq_orientDirection,
        cleanup_boundary_three_eq_lastGap_two_add_one_of_core,
        erase_departLeft_atLogical] at hrun
      rw [← cleanup_boundary_three_eq_lastGap_two_add_one_of_core] at hrun
      simpa [rawThree, searchRef, CounterControlPlan.resolve,
        afterThree, clearBoundary, spec, prefixSpec] using hrun
    · exact Or.inr hhalts
  have hgapTwo := cleanupGap_two_of_core
    (spec := spec) h.toCoreRepresents
  have hrunTwo := machine_reaches_boundary_erase_or_halts base c limit
    hshort ⟨growth, source, cleanupSearchBase + 1⟩ 2 .left
    (searchRef growth source (cleanupSearchBase + 2)) (some .left)
    hrawTwo
    (atLogical growth (afterThree spec T) (lastGapOffset registers 2))
    (RegisterLayout.values registers 2) hdistanceTwo
    (by simpa [spec, prefixSpec] using hgapTwo)
  have htwo :
      FullTM0.Reaches (CounterControlNestingBridge.machine base c)
          ⟨searchState base c
              ⟨growth, source, cleanupSearchBase + 1⟩,
            atLogical growth (afterThree spec T)
              (lastGapOffset registers 2)⟩
          ⟨searchState base c
              ⟨growth, source, cleanupSearchBase + 2⟩,
            atLogical growth (afterTwo spec T)
              (lastGapOffset registers 1)⟩ ∨
        FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
          ⟨searchState base c
              ⟨growth, source, cleanupSearchBase + 1⟩,
            atLogical growth (afterThree spec T)
              (lastGapOffset registers 2)⟩ := by
    rcases hrunTwo with hrun | hhalts
    · left
      have hstart : lastGapOffset registers 2 =
          boundaryOffset registers 2 + RegisterLayout.values registers 2 := by
        simp [lastGapOffset, boundaryOffset, CounterLayout.boundaryPos]
        omega
      have hfound :
          (atLogical growth (afterThree spec T)
              (lastGapOffset registers 2)).moveN
              (orient growth .left) (RegisterLayout.values registers 2) =
            atLogical growth (afterThree spec T)
              (boundaryOffset registers 2) := by
        rw [hstart, orient_eq_orientDirection, atLogical_moveN_left]
      simp only at hrun
      rw [hfound, orient_eq_orientDirection,
        cleanup_boundary_two_eq_lastGap_one_add_one_of_core,
        erase_departLeft_atLogical] at hrun
      rw [← cleanup_boundary_two_eq_lastGap_one_add_one_of_core] at hrun
      simpa [rawTwo, searchRef, CounterControlPlan.resolve,
        afterTwo, clearBoundary, spec, prefixSpec] using hrun
    · exact Or.inr hhalts
  have hgapOne := cleanupGap_one_of_core
    (spec := spec) h.toCoreRepresents
  have hrunOne := machine_reaches_boundary_erase_or_halts base c limit
    hshort ⟨growth, source, cleanupSearchBase + 2⟩ 1 .left
    (searchRef growth source (cleanupSearchBase + 3)) (some .left)
    hrawOne
    (atLogical growth (afterTwo spec T) (lastGapOffset registers 1))
    (RegisterLayout.values registers 1) hdistanceOne
    (by simpa [spec, prefixSpec] using hgapOne)
  have hone :
      FullTM0.Reaches (CounterControlNestingBridge.machine base c)
          ⟨searchState base c
              ⟨growth, source, cleanupSearchBase + 2⟩,
            atLogical growth (afterTwo spec T)
              (lastGapOffset registers 1)⟩
          ⟨searchState base c
              ⟨growth, source, cleanupSearchBase + 3⟩,
            atLogical growth (afterOne spec T)
              (lastGapOffset registers 0)⟩ ∨
        FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
          ⟨searchState base c
              ⟨growth, source, cleanupSearchBase + 2⟩,
            atLogical growth (afterTwo spec T)
              (lastGapOffset registers 1)⟩ := by
    rcases hrunOne with hrun | hhalts
    · left
      have hstart : lastGapOffset registers 1 =
          boundaryOffset registers 1 + RegisterLayout.values registers 1 := by
        simp [lastGapOffset, boundaryOffset, CounterLayout.boundaryPos]
        omega
      have hfound :
          (atLogical growth (afterTwo spec T)
              (lastGapOffset registers 1)).moveN
              (orient growth .left) (RegisterLayout.values registers 1) =
            atLogical growth (afterTwo spec T)
              (boundaryOffset registers 1) := by
        rw [hstart, orient_eq_orientDirection, atLogical_moveN_left]
      simp only at hrun
      rw [hfound, orient_eq_orientDirection,
        cleanup_boundary_one_eq_lastGap_zero_add_one_of_core,
        erase_departLeft_atLogical] at hrun
      rw [← cleanup_boundary_one_eq_lastGap_zero_add_one_of_core] at hrun
      simpa [rawOne, searchRef, CounterControlPlan.resolve,
        afterOne, clearBoundary, spec, prefixSpec] using hrun
    · exact Or.inr hhalts
  have hgapZero := cleanupGap_zero_of_core
    (spec := spec) h.toCoreRepresents
  have hrunZero := machine_reaches_boundary_erase_or_halts base c limit
    hshort ⟨growth, source, cleanupSearchBase + 3⟩ 0 .left
    (.sharedReturn growth) (some .left) hrawZero
    (atLogical growth (afterOne spec T) (lastGapOffset registers 0))
    (RegisterLayout.values registers 0) hdistanceZero
    (by simpa [spec, prefixSpec] using hgapZero)
  have hzero :
      FullTM0.Reaches (CounterControlNestingBridge.machine base c)
          ⟨searchState base c
              ⟨growth, source, cleanupSearchBase + 3⟩,
            atLogical growth (afterOne spec T)
              (lastGapOffset registers 0)⟩
          ⟨controllerReturn base c growth,
            atLogical growth (afterZero spec T) 0⟩ ∨
        FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
          ⟨searchState base c
              ⟨growth, source, cleanupSearchBase + 3⟩,
            atLogical growth (afterOne spec T)
              (lastGapOffset registers 0)⟩ := by
    rcases hrunZero with hrun | hhalts
    · left
      have hstart : lastGapOffset registers 0 =
          1 + RegisterLayout.values registers 0 := by
        simp [lastGapOffset, boundaryOffset, CounterLayout.boundaryPos]
        omega
      have hfound :
          (atLogical growth (afterOne spec T)
              (lastGapOffset registers 0)).moveN
              (orient growth .left) (RegisterLayout.values registers 0) =
            atLogical growth (afterOne spec T) 1 := by
        rw [hstart, orient_eq_orientDirection, atLogical_moveN_left]
      simp only at hrun
      rw [hfound, orient_eq_orientDirection,
        erase_departLeft_atLogical] at hrun
      simpa [rawZero, searchRef, CounterControlPlan.resolve,
        afterZero, clearBoundary, spec, prefixSpec] using hrun
    · exact Or.inr hhalts
  exact FullTM0.ResolvesTo.trans hthree
    (FullTM0.ResolvesTo.trans htwo
      (FullTM0.ResolvesTo.trans hone hzero))

/-- From the exact outward-collision endpoint, test the nonblank target,
step back onto erased boundary `4`, and perform exact tag-free cleanup. -/
theorem machine_reaches_collisionReturn_or_halts_of_prefix
    (base : Nat) (c : Nat.Partrec.Code) (source : Nat)
    {registers : Registers} {growth : Turing.Dir} {limit : Nat}
    {target : Target numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : CoreTargetRepresents registers growth limit target T)
    (hcollision : layoutEnd registers + 1 = limit)
    (hentry : cleanupEntryRule growth source ∈ rawDirectRules)
    (hcommands : ∀ raw, raw ∈ cleanupCommands growth source →
      raw ∈ rawCommands) :
    let spec := prefixSpec registers growth limit target
      h.core_before_limit
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨resolve base c (directRef growth source testDirectSlot),
          atLogical growth (afterFour spec T) limit⟩
        ⟨controllerReturn base c growth,
          atLogical growth (afterZero spec T) 0⟩ ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨resolve base c (directRef growth source testDirectSlot),
          atLogical growth (afterFour spec T) limit⟩ := by
  let spec := prefixSpec registers growth limit target h.core_before_limit
  have htargetRead :
      (atLogical growth (afterFour spec T) limit).read =
        logicalTape growth T limit := by
    rw [atLogical_read]
    simp only [afterFour, clearBoundary]
    apply writeLogical_of_ne
    simp [spec, prefixSpec, boundaryOffset_four]
    omega
  have htargetNonblank :
      (atLogical growth (afterFour spec T) limit).read ≠ blankSymbol := by
    rw [htargetRead]
    exact h.target_ne_blank
  have hentryRunLocal :=
    CounterControlDirectSemantics.reaches_directRule base c
      (cleanupEntryRule growth source) hentry
      (atLogical growth (afterFour spec T) limit) htargetNonblank
  have hmove :
      (atLogical growth (afterFour spec T) limit).move
          (orient growth .left) =
        atLogical growth (afterFour spec T) (layoutEnd registers) := by
    rw [← hcollision, orient_eq_orientDirection, atLogical_move_left]
  have hentryRun : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      ⟨resolve base c (directRef growth source testDirectSlot),
        atLogical growth (afterFour spec T) limit⟩
      ⟨searchState base c ⟨growth, source, cleanupSearchBase⟩,
        atLogical growth (afterFour spec T) (layoutEnd registers)⟩ := by
    simp only [cleanupEntryRule] at hentryRunLocal
    rw [hmove] at hentryRunLocal
    change FullTM0.Reaches
      (FiniteTM0.machine (CounterControlPlan.table base c)) _ _
    simpa [cleanupEntryRule, searchRef, CounterControlPlan.resolve] using
      hentryRunLocal
  have hcleanup := machine_reaches_cleanup_return_or_halts_of_prefix
    (target := target) base c source h.toCorePrefixRepresents hcommands
  exact FullTM0.ResolvesTo.trans (Or.inl hentryRun) hcleanup

/-- Complete body-level collision semantics for a finite tag-free prefix.
The successful endpoint retains the exact `afterZero` tape needed by global
unnesting; no coordinate-`0` symbol is inspected. -/
theorem machine_reaches_incrementCollisionBodyReturn_or_halts_of_prefix
    (base : Nat) (c : Nat.Partrec.Code) (source next : Nat)
    (register : Register)
    (hrule : (source, .increment register next) ∈
      GlobalSourceProgram.program)
    {registers : Registers} {growth : Turing.Dir} {limit : Nat}
    {target : Target numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : CoreTargetRepresents registers growth limit target T)
    (hcollision : layoutEnd registers + 1 = limit) :
    let spec := prefixSpec registers growth limit target
      h.core_before_limit
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨resolve base c
            (bodyEntry growth source (.increment register next)),
          atLogical growth T (layoutEnd registers)⟩
        ⟨controllerReturn base c growth,
          atLogical growth (afterZero spec T) 0⟩ ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨resolve base c
            (bodyEntry growth source (.increment register next)),
          atLogical growth T (layoutEnd registers)⟩ := by
  let spec := prefixSpec registers growth limit target h.core_before_limit
  let success : ControlRef := match register with
    | .clock => directRef growth source bodyDirectBase
    | _ => searchRef growth source (bodySearchBase + 1)
  have hraw : RawCommand.markerShift
      ⟨growth, source, bodySearchBase⟩ 4 .left .right
      success (some .left)
      (some (directRef growth source testDirectSlot)) ∈ rawCommands := by
    apply command_mem_rawCommands_of_rule growth hrule
    cases register <;>
      simp [success, commandsForRule, incrementCommands,
        incrementShiftCommands, incrementShiftCommandsAux,
        MarkerShift.incrementOrder]
  have hcollisionRun := machine_reaches_incrementCollision_of_prefix
    base c source success h hcollision hraw
  have hcollisionRun' : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      ⟨resolve base c
          (bodyEntry growth source (.increment register next)),
        atLogical growth T (layoutEnd registers)⟩
      ⟨resolve base c (directRef growth source testDirectSlot),
        atLogical growth (afterFour spec T) limit⟩ := by
    simpa [bodyEntry, searchRef, CounterControlPlan.resolve,
      spec, prefixSpec] using hcollisionRun
  have hentry : cleanupEntryRule growth source ∈ rawDirectRules := by
    apply directRule_mem_rawDirectRules_of_rule growth hrule
    change cleanupEntryRule growth source ∈
      validationRules growth source ++
        incrementRules growth source next register
    apply List.mem_append_right
    simp [cleanupEntryRule, incrementRules]
  have hcleanupCommands : ∀ raw,
      raw ∈ cleanupCommands growth source → raw ∈ rawCommands := by
    intro raw hraw'
    apply command_mem_rawCommands_of_rule growth hrule
    simp [commandsForRule, incrementCommands, hraw']
  have hcleanup := machine_reaches_collisionReturn_or_halts_of_prefix
    base c source h hcollision hentry hcleanupCommands
  exact FullTM0.ResolvesTo.trans (Or.inl hcollisionRun') hcleanup

/-! ## Uniform post-validation body interface -/

/-- Exact concrete configuration at the body of the looked-up instruction. -/
def bodyCfg (base : Nat) (c : Nat.Partrec.Code) (growth : Turing.Dir)
    (current : CounterMachine.Cfg) (instruction : Instruction)
    (T : FullTM0.Tape (Symbol numTags)) :
    FullTM0.Cfg (Symbol numTags) FiniteTM0.State :=
  ⟨resolve base c (bodyEntry growth current.state instruction),
    atLogical growth T (layoutEnd current.registers)⟩

/-- A body execution has reached the exact represented abstract successor. -/
def BodyLogicalStepReached
    (base : Nat) (c : Nat.Partrec.Code) (growth : Turing.Dir)
    (limit : Nat) (target : Target numTags)
    (current next : CounterMachine.Cfg) (instruction : Instruction)
    (T : FullTM0.Tape (Symbol numTags)) : Prop :=
  ∃ nextTape : FullTM0.Tape (Symbol numTags),
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        (bodyCfg base c growth current instruction T)
        ⟨logicalState base c growth next.state,
          atLogical growth nextTape (layoutEnd next.registers)⟩ ∧
      CoreTargetRepresents next.registers growth limit target nextTape

/-- A body execution has erased the finite core and reached the exact shared
return tape. -/
def BodyReturnReached
    (base : Nat) (c : Nat.Partrec.Code) (growth : Turing.Dir)
    (limit : Nat) (target : Target numTags)
    (current : CounterMachine.Cfg) (instruction : Instruction)
    (T : FullTM0.Tape (Symbol numTags))
    (hcore : layoutEnd current.registers < limit) : Prop :=
  let spec := prefixSpec current.registers growth limit target hcore
  FullTM0.Reaches (CounterControlNestingBridge.machine base c)
    (bodyCfg base c growth current instruction T)
    ⟨controllerReturn base c growth,
      atLogical growth (afterZero spec T) 0⟩

/-- A defined abstract step, starting after validation at its exact body,
either reaches the represented successor, reaches exact collision cleanup,
or halts.  This is the tag-free API consumed by arbitrary-entry validation. -/
theorem body_resolves_counterStep
    (base : Nat) (c : Nat.Partrec.Code)
    (current next : CounterMachine.Cfg) (instruction : Instruction)
    {growth : Turing.Dir} {limit : Nat} {target : Target numTags}
    {T : FullTM0.Tape (Symbol numTags)}
    (hlookup : CounterMachine.lookupInstruction
      GlobalSourceProgram.program current.state = some instruction)
    (hstep : CounterMachine.step GlobalSourceProgram.program current =
      some next)
    (h : CoreTargetRepresents current.registers growth limit target T) :
    BodyLogicalStepReached base c growth limit target current next
        instruction T ∨
      BodyReturnReached base c growth limit target current instruction T
        h.core_before_limit ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        (bodyCfg base c growth current instruction T) := by
  have hcase := CounterControlStepGeometry.stepCase_of_step_eq_some hstep
  cases hcase with
  | increment register nextState hlookup' hnext =>
      have hinstruction : instruction = .increment register nextState :=
        Option.some.inj (hlookup.symm.trans hlookup')
      subst instruction
      subst next
      have hrule := CounterProgram.rule_mem_of_lookupInstruction_eq_some
        hlookup'
      by_cases hroom :
          layoutEnd (current.registers.increment register) < limit
      · have hrun := machine_reaches_incrementBody_or_halts_of_prefix
          base c current.state nextState register hrule
          h.toCorePrefixRepresents hroom
        rcases hrun with hsuccess | hhalts
        · left
          refine ⟨incrementCoreTape current.registers growth register T,
            hsuccess.1, ?_⟩
          exact h.increment register hroom
        · exact Or.inr (Or.inr hhalts)
      · have hcollision : layoutEnd current.registers + 1 = limit := by
          rw [layoutEnd_increment] at hroom
          have hle : layoutEnd current.registers + 1 ≤ limit := by
            have hold := h.core_before_limit
            omega
          omega
        have hrun :=
          machine_reaches_incrementCollisionBodyReturn_or_halts_of_prefix
            base c current.state nextState register hrule h hcollision
        rcases hrun with hreturn | hhalts
        · exact Or.inr (Or.inl hreturn)
        · exact Or.inr (Or.inr hhalts)
  | decrementZero register ifZero ifPositive hlookup' hzero hnext =>
      have hinstruction : instruction =
          .decrement register ifZero ifPositive :=
        Option.some.inj (hlookup.symm.trans hlookup')
      subst instruction
      subst next
      have hrule := CounterProgram.rule_mem_of_lookupInstruction_eq_some
        hlookup'
      have hrun := machine_reaches_decrementZeroBody_or_halts_of_prefix
        base c growth current.state ifZero ifPositive register hrule
        h.toCorePrefixRepresents hzero
      rcases hrun with hsuccess | hhalts
      · left
        exact ⟨T, hsuccess.1, h⟩
      · exact Or.inr (Or.inr hhalts)
  | decrementPositive register ifZero ifPositive hlookup' hpositive hnext =>
      have hinstruction : instruction =
          .decrement register ifZero ifPositive :=
        Option.some.inj (hlookup.symm.trans hlookup')
      subst instruction
      subst next
      have hrule := CounterProgram.rule_mem_of_lookupInstruction_eq_some
        hlookup'
      have hrun := machine_reaches_decrementPositiveBody_or_halts_of_prefix
        base c current.state ifZero ifPositive register hrule
        h.toCorePrefixRepresents hpositive
      rcases hrun with hsuccess | hhalts
      · left
        refine ⟨decrementCoreTape current.registers growth register T,
          hsuccess.1, ?_⟩
        exact h.decrement register hpositive
      · exact Or.inr (Or.inr hhalts)

/-! ## Totality inside a finite tag-free envelope -/

/-- Stable data of one tag-free finite prefix while the abstract counter
configuration evolves. -/
structure PrefixEnvelope where
  growth : Turing.Dir
  limit : Nat
  target : Target numTags

/-- Canonical logical configuration associated with an abstract state. -/
def prefixLogicalCfg (base : Nat) (c : Nat.Partrec.Code)
    (frame : PrefixEnvelope)
    (abstract : CounterMachine.Cfg)
    (T : FullTM0.Tape (Symbol numTags)) :
    FullTM0.Cfg (Symbol numTags) FiniteTM0.State :=
  ⟨logicalState base c frame.growth abstract.state,
    atLogical frame.growth T (layoutEnd abstract.registers)⟩

/-- Exact represented finite prefix at an abstract logical configuration. -/
inductive PrefixLogical (base : Nat) (c : Nat.Partrec.Code)
    (frame : PrefixEnvelope)
    (abstract : CounterMachine.Cfg)
    (concrete : FullTM0.Cfg (Symbol numTags) FiniteTM0.State) : Prop where
  | intro
      (tape : FullTM0.Tape (Symbol numTags))
      (represented : CoreTargetRepresents abstract.registers frame.growth
        frame.limit frame.target tape)
      (concrete_eq : concrete = prefixLogicalCfg base c frame abstract tape)
      (state_lt : abstract.state < logicalSpan)

/-- Exact collision-cleanup outcome.  Besides the reached shared-return
configuration, the witness retains the collision-time represented prefix and
the arithmetic bound needed by the outer unnesting argument. -/
def PrefixReachesReturn (base : Nat) (c : Nat.Partrec.Code)
    (frame : PrefixEnvelope)
    (start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State) : Prop :=
  ∃ (registers : Registers) (T : FullTM0.Tape (Symbol numTags))
      (h : CoreTargetRepresents registers frame.growth frame.limit
        frame.target T),
    layoutEnd registers ≤ frame.limit - 1 ∧
      FullTM0.Reaches (CounterControlNestingBridge.machine base c) start
        ⟨controllerReturn base c frame.growth,
          atLogical frame.growth
            (afterZero
              (prefixSpec registers frame.growth frame.limit frame.target
                h.core_before_limit) T) 0⟩

/-- One defined abstract transition either preserves the exact target prefix,
reaches exact cleanup return, or concretely halts. -/
theorem prefixOneStepResolves
    (base : Nat) (c : Nat.Partrec.Code)
    (frame : PrefixEnvelope)
    {current next : CounterMachine.Cfg}
    {concrete : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (hstep : CounterMachine.step GlobalSourceProgram.program current =
      some next)
    (hlogical : PrefixLogical base c frame current concrete) :
    (∃ nextConcrete,
      FullTM0.Reaches (CounterControlNestingBridge.machine base c)
          concrete nextConcrete ∧
        PrefixLogical base c frame next nextConcrete) ∨
      PrefixReachesReturn base c frame concrete ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        concrete := by
  rcases hlogical with ⟨T, h, rfl, _hstate⟩
  have hcase := CounterControlStepGeometry.stepCase_of_step_eq_some hstep
  rcases CounterControlStepGeometry.rule_mem_of_stepCase hcase with
    ⟨instruction, hrule, hlookup⟩
  have hvalidation := machine_reaches_validation_or_halts_of_core
    base c frame.growth current.state instruction hrule h.toCoreRepresents
  rcases hvalidation with hvalidation | hvalidationHalts
  · have hbody := body_resolves_counterStep base c current next instruction
      hlookup hstep h
    rcases hbody with hnext | hreturn | hbodyHalts
    · rcases hnext with ⟨nextTape, hreach, hnext⟩
      let nextConcrete := prefixLogicalCfg base c frame next nextTape
      left
      refine ⟨nextConcrete, ?_, ?_⟩
      · exact hvalidation.trans hreach
      · exact ⟨nextTape, hnext, rfl,
          CounterControlAbstractTrace.state_lt_logicalSpan_of_step hstep⟩
    · right
      left
      refine ⟨current.registers, T, h, ?_, hvalidation.trans hreturn⟩
      have hlt := h.core_before_limit
      omega
    · exact Or.inr (Or.inr
        (FullTM0.HaltsFrom.of_reaches hvalidation hbodyHalts))
  · exact Or.inr (Or.inr hvalidationHalts)

/-- The prefix one-step law lifts over every finite abstract trace. -/
theorem reaches_prefix_or_return_or_halts
    (base : Nat) (c : Nat.Partrec.Code)
    (frame : PrefixEnvelope)
    {start finish : CounterMachine.Cfg}
    (hreach : StateTransition.Reaches
      (CounterMachine.step GlobalSourceProgram.program) start finish)
    {concrete : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (hlogical : PrefixLogical base c frame start concrete) :
    (∃ finishConcrete,
      FullTM0.Reaches (CounterControlNestingBridge.machine base c)
          concrete finishConcrete ∧
        PrefixLogical base c frame finish finishConcrete) ∨
      PrefixReachesReturn base c frame concrete ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        concrete := by
  induction hreach generalizing concrete with
  | refl =>
      exact Or.inl ⟨concrete, Relation.ReflTransGen.refl, hlogical⟩
  | @tail current next hprefix hlast ih =>
      rcases ih hlogical with hcurrent | hreturn | hhalts
      · rcases hcurrent with
          ⟨currentConcrete, hprefixConcrete, hcurrent⟩
        have hlast' : CounterMachine.step GlobalSourceProgram.program
            current = some next := by
          simpa using hlast
        rcases prefixOneStepResolves base c frame hlast' hcurrent with
          hnext | hreturn | hhalts
        · rcases hnext with ⟨nextConcrete, hstepConcrete, hnext⟩
          exact Or.inl
            ⟨nextConcrete, hprefixConcrete.trans hstepConcrete, hnext⟩
        · right
          left
          rcases hreturn with ⟨registers, T, h, hbound, hreturn⟩
          exact ⟨registers, T, h, hbound,
            hprefixConcrete.trans hreturn⟩
        · exact Or.inr (Or.inr
            (FullTM0.HaltsFrom.of_reaches hprefixConcrete hhalts))
      · exact Or.inr (Or.inl hreturn)
      · exact Or.inr (Or.inr hhalts)

/-- A mortal abstract computation either encounters collision cleanup first
or transfers its terminal abstract configuration to a concrete halt. -/
theorem prefix_return_or_halts_of_abstract_haltsFrom
    (base : Nat) (c : Nat.Partrec.Code)
    (frame : PrefixEnvelope)
    {start : CounterMachine.Cfg}
    (hhalts : CounterLiveness.HaltsFrom GlobalSourceProgram.program start)
    {concrete : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (hlogical : PrefixLogical base c frame start concrete) :
    PrefixReachesReturn base c frame concrete ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        concrete := by
  rcases hhalts with ⟨terminal, hterminalReach, hterminal⟩
  rcases reaches_prefix_or_return_or_halts base c frame hterminalReach
      hlogical with hfinish | hreturn | hhalts
  · rcases hfinish with
      ⟨finishConcrete, hfinishReach, hfinishLogical⟩
    rcases hfinishLogical with ⟨T, _h, rfl, hstate⟩
    right
    apply FullTM0.HaltsFrom.of_reaches hfinishReach
    refine ⟨prefixLogicalCfg base c frame terminal T,
      Relation.ReflTransGen.refl, ?_⟩
    simpa [prefixLogicalCfg] using
      (CounterControlTerminalSemantics.machine_step_eq_none_of_counter_step_none
        base c frame.growth terminal
        (atLogical frame.growth T (layoutEnd terminal.registers))
        hstate hterminal)
  · exact Or.inl hreturn
  · exact Or.inr hhalts

/-- An immortal abstract counter run cannot stay in one finite target prefix:
unbounded logical clock growth forces exact collision return (or an earlier
concrete internal-search halt). -/
theorem prefix_return_or_halts_of_abstract_immortalFrom
    (base : Nat) (c : Nat.Partrec.Code)
    (frame : PrefixEnvelope)
    {start : CounterMachine.Cfg}
    (himmortal : Dynamics.ImmortalFrom
      (CounterMachine.step GlobalSourceProgram.program) start)
    {concrete : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (hlogical : PrefixLogical base c frame start concrete) :
    PrefixReachesReturn base c frame concrete ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        concrete := by
  rcases GlobalSourceLiveness.cycleLaws
      |>.exists_reachable_logical_clock_ge_of_immortalFrom
        himmortal frame.limit with
    ⟨finish, hreach, _hfinishLogical, hclock⟩
  rcases reaches_prefix_or_return_or_halts base c frame hreach hlogical with
    hfinish | hreturn | hhalts
  · rcases hfinish with
      ⟨_finishConcrete, _hfinishReach, hfinishPrefix⟩
    rcases hfinishPrefix with
      ⟨_tape, hrepresented, _concreteEq, _stateLt⟩
    have hcore := hrepresented.core_before_limit
    have hclockEnd := clock_lt_layoutEnd finish.registers
    omega
  · exact Or.inl hreturn
  · exact Or.inr hhalts

/-- Every represented finite target prefix, from any abstract logical
configuration, reaches exact collision cleanup or concretely halts. -/
theorem prefix_return_or_halts
    (base : Nat) (c : Nat.Partrec.Code)
    (frame : PrefixEnvelope)
    {start : CounterMachine.Cfg}
    {concrete : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (hlogical : PrefixLogical base c frame start concrete) :
    PrefixReachesReturn base c frame concrete ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        concrete := by
  rcases CounterLiveness.haltsFrom_or_immortalFrom
      GlobalSourceProgram.program start with hhalts | himmortal
  · exact prefix_return_or_halts_of_abstract_haltsFrom base c frame
      hhalts hlogical
  · exact prefix_return_or_halts_of_abstract_immortalFrom base c frame
      himmortal hlogical

/-- Direct wrapper for the strongest commonly used input: an immortal
abstract logical configuration represented inside a finite target prefix. -/
theorem prefix_return_or_halts_from_immortal_logical
    (base : Nat) (c : Nat.Partrec.Code)
    (frame : PrefixEnvelope)
    (start : CounterMachine.Cfg)
    (T : FullTM0.Tape (Symbol numTags))
    (h : CoreTargetRepresents start.registers frame.growth frame.limit
      frame.target T)
    (hstate : start.state < logicalSpan)
    (himmortal : Dynamics.ImmortalFrom
      (CounterMachine.step GlobalSourceProgram.program) start) :
    PrefixReachesReturn base c frame
        (prefixLogicalCfg base c frame start T) ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        (prefixLogicalCfg base c frame start T) := by
  apply prefix_return_or_halts_of_abstract_immortalFrom base c frame
    himmortal
  exact ⟨T, h, rfl, hstate⟩

end

end CounterControlPrefixInstructionResolution
end Hooper
end Kari
end LeanWang
