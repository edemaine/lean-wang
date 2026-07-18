/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlCanonicalOpenMortality
import LeanWang.Kari.Hooper.CounterControlInstructionResolution

/-!
# Resolving instructions on a target-free open counter core

The finite-frame instruction theorems use `FramedMarkerTape.Represents`,
whose far matching target is needed for the outer Hooper induction.  A
logical instruction on the top-level open core should never inspect such a
target: each of its bounded searches is between two of the five represented
counter boundaries, while an outward increment writes into the infinite
blank runway.

This file begins the target-free factorization at the validation sweep.  It
rebuilds the route geometry from `CoreRepresents` alone and feeds the genuine
internal search gaps to the resolving Basic Lemma.  Thus every validation
search either reaches its represented boundary or exposes a concrete halt;
no finite outer target and no locality limit argument is used.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlOpenInstructionResolution

open Turing CounterMachine
open BoundedMarkerProgram FramedMarkerTape FramedCounterGeometry
open CounterControlPlan CounterControlCoreFrame
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
  have hsourcePositive : 0 < source := by
    simp [source, boundaryOffset]
  have hU (position : Int) :
      logicalTape growth U position =
        if position = source + 1 then boundarySymbol label
        else if position = source then blankSymbol
        else logicalTape growth T position := by
    simpa only [U, logicalTape_writeLogical_apply, Nat.cast_add, Nat.cast_one]
  have hrep : CoreOpenRepresents next growth U := by
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
    · intro position hpast
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
      exact h.runway position (hlower.trans_lt hpast)
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
  have hrep : CoreOpenRepresents next growth U := by
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
    · intro position hpast
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
        by_contra hold
        have hpositionLe : position ≤ layoutEnd current :=
          Nat.le_of_not_gt hold
        have hstrict : layoutEnd next < layoutEnd current := by omega
        have hsourceEnd := hshrink hstrict
        apply hsourcePosition
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
    installCore_eq_self_of_coreRepresents hrep.toCoreRepresents
  exact ⟨hself.symm.trans hinstall.symm, hrep⟩

/-! ## Internal routes from the tag-free core -/

/-- The converse Basic Lemma resolves every finite compiled search distance,
so it supplies `ShortResolves` at any chosen geometric limit. -/
theorem shortResolves_all (base : Nat) (c : Nat.Partrec.Code)
    (limit : Nat) :
    ShortResolves base c limit := by
  intro distance _hdistance
  exact CounterControlFiniteConverse.resolves_all base c distance

/-- One leftward route leg between adjacent represented boundaries. -/
theorem leftLeg_executesAt_of_core
    {registers : Registers} {growth : Turing.Dir}
    {T : FullTM0.Tape (Symbol numTags)}
    (h : CoreRepresents registers growth T) (i : Fin 4) :
    LegExecutesAt growth T ⟨i.castSucc, .left⟩
      (boundaryOffset registers i.succ)
      (boundaryOffset registers i.castSucc) := by
  rw [LegExecutesAt]
  refine ⟨RegisterLayout.values registers i, ?_, ?_⟩
  · simp only [boundaryOffset, Fin.val_succ, Fin.val_castSucc,
      CounterLayout.boundaryPos_succ]
    omega
  · change SearchGap (fun symbol => symbol = blankSymbol)
      (fun symbol => symbol = boundarySymbol i.castSucc)
      (atLogical growth T
        (boundaryOffset registers i.castSucc +
          RegisterLayout.values registers i))
      (OrientedMarkerTape.orientDirection growth .left)
      (RegisterLayout.values registers i)
    simpa only [boundaryOffset, lastGapOffset, Fin.val_castSucc,
      CounterLayout.boundaryPos_succ, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using h.searchGap_adjacent_left i

/-- One rightward route leg between adjacent represented boundaries. -/
theorem rightLeg_executesAt_of_core
    {registers : Registers} {growth : Turing.Dir}
    {T : FullTM0.Tape (Symbol numTags)}
    (h : CoreRepresents registers growth T) (i : Fin 4) :
    LegExecutesAt growth T ⟨i.succ, .right⟩
      (boundaryOffset registers i.castSucc)
      (boundaryOffset registers i.succ) := by
  rw [LegExecutesAt]
  refine ⟨RegisterLayout.values registers i, ?_, ?_⟩
  · change SearchGap (fun symbol => symbol = blankSymbol)
      (fun symbol => symbol = boundarySymbol i.succ)
      (atLogical growth T
        (boundaryOffset registers i.castSucc + 1))
      (OrientedMarkerTape.orientDirection growth .right)
      (RegisterLayout.values registers i)
    simpa only [boundaryOffset, firstGapOffset, Fin.val_castSucc,
      Nat.add_assoc, one_add_one_eq_two] using
        h.searchGap_adjacent_right i
  · simp only [boundaryOffset, Fin.val_succ, Fin.val_castSucc,
      CounterLayout.boundaryPos_succ]
    omega

/-- Every represented boundary coordinate lies before any limit strictly
beyond boundary `4`. -/
theorem boundaryOffset_lt_limit_of_core
    {registers : Registers} {growth : Turing.Dir}
    {T : FullTM0.Tape (Symbol numTags)}
    (_h : CoreRepresents registers growth T)
    {limit : Nat} (hlimit : layoutEnd registers < limit)
    (label : Fin 5) :
    boundaryOffset registers label < limit := by
  apply lt_of_le_of_lt _ hlimit
  simp only [boundaryOffset, layoutEnd]
  apply Nat.add_le_add_right
  exact CounterLayout.boundaryPos_mono
    (RegisterLayout.values registers) (by omega)

/-- The eight-leg validation sweep uses only the represented five-boundary
core.  The arbitrary `limit` is bookkeeping for the resolving search API;
it is not the position of an actual target. -/
theorem validation_executesWithin_of_core
    {registers : Registers} {growth : Turing.Dir}
    {T : FullTM0.Tape (Symbol numTags)}
    (h : CoreRepresents registers growth T)
    {limit : Nat} (hlimit : layoutEnd registers < limit) :
    RouteExecutesWithin growth T limit MarkerValidation.sweep
      (layoutEnd registers) (layoutEnd registers) := by
  change RouteExecutesWithin growth T limit _
    (boundaryOffset registers 4) (boundaryOffset registers 4)
  apply RouteExecutesWithin.cons _ _ _
    (boundaryOffset registers 3) _
    (boundaryOffset_lt_limit_of_core h hlimit 4)
    (leftLeg_executesAt_of_core h 3)
  apply RouteExecutesWithin.cons _ _ _
    (boundaryOffset registers 2) _
    (boundaryOffset_lt_limit_of_core h hlimit 3)
    (leftLeg_executesAt_of_core h 2)
  apply RouteExecutesWithin.cons _ _ _
    (boundaryOffset registers 1) _
    (boundaryOffset_lt_limit_of_core h hlimit 2)
    (leftLeg_executesAt_of_core h 1)
  apply RouteExecutesWithin.cons _ _ _
    (boundaryOffset registers 0) _
    (boundaryOffset_lt_limit_of_core h hlimit 1)
    (leftLeg_executesAt_of_core h 0)
  apply RouteExecutesWithin.cons _ _ _
    (boundaryOffset registers 1) _
    (boundaryOffset_lt_limit_of_core h hlimit 0)
    (rightLeg_executesAt_of_core h 0)
  apply RouteExecutesWithin.cons _ _ _
    (boundaryOffset registers 2) _
    (boundaryOffset_lt_limit_of_core h hlimit 1)
    (rightLeg_executesAt_of_core h 1)
  apply RouteExecutesWithin.cons _ _ _
    (boundaryOffset registers 3) _
    (boundaryOffset_lt_limit_of_core h hlimit 2)
    (rightLeg_executesAt_of_core h 2)
  apply RouteExecutesWithin.cons _ _ _
    (boundaryOffset registers 4) _
    (boundaryOffset_lt_limit_of_core h hlimit 3)
    (rightLeg_executesAt_of_core h 3)
  exact RouteExecutesWithin.nil _
    (boundaryOffset_lt_limit_of_core h hlimit 4)

/-- Navigation from boundary `4` to the predecessor of the selected register
gap uses only adjacent boundaries of the core. -/
theorem routeToDecrementStart_executesWithin_of_core
    {registers : Registers} {growth : Turing.Dir}
    {T : FullTM0.Tape (Symbol numTags)}
    (h : CoreRepresents registers growth T)
    {limit : Nat} (hlimit : layoutEnd registers < limit)
    (register : Register) :
    RouteExecutesWithin growth T limit
      (AnchoredCounterGeometry.routeToDecrementStart register)
      (layoutEnd registers)
      (boundaryOffset registers
        (MarkerSchedule.decrementStartBoundary register)) := by
  change RouteExecutesWithin growth T limit _
    (boundaryOffset registers 4) _
  cases register with
  | left =>
      apply RouteExecutesWithin.cons _ _ _
        (boundaryOffset registers 3) _
        (boundaryOffset_lt_limit_of_core h hlimit 4)
        (leftLeg_executesAt_of_core h 3)
      apply RouteExecutesWithin.cons _ _ _
        (boundaryOffset registers 2) _
        (boundaryOffset_lt_limit_of_core h hlimit 3)
        (leftLeg_executesAt_of_core h 2)
      apply RouteExecutesWithin.cons _ _ _
        (boundaryOffset registers 1) _
        (boundaryOffset_lt_limit_of_core h hlimit 2)
        (leftLeg_executesAt_of_core h 1)
      exact RouteExecutesWithin.nil _
        (boundaryOffset_lt_limit_of_core h hlimit 1)
  | right =>
      apply RouteExecutesWithin.cons _ _ _
        (boundaryOffset registers 3) _
        (boundaryOffset_lt_limit_of_core h hlimit 4)
        (leftLeg_executesAt_of_core h 3)
      apply RouteExecutesWithin.cons _ _ _
        (boundaryOffset registers 2) _
        (boundaryOffset_lt_limit_of_core h hlimit 3)
        (leftLeg_executesAt_of_core h 2)
      exact RouteExecutesWithin.nil _
        (boundaryOffset_lt_limit_of_core h hlimit 2)
  | temp =>
      apply RouteExecutesWithin.cons _ _ _
        (boundaryOffset registers 3) _
        (boundaryOffset_lt_limit_of_core h hlimit 4)
        (leftLeg_executesAt_of_core h 3)
      exact RouteExecutesWithin.nil _
        (boundaryOffset_lt_limit_of_core h hlimit 3)
  | clock =>
      exact RouteExecutesWithin.nil _
        (boundaryOffset_lt_limit_of_core h hlimit 4)

/-- Navigation from the shifted boundary back to boundary `4` after an
increment uses only adjacent boundaries of the updated core. -/
theorem routeFromIncrement_executesWithin_of_core
    {registers : Registers} {growth : Turing.Dir}
    {T : FullTM0.Tape (Symbol numTags)}
    (h : CoreRepresents registers growth T)
    {limit : Nat} (hlimit : layoutEnd registers < limit)
    (register : Register) :
    RouteExecutesWithin growth T limit
      (AnchoredCounterGeometry.routeFromIncrement register)
      (boundaryOffset registers
        (MarkerSchedule.decrementStartBoundary register))
      (layoutEnd registers) := by
  change RouteExecutesWithin growth T limit _ _
    (boundaryOffset registers 4)
  cases register with
  | left =>
      apply RouteExecutesWithin.cons _ _ _
        (boundaryOffset registers 2) _
        (boundaryOffset_lt_limit_of_core h hlimit 1)
        (rightLeg_executesAt_of_core h 1)
      apply RouteExecutesWithin.cons _ _ _
        (boundaryOffset registers 3) _
        (boundaryOffset_lt_limit_of_core h hlimit 2)
        (rightLeg_executesAt_of_core h 2)
      apply RouteExecutesWithin.cons _ _ _
        (boundaryOffset registers 4) _
        (boundaryOffset_lt_limit_of_core h hlimit 3)
        (rightLeg_executesAt_of_core h 3)
      exact RouteExecutesWithin.nil _
        (boundaryOffset_lt_limit_of_core h hlimit 4)
  | right =>
      apply RouteExecutesWithin.cons _ _ _
        (boundaryOffset registers 3) _
        (boundaryOffset_lt_limit_of_core h hlimit 2)
        (rightLeg_executesAt_of_core h 2)
      apply RouteExecutesWithin.cons _ _ _
        (boundaryOffset registers 4) _
        (boundaryOffset_lt_limit_of_core h hlimit 3)
        (rightLeg_executesAt_of_core h 3)
      exact RouteExecutesWithin.nil _
        (boundaryOffset_lt_limit_of_core h hlimit 4)
  | temp =>
      apply RouteExecutesWithin.cons _ _ _
        (boundaryOffset registers 4) _
        (boundaryOffset_lt_limit_of_core h hlimit 3)
        (rightLeg_executesAt_of_core h 3)
      exact RouteExecutesWithin.nil _
        (boundaryOffset_lt_limit_of_core h hlimit 4)
  | clock =>
      exact RouteExecutesWithin.nil _
        (boundaryOffset_lt_limit_of_core h hlimit 4)

/-- The zero-test recovery route returns from the empty selected gap to
boundary `4`, again using only represented adjacent-boundary searches. -/
theorem routeFromZero_executesWithin_of_core
    {registers : Registers} {growth : Turing.Dir}
    {T : FullTM0.Tape (Symbol numTags)}
    (h : CoreRepresents registers growth T)
    {limit : Nat} (hlimit : layoutEnd registers < limit)
    (register : Register) :
    RouteExecutesWithin growth T limit
      (AnchoredCounterGeometry.routeFromZero register)
      (boundaryOffset registers
        (AnchoredCounterGeometry.registerGap register).castSucc)
      (layoutEnd registers) := by
  change RouteExecutesWithin growth T limit _ _
    (boundaryOffset registers 4)
  cases register with
  | left =>
      apply RouteExecutesWithin.cons _ _ _
        (boundaryOffset registers 1) _
        (boundaryOffset_lt_limit_of_core h hlimit 0)
        (rightLeg_executesAt_of_core h 0)
      apply RouteExecutesWithin.cons _ _ _
        (boundaryOffset registers 2) _
        (boundaryOffset_lt_limit_of_core h hlimit 1)
        (rightLeg_executesAt_of_core h 1)
      apply RouteExecutesWithin.cons _ _ _
        (boundaryOffset registers 3) _
        (boundaryOffset_lt_limit_of_core h hlimit 2)
        (rightLeg_executesAt_of_core h 2)
      apply RouteExecutesWithin.cons _ _ _
        (boundaryOffset registers 4) _
        (boundaryOffset_lt_limit_of_core h hlimit 3)
        (rightLeg_executesAt_of_core h 3)
      exact RouteExecutesWithin.nil _
        (boundaryOffset_lt_limit_of_core h hlimit 4)
  | right =>
      apply RouteExecutesWithin.cons _ _ _
        (boundaryOffset registers 2) _
        (boundaryOffset_lt_limit_of_core h hlimit 1)
        (rightLeg_executesAt_of_core h 1)
      apply RouteExecutesWithin.cons _ _ _
        (boundaryOffset registers 3) _
        (boundaryOffset_lt_limit_of_core h hlimit 2)
        (rightLeg_executesAt_of_core h 2)
      apply RouteExecutesWithin.cons _ _ _
        (boundaryOffset registers 4) _
        (boundaryOffset_lt_limit_of_core h hlimit 3)
        (rightLeg_executesAt_of_core h 3)
      exact RouteExecutesWithin.nil _
        (boundaryOffset_lt_limit_of_core h hlimit 4)
  | temp =>
      apply RouteExecutesWithin.cons _ _ _
        (boundaryOffset registers 3) _
        (boundaryOffset_lt_limit_of_core h hlimit 2)
        (rightLeg_executesAt_of_core h 2)
      apply RouteExecutesWithin.cons _ _ _
        (boundaryOffset registers 4) _
        (boundaryOffset_lt_limit_of_core h hlimit 3)
        (rightLeg_executesAt_of_core h 3)
      exact RouteExecutesWithin.nil _
        (boundaryOffset_lt_limit_of_core h hlimit 4)
  | clock =>
      apply RouteExecutesWithin.cons _ _ _
        (boundaryOffset registers 4) _
        (boundaryOffset_lt_limit_of_core h hlimit 3)
        (rightLeg_executesAt_of_core h 3)
      exact RouteExecutesWithin.nil _
        (boundaryOffset_lt_limit_of_core h hlimit 4)

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
  have hfinal (r : Register) :
      CoreOpenRepresents (registers.increment r) growth
        (incrementCoreTape registers growth r T) :=
    incrementCoreTape_preserves_open h r
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
        machine_reaches_incrementClock_or_halts_of_open base c source
          bodySearchBase (directRef growth source bodyDirectBase)
          (some (directRef growth source testDirectSlot)) h hraw
  | temp =>
      let clockRegisters := registers.increment .clock
      let tempRegisters := registers.increment .temp
      let clockTape := incrementCoreTape registers growth .clock T
      let tempTape := incrementCoreTape registers growth .temp T
      have hclockOpen : CoreOpenRepresents clockRegisters growth clockTape := by
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
      have hfour := machine_reaches_incrementClock_or_halts_of_open base c
        source bodySearchBase (searchRef growth source (bodySearchBase + 1))
        (some (directRef growth source testDirectSlot)) h hrawFour
      have hthree := machine_reaches_incrementInternal_or_halts_of_open
        (next := tempRegisters) base c
        limit source (bodySearchBase + 1)
        (directRef growth source bodyDirectBase) none hclockOpen (3 : Fin 4)
        (by simp [clockRegisters, RegisterLayout.values, Registers.increment,
          Registers.set, Registers.get])
        (by simp [limit, clockRegisters, layoutEnd, CounterLayout.boundaryPos,
          RegisterLayout.clockBoundary_eq, RegisterLayout.values,
          Registers.increment, Registers.set, Registers.get] <;> omega)
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
      have hclockOpen : CoreOpenRepresents clockRegisters growth clockTape := by
        simpa [clockRegisters, clockTape] using hfinal .clock
      have htempOpen : CoreOpenRepresents tempRegisters growth tempTape := by
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
      have hfour := machine_reaches_incrementClock_or_halts_of_open base c
        source bodySearchBase (searchRef growth source (bodySearchBase + 1))
        (some (directRef growth source testDirectSlot)) h hrawFour
      have hthree := machine_reaches_incrementInternal_or_halts_of_open
        (next := tempRegisters) base c
        limit source (bodySearchBase + 1)
        (searchRef growth source (bodySearchBase + 2)) none hclockOpen
        (3 : Fin 4)
        (by simp [clockRegisters, RegisterLayout.values, Registers.increment,
          Registers.set, Registers.get])
        (by simp [limit, clockRegisters, layoutEnd, CounterLayout.boundaryPos,
          RegisterLayout.clockBoundary_eq, RegisterLayout.values,
          Registers.increment, Registers.set, Registers.get] <;> omega)
        (by simp [clockRegisters, tempRegisters, layoutEnd_increment])
        (by simp [clockRegisters, tempRegisters, layoutEnd_increment])
        (by simp [clockRegisters, tempRegisters, layoutEnd_increment])
        (by simpa [clockRegisters, tempRegisters] using
          MarkerSchedule.moveTempBoundary_after_clock registers)
        hrawThree
      have htwo := machine_reaches_incrementInternal_or_halts_of_open
        (next := rightRegisters) base c
        limit source (bodySearchBase + 2)
        (directRef growth source bodyDirectBase) none htempOpen (2 : Fin 4)
        (by simp [tempRegisters, RegisterLayout.values, Registers.increment,
          Registers.set, Registers.get])
        (by simp [limit, tempRegisters, layoutEnd, CounterLayout.boundaryPos,
          RegisterLayout.clockBoundary_eq, RegisterLayout.values,
          Registers.increment, Registers.set, Registers.get] <;> omega)
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
      have hclockOpen : CoreOpenRepresents clockRegisters growth clockTape := by
        simpa [clockRegisters, clockTape] using hfinal .clock
      have htempOpen : CoreOpenRepresents tempRegisters growth tempTape := by
        simpa [tempRegisters, tempTape] using hfinal .temp
      have hrightOpen : CoreOpenRepresents rightRegisters growth rightTape := by
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
      have hfour := machine_reaches_incrementClock_or_halts_of_open base c
        source bodySearchBase (searchRef growth source (bodySearchBase + 1))
        (some (directRef growth source testDirectSlot)) h hrawFour
      have hthree := machine_reaches_incrementInternal_or_halts_of_open
        (next := tempRegisters) base c
        limit source (bodySearchBase + 1)
        (searchRef growth source (bodySearchBase + 2)) none hclockOpen
        (3 : Fin 4)
        (by simp [clockRegisters, RegisterLayout.values, Registers.increment,
          Registers.set, Registers.get])
        (by simp [limit, clockRegisters, layoutEnd, CounterLayout.boundaryPos,
          RegisterLayout.clockBoundary_eq, RegisterLayout.values,
          Registers.increment, Registers.set, Registers.get] <;> omega)
        (by simp [clockRegisters, tempRegisters, layoutEnd_increment])
        (by simp [clockRegisters, tempRegisters, layoutEnd_increment])
        (by simp [clockRegisters, tempRegisters, layoutEnd_increment])
        (by simpa [clockRegisters, tempRegisters] using
          MarkerSchedule.moveTempBoundary_after_clock registers)
        hrawThree
      have htwo := machine_reaches_incrementInternal_or_halts_of_open
        (next := rightRegisters) base c
        limit source (bodySearchBase + 2)
        (searchRef growth source (bodySearchBase + 3)) none htempOpen
        (2 : Fin 4)
        (by simp [tempRegisters, RegisterLayout.values, Registers.increment,
          Registers.set, Registers.get])
        (by simp [limit, tempRegisters, layoutEnd, CounterLayout.boundaryPos,
          RegisterLayout.clockBoundary_eq, RegisterLayout.values,
          Registers.increment, Registers.set, Registers.get] <;> omega)
        (by simp [tempRegisters, rightRegisters, layoutEnd_increment])
        (by simp [tempRegisters, rightRegisters, layoutEnd_increment])
        (by simp [tempRegisters, rightRegisters, layoutEnd_increment])
        (by simpa [tempRegisters, rightRegisters] using
          MarkerSchedule.moveRightBoundary_after_temp registers)
        hrawTwo
      have hone := machine_reaches_incrementInternal_or_halts_of_open
        (next := leftRegisters) base c
        limit source (bodySearchBase + 3)
        (directRef growth source bodyDirectBase) none hrightOpen (1 : Fin 4)
        (by simp [rightRegisters, RegisterLayout.values, Registers.increment,
          Registers.set, Registers.get])
        (by simp [limit, rightRegisters, layoutEnd, CounterLayout.boundaryPos,
          RegisterLayout.clockBoundary_eq, RegisterLayout.values,
          Registers.increment, Registers.set, Registers.get] <;> omega)
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
    {registers : Registers} {growth : Turing.Dir}
    {T : FullTM0.Tape (Symbol numTags)}
    (h : CoreOpenRepresents registers growth T) (register : Register) :
    logicalTape growth (incrementCoreTape registers growth register T)
        (boundaryOffset registers
          (MarkerSchedule.decrementStartBoundary register)) =
      blankSymbol := by
  have hnext := incrementCoreTape_preserves_open h register
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
    exact incrementCoreSchedule_source_blank h register
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

/-- The one-shift clock-decrement schedule resolves on an open core. -/
theorem machine_reaches_decrementClockSchedule_or_halts_of_open
    (base : Nat) (c : Nat.Partrec.Code) (source : Nat)
    {registers : Registers} {growth : Turing.Dir}
    {T : FullTM0.Tape (Symbol numTags)}
    (h : CoreOpenRepresents registers growth T)
    (hpositive : 0 < registers.get .clock)
    (hraw : RawCommand.markerShift
      ⟨growth, source, secondarySearchBase⟩ 4 .right .left
      (directRef growth source finishDirectSlot) (some .right) none ∈
        rawCommands) :
    (FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨growth, source, secondarySearchBase⟩,
          atLogical growth T (layoutEnd registers)⟩
        ⟨resolve base c (directRef growth source finishDirectSlot),
          atLogical growth
            (decrementCoreTape registers growth .clock T)
            (layoutEnd registers)⟩ ∧
      CoreOpenRepresents (registers.decrement .clock) growth
        (decrementCoreTape registers growth .clock T)) ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨growth, source, secondarySearchBase⟩,
          atLogical growth T (layoutEnd registers)⟩ := by
  let limit := layoutEnd registers + 1
  let next := registers.decrement .clock
  have hp : 0 < registers.clock := by
    simpa [Registers.get] using hpositive
  have hend : layoutEnd next + 1 = layoutEnd registers := by
    simpa [next] using
      layoutEnd_decrement_add_one registers .clock hpositive
  have hmove : MarkerMachine.moveAt .left
      (MarkerTape.canonicalTape registers)
      (MarkerTape.boundaryPosition registers 4) 4 =
    MarkerTape.canonicalTape next := by
    have hm := MarkerSchedule.moveClockBoundary_after_increment next
    have hinv := MarkerSchedule.increment_decrement_registers
      registers .clock hpositive
    rw [hinv] at hm
    exact hm
  have hrun := machine_reaches_decrementFirst_or_halts_of_open
    (next := next) base c limit source secondarySearchBase
    (directRef growth source finishDirectSlot) (by simp [limit]) h
    (3 : Fin 4) (by simpa [RegisterLayout.values] using hp)
    (by omega) (by omega) (boundaryOffset_le_layoutEnd registers 4)
    (by change layoutEnd registers - 1 ≤ layoutEnd next; omega)
    (by intro _; rfl) hmove hraw
  simpa [next, decrementCoreTape, clearOldCoreEnd,
    MarkerSchedule.decrementStartBoundary, boundaryOffset_four] using hrun

/-- The two-shift temp-decrement schedule resolves on an open core. -/
theorem machine_reaches_decrementTempSchedule_or_halts_of_open
    (base : Nat) (c : Nat.Partrec.Code) (source : Nat)
    {registers : Registers} {growth : Turing.Dir}
    {T : FullTM0.Tape (Symbol numTags)}
    (h : CoreOpenRepresents registers growth T)
    (hpositive : 0 < registers.get .temp)
    (hcommands : ∀ raw,
      raw ∈ decrementShiftCommands growth source .temp →
        raw ∈ rawCommands) :
    (FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨growth, source, secondarySearchBase⟩,
          atLogical growth T (boundaryOffset registers 3)⟩
        ⟨resolve base c (directRef growth source finishDirectSlot),
          atLogical growth
            (decrementCoreTape registers growth .temp T)
            (layoutEnd registers)⟩ ∧
      CoreOpenRepresents (registers.decrement .temp) growth
        (decrementCoreTape registers growth .temp T)) ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨growth, source, secondarySearchBase⟩,
          atLogical growth T (boundaryOffset registers 3)⟩ := by
  let limit := layoutEnd registers + 1
  let final := registers.decrement .temp
  have hp : 0 < registers.temp := by
    simpa [Registers.get] using hpositive
  have hinv : final.increment .temp = registers := by
    exact MarkerSchedule.increment_decrement_registers
      registers .temp hpositive
  let clockRegs := final.increment .clock
  let clockTape := installCore clockRegs growth T
  have hclockEnd : layoutEnd clockRegs = layoutEnd registers := by
    rw [← hinv]
    simp only [clockRegs, layoutEnd_increment]
  have hclockOpen : CoreOpenRepresents clockRegs growth clockTape := by
    apply installCore_open_of_extension h
    rw [hclockEnd]
  have hmoveThree : MarkerMachine.moveAt .left
      (MarkerTape.canonicalTape registers)
      (MarkerTape.boundaryPosition registers 3) 3 =
    MarkerTape.canonicalTape clockRegs := by
    have hm := MarkerSchedule.moveTempBoundary_before_clock final
    rw [hinv] at hm
    exact hm
  have hrawThree : RawCommand.markerShift
      ⟨growth, source, secondarySearchBase⟩ 3 .right .left
      (searchRef growth source (secondarySearchBase + 1))
      (some .right) none ∈ rawCommands := by
    apply hcommands
    simp [decrementShiftCommands, decrementShiftCommandsAux,
      MarkerShift.decrementOrder]
  have hthree := machine_reaches_decrementFirst_or_halts_of_open
    (next := clockRegs) base c limit source secondarySearchBase
    (searchRef growth source (secondarySearchBase + 1)) (by simp [limit]) h
    (2 : Fin 4) (by simpa [RegisterLayout.values] using hp)
    (by rw [hclockEnd]) (by rw [hclockEnd]; omega)
    (boundaryOffset_le_layoutEnd registers 3)
    (by change boundaryOffset registers 3 - 1 ≤ layoutEnd clockRegs
        rw [hclockEnd];
        have hb := boundaryOffset_le_layoutEnd registers (3 : Fin 5); omega)
    (by intro hlt; rw [hclockEnd] at hlt; omega)
    hmoveThree hrawThree
  have hfinalEnd : layoutEnd final + 1 = layoutEnd clockRegs := by
    rw [hclockEnd]
    exact layoutEnd_decrement_add_one registers .temp hpositive
  have hmoveFour : MarkerMachine.moveAt .left
      (MarkerTape.canonicalTape clockRegs)
      (MarkerTape.boundaryPosition clockRegs 4) 4 =
    MarkerTape.canonicalTape final := by
    simpa [clockRegs] using
      MarkerSchedule.moveClockBoundary_after_increment final
  have hrawFour : RawCommand.markerShift
      ⟨growth, source, secondarySearchBase + 1⟩ 4 .right .left
      (directRef growth source finishDirectSlot) (some .right) none ∈
        rawCommands := by
    apply hcommands
    simp [decrementShiftCommands, decrementShiftCommandsAux,
      MarkerShift.decrementOrder]
  have hfour := machine_reaches_decrementFollowing_or_halts_of_open
    (next := final) base c limit source (secondarySearchBase + 1)
    (directRef growth source finishDirectSlot) hclockOpen (3 : Fin 4)
    (by simp [clockRegs, final, RegisterLayout.values,
      Registers.increment, Registers.decrement, Registers.set,
      Registers.get])
    (by simp [limit, clockRegs, final, layoutEnd,
      RegisterLayout.clockBoundary_eq, RegisterLayout.values,
      Registers.increment, Registers.decrement, Registers.set,
      Registers.get] <;> omega)
    (by omega) (by omega) (boundaryOffset_le_layoutEnd clockRegs 4)
    (by change layoutEnd clockRegs - 1 ≤ layoutEnd final; omega)
    (by intro _; rfl) hmoveFour hrawFour
  have hsuccTwo : Fin.succ (2 : Fin 4) = (3 : Fin 5) := rfl
  have hsuccThree : Fin.succ (3 : Fin 4) = (4 : Fin 5) := rfl
  simp only [hsuccTwo] at hthree
  simp only [hsuccThree] at hfour
  have hhead : boundaryOffset registers 3 = firstGapOffset clockRegs 3 := by
    simp [clockRegs, final, firstGapOffset, boundaryOffset,
      CounterLayout.boundaryPos, RegisterLayout.values,
      Registers.increment, Registers.decrement, Registers.set,
      Registers.get] <;> omega
  have htapeThree : installCore clockRegs growth
      (writeLogical growth T (boundaryOffset registers 3) blankSymbol) =
      clockTape := by
    dsimp only [clockTape]
    apply installCore_write_inside
    · simp [boundaryOffset]
    · rw [hclockEnd]
      exact boundaryOffset_le_layoutEnd registers 3
  rw [htapeThree] at hthree
  have hfinalTape : installCore final growth
      (writeLogical growth clockTape (boundaryOffset clockRegs 4) blankSymbol) =
      decrementCoreTape registers growth .temp T := by
    rw [show boundaryOffset clockRegs (4 : Fin 5) =
      layoutEnd clockRegs by rfl]
    dsimp only [clockTape]
    rw [installCore_clear_old_overlay clockRegs final growth T hfinalEnd]
    rw [hclockEnd]
    rfl
  rw [hfinalTape] at hfour
  rw [hhead] at hthree
  rw [show boundaryOffset clockRegs (4 : Fin 5) =
    layoutEnd clockRegs by rfl, hclockEnd] at hfour
  simp only [searchRef, CounterControlPlan.resolve] at hthree
  have hrun := FullTM0.ResolvesTo.trans
    (hthree.imp (fun hsuccess => hsuccess.1) id)
    (hfour.imp (fun hsuccess => hsuccess.1) id)
  rcases hrun with hrun | hhalts
  · exact Or.inl ⟨by simpa [hhead] using hrun,
        decrementCoreTape_preserves_open h .temp hpositive⟩
  · exact Or.inr (by simpa [hhead] using hhalts)

/-- The three-shift right-decrement schedule resolves on an open core. -/
theorem machine_reaches_decrementRightSchedule_or_halts_of_open
    (base : Nat) (c : Nat.Partrec.Code) (source : Nat)
    {registers : Registers} {growth : Turing.Dir}
    {T : FullTM0.Tape (Symbol numTags)}
    (h : CoreOpenRepresents registers growth T)
    (hpositive : 0 < registers.get .right)
    (hcommands : ∀ raw,
      raw ∈ decrementShiftCommands growth source .right →
        raw ∈ rawCommands) :
    (FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨growth, source, secondarySearchBase⟩,
          atLogical growth T (boundaryOffset registers 2)⟩
        ⟨resolve base c (directRef growth source finishDirectSlot),
          atLogical growth
            (decrementCoreTape registers growth .right T)
            (layoutEnd registers)⟩ ∧
      CoreOpenRepresents (registers.decrement .right) growth
        (decrementCoreTape registers growth .right T)) ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨growth, source, secondarySearchBase⟩,
          atLogical growth T (boundaryOffset registers 2)⟩ := by
  let limit := layoutEnd registers + 1
  let final := registers.decrement .right
  have hinv : final.increment .right = registers :=
    MarkerSchedule.increment_decrement_registers registers .right hpositive
  let tempRegs := final.increment .temp
  let clockRegs := final.increment .clock
  let tempTape := installCore tempRegs growth T
  let clockTape := installCore clockRegs growth T
  have htempEnd : layoutEnd tempRegs = layoutEnd registers := by
    rw [← hinv]
    simp only [tempRegs, layoutEnd_increment]
  have hclockEnd : layoutEnd clockRegs = layoutEnd registers := by
    rw [← hinv]
    simp only [clockRegs, layoutEnd_increment]
  have htempOpen : CoreOpenRepresents tempRegs growth tempTape := by
    apply installCore_open_of_extension h
    rw [htempEnd]
  have hclockOpen : CoreOpenRepresents clockRegs growth clockTape := by
    apply installCore_open_of_extension h
    rw [hclockEnd]
  have hmoveTwo : MarkerMachine.moveAt .left
      (MarkerTape.canonicalTape registers)
      (MarkerTape.boundaryPosition registers 2) 2 =
    MarkerTape.canonicalTape tempRegs := by
    have hm := MarkerSchedule.moveRightBoundary_before_temp final
    rw [hinv] at hm
    exact hm
  have hrawTwo : RawCommand.markerShift
      ⟨growth, source, secondarySearchBase⟩ 2 .right .left
      (searchRef growth source (secondarySearchBase + 1))
      (some .right) none ∈ rawCommands := by
    apply hcommands
    simp [decrementShiftCommands, decrementShiftCommandsAux,
      MarkerShift.decrementOrder]
  have htwo := machine_reaches_decrementFirst_or_halts_of_open
    (next := tempRegs) base c limit source secondarySearchBase
    (searchRef growth source (secondarySearchBase + 1)) (by simp [limit]) h
    (1 : Fin 4)
    (by simpa [RegisterLayout.values, Registers.get] using hpositive)
    (by rw [htempEnd]) (by rw [htempEnd]; omega)
    (boundaryOffset_le_layoutEnd registers 2)
    (by change boundaryOffset registers 2 - 1 ≤ layoutEnd tempRegs
        rw [htempEnd]
        have hb := boundaryOffset_le_layoutEnd registers (2 : Fin 5)
        omega)
    (by intro hlt; rw [htempEnd] at hlt; omega)
    hmoveTwo hrawTwo
  have hmoveThree : MarkerMachine.moveAt .left
      (MarkerTape.canonicalTape tempRegs)
      (MarkerTape.boundaryPosition tempRegs 3) 3 =
    MarkerTape.canonicalTape clockRegs := by
    simpa [tempRegs, clockRegs] using
      MarkerSchedule.moveTempBoundary_before_clock final
  have hrawThree : RawCommand.markerShift
      ⟨growth, source, secondarySearchBase + 1⟩ 3 .right .left
      (searchRef growth source (secondarySearchBase + 2))
      (some .right) none ∈ rawCommands := by
    apply hcommands
    simp [decrementShiftCommands, decrementShiftCommandsAux,
      MarkerShift.decrementOrder]
  have hthree := machine_reaches_decrementFollowing_or_halts_of_open
    (next := clockRegs) base c limit source (secondarySearchBase + 1)
    (searchRef growth source (secondarySearchBase + 2)) htempOpen (2 : Fin 4)
    (by simp [tempRegs, final, RegisterLayout.values,
      Registers.increment, Registers.decrement, Registers.set,
      Registers.get])
    (by simp [limit, tempRegs, final, layoutEnd,
      RegisterLayout.clockBoundary_eq, RegisterLayout.values,
      Registers.increment, Registers.decrement, Registers.set,
      Registers.get] <;> omega)
    (by rw [hclockEnd, htempEnd])
    (by rw [hclockEnd, htempEnd]; omega)
    (boundaryOffset_le_layoutEnd tempRegs 3)
    (by
      change boundaryOffset tempRegs 3 - 1 ≤ layoutEnd clockRegs
      have hb := boundaryOffset_le_layoutEnd tempRegs (3 : Fin 5)
      rw [hclockEnd, ← htempEnd]
      omega)
    (by intro hlt; rw [hclockEnd, htempEnd] at hlt; omega)
    hmoveThree hrawThree
  have hfinalEnd : layoutEnd final + 1 = layoutEnd clockRegs := by
    rw [hclockEnd]
    exact layoutEnd_decrement_add_one registers .right hpositive
  have hmoveFour : MarkerMachine.moveAt .left
      (MarkerTape.canonicalTape clockRegs)
      (MarkerTape.boundaryPosition clockRegs 4) 4 =
    MarkerTape.canonicalTape final := by
    simpa [clockRegs] using
      MarkerSchedule.moveClockBoundary_after_increment final
  have hrawFour : RawCommand.markerShift
      ⟨growth, source, secondarySearchBase + 2⟩ 4 .right .left
      (directRef growth source finishDirectSlot) (some .right) none ∈
        rawCommands := by
    apply hcommands
    simp [decrementShiftCommands, decrementShiftCommandsAux,
      MarkerShift.decrementOrder]
  have hfour := machine_reaches_decrementFollowing_or_halts_of_open
    (next := final) base c limit source (secondarySearchBase + 2)
    (directRef growth source finishDirectSlot) hclockOpen (3 : Fin 4)
    (by simp [clockRegs, final, RegisterLayout.values,
      Registers.increment, Registers.decrement, Registers.set,
      Registers.get])
    (by simp [limit, clockRegs, final, layoutEnd,
      RegisterLayout.clockBoundary_eq, RegisterLayout.values,
      Registers.increment, Registers.decrement, Registers.set,
      Registers.get] <;> omega)
    (by omega) (by omega) (boundaryOffset_le_layoutEnd clockRegs 4)
    (by change layoutEnd clockRegs - 1 ≤ layoutEnd final; omega)
    (by intro _; rfl) hmoveFour hrawFour
  have hsuccOne : Fin.succ (1 : Fin 4) = (2 : Fin 5) := rfl
  have hsuccTwo : Fin.succ (2 : Fin 4) = (3 : Fin 5) := rfl
  have hsuccThree : Fin.succ (3 : Fin 4) = (4 : Fin 5) := rfl
  simp only [hsuccOne] at htwo
  simp only [hsuccTwo] at hthree
  simp only [hsuccThree] at hfour
  have hheadTwo : boundaryOffset registers 2 =
      firstGapOffset tempRegs 2 := by
    rw [← hinv]
    simp [tempRegs, final, firstGapOffset, boundaryOffset,
      CounterLayout.boundaryPos, RegisterLayout.values,
      Registers.increment, Registers.decrement, Registers.set,
      Registers.get] <;> omega
  have hheadThree : boundaryOffset tempRegs 3 =
      firstGapOffset clockRegs 3 := by
    simp [tempRegs, clockRegs, final, firstGapOffset, boundaryOffset,
      CounterLayout.boundaryPos, RegisterLayout.values,
      Registers.increment, Registers.decrement, Registers.set,
      Registers.get] <;> omega
  have htapeTwo : installCore tempRegs growth
      (writeLogical growth T (boundaryOffset registers 2) blankSymbol) =
      tempTape := by
    dsimp only [tempTape]
    apply installCore_write_inside
    · simp [boundaryOffset]
    · rw [htempEnd]
      exact boundaryOffset_le_layoutEnd registers 2
  rw [htapeTwo] at htwo
  have htapeThree : installCore clockRegs growth
      (writeLogical growth tempTape (boundaryOffset tempRegs 3) blankSymbol) =
      clockTape := by
    dsimp only [tempTape, clockTape]
    apply installCore_after_internal_left
    · rw [hclockEnd, htempEnd]
    · simp [boundaryOffset]
    · rw [hclockEnd, ← htempEnd]
      exact boundaryOffset_le_layoutEnd tempRegs 3
  rw [htapeThree] at hthree
  have hfinalTape : installCore final growth
      (writeLogical growth clockTape (boundaryOffset clockRegs 4) blankSymbol) =
      decrementCoreTape registers growth .right T := by
    rw [show boundaryOffset clockRegs (4 : Fin 5) =
      layoutEnd clockRegs by rfl]
    dsimp only [clockTape]
    rw [installCore_clear_old_overlay clockRegs final growth T hfinalEnd]
    rw [hclockEnd]
    rfl
  rw [hfinalTape] at hfour
  rw [hheadTwo] at htwo
  rw [hheadThree] at hthree
  rw [show boundaryOffset clockRegs (4 : Fin 5) =
    layoutEnd clockRegs by rfl, hclockEnd] at hfour
  simp only [searchRef, CounterControlPlan.resolve] at htwo hthree
  have hrun := FullTM0.ResolvesTo.trans
    (htwo.imp (fun hsuccess => hsuccess.1) id)
    (FullTM0.ResolvesTo.trans
      (hthree.imp (fun hsuccess => hsuccess.1) id)
      (hfour.imp (fun hsuccess => hsuccess.1) id))
  rcases hrun with hrun | hhalts
  · exact Or.inl ⟨by simpa [hheadTwo] using hrun,
        decrementCoreTape_preserves_open h .right hpositive⟩
  · exact Or.inr (by simpa [hheadTwo] using hhalts)

/-- The four-shift left-decrement schedule resolves on an open core. -/
theorem machine_reaches_decrementLeftSchedule_or_halts_of_open
    (base : Nat) (c : Nat.Partrec.Code) (source : Nat)
    {registers : Registers} {growth : Turing.Dir}
    {T : FullTM0.Tape (Symbol numTags)}
    (h : CoreOpenRepresents registers growth T)
    (hpositive : 0 < registers.get .left)
    (hcommands : ∀ raw,
      raw ∈ decrementShiftCommands growth source .left →
        raw ∈ rawCommands) :
    (FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨growth, source, secondarySearchBase⟩,
          atLogical growth T (boundaryOffset registers 1)⟩
        ⟨resolve base c (directRef growth source finishDirectSlot),
          atLogical growth
            (decrementCoreTape registers growth .left T)
            (layoutEnd registers)⟩ ∧
      CoreOpenRepresents (registers.decrement .left) growth
        (decrementCoreTape registers growth .left T)) ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨growth, source, secondarySearchBase⟩,
          atLogical growth T (boundaryOffset registers 1)⟩ := by
  let limit := layoutEnd registers + 1
  let final := registers.decrement .left
  have hinv : final.increment .left = registers :=
    MarkerSchedule.increment_decrement_registers registers .left hpositive
  let rightRegs := final.increment .right
  let tempRegs := final.increment .temp
  let clockRegs := final.increment .clock
  let rightTape := installCore rightRegs growth T
  let tempTape := installCore tempRegs growth T
  let clockTape := installCore clockRegs growth T
  have hrightEnd : layoutEnd rightRegs = layoutEnd registers := by
    rw [← hinv]
    simp only [rightRegs, layoutEnd_increment]
  have htempEnd : layoutEnd tempRegs = layoutEnd registers := by
    rw [← hinv]
    simp only [tempRegs, layoutEnd_increment]
  have hclockEnd : layoutEnd clockRegs = layoutEnd registers := by
    rw [← hinv]
    simp only [clockRegs, layoutEnd_increment]
  have hrightOpen : CoreOpenRepresents rightRegs growth rightTape := by
    apply installCore_open_of_extension h
    rw [hrightEnd]
  have htempOpen : CoreOpenRepresents tempRegs growth tempTape := by
    apply installCore_open_of_extension h
    rw [htempEnd]
  have hclockOpen : CoreOpenRepresents clockRegs growth clockTape := by
    apply installCore_open_of_extension h
    rw [hclockEnd]
  have hmoveOne : MarkerMachine.moveAt .left
      (MarkerTape.canonicalTape registers)
      (MarkerTape.boundaryPosition registers 1) 1 =
    MarkerTape.canonicalTape rightRegs := by
    have hm := MarkerSchedule.moveLeftBoundary_before_right final
    rw [hinv] at hm
    exact hm
  have hrawOne : RawCommand.markerShift
      ⟨growth, source, secondarySearchBase⟩ 1 .right .left
      (searchRef growth source (secondarySearchBase + 1))
      (some .right) none ∈ rawCommands := by
    apply hcommands
    simp [decrementShiftCommands, decrementShiftCommandsAux,
      MarkerShift.decrementOrder]
  have hone := machine_reaches_decrementFirst_or_halts_of_open
    (next := rightRegs) base c limit source secondarySearchBase
    (searchRef growth source (secondarySearchBase + 1)) (by simp [limit]) h
    (0 : Fin 4)
    (by simpa [RegisterLayout.values, Registers.get] using hpositive)
    (by rw [hrightEnd]) (by rw [hrightEnd]; omega)
    (boundaryOffset_le_layoutEnd registers 1)
    (by change boundaryOffset registers 1 - 1 ≤ layoutEnd rightRegs
        rw [hrightEnd]
        have hb := boundaryOffset_le_layoutEnd registers (1 : Fin 5)
        omega)
    (by intro hlt; rw [hrightEnd] at hlt; omega)
    hmoveOne hrawOne
  have hmoveTwo : MarkerMachine.moveAt .left
      (MarkerTape.canonicalTape rightRegs)
      (MarkerTape.boundaryPosition rightRegs 2) 2 =
    MarkerTape.canonicalTape tempRegs := by
    simpa [rightRegs, tempRegs] using
      MarkerSchedule.moveRightBoundary_before_temp final
  have hrawTwo : RawCommand.markerShift
      ⟨growth, source, secondarySearchBase + 1⟩ 2 .right .left
      (searchRef growth source (secondarySearchBase + 2))
      (some .right) none ∈ rawCommands := by
    apply hcommands
    simp [decrementShiftCommands, decrementShiftCommandsAux,
      MarkerShift.decrementOrder]
  have htwo := machine_reaches_decrementFollowing_or_halts_of_open
    (next := tempRegs) base c limit source (secondarySearchBase + 1)
    (searchRef growth source (secondarySearchBase + 2)) hrightOpen (1 : Fin 4)
    (by simp [rightRegs, final, RegisterLayout.values,
      Registers.increment, Registers.decrement, Registers.set,
      Registers.get])
    (by simp [limit, rightRegs, final, layoutEnd,
      RegisterLayout.clockBoundary_eq, RegisterLayout.values,
      Registers.increment, Registers.decrement, Registers.set,
      Registers.get] <;> omega)
    (by rw [htempEnd, hrightEnd])
    (by rw [htempEnd, hrightEnd]; omega)
    (boundaryOffset_le_layoutEnd rightRegs 2)
    (by
      change boundaryOffset rightRegs 2 - 1 ≤ layoutEnd tempRegs
      have hb := boundaryOffset_le_layoutEnd rightRegs (2 : Fin 5)
      rw [htempEnd, ← hrightEnd]
      omega)
    (by intro hlt; rw [htempEnd, hrightEnd] at hlt; omega)
    hmoveTwo hrawTwo
  have hmoveThree : MarkerMachine.moveAt .left
      (MarkerTape.canonicalTape tempRegs)
      (MarkerTape.boundaryPosition tempRegs 3) 3 =
    MarkerTape.canonicalTape clockRegs := by
    simpa [tempRegs, clockRegs] using
      MarkerSchedule.moveTempBoundary_before_clock final
  have hrawThree : RawCommand.markerShift
      ⟨growth, source, secondarySearchBase + 2⟩ 3 .right .left
      (searchRef growth source (secondarySearchBase + 3))
      (some .right) none ∈ rawCommands := by
    apply hcommands
    simp [decrementShiftCommands, decrementShiftCommandsAux,
      MarkerShift.decrementOrder]
  have hthree := machine_reaches_decrementFollowing_or_halts_of_open
    (next := clockRegs) base c limit source (secondarySearchBase + 2)
    (searchRef growth source (secondarySearchBase + 3)) htempOpen (2 : Fin 4)
    (by simp [tempRegs, final, RegisterLayout.values,
      Registers.increment, Registers.decrement, Registers.set,
      Registers.get])
    (by simp [limit, tempRegs, final, layoutEnd,
      RegisterLayout.clockBoundary_eq, RegisterLayout.values,
      Registers.increment, Registers.decrement, Registers.set,
      Registers.get] <;> omega)
    (by rw [hclockEnd, htempEnd])
    (by rw [hclockEnd, htempEnd]; omega)
    (boundaryOffset_le_layoutEnd tempRegs 3)
    (by
      change boundaryOffset tempRegs 3 - 1 ≤ layoutEnd clockRegs
      have hb := boundaryOffset_le_layoutEnd tempRegs (3 : Fin 5)
      rw [hclockEnd, ← htempEnd]
      omega)
    (by intro hlt; rw [hclockEnd, htempEnd] at hlt; omega)
    hmoveThree hrawThree
  have hfinalEnd : layoutEnd final + 1 = layoutEnd clockRegs := by
    rw [hclockEnd]
    exact layoutEnd_decrement_add_one registers .left hpositive
  have hmoveFour : MarkerMachine.moveAt .left
      (MarkerTape.canonicalTape clockRegs)
      (MarkerTape.boundaryPosition clockRegs 4) 4 =
    MarkerTape.canonicalTape final := by
    simpa [clockRegs] using
      MarkerSchedule.moveClockBoundary_after_increment final
  have hrawFour : RawCommand.markerShift
      ⟨growth, source, secondarySearchBase + 3⟩ 4 .right .left
      (directRef growth source finishDirectSlot) (some .right) none ∈
        rawCommands := by
    apply hcommands
    simp [decrementShiftCommands, decrementShiftCommandsAux,
      MarkerShift.decrementOrder]
  have hfour := machine_reaches_decrementFollowing_or_halts_of_open
    (next := final) base c limit source (secondarySearchBase + 3)
    (directRef growth source finishDirectSlot) hclockOpen (3 : Fin 4)
    (by simp [clockRegs, final, RegisterLayout.values,
      Registers.increment, Registers.decrement, Registers.set,
      Registers.get])
    (by simp [limit, clockRegs, final, layoutEnd,
      RegisterLayout.clockBoundary_eq, RegisterLayout.values,
      Registers.increment, Registers.decrement, Registers.set,
      Registers.get] <;> omega)
    (by omega) (by omega) (boundaryOffset_le_layoutEnd clockRegs 4)
    (by change layoutEnd clockRegs - 1 ≤ layoutEnd final; omega)
    (by intro _; rfl) hmoveFour hrawFour
  have hsuccZero : Fin.succ (0 : Fin 4) = (1 : Fin 5) := rfl
  have hsuccOne : Fin.succ (1 : Fin 4) = (2 : Fin 5) := rfl
  have hsuccTwo : Fin.succ (2 : Fin 4) = (3 : Fin 5) := rfl
  have hsuccThree : Fin.succ (3 : Fin 4) = (4 : Fin 5) := rfl
  simp only [hsuccZero] at hone
  simp only [hsuccOne] at htwo
  simp only [hsuccTwo] at hthree
  simp only [hsuccThree] at hfour
  have hheadOne : boundaryOffset registers 1 =
      firstGapOffset rightRegs 1 := by
    rw [← hinv]
    simp [rightRegs, final, firstGapOffset, boundaryOffset,
      CounterLayout.boundaryPos, RegisterLayout.values,
      Registers.increment, Registers.decrement, Registers.set,
      Registers.get] <;> omega
  have hheadTwo : boundaryOffset rightRegs 2 =
      firstGapOffset tempRegs 2 := by
    simp [rightRegs, tempRegs, final, firstGapOffset, boundaryOffset,
      CounterLayout.boundaryPos, RegisterLayout.values,
      Registers.increment, Registers.decrement, Registers.set,
      Registers.get] <;> omega
  have hheadThree : boundaryOffset tempRegs 3 =
      firstGapOffset clockRegs 3 := by
    simp [tempRegs, clockRegs, final, firstGapOffset, boundaryOffset,
      CounterLayout.boundaryPos, RegisterLayout.values,
      Registers.increment, Registers.decrement, Registers.set,
      Registers.get] <;> omega
  have htapeOne : installCore rightRegs growth
      (writeLogical growth T (boundaryOffset registers 1) blankSymbol) =
      rightTape := by
    dsimp only [rightTape]
    apply installCore_write_inside
    · simp [boundaryOffset]
    · rw [hrightEnd]
      exact boundaryOffset_le_layoutEnd registers 1
  rw [htapeOne] at hone
  have htapeTwo : installCore tempRegs growth
      (writeLogical growth rightTape (boundaryOffset rightRegs 2) blankSymbol) =
      tempTape := by
    dsimp only [rightTape, tempTape]
    apply installCore_after_internal_left
    · rw [htempEnd, hrightEnd]
    · simp [boundaryOffset]
    · rw [htempEnd, ← hrightEnd]
      exact boundaryOffset_le_layoutEnd rightRegs 2
  rw [htapeTwo] at htwo
  have htapeThree : installCore clockRegs growth
      (writeLogical growth tempTape (boundaryOffset tempRegs 3) blankSymbol) =
      clockTape := by
    dsimp only [tempTape, clockTape]
    apply installCore_after_internal_left
    · rw [hclockEnd, htempEnd]
    · simp [boundaryOffset]
    · rw [hclockEnd, ← htempEnd]
      exact boundaryOffset_le_layoutEnd tempRegs 3
  rw [htapeThree] at hthree
  have hfinalTape : installCore final growth
      (writeLogical growth clockTape (boundaryOffset clockRegs 4) blankSymbol) =
      decrementCoreTape registers growth .left T := by
    rw [show boundaryOffset clockRegs (4 : Fin 5) =
      layoutEnd clockRegs by rfl]
    dsimp only [clockTape]
    rw [installCore_clear_old_overlay clockRegs final growth T hfinalEnd]
    rw [hclockEnd]
    rfl
  rw [hfinalTape] at hfour
  rw [hheadOne] at hone
  rw [hheadTwo] at htwo
  rw [hheadThree] at hthree
  rw [show boundaryOffset clockRegs (4 : Fin 5) =
    layoutEnd clockRegs by rfl, hclockEnd] at hfour
  simp only [searchRef, CounterControlPlan.resolve] at hone htwo hthree
  have hrun := FullTM0.ResolvesTo.trans
    (hone.imp (fun hsuccess => hsuccess.1) id)
    (FullTM0.ResolvesTo.trans
      (htwo.imp (fun hsuccess => hsuccess.1) id)
      (FullTM0.ResolvesTo.trans
        (hthree.imp (fun hsuccess => hsuccess.1) id)
        (hfour.imp (fun hsuccess => hsuccess.1) id)))
  rcases hrun with hrun | hhalts
  · exact Or.inl ⟨by simpa [hheadOne] using hrun,
        decrementCoreTape_preserves_open h .left hpositive⟩
  · exact Or.inr (by simpa [hheadOne] using hhalts)

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
  cases register with
  | clock =>
      have hraw : RawCommand.markerShift
          ⟨growth, source, secondarySearchBase⟩ 4 .right .left
          (directRef growth source finishDirectSlot) (some .right) none ∈
            rawCommands := by
        apply hcommands
        simp [decrementShiftCommands, decrementShiftCommandsAux,
          MarkerShift.decrementOrder]
      simpa [MarkerSchedule.decrementStartBoundary] using
        machine_reaches_decrementClockSchedule_or_halts_of_open base c source
          h hpositive hraw
  | temp =>
      simpa [MarkerSchedule.decrementStartBoundary] using
        machine_reaches_decrementTempSchedule_or_halts_of_open base c source
          h hpositive hcommands
  | right =>
      simpa [MarkerSchedule.decrementStartBoundary] using
        machine_reaches_decrementRightSchedule_or_halts_of_open base c source
          h hpositive hcommands
  | left =>
      simpa [MarkerSchedule.decrementStartBoundary] using
        machine_reaches_decrementLeftSchedule_or_halts_of_open base c source
          h hpositive hcommands

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
      blankSymbol := by
  rw [atLogical_read]
  cases register with
  | left =>
      have hp : 0 < registers.left := by
        simpa [Registers.get] using hpositive
      have hb := h.gap_blank (0 : Fin 4) (registers.left - 1) (by
        simp [RegisterLayout.values]
        omega)
      have hcoord : (firstGapOffset registers 0 : Int) +
          (registers.left - 1 : Nat) =
          (boundaryOffset registers 1 - 1 : Nat) := by
        simp [firstGapOffset, boundaryOffset, CounterLayout.boundaryPos,
          RegisterLayout.values]
        omega
      rw [hcoord] at hb
      simpa [MarkerSchedule.decrementStartBoundary] using hb
  | right =>
      have hp : 0 < registers.right := by
        simpa [Registers.get] using hpositive
      have hb := h.gap_blank (1 : Fin 4) (registers.right - 1) (by
        simp [RegisterLayout.values]
        omega)
      have hcoord : (firstGapOffset registers 1 : Int) +
          (registers.right - 1 : Nat) =
          (boundaryOffset registers 2 - 1 : Nat) := by
        simp [firstGapOffset, boundaryOffset, CounterLayout.boundaryPos,
          RegisterLayout.values]
        omega
      rw [hcoord] at hb
      simpa [MarkerSchedule.decrementStartBoundary] using hb
  | temp =>
      have hp : 0 < registers.temp := by
        simpa [Registers.get] using hpositive
      have hb := h.gap_blank (2 : Fin 4) (registers.temp - 1) (by
        simp [RegisterLayout.values]
        omega)
      have hcoord : (firstGapOffset registers 2 : Int) +
          (registers.temp - 1 : Nat) =
          (boundaryOffset registers 3 - 1 : Nat) := by
        simp [firstGapOffset, boundaryOffset, CounterLayout.boundaryPos,
          RegisterLayout.values]
        omega
      rw [hcoord] at hb
      simpa [MarkerSchedule.decrementStartBoundary] using hb
  | clock =>
      have hp : 0 < registers.clock := by
        simpa [Registers.get] using hpositive
      have hb := h.gap_blank (3 : Fin 4) (registers.clock - 1) (by
        simp [RegisterLayout.values]
        omega)
      have hcoord : (firstGapOffset registers 3 : Int) +
          (registers.clock - 1 : Nat) =
          (boundaryOffset registers 4 - 1 : Nat) := by
        simp [firstGapOffset, boundaryOffset, CounterLayout.boundaryPos,
          RegisterLayout.values, layoutEnd,
          RegisterLayout.clockBoundary_eq]
        omega
      rw [hcoord] at hb
      simpa [MarkerSchedule.decrementStartBoundary] using hb

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
            (directRef growth source bodyDirectBase) 4 bodySearchBase
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
      simpa [route] using hraw
    rcases List.mem_append.mp hraw' with hentry | hcontinuation
    · simp only [decrementRules, List.mem_append]
      exact Or.inl (Or.inl (Or.inl hentry))
    · simp only [decrementRules, List.mem_append]
      exact Or.inl (Or.inl (Or.inr hcontinuation))
  cases register with
  | clock => exact Or.inl Relation.ReflTransGen.refl
  | temp =>
      have hrun := route_reaches_or_halts_at_of_ne_nil base c limit
        (shortResolves_all base c limit) growth source bodySearchBase
        (bodyDirectBase + 1) (directRef growth source bodyDirectBase)
        (directRef growth source testDirectSlot) 4
        (AnchoredCounterGeometry.routeToDecrementStart .temp)
        (by simp [AnchoredCounterGeometry.routeToDecrementStart]) T
        (layoutEnd registers) (boundaryOffset registers 3)
        h.read_boundary_four
        (routeToDecrementStart_executesWithin_of_core h hlimit .temp)
        (by intro raw hraw; exact hcommands raw hraw)
        (by intro raw hraw; exact hrules raw hraw)
      change (FullTM0.Reaches (CounterControlNestingBridge.machine base c)
          ⟨resolve base c
              (bodyEntry growth source
                (.decrement .temp ifZero ifPositive)),
            atLogical growth T (layoutEnd registers)⟩
          ⟨resolve base c (directRef growth source testDirectSlot),
            atLogical growth T (boundaryOffset registers 3)⟩ ∨
        FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
          ⟨resolve base c
              (bodyEntry growth source
                (.decrement .temp ifZero ifPositive)),
            atLogical growth T (layoutEnd registers)⟩) at hrun
      exact hrun
  | right =>
      have hrun := route_reaches_or_halts_at_of_ne_nil base c limit
        (shortResolves_all base c limit) growth source bodySearchBase
        (bodyDirectBase + 1) (directRef growth source bodyDirectBase)
        (directRef growth source testDirectSlot) 4
        (AnchoredCounterGeometry.routeToDecrementStart .right)
        (by simp [AnchoredCounterGeometry.routeToDecrementStart]) T
        (layoutEnd registers) (boundaryOffset registers 2)
        h.read_boundary_four
        (routeToDecrementStart_executesWithin_of_core h hlimit .right)
        (by intro raw hraw; exact hcommands raw hraw)
        (by intro raw hraw; exact hrules raw hraw)
      change (FullTM0.Reaches (CounterControlNestingBridge.machine base c)
          ⟨resolve base c
              (bodyEntry growth source
                (.decrement .right ifZero ifPositive)),
            atLogical growth T (layoutEnd registers)⟩
          ⟨resolve base c (directRef growth source testDirectSlot),
            atLogical growth T (boundaryOffset registers 2)⟩ ∨
        FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
          ⟨resolve base c
              (bodyEntry growth source
                (.decrement .right ifZero ifPositive)),
            atLogical growth T (layoutEnd registers)⟩) at hrun
      exact hrun
  | left =>
      have hrun := route_reaches_or_halts_at_of_ne_nil base c limit
        (shortResolves_all base c limit) growth source bodySearchBase
        (bodyDirectBase + 1) (directRef growth source bodyDirectBase)
        (directRef growth source testDirectSlot) 4
        (AnchoredCounterGeometry.routeToDecrementStart .left)
        (by simp [AnchoredCounterGeometry.routeToDecrementStart]) T
        (layoutEnd registers) (boundaryOffset registers 1)
        h.read_boundary_four
        (routeToDecrementStart_executesWithin_of_core h hlimit .left)
        (by intro raw hraw; exact hcommands raw hraw)
        (by intro raw hraw; exact hrules raw hraw)
      change (FullTM0.Reaches (CounterControlNestingBridge.machine base c)
          ⟨resolve base c
              (bodyEntry growth source
                (.decrement .left ifZero ifPositive)),
            atLogical growth T (layoutEnd registers)⟩
          ⟨resolve base c (directRef growth source testDirectSlot),
            atLogical growth T (boundaryOffset registers 1)⟩ ∨
        FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
          ⟨resolve base c
              (bodyEntry growth source
                (.decrement .left ifZero ifPositive)),
            atLogical growth T (layoutEnd registers)⟩) at hrun
      exact hrun

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
        (AnchoredCounterGeometry.registerGap register).castSucc := by
    cases register with
    | left =>
        have hz : registers.left = 0 := by
          simpa [Registers.get] using hzero
        simp [MarkerSchedule.decrementStartBoundary,
          AnchoredCounterGeometry.registerGap, boundaryOffset,
          CounterLayout.boundaryPos, RegisterLayout.values, hz]
    | right =>
        have hz : registers.right = 0 := by
          simpa [Registers.get] using hzero
        simp [MarkerSchedule.decrementStartBoundary,
          AnchoredCounterGeometry.registerGap, boundaryOffset,
          CounterLayout.boundaryPos, RegisterLayout.values, hz]
    | temp =>
        have hz : registers.temp = 0 := by
          simpa [Registers.get] using hzero
        simp [MarkerSchedule.decrementStartBoundary,
          AnchoredCounterGeometry.registerGap, boundaryOffset,
          CounterLayout.boundaryPos, RegisterLayout.values, hz]
    | clock =>
        have hz : registers.clock = 0 := by
          simpa [Registers.get] using hzero
        simp [MarkerSchedule.decrementStartBoundary,
          AnchoredCounterGeometry.registerGap, boundaryOffset,
          CounterLayout.boundaryPos, RegisterLayout.values, hz]
  have hrun := route_reaches_or_halts_at_of_ne_nil base c limit
    (shortResolves_all base c limit) growth source zeroSearchBase
    zeroDirectBase (directRef growth source branchDirectSlot)
    (.logical growth ifZero)
    (AnchoredCounterGeometry.registerGap register).castSucc route
    (by cases register <;> simp [route,
      AnchoredCounterGeometry.routeFromZero]) T
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
