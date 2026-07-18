/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlShiftSemantics

/-!
# Semantics of compiled counter-update schedules

This module lifts the individual compiled marker shifts to complete register
updates on a tagged, oriented counter frame.  Recovery navigation is kept
separate: the endpoints here retain the head position at which the final
shift command returns.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlScheduleSemantics

open Turing CounterMachine
open BoundedMarkerProgram FramedMarkerTape FramedCounterGeometry
open CounterControlPlan CounterControlShiftSemantics

noncomputable section

/-! ## Logical writes -/

theorem logicalTape_writeLogical_apply {numTags : Nat}
    (growth : Turing.Dir) (T : FullTM0.Tape (Symbol numTags))
    (source : Nat) (written : Symbol numTags) (position : Int) :
    logicalTape growth (writeLogical growth T source written) position =
      if position = source then written else logicalTape growth T position := by
  rw [logicalTape_apply, writeLogical]
  by_cases hposition : position = source
  · subst position
    simp
  · rw [Function.update_of_ne]
    · simp [hposition]
    · intro hphysical
      apply hposition
      exact physicalCoord_injective growth hphysical

/-! ## Canonical-overlay normalization -/

/-- Reinstalling the canonical overlay of a represented frame is a no-op.
This lets the operational shift proof use `install` as an exact intermediate
tape without strengthening the public frame hypothesis. -/
theorem install_eq_self_of_represents {numTags : Nat}
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T) :
    install spec.registers spec.growth spec.returnTag T = T := by
  have hlogical : logicalTape spec.growth
        (install spec.registers spec.growth spec.returnTag T) =
      logicalTape spec.growth T := by
    funext position
    rw [logicalTape_install]
    by_cases hzero : position = 0
    · subst position
      simpa using h.tag.symm
    by_cases hcore : 1 ≤ position ∧ position ≤ layoutEnd spec.registers
    · have hnonnegative : 0 ≤ position := by omega
      obtain ⟨corePosition, rfl⟩ := Int.eq_ofNat_of_zero_le hnonnegative
      have hpositive : 0 < corePosition := by exact_mod_cast hcore.1
      obtain ⟨position, rfl⟩ :=
        Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpositive)
      have hboundNat : position + 1 ≤ layoutEnd spec.registers := by
        exact_mod_cast hcore.2
      have hbound : position ≤ RegisterLayout.clockBoundary spec.registers := by
        apply Nat.le_of_succ_le_succ
        simpa only [layoutEnd] using hboundNat
      rw [logicalOverlay, if_neg (by omega), if_pos]
      · simpa using (h.core position hbound).symm
      · constructor <;> omega
    · rw [logicalOverlay, if_neg hzero, if_neg hcore]
  calc
    install spec.registers spec.growth spec.returnTag T =
        logicalTape spec.growth (logicalTape spec.growth
          (install spec.registers spec.growth spec.returnTag T)) := by
      rw [logicalTape_involutive]
    _ = logicalTape spec.growth (logicalTape spec.growth T) :=
      congrArg (logicalTape spec.growth) hlogical
    _ = T := logicalTape_involutive spec.growth T

/-- The canonical overlay depends on its backing tape only outside the
installed core interval. -/
theorem install_congr_of_outside {numTags : Nat} (registers : Registers)
    (growth : Turing.Dir) (tag : Fin numTags)
    (T U : FullTM0.Tape (Symbol numTags))
    (houtside : ∀ position : Int,
      ¬(1 ≤ position ∧ position ≤ layoutEnd registers) →
        logicalTape growth T position = logicalTape growth U position) :
    install registers growth tag T = install registers growth tag U := by
  have hlogical : logicalTape growth (install registers growth tag T) =
      logicalTape growth (install registers growth tag U) := by
    simp only [logicalTape_install]
    funext position
    unfold logicalOverlay
    by_cases hzero : position = 0
    · simp [hzero]
    · simp only [hzero, ↓reduceIte]
      by_cases hcore : 1 ≤ position ∧ position ≤ layoutEnd registers
      · simp [hcore]
      · rw [if_neg hcore, if_neg hcore]
        exact houtside position hcore
  calc
    install registers growth tag T =
        logicalTape growth (logicalTape growth
          (install registers growth tag T)) := by
      rw [logicalTape_involutive]
    _ = logicalTape growth (logicalTape growth
        (install registers growth tag U)) :=
      congrArg (logicalTape growth) hlogical
    _ = install registers growth tag U :=
      logicalTape_involutive growth _

/-! ## One canonical boundary rewrite -/

/-- The native tagged core records the same rightward boundary rewrite as
the six-symbol marker tape. -/
theorem coreSymbol_of_moveAt_right {numTags : Nat}
    (current next : Registers) (label : Fin 5)
    (hmove : MarkerMachine.moveAt .right
        (MarkerTape.canonicalTape current)
        (MarkerTape.boundaryPosition current label) label =
      MarkerTape.canonicalTape next)
    (position : Nat) :
    coreSymbol (numTags := numTags) next position =
      if position = CounterLayout.boundaryPos
          (RegisterLayout.values current) label + 1 then
        boundarySymbol label
      else if position = CounterLayout.boundaryPos
          (RegisterLayout.values current) label then
        blankSymbol
      else coreSymbol current position := by
  have hp := congrFun hmove (position : Int)
  change baseSymbol (MarkerMachine.encodeSymbol
      (MarkerTape.canonicalTape next position)) = _
  rw [← hp]
  by_cases htarget : position = CounterLayout.boundaryPos
      (RegisterLayout.values current) label + 1
  · subst position
    simp [MarkerMachine.moveAt, MarkerShift.writeAt,
      MarkerTape.boundaryPosition, boundarySymbol]
  by_cases hsource : position = CounterLayout.boundaryPos
      (RegisterLayout.values current) label
  · subst position
    simp [MarkerMachine.moveAt, MarkerShift.writeAt,
      MarkerTape.boundaryPosition, htarget, blankSymbol]
  · have htargetInt : (position : Int) ≠
        CounterLayout.boundaryPos (RegisterLayout.values current) label + 1 := by
      exact_mod_cast htarget
    have hsourceInt : (position : Int) ≠
        CounterLayout.boundaryPos (RegisterLayout.values current) label := by
      exact_mod_cast hsource
    simp [MarkerMachine.moveAt, MarkerShift.writeAt,
      MarkerTape.boundaryPosition, htarget, hsource,
      htargetInt, hsourceInt, coreSymbol]

/-- Leftward counterpart of `coreSymbol_of_moveAt_right`. -/
theorem coreSymbol_of_moveAt_left {numTags : Nat}
    (current next : Registers) (label : Fin 5)
    (hpositive : 0 < CounterLayout.boundaryPos
      (RegisterLayout.values current) label)
    (hmove : MarkerMachine.moveAt .left
        (MarkerTape.canonicalTape current)
        (MarkerTape.boundaryPosition current label) label =
      MarkerTape.canonicalTape next)
    (position : Nat) :
    coreSymbol (numTags := numTags) next position =
      if position + 1 = CounterLayout.boundaryPos
          (RegisterLayout.values current) label then
        boundarySymbol label
      else if position = CounterLayout.boundaryPos
          (RegisterLayout.values current) label then
        blankSymbol
      else coreSymbol current position := by
  have hp := congrFun hmove (position : Int)
  change baseSymbol (MarkerMachine.encodeSymbol
      (MarkerTape.canonicalTape next position)) = _
  rw [← hp]
  by_cases htarget : position + 1 = CounterLayout.boundaryPos
      (RegisterLayout.values current) label
  · have htargetInt : (position : Int) =
        CounterLayout.boundaryPos (RegisterLayout.values current) label - 1 := by
      have hcast : (position : Int) + 1 =
          CounterLayout.boundaryPos (RegisterLayout.values current) label := by
        exact_mod_cast htarget
      omega
    have hdelta : (CounterLayout.boundaryPos
          (RegisterLayout.values current) label : Int) - 1 =
        CounterLayout.boundaryPos (RegisterLayout.values current) label +
          (-1 : Int) := by omega
    simp [MarkerMachine.moveAt, MarkerShift.writeAt,
      MarkerTape.boundaryPosition, htarget, htargetInt, hdelta,
      boundarySymbol]
  by_cases hsource : position = CounterLayout.boundaryPos
      (RegisterLayout.values current) label
  · subst position
    have hne : (CounterLayout.boundaryPos
        (RegisterLayout.values current) label : Int) ≠
          CounterLayout.boundaryPos (RegisterLayout.values current) label - 1 := by
      omega
    simp [MarkerMachine.moveAt, MarkerShift.writeAt,
      MarkerTape.boundaryPosition, htarget, hne, blankSymbol]
  · have htargetInt : (position : Int) ≠
        CounterLayout.boundaryPos (RegisterLayout.values current) label - 1 := by
      intro heq
      apply htarget
      have hcast : (position : Int) + 1 =
          CounterLayout.boundaryPos (RegisterLayout.values current) label := by
        omega
      exact_mod_cast hcast
    have hsourceInt : (position : Int) ≠
        CounterLayout.boundaryPos (RegisterLayout.values current) label := by
      exact_mod_cast hsource
    have htargetInt' : (position : Int) ≠
        CounterLayout.boundaryPos (RegisterLayout.values current) label +
          (-1 : Int) := by
      intro heq
      apply htargetInt
      omega
    simp [MarkerMachine.moveAt, MarkerShift.writeAt,
      MarkerTape.boundaryPosition, htarget, hsource,
      htargetInt, htargetInt', hsourceInt, coreSymbol]

/-! ## Representation-preserving primitive shifts -/

/-- Moving one canonical boundary right preserves a finite frame.  The
arithmetic hypotheses isolate the two cases used by increment schedules:
an internal redistribution with unchanged far end, or the first shift which
extends the far end by exactly one cell. -/
theorem moveRight_represents {numTags : Nat}
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T) (next : Registers) (label : Fin 5)
    (hnextCore : layoutEnd next < spec.outerDistance)
    (hlower : layoutEnd spec.registers ≤ layoutEnd next)
    (hupper : layoutEnd next ≤ layoutEnd spec.registers + 1)
    (hsource : boundaryOffset spec.registers label ≤
      layoutEnd spec.registers)
    (htarget : boundaryOffset spec.registers label + 1 ≤ layoutEnd next)
    (hextend : layoutEnd spec.registers < layoutEnd next →
      boundaryOffset spec.registers label + 1 = layoutEnd next)
    (hmove : MarkerMachine.moveAt .right
        (MarkerTape.canonicalTape spec.registers)
        (MarkerTape.boundaryPosition spec.registers label) label =
      MarkerTape.canonicalTape next) :
    Represents (updateSpec spec next hnextCore)
      (writeLogical spec.growth
        (writeLogical spec.growth T
          (boundaryOffset spec.registers label) blankSymbol)
        (boundaryOffset spec.registers label + 1) (boundarySymbol label)) := by
  let source := boundaryOffset spec.registers label
  let U := writeLogical spec.growth
    (writeLogical spec.growth T source blankSymbol)
    (source + 1) (boundarySymbol label)
  have hsourcePositive : 0 < source := by
    simp [source, boundaryOffset]
  have htargetCore : source + 1 ≤ layoutEnd next := htarget
  have hsourceCore : source ≤ layoutEnd next :=
    hsource.trans hlower
  have hU (position : Int) :
      logicalTape spec.growth U position =
        if position = source + 1 then boundarySymbol label
        else if position = source then blankSymbol
        else logicalTape spec.growth T position := by
    simpa only [U, logicalTape_writeLogical_apply, Nat.cast_add, Nat.cast_one]
  constructor
  · change logicalTape spec.growth U 0 = tagSymbol spec.returnTag
    rw [hU]
    have hsourceNe : (0 : Int) ≠ (source : Int) := by
      intro heq
      have : source = 0 := by exact_mod_cast heq.symm
      omega
    have htargetNe : (0 : Int) ≠ (source : Int) + 1 := by omega
    simp only [hsourceNe, htargetNe, ↓reduceIte]
    simpa [logicalTape_apply] using h.tag
  · intro position hposition
    change position ≤ RegisterLayout.clockBoundary next at hposition
    change logicalTape spec.growth U (position + 1) = coreSymbol next position
    rw [hU, coreSymbol_of_moveAt_right spec.registers next label hmove]
    have hsourcePosition :
        (position : Int) + 1 = (source : Nat) ↔
          position = CounterLayout.boundaryPos
            (RegisterLayout.values spec.registers) label := by
      simp only [source, boundaryOffset]
      constructor <;> intro heq <;> exact_mod_cast (by omega : _)
    have htargetPosition :
        (position : Int) + 1 = (source : Int) + 1 ↔
          position = CounterLayout.boundaryPos
            (RegisterLayout.values spec.registers) label + 1 := by
      simp only [source, boundaryOffset]
      constructor <;> intro heq <;> exact_mod_cast (by omega : _)
    simp only [htargetPosition, hsourcePosition]
    by_cases htargetMarker : position = CounterLayout.boundaryPos
        (RegisterLayout.values spec.registers) label + 1
    · simp [htargetMarker]
    by_cases hsourceMarker : position = CounterLayout.boundaryPos
        (RegisterLayout.values spec.registers) label
    · simp [hsourceMarker, htargetMarker]
    · simp only [htargetMarker, hsourceMarker, ↓reduceIte]
      apply h.core position
      by_contra hold
      have hpast : RegisterLayout.clockBoundary spec.registers < position :=
        Nat.lt_of_not_ge hold
      have hstrictEnds : layoutEnd spec.registers < layoutEnd next := by
        simp only [layoutEnd] at hposition hpast ⊢
        omega
      have hnextEnd : layoutEnd next = layoutEnd spec.registers + 1 := by
        omega
      have hpositionEnd : position + 1 = layoutEnd next := by
        simp only [layoutEnd] at hposition hpast hnextEnd ⊢
        omega
      have hsourceEnd := hextend hstrictEnds
      apply htargetMarker
      simp only [boundaryOffset] at hsourceEnd
      omega
  · intro position hpast hbefore
    change layoutEnd next < position at hpast
    change position < spec.outerDistance at hbefore
    change logicalTape spec.growth U position = blankSymbol
    rw [hU]
    have hneTarget : (position : Int) ≠ (source : Int) + 1 := by
      intro heq
      have heqNat : position = source + 1 := by exact_mod_cast heq
      omega
    have hneSource : (position : Int) ≠ (source : Nat) := by
      intro heq
      have : position = source := by exact_mod_cast heq
      omega
    simp only [hneTarget, hneSource, ↓reduceIte]
    exact h.runway position (lt_of_le_of_lt hlower hpast) hbefore
  · change spec.outerTarget.Matches
      (logicalTape spec.growth U spec.outerDistance)
    rw [hU]
    have htargetNe : (spec.outerDistance : Int) ≠ (source : Int) + 1 := by
      intro heq
      have heqNat : spec.outerDistance = source + 1 := by exact_mod_cast heq
      omega
    have hsourceNe : (spec.outerDistance : Int) ≠ (source : Nat) := by
      intro heq
      have : spec.outerDistance = source := by exact_mod_cast heq
      omega
    simp only [htargetNe, hsourceNe, ↓reduceIte]
    exact h.target

/-- A represented rightward rewrite is exactly the extensional canonical
installation over the pre-rewrite tape. -/
theorem moveRight_eq_install {numTags : Nat}
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (next : Registers) (label : Fin 5)
    (hnextCore : layoutEnd next < spec.outerDistance)
    (hsourcePositive : 0 < boundaryOffset spec.registers label)
    (hsourceCore : boundaryOffset spec.registers label ≤ layoutEnd next)
    (htargetCore : boundaryOffset spec.registers label + 1 ≤ layoutEnd next)
    (hrep : Represents (updateSpec spec next hnextCore)
      (writeLogical spec.growth
        (writeLogical spec.growth T
          (boundaryOffset spec.registers label) blankSymbol)
        (boundaryOffset spec.registers label + 1) (boundarySymbol label))) :
    writeLogical spec.growth
        (writeLogical spec.growth T
          (boundaryOffset spec.registers label) blankSymbol)
        (boundaryOffset spec.registers label + 1) (boundarySymbol label) =
      install next spec.growth spec.returnTag T := by
  let source := boundaryOffset spec.registers label
  let U := writeLogical spec.growth
    (writeLogical spec.growth T source blankSymbol)
    (source + 1) (boundarySymbol label)
  have houtside : ∀ position : Int,
      ¬(1 ≤ position ∧ position ≤ layoutEnd next) →
        logicalTape spec.growth T position =
          logicalTape spec.growth U position := by
    intro position houtside
    simp only [U, logicalTape_writeLogical_apply, Nat.cast_add, Nat.cast_one]
    have hsourceNe : position ≠ (source : Int) := by
      intro heq
      apply houtside
      rw [heq]
      constructor
      · exact_mod_cast hsourcePositive
      · exact_mod_cast hsourceCore
    have htargetNe : position ≠ (source : Int) + 1 := by
      intro heq
      apply houtside
      rw [heq]
      constructor
      · omega
      · exact_mod_cast htargetCore
    simp [hsourceNe, htargetNe]
  have hinstall := install_congr_of_outside next spec.growth spec.returnTag
    T U houtside
  have hself : install next spec.growth spec.returnTag U = U := by
    simpa [U, updateSpec] using install_eq_self_of_represents hrep
  change U = install next spec.growth spec.returnTag T
  exact hself.symm.trans hinstall.symm

/-- Leftward boundary motion preserves a frame while allowing the final
boundary-`4` shift to shorten the far end by one cell. -/
theorem moveLeft_represents {numTags : Nat}
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T) (next : Registers) (label : Fin 5)
    (hnextCore : layoutEnd next < spec.outerDistance)
    (hlower : layoutEnd next ≤ layoutEnd spec.registers)
    (hupper : layoutEnd spec.registers ≤ layoutEnd next + 1)
    (hsourcePositive : 1 < boundaryOffset spec.registers label)
    (hsource : boundaryOffset spec.registers label ≤
      layoutEnd spec.registers)
    (hdestination : boundaryOffset spec.registers label - 1 ≤ layoutEnd next)
    (hshrink : layoutEnd next < layoutEnd spec.registers →
      boundaryOffset spec.registers label = layoutEnd spec.registers)
    (hmove : MarkerMachine.moveAt .left
        (MarkerTape.canonicalTape spec.registers)
        (MarkerTape.boundaryPosition spec.registers label) label =
      MarkerTape.canonicalTape next) :
    Represents (updateSpec spec next hnextCore)
      (writeLogical spec.growth
        (writeLogical spec.growth T
          (boundaryOffset spec.registers label) blankSymbol)
        (boundaryOffset spec.registers label - 1) (boundarySymbol label)) := by
  let source := boundaryOffset spec.registers label
  let destination := source - 1
  let U := writeLogical spec.growth
    (writeLogical spec.growth T source blankSymbol)
    destination (boundarySymbol label)
  have hdestinationPositive : 0 < destination := by
    simp only [destination]
    omega
  have hsourceBound : source ≤ layoutEnd spec.registers := hsource
  have hmarkerPositive : 0 < CounterLayout.boundaryPos
      (RegisterLayout.values spec.registers) label := by
    simp only [source, boundaryOffset] at hsourcePositive
    omega
  have hU (position : Int) :
      logicalTape spec.growth U position =
        if position = destination then boundarySymbol label
        else if position = source then blankSymbol
        else logicalTape spec.growth T position := by
    simpa only [U, logicalTape_writeLogical_apply]
  constructor
  · change logicalTape spec.growth U 0 = tagSymbol spec.returnTag
    rw [hU]
    have hdestinationNe : (0 : Int) ≠ (destination : Int) := by
      intro heq
      have : destination = 0 := by exact_mod_cast heq.symm
      omega
    have hsourceNe : (0 : Int) ≠ (source : Int) := by omega
    simp only [hdestinationNe, hsourceNe, ↓reduceIte]
    simpa [logicalTape_apply] using h.tag
  · intro position hposition
    change position ≤ RegisterLayout.clockBoundary next at hposition
    change logicalTape spec.growth U (position + 1) = coreSymbol next position
    rw [hU, coreSymbol_of_moveAt_left spec.registers next label
      hmarkerPositive hmove]
    have hsourcePosition :
        (position : Int) + 1 = (source : Int) ↔
          position = CounterLayout.boundaryPos
            (RegisterLayout.values spec.registers) label := by
      simp only [source, boundaryOffset]
      constructor <;> intro heq <;> exact_mod_cast (by omega : _)
    have hdestinationPosition :
        (position : Int) + 1 = (destination : Int) ↔
          position + 1 = CounterLayout.boundaryPos
            (RegisterLayout.values spec.registers) label := by
      simp only [destination, source, boundaryOffset]
      have hboundaryPositive : 0 < CounterLayout.boundaryPos
          (RegisterLayout.values spec.registers) label := hmarkerPositive
      constructor
      · intro heq
        have hcast : (position : Int) + 1 =
            CounterLayout.boundaryPos
              (RegisterLayout.values spec.registers) label := by
          push_cast at heq
          omega
        exact_mod_cast hcast
      · intro heq
        have hcast : (position : Int) + 1 =
            CounterLayout.boundaryPos
              (RegisterLayout.values spec.registers) label := by
          exact_mod_cast heq
        push_cast
        omega
    simp only [hdestinationPosition, hsourcePosition]
    by_cases hdestinationMarker : position + 1 =
        CounterLayout.boundaryPos (RegisterLayout.values spec.registers) label
    · simp [hdestinationMarker]
    by_cases hsourceMarker : position =
        CounterLayout.boundaryPos (RegisterLayout.values spec.registers) label
    · simp [hsourceMarker, hdestinationMarker]
    · simp only [hdestinationMarker, hsourceMarker, ↓reduceIte]
      apply h.core position
      simp only [layoutEnd] at hlower hposition
      omega
  · intro position hpast hbefore
    change layoutEnd next < position at hpast
    change position < spec.outerDistance at hbefore
    change logicalTape spec.growth U position = blankSymbol
    rw [hU]
    by_cases hsourcePosition : position = source
    · have hsourceInt : (position : Int) = (source : Int) := by
        exact_mod_cast hsourcePosition
      have hdestinationInt : (position : Int) ≠ (destination : Int) := by
        intro heq
        have : source = destination := by exact_mod_cast hsourceInt.symm.trans heq
        omega
      have hsourceDestination : source ≠ destination := by
        simp only [destination]
        omega
      simp [hsourceInt, hdestinationInt, hsourceDestination]
    · have hdestinationNe : (position : Int) ≠ (destination : Int) := by
        intro heq
        have heqNat : position = destination := by exact_mod_cast heq
        omega
      have hsourceNe : (position : Int) ≠ (source : Int) := by
        exact_mod_cast hsourcePosition
      simp only [hdestinationNe, hsourceNe, ↓reduceIte]
      apply h.runway position
      · by_contra hold
        have hpositionLe : position ≤ layoutEnd spec.registers :=
          Nat.le_of_not_gt hold
        have hstrict : layoutEnd next < layoutEnd spec.registers := by omega
        have hsourceEnd := hshrink hstrict
        apply hsourcePosition
        omega
      · exact hbefore
  · change spec.outerTarget.Matches
      (logicalTape spec.growth U spec.outerDistance)
    rw [hU]
    have hdestinationNe : (spec.outerDistance : Int) ≠
        (destination : Int) := by
      intro heq
      have heqNat : spec.outerDistance = destination := by exact_mod_cast heq
      have hdestinationLt : destination < source := by
        simp only [destination]
        omega
      have hlt : destination < spec.outerDistance :=
        (hdestinationLt.trans_le hsourceBound).trans spec.core_before_target
      exact hlt.ne heqNat.symm
    have hsourceNe : (spec.outerDistance : Int) ≠ (source : Int) := by
      intro heq
      have heqNat : spec.outerDistance = source := by exact_mod_cast heq
      have hlt : source < spec.outerDistance :=
        hsourceBound.trans_lt spec.core_before_target
      exact hlt.ne heqNat.symm
    simp only [hdestinationNe, hsourceNe, ↓reduceIte]
    exact h.target

/-- A represented leftward rewrite is exactly an installation over the tape
with its old source cell cleared.  This formulation covers both internal
decrement shifts and the final boundary-`4` shift which exposes the cleared
source as the first runway blank. -/
theorem moveLeft_eq_install_cleared {numTags : Nat}
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (next : Registers) (label : Fin 5)
    (hnextCore : layoutEnd next < spec.outerDistance)
    (hdestinationPositive : 0 < boundaryOffset spec.registers label - 1)
    (hdestinationCore : boundaryOffset spec.registers label - 1 ≤
      layoutEnd next)
    (hrep : Represents (updateSpec spec next hnextCore)
      (writeLogical spec.growth
        (writeLogical spec.growth T
          (boundaryOffset spec.registers label) blankSymbol)
        (boundaryOffset spec.registers label - 1) (boundarySymbol label))) :
    writeLogical spec.growth
        (writeLogical spec.growth T
          (boundaryOffset spec.registers label) blankSymbol)
        (boundaryOffset spec.registers label - 1) (boundarySymbol label) =
      install next spec.growth spec.returnTag
        (writeLogical spec.growth T
          (boundaryOffset spec.registers label) blankSymbol) := by
  let source := boundaryOffset spec.registers label
  let destination := source - 1
  let cleared := writeLogical spec.growth T source blankSymbol
  let U := writeLogical spec.growth cleared destination (boundarySymbol label)
  have houtside : ∀ position : Int,
      ¬(1 ≤ position ∧ position ≤ layoutEnd next) →
        logicalTape spec.growth cleared position =
          logicalTape spec.growth U position := by
    intro position houtside
    simp only [U, logicalTape_writeLogical_apply]
    have hdestinationNe : position ≠ (destination : Int) := by
      intro heq
      apply houtside
      rw [heq]
      constructor
      · exact_mod_cast hdestinationPositive
      · exact_mod_cast hdestinationCore
    simp [hdestinationNe]
  have hinstall := install_congr_of_outside next spec.growth spec.returnTag
    cleared U houtside
  have hself : install next spec.growth spec.returnTag U = U := by
    simpa [U, cleared, destination, source, updateSpec] using
      install_eq_self_of_represents hrep
  change U = install next spec.growth spec.returnTag cleared
  exact hself.symm.trans hinstall.symm

/-- When the cleared source remains inside the updated core, the backing-tape
clear is hidden by installation and may be dropped. -/
theorem install_clear_inside {numTags : Nat} (registers : Registers)
    (growth : Turing.Dir) (tag : Fin numTags)
    (T : FullTM0.Tape (Symbol numTags)) (source : Nat)
    (hpositive : 0 < source) (hcore : source ≤ layoutEnd registers) :
    install registers growth tag
        (writeLogical growth T source blankSymbol) =
      install registers growth tag T := by
  apply install_congr_of_outside
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

/-! ## Compiled schedule endpoints -/

theorem lastGapOffset_eq_boundaryOffset_add_value
    (registers : Registers) (i : Fin 4) :
    lastGapOffset registers i =
      boundaryOffset registers i.castSucc +
        RegisterLayout.values registers i := by
  simp only [lastGapOffset, boundaryOffset, Fin.val_castSucc]
  rw [CounterLayout.boundaryPos_succ]
  omega

/-- One internal rightward suffix shift, after boundary `4` has already
moved, executes from the last cell of its positive gap and lands on the exact
next canonical installation. -/
theorem machine_reaches_incrementInternal
    (base : Nat) (c : Nat.Partrec.Code) (counterState searchSlot : Nat)
    (success : ControlRef) (collision : Option ControlRef)
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T) (next : Registers) (i : Fin 4)
    (hpositive : 0 < RegisterLayout.values spec.registers i)
    (hnextCore : layoutEnd next < spec.outerDistance)
    (hsameEnd : layoutEnd next = layoutEnd spec.registers)
    (hmove : MarkerMachine.moveAt .right
        (MarkerTape.canonicalTape spec.registers)
        (MarkerTape.boundaryPosition spec.registers i.castSucc) i.castSucc =
      MarkerTape.canonicalTape next)
    (hnear : RegisterLayout.values spec.registers i ≤
      NestingMachine.bound (CanonicalInitializer.radius c))
    (hraw : RawCommand.markerShift
      ⟨spec.growth, counterState, searchSlot⟩ i.castSucc .left .right
      success (some .left) collision ∈ rawCommands) :
    FullTM0.Reaches (BoundedMarkerProgram.machine base
        (CanonicalInitializer.radius c) (commands base c) (coreTable base c))
      ⟨entryState (CanonicalInitializer.radius c)
          (searchState base c ⟨spec.growth, counterState, searchSlot⟩),
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
  have hrun := machine_reaches_incrementShift_near base c spec.growth
    counterState searchSlot source i.castSucc success collision hraw T distance
    (by simpa [hstart] using hgap) hnear hblank
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

/-- Generic canonical leftward suffix shift used by every positive-decrement
schedule.  The endpoint keeps the old source cell under the head and exposes
the exact cleared backing tape needed by the final boundary-`4` shift. -/
theorem machine_reaches_decrementCanonical
    (base : Nat) (c : Nat.Partrec.Code) (counterState searchSlot : Nat)
    (success : ControlRef) (collision : Option ControlRef)
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T) (next : Registers) (label : Fin 5)
    (origin distance : Nat)
    (hsourcePositive : 1 < boundaryOffset spec.registers label)
    (horigin : origin + distance = boundaryOffset spec.registers label)
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary label).Matches (atLogical spec.growth T origin)
      (OrientedMarkerTape.orientDirection spec.growth .right) distance)
    (hblank : logicalTape spec.growth T
      ((boundaryOffset spec.registers label - 1 : Nat) : Int) = blankSymbol)
    (hnear : distance ≤
      NestingMachine.bound (CanonicalInitializer.radius c))
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
    FullTM0.Reaches (BoundedMarkerProgram.machine base
        (CanonicalInitializer.radius c) (commands base c) (coreTable base c))
      ⟨entryState (CanonicalInitializer.radius c)
          (searchState base c ⟨spec.growth, counterState, searchSlot⟩),
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
  have hrun := machine_reaches_decrementShift_near base c spec.growth
    counterState searchSlot origin destination distance label success collision
    hraw T hposition hgap hnear (by simpa [source, destination] using hblank)
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

/-- The singleton clock-increment schedule executes in either physical
orientation and lands on the exact extensional frame update.  This is also
the first step shared by every longer increment schedule. -/
theorem machine_reaches_incrementClock
    (base : Nat) (c : Nat.Partrec.Code) (counterState : Nat)
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T)
    (hroom : layoutEnd (spec.registers.increment .clock) <
      spec.outerDistance)
    (hraw : RawCommand.markerShift
      ⟨spec.growth, counterState, bodySearchBase⟩ 4 .left .right
      (directRef spec.growth counterState bodyDirectBase) (some .left)
      (some (directRef spec.growth counterState testDirectSlot)) ∈
        rawCommands) :
    FullTM0.Reaches (BoundedMarkerProgram.machine base
        (CanonicalInitializer.radius c) (commands base c) (coreTable base c))
      ⟨entryState (CanonicalInitializer.radius c)
          (searchState base c
            ⟨spec.growth, counterState, bodySearchBase⟩),
        atLogical spec.growth T (layoutEnd spec.registers)⟩
      ⟨resolve base c (directRef spec.growth counterState bodyDirectBase),
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
  have hrun := machine_reaches_incrementShift_near base c spec.growth
    counterState bodySearchBase (layoutEnd spec.registers) 4
    (directRef spec.growth counterState bodyDirectBase)
    (some (directRef spec.growth counterState testDirectSlot)) hraw T 0
    hgap (by simp) hblank
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

/-- The singleton positive clock-decrement schedule lands exactly on
`decrementTape`; its cleared old boundary is the first cell of the enlarged
runway and remains under the head for the finish rule. -/
theorem machine_reaches_decrementClock
    (base : Nat) (c : Nat.Partrec.Code) (counterState : Nat)
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T)
    (hpositive : 0 < spec.registers.get .clock)
    (hraw : RawCommand.markerShift
      ⟨spec.growth, counterState, secondarySearchBase⟩ 4 .right .left
      (directRef spec.growth counterState finishDirectSlot) (some .right)
      none ∈ rawCommands) :
    FullTM0.Reaches (BoundedMarkerProgram.machine base
        (CanonicalInitializer.radius c) (commands base c) (coreTable base c))
      ⟨entryState (CanonicalInitializer.radius c)
          (searchState base c
            ⟨spec.growth, counterState, secondarySearchBase⟩),
        atLogical spec.growth T (layoutEnd spec.registers)⟩
      ⟨resolve base c (directRef spec.growth counterState finishDirectSlot),
        atLogical spec.growth (decrementTape spec .clock T)
          (layoutEnd spec.registers)⟩ := by
  let next := spec.registers.decrement .clock
  have hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary 4).Matches
      (atLogical spec.growth T (layoutEnd spec.registers))
      (OrientedMarkerTape.orientDirection spec.growth .right) 0 := by
    rw [SearchGap.zero]
    change (atLogical spec.growth T (layoutEnd spec.registers)).read =
      boundarySymbol 4
    exact h.read_boundary_four
  have hsourcePositive : 1 < boundaryOffset spec.registers 4 := by
    simp only [boundaryOffset_four]
    simp [layoutEnd, RegisterLayout.clockBoundary_eq]
  have hblank : logicalTape spec.growth T
      ((boundaryOffset spec.registers 4 - 1 : Nat) : Int) = blankSymbol := by
    have hgapBlank := h.gap_blank (3 : Fin 4)
      (RegisterLayout.values spec.registers 3 - 1) (by
        simpa [RegisterLayout.values, Registers.get] using hpositive)
    have hcoord : boundaryOffset spec.registers 4 - 1 =
        firstGapOffset spec.registers 3 +
          (RegisterLayout.values spec.registers 3 - 1) := by
      have hclock : 0 < spec.registers.clock := by
        simpa [Registers.get] using hpositive
      simp only [boundaryOffset_four, layoutEnd,
        RegisterLayout.clockBoundary_eq, firstGapOffset,
        CounterLayout.boundaryPos, RegisterLayout.values_zero,
        RegisterLayout.values_one, RegisterLayout.values_two,
        RegisterLayout.values_three]
      omega
    rw [show ((boundaryOffset spec.registers 4 - 1 : Nat) : Int) =
        ((firstGapOffset spec.registers 3 +
          (RegisterLayout.values spec.registers 3 - 1) : Nat) : Int) by
      exact_mod_cast hcoord]
    simpa only [Nat.cast_add] using hgapBlank
  have hnextCore : layoutEnd next < spec.outerDistance := by
    exact (layoutEnd_decrement_lt spec.registers .clock hpositive).trans
      spec.core_before_target
  have hend : layoutEnd next + 1 = layoutEnd spec.registers := by
    exact layoutEnd_decrement_add_one spec.registers .clock hpositive
  have hmove : MarkerMachine.moveAt .left
      (MarkerTape.canonicalTape spec.registers)
      (MarkerTape.boundaryPosition spec.registers 4) 4 =
      MarkerTape.canonicalTape next := by
    have hm := MarkerSchedule.moveClockBoundary_after_increment next
    have hinverse := MarkerSchedule.increment_decrement_registers
      spec.registers .clock hpositive
    rw [hinverse] at hm
    exact hm
  have hrun := machine_reaches_decrementCanonical base c counterState
    secondarySearchBase
    (directRef spec.growth counterState finishDirectSlot) none h next 4
    (layoutEnd spec.registers) 0 hsourcePositive (by simp)
    hgap hblank (by simp) hnextCore (by omega) (by omega)
    (by simp) (by simp only [boundaryOffset_four]; omega)
    (by intro _; simp) hmove hraw
  simpa [next, decrementTape, clearOldLayoutEnd] using hrun

end

end CounterControlScheduleSemantics
end Hooper
end Kari
end LeanWang
