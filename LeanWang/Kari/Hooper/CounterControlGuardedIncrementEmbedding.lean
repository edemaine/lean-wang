/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlGuardedShiftEmbedding

/-!
# Embedding guarded increment shifts

The increment shift moves consecutive boundaries from right to left, while
each boundary itself moves one cell to the right.  This file reverses a
completed shift suffix from its canonically anchored last boundary.  The
result identifies the exact canonical coordinate of the first moved
boundary and retains the generic backward geometry used to transport the
original guarded blank prefix.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlGuardedIncrementEmbedding

open Turing CounterMachine
open BoundedMarkerProgram FramedMarkerTape
open CounterControlPlan CounterControlBridge
open CounterControlCoreFrame CounterControlPrefixInstructionResolution
open CounterControlGlobalUnnesting CounterControlGuardedSearch
open CounterControlGuardedSearch.GuardedSearch
open CounterControlParentContinuation CounterControlParentEmbedding
open CounterControlResumedShiftCoordinates
open CounterControlGuardedShiftCompletion
open CounterControlGuardedShiftEmbedding
open CounterControlGuardedParentContinuation
open CounterControlLogicalLimitContinuation

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-! ## Consecutive descending schedules -/

/-- A suffix of an increment schedule consists of consecutive decreasing
boundary labels and ends at a specified final label. -/
inductive DescendingTo : Fin 5 → List (Fin 5) → Fin 5 → Prop where
  | done (label : Fin 5) : DescendingTo label [] label
  | step (i : Fin 4) {remaining : List (Fin 5)} {last : Fin 5}
      (tail : DescendingTo i.castSucc remaining last) :
      DescendingTo i.succ (i.castSucc :: remaining) last

/-- Every selected position in a descending schedule retains a descending
suffix to the same final label. -/
theorem DescendingTo.position
    {first last current : Fin 5} {following before remaining : List (Fin 5)}
    (schedule : DescendingTo first following last)
    (hposition : first :: following = before ++ current :: remaining) :
    DescendingTo current remaining last := by
  induction schedule generalizing before current remaining with
  | done label =>
      cases before with
      | nil =>
          simp only [List.nil_append, List.cons.injEq] at hposition
          rcases hposition with ⟨rfl, rfl⟩
          exact .done label
      | cons first before =>
          simp at hposition
  | step i tail ih =>
      cases before with
      | nil =>
          simp only [List.nil_append, List.cons.injEq] at hposition
          rcases hposition with ⟨rfl, rfl⟩
          exact .step i tail
      | cons first before =>
          simp only [List.cons_append, List.cons.injEq] at hposition
          exact ih hposition.2

/-- The retained position of every increment shift is a consecutive
descending suffix ending at the recovery-source boundary. -/
theorem incrementShiftPosition_descendingTo
    {growth : Turing.Dir} {source : Nat} {register : Register}
    {raw : RawCommand}
    (position : IncrementShiftPosition growth source bodySearchBase true
      (MarkerShift.incrementOrder register) raw) :
    DescendingTo position.current position.remaining
      (MarkerSchedule.decrementStartBoundary register) := by
  cases register with
  | left =>
      apply (DescendingTo.step 3
        (.step 2 (.step 1 (.done 1)))).position
      simpa [MarkerShift.incrementOrder] using position.labels_eq
  | right =>
      apply (DescendingTo.step 3 (.step 2 (.done 2))).position
      simpa [MarkerShift.incrementOrder] using position.labels_eq
  | temp =>
      apply (DescendingTo.step 3 (.done 3)).position
      simpa [MarkerShift.incrementOrder] using position.labels_eq
  | clock =>
      apply (DescendingTo.done 4).position
      simpa [MarkerShift.incrementOrder] using position.labels_eq

/-! ## Reversing one shifted gap -/

/-- Viewed from the newly shifted boundary, the old gap reverses into the
blank gap leading to the previously shifted boundary. -/
theorem shiftStepTape_reverseGap
    (direction : Turing.Dir)
    (outer : FullTM0.Tape (Symbol numTags)) (distance : Nat)
    (expected source : Fin 5)
    (gap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary expected).Matches outer direction distance)
    (positive : 0 < distance)
    (hsource : (outer.move
      (NestingMachine.opposite direction)).read = boundarySymbol source) :
    SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary source).Matches
      ((shiftStepTape direction outer distance expected).move
        (NestingMachine.opposite direction) |>.move
          (NestingMachine.opposite direction))
      (NestingMachine.opposite direction) (distance - 1) := by
  constructor
  · intro k hk
    have hbetween := shiftStepTape_between direction outer distance (k + 1)
      expected gap (by omega) (by omega)
    cases direction <;>
      simp [NestingMachine.opposite, FullTM0.Tape.read,
        FullTM0.Tape.move, FullTM0.Tape.moveN, FullTM0.Tape.offset]
        at hbetween ⊢ <;>
      rw [← hbetween] <;> congr 1 <;> ring
  · have hbehind := shiftStepTape_behind direction outer distance 0
      expected positive
    have hsource' :
        (((outer.move (NestingMachine.opposite direction)).moveN
          (NestingMachine.opposite direction) 0).read) =
            boundarySymbol source := by
      simpa using hsource
    rw [hsource'] at hbehind
    have hdistance : distance - 1 + 1 = distance := by omega
    cases direction <;>
      simp [Target.Matches, NestingMachine.opposite, FullTM0.Tape.read,
        FullTM0.Tape.move, FullTM0.Tape.moveN, FullTM0.Tape.offset]
        at hbehind ⊢ <;>
      rw [← hbehind] <;> congr 1 <;> norm_num at hdistance ⊢ <;> omega

/-! ## Canonical backward geometry -/

/-- A completed descending shift suffix, anchored at its final canonical
boundary, retains both exact backward travel and agreement with the
canonical core on the ray beyond its first moved boundary. -/
structure CanonicalBackwardGeometry
    (growth : Turing.Dir) (current : Fin 5) (remaining : List (Fin 5))
    (start finish : FullTM0.Tape (Symbol numTags))
    (registers : Registers) (coreTape : FullTM0.Tape (Symbol numTags))
    (last : Fin 5) : Type where
  geometry : ShiftTailBackwardGeometry (orient growth .left) remaining
    start finish
  coordinate : boundaryOffset registers last + geometry.travel =
    boundaryOffset registers current
  ahead : ∀ back,
    (((start.move (orient growth .right)).moveN
      (orient growth .right) back).read) =
      logicalTape growth coreTape (boundaryOffset registers current + back)

/-- Reverse a consecutive increment-shift suffix from its canonical final
boundary to the canonical boundary shifted by its selected first command. -/
theorem descendingShift_canonicalBackwardGeometry
    {growth : Turing.Dir} {current last : Fin 5}
    {remaining : List (Fin 5)}
    {start finish coreTape : FullTM0.Tape (Symbol numTags)}
    {registers : Registers}
    (schedule : DescendingTo current remaining last)
    (trace : ShiftTailGaps (orient growth .left) remaining start finish)
    (hstartRead : (start.move (orient growth .right)).read =
      boundarySymbol current)
    (hcore : CoreRepresents registers growth coreTape)
    (hfinish : finish.move (orient growth .right) =
      atLogical growth coreTape (boundaryOffset registers last)) :
    Nonempty (CanonicalBackwardGeometry growth current remaining start finish
      registers coreTape last) := by
  induction schedule generalizing start finish with
  | done label =>
      cases trace with
      | nil =>
          let geometry : ShiftTailBackwardGeometry (orient growth .left) []
              start start := ⟨0, by simp, by
            intro forbidden hstart _ back hback
            have hbackZero : back = 0 := by omega
            subst back
            simpa using hstart⟩
          refine ⟨⟨geometry, by simp [geometry], ?_⟩⟩
          intro back
          rw [hfinish]
          simp only [orient_eq_orientDirection]
          rw [atLogical_moveN_right, atLogical_read]
          simp only [Nat.cast_add]
  | step i tail ih =>
      cases trace with
      | cons expected following outer distance gap positive finish trace =>
          let shifted := shiftStepTape (orient growth .left) start distance
            i.castSucc
          have hopposite : NestingMachine.opposite (orient growth .left) =
              orient growth .right := by
            cases growth <;> rfl
          have hshiftedRead :
              (shifted.move (orient growth .right)).read =
                boundarySymbol i.castSucc := by
            have hread := shiftStepTape_destination (orient growth .left)
              start distance i.castSucc
            rw [hopposite] at hread
            simpa [shifted] using hread
          rcases ih trace hshiftedRead hfinish with ⟨suffix⟩
          have hstartRead' :
              (start.move
                (NestingMachine.opposite (orient growth .left))).read =
                  boundarySymbol i.succ := by
            rw [hopposite]
            exact hstartRead
          have hreverse := shiftStepTape_reverseGap (orient growth .left)
            start distance i.castSucc i.succ gap positive hstartRead'
          have hcanonicalOnShifted : SearchGap
              (fun symbol => symbol = blankSymbol)
              (Target.boundary i.succ).Matches
              ((shifted.move (orient growth .right)).move
                (orient growth .right))
              (orient growth .right)
              (RegisterLayout.values registers i) := by
            constructor
            · intro k hk
              have hahead := suffix.ahead (k + 1)
              have hcoordinate : boundaryOffset registers i.castSucc +
                  (k + 1) = firstGapOffset registers i + k := by
                simp [boundaryOffset, firstGapOffset]
                omega
              have hcoordinateInt :
                  (boundaryOffset registers i.castSucc : Int) +
                    (k + 1) = firstGapOffset registers i + k := by
                exact_mod_cast hcoordinate
              change (((shifted.move (orient growth .right)).moveN
                (orient growth .right) (k + 1)).read) = _ at hahead
              have hahead' :
                  (((shifted.move (orient growth .right)).moveN
                    (orient growth .right) (k + 1)).read) =
                      logicalTape growth coreTape
                        (firstGapOffset registers i + k) := by
                calc
                  _ = logicalTape growth coreTape
                      ((boundaryOffset registers i.castSucc : Int) +
                        (k + 1)) := hahead
                  _ = logicalTape growth coreTape
                      (firstGapOffset registers i + k) := by
                        congr 1
              have hblankRead :
                  ((((shifted.move (orient growth .right)).move
                    (orient growth .right)).moveN
                      (orient growth .right) k).read) = blankSymbol := by
                calc
                  ((((shifted.move (orient growth .right)).move
                      (orient growth .right)).moveN
                        (orient growth .right) k).read) =
                      (((shifted.move (orient growth .right)).moveN
                        (orient growth .right) (k + 1)).read) := by
                          rw [FullTM0.Tape.move_moveN]
                  _ = logicalTape growth coreTape
                        (firstGapOffset registers i + k) := hahead'
                  _ = blankSymbol := hcore.gap_blank i k hk
              simpa only [FullTM0.Tape.read_moveN] using hblankRead
            · have hahead := suffix.ahead
                  (RegisterLayout.values registers i + 1)
              have hcoordinate : boundaryOffset registers i.castSucc +
                  (RegisterLayout.values registers i + 1) =
                    boundaryOffset registers i.succ := by
                simp [boundaryOffset, CounterLayout.boundaryPos_succ]
                omega
              have hcoordinateInt :
                  (boundaryOffset registers i.castSucc : Int) +
                    (RegisterLayout.values registers i + 1) =
                      boundaryOffset registers i.succ := by
                exact_mod_cast hcoordinate
              change (((shifted.move (orient growth .right)).moveN
                (orient growth .right)
                (RegisterLayout.values registers i + 1)).read) = _
                  at hahead
              have hahead' :
                  (((shifted.move (orient growth .right)).moveN
                    (orient growth .right)
                    (RegisterLayout.values registers i + 1)).read) =
                      logicalTape growth coreTape
                        (boundaryOffset registers i.succ) := by
                calc
                  _ = logicalTape growth coreTape
                      ((boundaryOffset registers i.castSucc : Int) +
                        (RegisterLayout.values registers i + 1)) := hahead
                  _ = logicalTape growth coreTape
                      (boundaryOffset registers i.succ) := by
                        congr 1
              rw [hcore.boundary i.succ] at hahead'
              have hmarkedRead :
                  ((((shifted.move (orient growth .right)).move
                    (orient growth .right)).moveN (orient growth .right)
                    (RegisterLayout.values registers i)).read) =
                      boundarySymbol i.succ := by
                calc
                  ((((shifted.move (orient growth .right)).move
                      (orient growth .right)).moveN
                        (orient growth .right)
                        (RegisterLayout.values registers i)).read) =
                      (((shifted.move (orient growth .right)).moveN
                        (orient growth .right)
                        (RegisterLayout.values registers i + 1)).read) := by
                          rw [FullTM0.Tape.move_moveN]
                  _ = boundarySymbol i.succ := hahead'
              simpa [Target.Matches, FullTM0.Tape.read_moveN] using
                hmarkedRead
          have hreverse' : SearchGap (fun symbol => symbol = blankSymbol)
              (Target.boundary i.succ).Matches
              ((shifted.move (orient growth .right)).move
                (orient growth .right))
              (orient growth .right) (distance - 1) := by
            rw [hopposite] at hreverse
            simpa [shifted] using hreverse
          have hdistanceSub : distance - 1 =
              RegisterLayout.values registers i :=
            BoundedMarkerProgram.boundaryGap_distance_unique hreverse' hcanonicalOnShifted
          have hdistance : distance =
              RegisterLayout.values registers i + 1 := by
            omega
          let geometry := suffix.geometry.prepend gap positive
          have hboundaryStep : boundaryOffset registers i.castSucc +
              distance = boundaryOffset registers i.succ := by
            rw [hdistance]
            simp [boundaryOffset, CounterLayout.boundaryPos_succ]
            omega
          refine ⟨⟨geometry, ?_, ?_⟩⟩
          · dsimp [geometry, ShiftTailBackwardGeometry.prepend]
            rw [← Nat.add_assoc, suffix.coordinate]
            exact hboundaryStep
          · intro back
            have hbehind := shiftStepTape_behind (orient growth .left)
              start distance back i.castSucc positive
            have hahead := suffix.ahead (distance + back)
            have hcoordinate : boundaryOffset registers i.castSucc +
                (distance + back) =
                  boundaryOffset registers i.succ + back := by
              omega
            have hcoordinateInt :
                (boundaryOffset registers i.castSucc : Int) +
                  (distance + back) =
                    boundaryOffset registers i.succ + back := by
              exact_mod_cast hcoordinate
            change (((shifted.move (orient growth .right)).moveN
              (orient growth .right) (distance + back)).read) = _ at hahead
            have hahead' :
                (((shifted.move (orient growth .right)).moveN
                  (orient growth .right) (distance + back)).read) =
                    logicalTape growth coreTape
                      (boundaryOffset registers i.succ + back) := by
              calc
                _ = logicalTape growth coreTape
                    ((boundaryOffset registers i.castSucc : Int) +
                      (distance + back)) := hahead
                _ = logicalTape growth coreTape
                    (boundaryOffset registers i.succ + back) := by
                      congr 1
            rw [hopposite] at hbehind
            exact hbehind.symm.trans hahead'

/-! ## Guarded increment continuation -/

/-- A nonempty increment-recovery route strictly escapes the original
guarded caller.  Reverse shift geometry locates the selected moved boundary
inside the reconstructed canonical core, after which the generic blank
transport bounds the old gap by the core's first obstruction. -/
theorem incrementRecovery_foundGuardedParentOutcome
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (current : GuardedSearch base c)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      (foundCfg current.current))
    (growth : Turing.Dir) (source : Nat) (register : Register) (next : Nat)
    (first : MarkerValidation.Leg) (rest : List MarkerValidation.Leg)
    (handoff : IncrementRecoverySearchHandoff current growth source register
      next first rest) :
    Nonempty (FoundGuardedParentOutcome current) := by
  rcases incrementRecoveryCenteredEnd base c hmortal current himmortal growth
      source register next first rest handoff with ⟨centered⟩
  have hdirection : current.direction = orient growth .left := by
    have hdirection := current.selectedRaw_direction_eq
    rw [CounterControlCommandAt.compileRawCommand_searchDirection]
      at hdirection
    rw [handoff.direct.suffix.position.raw_eq] at hdirection
    exact hdirection.symm
  have hopposite : NestingMachine.opposite (orient growth .left) =
      orient growth .right := by
    cases growth <;> rfl
  have hstartRead :
      ((current.shiftedParentBacking
        handoff.direct.suffix.position.current).move
          (orient growth .right)).read =
        boundarySymbol handoff.direct.suffix.position.current := by
    have hread := handoff.direct.suffix.handoff.destination_boundary
    rw [hdirection, hopposite] at hread
    exact hread
  have hfinish : handoff.direct.suffix.finish.move
      (orient growth .right) =
        atLogical growth centered.core.tape
          (boundaryOffset centered.core.registers
            (MarkerSchedule.decrementStartBoundary register)) := by
    simpa [incrementAfterShiftTape] using centered.shift_center
  have schedule := incrementShiftPosition_descendingTo
    handoff.direct.suffix.position
  rcases descendingShift_canonicalBackwardGeometry schedule
      handoff.direct.suffix.tailGaps hstartRead centered.core_represents
      hfinish with ⟨canonical⟩
  unfold GuardedSearch.shiftedParentBacking at canonical
  rw [hdirection] at canonical
  let geometry := canonical.geometry
  have hcoordinate :
      boundaryOffset centered.core.registers
          (MarkerSchedule.decrementStartBoundary register) +
          geometry.travel =
        boundaryOffset centered.core.registers
          handoff.direct.suffix.position.current := by
    exact canonical.coordinate
  have hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary handoff.direct.suffix.position.current).Matches
      current.parentOuter (orient growth .left)
      (current.current.distance + 1) := by
    have hgap := current.parentGap
    rw [← current.compileRawCommand_selectedRaw,
      CounterControlCommandAt.compileRawCommand_spec] at hgap
    rw [hdirection] at hgap
    simpa [handoff.direct.suffix.position.raw_eq,
      CounterControlCommandAt.compileRawAtTag, Command.target,
      Command.searchDirection] using hgap
  have hanchorPositive : 0 < boundaryOffset centered.core.registers
      (MarkerSchedule.decrementStartBoundary register) := by
    simp [boundaryOffset]
  have hanchor :
      boundaryOffset centered.core.registers
          (MarkerSchedule.decrementStartBoundary register) +
          geometry.travel ≤ layoutEnd centered.core.registers := by
    rw [hcoordinate]
    exact
      CounterControlInstructionSemantics.boundaryOffset_le_layoutEnd
        centered.core.registers handoff.direct.suffix.position.current
  have hcenter' : handoff.direct.suffix.finish.move
      (NestingMachine.opposite (orient growth .left)) =
        atLogical growth centered.core.tape
          (boundaryOffset centered.core.registers
            (MarkerSchedule.decrementStartBoundary register)) := by
    rw [hopposite]
    exact hfinish
  have hdistance : current.current.distance < centered.core.limit - 1 := by
    apply geometry.prefixLength_lt_limit_sub_one_of_anchor hgap
      centered.core.registers centered.core.limit centered.core.target
      centered.core.represented
      (boundaryOffset centered.core.registers
        (MarkerSchedule.decrementStartBoundary register))
    · exact hanchorPositive
    · exact hanchor
    · simpa [centered.core_growth] using hopposite
    · simpa [centered.core_growth] using hcenter'
    · omega
  exact foundGuardedParentOutcome_of_logicalLimit base c hmortal current
    centered.core centered.reaches hdistance himmortal

/-- Escape-sum wrapper for a nonempty increment-recovery route. -/
theorem incrementRecovery_foundGuardedEscapeOutcome
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (current : GuardedSearch base c)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      (foundCfg current.current))
    (growth : Turing.Dir) (source : Nat) (register : Register) (next : Nat)
    (first : MarkerValidation.Leg) (rest : List MarkerValidation.Leg)
    (handoff : IncrementRecoverySearchHandoff current growth source register
      next first rest) :
    Nonempty (FoundGuardedEscapeOutcome current) := by
  rcases incrementRecovery_foundGuardedParentOutcome base c hmortal current
      himmortal growth source register next first rest handoff with ⟨outcome⟩
  exact ⟨.parent outcome⟩

/-- Every guarded caller selected inside an increment-shift schedule reaches
a strict parent continuation: the clock schedule uses its empty direct route,
while all other completed schedules use the canonically reversed recovery
route. -/
theorem incrementShift_foundGuardedParentOutcome
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (current : GuardedSearch base c)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      (foundCfg current.current))
    (growth : Turing.Dir) (source : Nat) (register : Register) (next : Nat)
    (hrule : (source, .increment register next) ∈
      GlobalSourceProgram.program)
    (hcommand : current.selectedRaw ∈
      incrementShiftCommands growth source register) :
    Nonempty (FoundGuardedParentOutcome current) := by
  rcases current.incrementShift_suffix_of_immortal base c hmortal growth
      source register next hrule hcommand himmortal with ⟨suffix⟩
  rcases incrementDirectCompletion base c current growth source register
      next hrule suffix with ⟨completion⟩
  cases completion with
  | logical direct hroute =>
      exact incrementLogical_foundGuardedParentOutcome base c hmortal current
        himmortal growth source register next direct hroute
  | recovery first rest handoff =>
      exact incrementRecovery_foundGuardedParentOutcome base c hmortal
        current himmortal growth source register next first rest handoff

/-- Escape-sum wrapper for the guarded increment-shift continuation. -/
theorem incrementShift_foundGuardedEscapeOutcome
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (current : GuardedSearch base c)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      (foundCfg current.current))
    (growth : Turing.Dir) (source : Nat) (register : Register) (next : Nat)
    (hrule : (source, .increment register next) ∈
      GlobalSourceProgram.program)
    (hcommand : current.selectedRaw ∈
      incrementShiftCommands growth source register) :
    Nonempty (FoundGuardedEscapeOutcome current) := by
  rcases incrementShift_foundGuardedParentOutcome base c hmortal current
      himmortal growth source register next hrule hcommand with ⟨outcome⟩
  exact ⟨.parent outcome⟩

end

end CounterControlGuardedIncrementEmbedding
end Hooper
end Kari
end LeanWang
