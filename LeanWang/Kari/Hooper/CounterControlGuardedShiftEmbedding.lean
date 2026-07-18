/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlGuardedShiftCompletion
import LeanWang.Kari.Hooper.CounterControlGuardedParentContinuation
import LeanWang.Kari.Hooper.CounterControlResumedRouteEmbedding

/-!
# Embedding guarded marker-shift completions

Marker-shift schedules change the tape while traversing their boundary
suffix.  This file retains enough absolute geometry to compare the guarded
parent gap with the logical core reconstructed at the completed schedule.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlGuardedShiftEmbedding

open Turing CounterMachine
open BoundedMarkerProgram FramedMarkerTape
open CounterControlPlan CounterControlBridge
open CounterControlCoreFrame CounterControlPrefixInstructionResolution
open CounterControlGlobalUnnesting CounterControlGuardedSearch
open CounterControlGuardedSearch.GuardedSearch
open CounterControlGuardedParentContinuation
open CounterControlParentContinuation CounterControlParentEmbedding
open CounterControlResumedShiftCoordinates
open CounterControlGuardedShiftCompletion

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-! ## Pure geometry of a shifted suffix -/

/-- Cells weakly behind the boundary moved by one shift are inherited from
the tape weakly behind the previously moved boundary. -/
theorem shiftStepTape_behind
    (direction : Turing.Dir)
    (outer : FullTM0.Tape (Symbol numTags)) (distance back : Nat)
    (expected : Fin 5) (positive : 0 < distance) :
    ((((shiftStepTape direction outer distance expected).move
          (NestingMachine.opposite direction)).moveN
        (NestingMachine.opposite direction) (distance + back)).read) =
      (((outer.move (NestingMachine.opposite direction)).moveN
        (NestingMachine.opposite direction) back).read) := by
  cases direction <;>
    simp [shiftStepTape, NestingMachine.opposite,
      FullTM0.Tape.read, FullTM0.Tape.move,
      FullTM0.Tape.moveN, FullTM0.Tape.offset,
      FullTM0.Tape.write] <;>
    split_ifs <;> try omega
  all_goals
    apply congrArg outer
    ring

/-- The cells strictly between two consecutively moved boundaries remain
blank after the second boundary is shifted. -/
theorem shiftStepTape_between
    (direction : Turing.Dir)
    (outer : FullTM0.Tape (Symbol numTags)) (distance back : Nat)
    (expected : Fin 5)
    (gap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary expected).Matches outer direction distance)
    (hbackPositive : 0 < back) (hback : back < distance) :
    ((((shiftStepTape direction outer distance expected).move
          (NestingMachine.opposite direction)).moveN
        (NestingMachine.opposite direction) back).read) =
      blankSymbol := by
  let position := distance - (back + 1)
  have hsum : position + (back + 1) = distance := by
    dsimp [position]
    exact Nat.sub_add_cancel (by omega)
  have hposition : position < distance := by
    dsimp [position]
    omega
  have hblank := gap.blank hposition
  cases direction <;>
    simp [shiftStepTape, NestingMachine.opposite,
      FullTM0.Tape.read, FullTM0.Tape.move,
      FullTM0.Tape.moveN, FullTM0.Tape.offset,
      FullTM0.Tape.write] <;>
    split_ifs <;> try omega
  all_goals
    rw [← hblank]
    apply congrArg outer
    simp only [FullTM0.Tape.offset_left, FullTM0.Tape.offset_right]
    omega

/-- The shifted boundary is one cell behind the returned source head. -/
theorem shiftStepTape_destination
    (direction : Turing.Dir)
    (outer : FullTM0.Tape (Symbol numTags)) (distance : Nat)
    (expected : Fin 5) :
    ((shiftStepTape direction outer distance expected).move
      (NestingMachine.opposite direction)).read =
        boundarySymbol expected := by
  cases direction <;>
    simp [shiftStepTape, NestingMachine.opposite,
      FullTM0.Tape.read, FullTM0.Tape.move,
      FullTM0.Tape.write]

/-- Backward coordinate summary of a completed shift suffix.  `travel` is
the distance between the boundary moved before the suffix and the boundary
moved last.  The two fields state that cells behind the first boundary are
preserved, and that a boundary label absent from the schedule cannot occur
inside the traversed segment. -/
structure ShiftTailBackwardGeometry
    (direction : Turing.Dir) (labels : List (Fin 5))
    (start finish : FullTM0.Tape (Symbol numTags)) : Type where
  travel : Nat
  behind : ∀ back,
    ((((finish.move (NestingMachine.opposite direction)).moveN
          (NestingMachine.opposite direction) (travel + back)).read) =
      (((start.move (NestingMachine.opposite direction)).moveN
          (NestingMachine.opposite direction) back).read))
  avoids : ∀ forbidden : Fin 5,
    (start.move (NestingMachine.opposite direction)).read ≠
        boundarySymbol forbidden →
    (∀ label ∈ labels, label ≠ forbidden) →
    ∀ back ≤ travel,
      ((finish.move (NestingMachine.opposite direction)).moveN
        (NestingMachine.opposite direction) back).read ≠
          boundarySymbol forbidden

/-- Every exact shift trace has its backward coordinate summary. -/
theorem shiftTailGaps_backwardGeometry
    {direction : Turing.Dir} {labels : List (Fin 5)}
    {start finish : FullTM0.Tape (Symbol numTags)}
    (trace : ShiftTailGaps direction labels start finish) :
    Nonempty (ShiftTailBackwardGeometry direction labels start finish) := by
  induction trace with
  | nil T =>
      refine ⟨⟨0, ?_, ?_⟩⟩
      · intro back
        simp
      · intro forbidden hstart _labels back hback
        have hzero : back = 0 := by omega
        subst back
        simpa using hstart
  | cons expected remaining outer distance gap positive finish tail ih =>
      rcases ih with ⟨geometry⟩
      let shifted := shiftStepTape direction outer distance expected
      refine ⟨⟨geometry.travel + distance, ?_, ?_⟩⟩
      · intro back
        calc
          (((finish.move (NestingMachine.opposite direction)).moveN
                (NestingMachine.opposite direction)
                (geometry.travel + distance + back)).read) =
              (((shifted.move (NestingMachine.opposite direction)).moveN
                (NestingMachine.opposite direction)
                (distance + back)).read) := by
            simpa [shifted, Nat.add_assoc] using
              geometry.behind (distance + back)
          _ = (((outer.move (NestingMachine.opposite direction)).moveN
                (NestingMachine.opposite direction) back).read) := by
            exact shiftStepTape_behind direction outer distance back expected
              positive
      · intro forbidden hstart hlabels back hback
        have hexpected : expected ≠ forbidden :=
          hlabels expected (by simp)
        have hremaining : ∀ label ∈ remaining, label ≠ forbidden := by
          intro label hlabel
          exact hlabels label (by simp [hlabel])
        have hshifted :
            (shifted.move (NestingMachine.opposite direction)).read ≠
              boundarySymbol forbidden := by
          rw [shiftStepTape_destination]
          intro heq
          exact hexpected
            ((boundarySymbol_injective expected forbidden).mp heq)
        by_cases hprefix : back ≤ geometry.travel
        · exact geometry.avoids forbidden hshifted hremaining back hprefix
        · let localBack := back - geometry.travel
          have hlocalPositive : 0 < localBack := by
            dsimp [localBack]
            omega
          have hlocal : localBack ≤ distance := by
            dsimp [localBack]
            omega
          have hbackEq : back = geometry.travel + localBack := by
            dsimp [localBack]
            omega
          rw [hbackEq, geometry.behind localBack]
          by_cases hstrict : localBack < distance
          · rw [shiftStepTape_between direction outer distance localBack
                expected gap hlocalPositive hstrict]
            exact blankSymbol_ne_boundarySymbol forbidden
          · have heq : localBack = distance := by omega
            have hreturn :
                ((shifted.move (NestingMachine.opposite direction)).moveN
                    (NestingMachine.opposite direction) distance).read =
                  (outer.move
                    (NestingMachine.opposite direction)).read := by
              simpa [shifted] using
                shiftStepTape_behind direction outer distance 0 expected
                  positive
            rw [heq, hreturn]
            exact hstart

private theorem decrementOrder_label_ne_zero
    (register : Register) (label : Fin 5)
    (hlabel : label ∈ MarkerShift.decrementOrder register) :
    label ≠ 0 := by
  cases register <;> fin_cases label <;>
    simp_all [MarkerShift.decrementOrder]

/-! ## Strict containment after a positive decrement -/

/-- A completed decrement-shift suffix cannot carry its first moved boundary
past canonical boundary `0`.  Thus its retained backward travel is shorter
than the span from boundary `4` to boundary `0`. -/
theorem decrementShift_travel_lt_layoutEnd_sub_one
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GuardedSearch base c)
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (suffix : DecrementShiftSuffixReached current growth source register)
    (registers : Registers)
    (coreTape : FullTM0.Tape (Symbol numTags))
    (hcore : CoreRepresents registers growth coreTape)
    (hcenter : decrementPositiveTape suffix =
      atLogical growth coreTape (layoutEnd registers))
    (geometry : ShiftTailBackwardGeometry (orient growth .right)
      suffix.position.remaining
      (current.shiftedParentBacking suffix.position.current)
      suffix.finish) :
    geometry.travel < layoutEnd registers - 1 := by
  have hdirection : current.direction = orient growth .right := by
    have hdirection := current.selectedRaw_direction_eq
    rw [CounterControlCommandAt.compileRawCommand_searchDirection]
      at hdirection
    rw [suffix.position.raw_eq] at hdirection
    exact hdirection.symm
  have hopposite : NestingMachine.opposite (orient growth .right) =
      orient growth .left := by
    cases growth <;> rfl
  have hcurrentMem : suffix.position.current ∈
      MarkerShift.decrementOrder register := by
    have heq := congrArg
      (fun labels : List (Fin 5) => suffix.position.current ∈ labels)
      suffix.position.labels_eq
    exact heq.mpr (by simp)
  have hcurrentNe : suffix.position.current ≠ 0 :=
    decrementOrder_label_ne_zero register suffix.position.current hcurrentMem
  have hremaining : ∀ label ∈ suffix.position.remaining,
      label ≠ (0 : Fin 5) := by
    intro label hlabel
    apply decrementOrder_label_ne_zero register label
    have heq := congrArg (fun labels : List (Fin 5) => label ∈ labels)
      suffix.position.labels_eq
    exact heq.mpr (by simp [hlabel])
  have hstartRead :
      ((current.shiftedParentBacking suffix.position.current).move
        (NestingMachine.opposite (orient growth .right))).read =
          boundarySymbol suffix.position.current := by
    have hread := suffix.handoff.destination_boundary
    rw [hdirection] at hread
    exact hread
  have hstartAvoid :
      ((current.shiftedParentBacking suffix.position.current).move
        (NestingMachine.opposite (orient growth .right))).read ≠
          boundarySymbol 0 := by
    rw [hstartRead]
    intro heq
    exact hcurrentNe
      ((boundarySymbol_injective suffix.position.current 0).mp heq)
  have hfinishEq :
      suffix.finish.move
          (NestingMachine.opposite (orient growth .right)) =
        atLogical growth coreTape (layoutEnd registers) := by
    rw [hopposite]
    exact hcenter
  have hendPositive : 1 < layoutEnd registers := by
    simp [layoutEnd, RegisterLayout.clockBoundary_eq]
  have hboundaryZero :
      ((suffix.finish.move
          (NestingMachine.opposite (orient growth .right))).moveN
            (NestingMachine.opposite (orient growth .right))
            (layoutEnd registers - 1)).read = boundarySymbol 0 := by
    rw [hfinishEq, hopposite]
    have hend : layoutEnd registers = 1 + (layoutEnd registers - 1) := by
      omega
    conv_lhs =>
      enter [1, 1]
      rw [hend]
    simp only [orient_eq_orientDirection]
    rw [atLogical_moveN_left, atLogical_read]
    simpa using hcore.boundary (0 : Fin 5)
  by_contra hnot
  have hle : layoutEnd registers - 1 ≤ geometry.travel :=
    Nat.le_of_not_gt hnot
  have havoid := geometry.avoids (0 : Fin 5) hstartAvoid hremaining
    (layoutEnd registers - 1) hle
  exact havoid hboundaryZero

/-- The parent gap of any guarded shift caller is strictly contained in a
canonical core centered at the completed positive-decrement endpoint.

The proof does not assume that the shift caller was itself part of an
already represented frame.  Instead it follows the shifted boundary segment
backward.  Boundary `0` cannot occur among the nonzero decrement labels; if
the retained parent gap were too long, canonical boundary `0` would therefore
be one of its cells, contradicting blankness. -/
theorem decrementShift_distance_lt_layoutEnd
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GuardedSearch base c)
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (suffix : DecrementShiftSuffixReached current growth source register)
    (registers : Registers)
    (coreTape : FullTM0.Tape (Symbol numTags))
    (hcore : CoreRepresents registers growth coreTape)
    (hcenter : decrementPositiveTape suffix =
      atLogical growth coreTape (layoutEnd registers)) :
    current.current.distance < layoutEnd registers := by
  have hdirection : current.direction = orient growth .right := by
    have hdirection := current.selectedRaw_direction_eq
    rw [CounterControlCommandAt.compileRawCommand_searchDirection]
      at hdirection
    rw [suffix.position.raw_eq] at hdirection
    exact hdirection.symm
  have hopposite : NestingMachine.opposite (orient growth .right) =
      orient growth .left := by
    cases growth <;> rfl
  rcases shiftTailGaps_backwardGeometry suffix.tailGaps with
    ⟨geometry⟩
  have hcurrentMem : suffix.position.current ∈
      MarkerShift.decrementOrder register := by
    have heq := congrArg
      (fun labels : List (Fin 5) => suffix.position.current ∈ labels)
      suffix.position.labels_eq
    exact heq.mpr (by simp)
  have hcurrentNe : suffix.position.current ≠ 0 :=
    decrementOrder_label_ne_zero register suffix.position.current hcurrentMem
  have hremaining : ∀ label ∈ suffix.position.remaining,
      label ≠ (0 : Fin 5) := by
    intro label hlabel
    apply decrementOrder_label_ne_zero register label
    have heq := congrArg (fun labels : List (Fin 5) => label ∈ labels)
      suffix.position.labels_eq
    exact heq.mpr (by simp [hlabel])
  have hstartRead :
      ((current.shiftedParentBacking suffix.position.current).move
        (NestingMachine.opposite (orient growth .right))).read =
          boundarySymbol suffix.position.current := by
    have hread := suffix.handoff.destination_boundary
    rw [hdirection] at hread
    exact hread
  have hstartAvoid :
      ((current.shiftedParentBacking suffix.position.current).move
        (NestingMachine.opposite (orient growth .right))).read ≠
          boundarySymbol 0 := by
    rw [hstartRead]
    intro heq
    exact hcurrentNe
      ((boundarySymbol_injective suffix.position.current 0).mp heq)
  have hfinishEq :
      suffix.finish.move
          (NestingMachine.opposite (orient growth .right)) =
        atLogical growth coreTape (layoutEnd registers) := by
    rw [hopposite]
    exact hcenter
  have hendPositive : 1 < layoutEnd registers := by
    simp [layoutEnd, RegisterLayout.clockBoundary_eq]
  have hboundaryZero :
      ((suffix.finish.move
          (NestingMachine.opposite (orient growth .right))).moveN
            (NestingMachine.opposite (orient growth .right))
            (layoutEnd registers - 1)).read = boundarySymbol 0 := by
    rw [hfinishEq, hopposite]
    have hend : layoutEnd registers = 1 + (layoutEnd registers - 1) := by
      omega
    conv_lhs =>
      enter [1, 1]
      rw [hend]
    simp only [orient_eq_orientDirection]
    rw [atLogical_moveN_left, atLogical_read]
    simpa using hcore.boundary (0 : Fin 5)
  have htravel : geometry.travel < layoutEnd registers - 1 := by
    by_contra hnot
    have hle : layoutEnd registers - 1 ≤ geometry.travel :=
      Nat.le_of_not_gt hnot
    have havoid := geometry.avoids (0 : Fin 5) hstartAvoid hremaining
      (layoutEnd registers - 1) hle
    exact havoid hboundaryZero
  by_contra hnot
  have hdistance : layoutEnd registers ≤ current.current.distance :=
    Nat.le_of_not_gt hnot
  let back := layoutEnd registers - 1 - geometry.travel
  have hbackPositive : 0 < back := by
    dsimp [back]
    omega
  have hbackLt : back < current.current.distance + 1 := by
    dsimp [back]
    omega
  have hsum : geometry.travel + back = layoutEnd registers - 1 := by
    dsimp [back]
    omega
  have htransport := geometry.behind back
  rw [hsum, hboundaryZero] at htransport
  have hparentGap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary suffix.position.current).Matches
      current.parentOuter (orient growth .right)
      (current.current.distance + 1) := by
    have hgap := current.parentGap
    rw [← current.compileRawCommand_selectedRaw,
      CounterControlCommandAt.compileRawCommand_spec] at hgap
    rw [hdirection] at hgap
    simpa [suffix.position.raw_eq,
      CounterControlCommandAt.compileRawAtTag, Command.target,
      Command.searchDirection] using hgap
  have hblank := shiftStepTape_between (orient growth .right)
    current.parentOuter (current.current.distance + 1) back
    suffix.position.current hparentGap hbackPositive hbackLt
  change (((shiftStepTape (orient growth .right) current.parentOuter
      (current.current.distance + 1) suffix.position.current).move
        (NestingMachine.opposite (orient growth .right))).moveN
        (NestingMachine.opposite (orient growth .right)) back).read =
      blankSymbol at hblank
  rw [← hdirection] at hblank
  change (((current.shiftedParentBacking suffix.position.current).move
      (NestingMachine.opposite current.direction)).moveN
        (NestingMachine.opposite current.direction) back).read =
      blankSymbol at hblank
  rw [hdirection] at hblank
  rw [hblank] at htransport
  exact blankSymbol_ne_boundarySymbol 0 htransport.symm

private theorem immortalFrom_of_reaches
    (base : Nat) (c : Nat.Partrec.Code)
    {first second : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) first)
    (hreach : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c) first second) :
    FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) second := by
  rw [FullTM0.HaltsFrom.immortalFrom_iff_not] at himmortal ⊢
  intro hhalts
  exact himmortal (FullTM0.HaltsFrom.of_reaches hreach hhalts)

/-- Reconstructed logical endpoint of a completed positive-decrement shift,
retaining strict containment separately from the final parent-outcome sum. -/
structure DecrementPositiveLogicalEnd
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GuardedSearch base c) : Type where
  core : LogicalCore base c
  reaches : FullTM0.Reaches
    (CounterControlNestingBridge.machine base c)
    (foundCfg current.current) core.cfg
  strictly_inside : current.current.distance < layoutEnd core.registers

/-- The same endpoint with the reconstruction equality and core invariant
exposed for callers which began before the first decrement shift. -/
structure DecrementPositiveCenteredEnd
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GuardedSearch base c)
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (ifZero ifPositive : Nat)
    (direct : DecrementPositiveDirectHandoff current growth source register
      ifZero ifPositive) : Type where
  core : LogicalCore base c
  core_represents : CoreRepresents core.registers growth core.tape
  center : decrementPositiveTape direct.suffix =
    atLogical growth core.tape (layoutEnd core.registers)
  reaches : FullTM0.Reaches
    (CounterControlNestingBridge.machine base c)
    (foundCfg current.current) core.cfg
  strictly_inside : current.current.distance < layoutEnd core.registers

/-- Immortality at the guarded found state turns the completed positive
decrement handoff into a represented logical core which strictly contains
the guarded parent gap. -/
theorem decrementPositiveCenteredEnd
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (current : GuardedSearch base c)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      (foundCfg current.current))
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (ifZero ifPositive : Nat)
    (direct : DecrementPositiveDirectHandoff current growth source register
      ifZero ifPositive) :
    Nonempty (DecrementPositiveCenteredEnd current growth source register
      ifZero ifPositive direct) := by
  have himmortalLogical := immortalFrom_of_reaches base c himmortal
    direct.reaches
  change FullTM0.ImmortalFrom
    (CounterControlNestingBridge.machine base c)
    ⟨logicalState base c growth ifPositive,
      decrementPositiveTape direct.suffix⟩ at himmortalLogical
  rcases CounterControlValidationRoundtrip.logical_reconstructs_coreTarget_fields_of_immortal
      base c hmortal growth ifPositive direct.target_lt
      (decrementPositiveTape direct.suffix) himmortalLogical with
    ⟨instruction, registers, coreTape, limit, target, _hrule, hcore,
      hcoreBefore, hrunway, htarget, hcenter, _hbody⟩
  let represented : CoreTargetRepresents registers growth limit target
      coreTape := {
    toCorePrefixRepresents := {
      toCoreRepresents := hcore
      core_before_limit := hcoreBefore
      runway := hrunway }
    target_matches := htarget }
  let core : LogicalCore base c := {
    growth := growth
    source := ifPositive
    source_lt := direct.target_lt
    registers := registers
    tape := coreTape
    limit := limit
    target := target
    represented := represented }
  have hinside : current.current.distance < layoutEnd registers :=
    decrementShift_distance_lt_layoutEnd current growth source register
      direct.suffix registers coreTape hcore hcenter
  have hreaches : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      (foundCfg current.current) core.cfg := by
    have hrun := direct.reaches
    change FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      (foundCfg current.current)
      ⟨logicalState base c growth ifPositive,
        decrementPositiveTape direct.suffix⟩ at hrun
    rw [hcenter] at hrun
    simpa [core, LogicalCore.cfg, LogicalCore.frame,
      LogicalCore.abstract, prefixLogicalCfg] using hrun
  exact ⟨⟨core, hcore, hcenter, hreaches, hinside⟩⟩

/-- Consumer-facing projection of `decrementPositiveCenteredEnd`. -/
theorem decrementPositiveLogicalEnd
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (current : GuardedSearch base c)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      (foundCfg current.current))
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (ifZero ifPositive : Nat)
    (direct : DecrementPositiveDirectHandoff current growth source register
      ifZero ifPositive) :
    Nonempty (DecrementPositiveLogicalEnd current) := by
  rcases decrementPositiveCenteredEnd base c hmortal current himmortal growth
      source register ifZero ifPositive direct with ⟨endpoint⟩
  exact ⟨⟨endpoint.core, endpoint.reaches, endpoint.strictly_inside⟩⟩

/-- Completed positive-decrement shifts supply the logical branch of the
found guarded-parent continuation law. -/
theorem decrementPositive_foundGuardedParentOutcome
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (current : GuardedSearch base c)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      (foundCfg current.current))
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (ifZero ifPositive : Nat)
    (direct : DecrementPositiveDirectHandoff current growth source register
      ifZero ifPositive) :
    Nonempty (FoundGuardedParentOutcome current) := by
  rcases decrementPositiveLogicalEnd base c hmortal current himmortal growth
      source register ifZero ifPositive direct with ⟨endpoint⟩
  exact ⟨FoundGuardedParentOutcome.logical endpoint.core endpoint.reaches
    endpoint.strictly_inside⟩

end

end CounterControlGuardedShiftEmbedding
end Hooper
end Kari
end LeanWang
