/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlArbitraryMortality
import LeanWang.Kari.Hooper.CounterControlValidationConverse

/-!
# Validation routes on immortal arbitrary orbits

Successful preserving boundary searches and their one-cell direct
continuations can be chained without assuming a counter representation in
advance.  The resulting gap trace is the converse input used to reconstruct
the finite counter core.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlValidationMortality

open Turing CounterMachine
open BoundedMarkerProgram FramedMarkerTape
open CounterControlPlan CounterControlInstructionSemantics
open CounterControlBridge

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-- Tape-level trace of a nonempty preserving boundary route.  Each search
starts one cell beyond the preceding boundary; the final tape is centered on
the last boundary found. -/
inductive RouteGaps (growth : Turing.Dir) :
    List MarkerValidation.Leg →
      FullTM0.Tape (Symbol numTags) →
      FullTM0.Tape (Symbol numTags) → Prop
  | last (leg : MarkerValidation.Leg)
      (outer : FullTM0.Tape (Symbol numTags)) (distance : Nat)
      (gap : SearchGap (fun symbol => symbol = blankSymbol)
        (Target.boundary leg.target).Matches outer
        (orient growth leg.direction) distance) :
      RouteGaps growth [leg] outer
        (outer.moveN (orient growth leg.direction) distance)
  | cons (leg next : MarkerValidation.Leg)
      (rest : List MarkerValidation.Leg)
      (outer : FullTM0.Tape (Symbol numTags)) (distance : Nat)
      (gap : SearchGap (fun symbol => symbol = blankSymbol)
        (Target.boundary leg.target).Matches outer
        (orient growth leg.direction) distance)
      (finish : FullTM0.Tape (Symbol numTags))
      (tail : RouteGaps growth (next :: rest)
        ((outer.moveN (orient growth leg.direction) distance).move
          (orient growth next.direction)) finish) :
      RouteGaps growth (leg :: next :: rest) outer finish

/-- Every reached generated preserving route on an immortal orbit produces
a genuine tape-level gap trace and reaches its advertised final symbolic
continuation. -/
theorem reaches_routeGaps_of_immortal
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    {start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) start)
    (growth : Turing.Dir) (counterState searchSlot directSlot : Nat)
    (after : ControlRef) (first : MarkerValidation.Leg)
    (rest : List MarkerValidation.Leg)
    (outer : FullTM0.Tape (Symbol numTags))
    (hreach : FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      start ⟨searchState base c ⟨growth, counterState, searchSlot⟩,
        outer⟩)
    (hcommands : ∀ raw,
      raw ∈ routeCommandsAux growth counterState searchSlot directSlot
          after (first :: rest) →
        raw ∈ rawCommands)
    (hcontinuations : ∀ rule,
      rule ∈ routeContinuationRules growth counterState searchSlot
          directSlot (first :: rest) →
        rule ∈ rawDirectRules) :
    ∃ finish,
      RouteGaps growth (first :: rest) outer finish ∧
        FullTM0.Reaches (CounterControlNestingBridge.machine base c) start
          ⟨resolve base c after, finish⟩ := by
  induction rest generalizing first searchSlot directSlot outer with
  | nil =>
      let raw : RawCommand :=
        .boundaryNavigation ⟨growth, counterState, searchSlot⟩
          first.target first.direction after .preserve
      have hraw : raw ∈ rawCommands := by
        apply hcommands raw
        simp [raw, routeCommandsAux]
      rcases CounterControlImmortalSearch.reaches_boundary_preserve_of_immortal
          base c hmortal
          (CounterControlOpenStepLaw.openStepContinuesOrHalts base c)
          himmortal ⟨growth, counterState, searchSlot⟩ first.target
          first.direction after hraw outer hreach with
        ⟨distance, hgap, hfinish⟩
      exact ⟨outer.moveN (orient growth first.direction) distance,
        .last first outer distance hgap, hfinish⟩
  | cons next tail ih =>
      let handoff := directRef growth counterState directSlot
      let raw : RawCommand :=
        .boundaryNavigation ⟨growth, counterState, searchSlot⟩
          first.target first.direction handoff .preserve
      let continuation : RawDirectRule :=
        ⟨growth, handoff, .boundary first.target,
          searchRef growth counterState (searchSlot + 1), next.direction⟩
      have hraw : raw ∈ rawCommands := by
        apply hcommands raw
        simp [raw, handoff, routeCommandsAux]
      have hcontinuation : continuation ∈ rawDirectRules := by
        apply hcontinuations continuation
        simp [continuation, handoff, routeContinuationRules,
          routeContinuationRulesFrom]
      rcases CounterControlArbitraryMortality.reaches_nextSearch_of_immortal_boundary_preserve
          base c hmortal himmortal ⟨growth, counterState, searchSlot⟩
          first.target first.direction handoff
          ⟨growth, counterState, searchSlot + 1⟩ next.direction
          hraw hcontinuation outer hreach with
        ⟨distance, hgap, hnext⟩
      let nextOuter :=
        (outer.moveN (orient growth first.direction) distance).move
          (orient growth next.direction)
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
      rcases ih (searchSlot + 1) (directSlot + 1) next nextOuter
          (by simpa [nextOuter] using hnext) hcommandsTail
          hcontinuationsTail with ⟨finish, htail, hfinish⟩
      exact ⟨finish, .cons first next tail outer distance hgap finish htail,
        hfinish⟩

/-- Convert any nonempty all-right tape trace into its coordinate-level route
on a single logical tape. -/
theorem routeExecutesAt_of_routeGaps_allRight
    (growth : Turing.Dir) (T : FullTM0.Tape (Symbol numTags))
    {route : List MarkerValidation.Leg}
    {outer finishTape : FullTM0.Tape (Symbol numTags)} {source : Nat}
    (hdirections : ∀ leg, leg ∈ route → leg.direction = .right)
    (houter : outer = atLogical growth T (source + 1))
    (htrace : RouteGaps growth route outer finishTape) :
    ∃ finish, RouteExecutesAt growth T route source finish ∧
      finishTape = atLogical growth T finish := by
  induction htrace generalizing source with
  | last leg outer distance gap =>
      have hright : leg.direction = .right := hdirections leg (by simp)
      let finish := source + distance + 1
      have hfirst : LegExecutesAt growth T leg source finish := by
        simp only [LegExecutesAt, hright]
        refine ⟨distance, ?_, by simp [finish]⟩
        simpa only [houter, hright, orient_eq_orientDirection] using gap
      refine ⟨finish, .cons leg [] source finish finish hfirst (.nil finish), ?_⟩
      rw [houter, hright, orient_eq_orientDirection, atLogical_moveN_right]
      congr 1
      omega
  | cons leg next rest outer distance gap finishTape tail ih =>
      have hright : leg.direction = .right := hdirections leg (by simp)
      have hnext : next.direction = .right := hdirections next (by simp)
      let middle := source + distance + 1
      have hfirst : LegExecutesAt growth T leg source middle := by
        simp only [LegExecutesAt, hright]
        refine ⟨distance, ?_, by simp [middle]⟩
        simpa only [houter, hright, orient_eq_orientDirection] using gap
      have hnextOuter :
          ((outer.moveN (orient growth leg.direction) distance).move
              (orient growth next.direction)) =
            atLogical growth T (middle + 1) := by
        rw [houter, hright, hnext, orient_eq_orientDirection,
          atLogical_moveN_right, atLogical_move_right]
        congr 1
        omega
      have htailDirections : ∀ candidate, candidate ∈ next :: rest →
          candidate.direction = .right := by
        intro candidate hcandidate
        exact hdirections candidate (List.mem_cons_of_mem leg hcandidate)
      rcases ih htailDirections hnextOuter with
        ⟨finish, htail, hfinish⟩
      exact ⟨finish,
        .cons leg (next :: rest) source middle finish hfirst htail, hfinish⟩

/-- The tape-level trace of the four outward validation legs is the native
coordinate-level route required by the validation converse. -/
theorem outwardSweep_executesAt_of_routeGaps
    (growth : Turing.Dir) (T finishTape : FullTM0.Tape (Symbol numTags))
    (htrace : RouteGaps growth
      CounterControlValidationConverse.outwardSweep
      (T.move (orient growth .right)) finishTape) :
    ∃ finish,
      RouteExecutesAt growth T
          CounterControlValidationConverse.outwardSweep 0 finish ∧
        finishTape = atLogical growth T finish := by
  apply routeExecutesAt_of_routeGaps_allRight growth T
    (route := CounterControlValidationConverse.outwardSweep)
    (outer := T.move (orient growth .right))
    (source := 0) (finishTape := finishTape)
  · intro leg hleg
    simp [CounterControlValidationConverse.outwardSweep] at hleg
    rcases hleg with rfl | rfl | rfl | rfl <;> rfl
  · simpa [orient_eq_orientDirection, atLogical] using
      (atLogical_move_right growth T 0)
  · exact htrace

/-- Four successful outward validation searches reconstruct both the
boundary-zero view and the ordinary tag-free finite counter core.  The final
tape is centered on the reconstructed boundary `4`. -/
theorem outwardRouteGaps_reconstructs
    (growth : Turing.Dir) (T finishTape : FullTM0.Tape (Symbol numTags))
    (hsource : T.read = boundarySymbol 0)
    (htrace : RouteGaps growth
      CounterControlValidationConverse.outwardSweep
      (T.move (orient growth .right)) finishTape) :
    ∃ registers : Registers,
      CounterControlValidationConverse.BoundaryZeroRepresents
          registers growth T ∧
        CounterControlCoreFrame.CoreRepresents registers growth
          (T.move (orient growth .left)) ∧
        finishTape = atLogical growth T
          (RegisterLayout.clockBoundary registers) := by
  rcases outwardSweep_executesAt_of_routeGaps growth T finishTape htrace with
    ⟨finish, hexec, hfinish⟩
  have hsource' : (atLogical growth T 0).read = boundarySymbol 0 := by
    simpa [atLogical] using hsource
  rcases CounterControlValidationConverse.outwardSweep_reconstructs
      growth T 0 finish hsource' hexec with
    ⟨registers, hboundary, hposition⟩
  have hzero : atLogical growth T 0 = T := by simp [atLogical]
  rw [hzero] at hboundary
  have hcore : CounterControlCoreFrame.CoreRepresents registers growth
      (T.move (orient growth .left)) := by
    simpa only [orient_eq_orientDirection] using hboundary.toCoreRepresents
  refine ⟨registers, hboundary, hcore, ?_⟩
  rw [hfinish, hposition]
  simp

/-- Starting at the first outward validation search on an immortal orbit,
the four generated searches reconstruct a finite counter core and reach the
instruction body at boundary `4`. -/
theorem outward_validation_reconstructs_of_immortal
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    {start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) start)
    (growth : Turing.Dir) (source : Nat)
    (instruction : CounterMachine.Instruction)
    (hrule : (source, instruction) ∈ GlobalSourceProgram.program)
    (T : FullTM0.Tape (Symbol numTags))
    (hsource : (atLogical growth T 0).read = boundarySymbol 0)
    (hreach : FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      start ⟨searchState base c ⟨growth, source, 4⟩,
        atLogical growth T 1⟩) :
    ∃ registers : Registers,
      CounterControlValidationConverse.BoundaryZeroRepresents
          registers growth T ∧
        CounterControlCoreFrame.CoreRepresents registers growth
          (T.move (orient growth .left)) ∧
        FullTM0.Reaches (CounterControlNestingBridge.machine base c) start
          ⟨resolve base c (bodyEntry growth source instruction),
            atLogical growth T
              (RegisterLayout.clockBoundary registers)⟩ := by
  have hcommands : ∀ raw,
      raw ∈ routeCommandsAux growth source 4 4
          (bodyEntry growth source instruction)
          CounterControlValidationConverse.outwardSweep →
        raw ∈ rawCommands := by
    intro raw hraw
    apply CounterControlInstructionSemantics.command_mem_rawCommands_of_rule
      growth hrule
    cases instruction <;>
      simp_all [commandsForRule, validationCommands,
        CounterControlValidationConverse.outwardSweep,
        MarkerValidation.sweep, routeCommandsAux, validationSearchBase,
        validationDirectBase, directRef] <;> aesop
  have hcontinuations : ∀ rule,
      rule ∈ routeContinuationRules growth source 4 4
          CounterControlValidationConverse.outwardSweep →
        rule ∈ rawDirectRules := by
    intro rule hraw
    apply CounterControlInstructionSemantics.directRule_mem_rawDirectRules_of_rule
      growth hrule
    cases instruction <;>
      simp_all [directRulesForRule, validationRules,
        CounterControlValidationConverse.outwardSweep,
        MarkerValidation.sweep, routeEntryRules, routeContinuationRules,
        routeContinuationRulesFrom, validationSearchBase,
        validationDirectBase, directRef, searchRef] <;> aesop
  have hone : atLogical growth T 1 = T.move (orient growth .right) := by
    simpa [atLogical, orient_eq_orientDirection] using
      (atLogical_move_right growth T 0).symm
  have hreach' : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c) start
      ⟨searchState base c ⟨growth, source, 4⟩,
        T.move (orient growth .right)⟩ := by
    simpa [hone] using hreach
  rcases reaches_routeGaps_of_immortal base c hmortal himmortal growth
      source 4 4 (bodyEntry growth source instruction)
      ⟨1, .right⟩ [⟨2, .right⟩, ⟨3, .right⟩, ⟨4, .right⟩]
      (T.move (orient growth .right)) hreach' hcommands hcontinuations with
    ⟨finishTape, htrace, hfinish⟩
  have hsource' : T.read = boundarySymbol 0 := by
    simpa [atLogical] using hsource
  rcases outwardRouteGaps_reconstructs growth T finishTape hsource' htrace with
    ⟨registers, hboundary, hcore, hfinishTape⟩
  refine ⟨registers, hboundary, hcore, ?_⟩
  rw [hfinishTape] at hfinish
  exact hfinish

/-- The four inward validation searches anchor an arbitrary tape at the
successfully found boundary `0` and reach the first outward search. -/
theorem reaches_outward_validation_of_immortal
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    {start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) start)
    (growth : Turing.Dir) (source : Nat)
    (instruction : CounterMachine.Instruction)
    (hrule : (source, instruction) ∈ GlobalSourceProgram.program)
    (outer : FullTM0.Tape (Symbol numTags))
    (hreach : FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      start ⟨searchState base c ⟨growth, source, 0⟩, outer⟩) :
    ∃ T : FullTM0.Tape (Symbol numTags),
      T.read = boundarySymbol 0 ∧
        FullTM0.Reaches (CounterControlNestingBridge.machine base c) start
          ⟨searchState base c ⟨growth, source, 4⟩,
            atLogical growth T 1⟩ := by
  have hcommands : ∀ raw,
      raw ∈ validationCommands growth source instruction →
        raw ∈ rawCommands := by
    intro raw hraw
    apply CounterControlInstructionSemantics.command_mem_rawCommands_of_rule
      growth hrule
    cases instruction <;> simp [commandsForRule, hraw]
  have hrules : ∀ rule, rule ∈ validationRules growth source →
      rule ∈ rawDirectRules := by
    intro rule hraw
    apply CounterControlInstructionSemantics.directRule_mem_rawDirectRules_of_rule
      growth hrule
    cases instruction <;> simp [directRulesForRule, hraw]
  have hraw0 := hcommands
    (.boundaryNavigation ⟨growth, source, 0⟩ 3 .left
      (directRef growth source 0) .preserve) (by
      simp [validationCommands, routeCommandsAux, MarkerValidation.sweep,
        validationSearchBase, validationDirectBase, directRef])
  have hcont0 := hrules
    (RawDirectRule.mk growth (directRef growth source 0) (.boundary 3)
      (.search ⟨growth, source, 1⟩) .left) (by
      simp [validationRules, routeEntryRules, routeContinuationRules,
        routeContinuationRulesFrom, MarkerValidation.sweep,
        validationSearchBase, validationDirectBase, directRef, searchRef])
  rcases CounterControlArbitraryMortality.reaches_nextSearch_of_immortal_boundary_preserve
      base c hmortal himmortal ⟨growth, source, 0⟩ 3 .left
      (directRef growth source 0) ⟨growth, source, 1⟩ .left hraw0 hcont0
      outer hreach with ⟨d0, _hgap0, hreach1⟩
  let outer1 := (outer.moveN (orient growth .left) d0).move
    (orient growth .left)
  have hraw1 := hcommands
    (.boundaryNavigation ⟨growth, source, 1⟩ 2 .left
      (directRef growth source 1) .preserve) (by
      simp [validationCommands, routeCommandsAux, MarkerValidation.sweep,
        validationSearchBase, validationDirectBase, directRef])
  have hcont1 := hrules
    (RawDirectRule.mk growth (directRef growth source 1) (.boundary 2)
      (.search ⟨growth, source, 2⟩) .left) (by
      simp [validationRules, routeEntryRules, routeContinuationRules,
        routeContinuationRulesFrom, MarkerValidation.sweep,
        validationSearchBase, validationDirectBase, directRef, searchRef])
  rcases CounterControlArbitraryMortality.reaches_nextSearch_of_immortal_boundary_preserve
      base c hmortal himmortal ⟨growth, source, 1⟩ 2 .left
      (directRef growth source 1) ⟨growth, source, 2⟩ .left hraw1 hcont1
      outer1 (by simpa [outer1] using hreach1) with
    ⟨d1, _hgap1, hreach2⟩
  let outer2 := (outer1.moveN (orient growth .left) d1).move
    (orient growth .left)
  have hraw2 := hcommands
    (.boundaryNavigation ⟨growth, source, 2⟩ 1 .left
      (directRef growth source 2) .preserve) (by
      simp [validationCommands, routeCommandsAux, MarkerValidation.sweep,
        validationSearchBase, validationDirectBase, directRef])
  have hcont2 := hrules
    (RawDirectRule.mk growth (directRef growth source 2) (.boundary 1)
      (.search ⟨growth, source, 3⟩) .left) (by
      simp [validationRules, routeEntryRules, routeContinuationRules,
        routeContinuationRulesFrom, MarkerValidation.sweep,
        validationSearchBase, validationDirectBase, directRef, searchRef])
  rcases CounterControlArbitraryMortality.reaches_nextSearch_of_immortal_boundary_preserve
      base c hmortal himmortal ⟨growth, source, 2⟩ 1 .left
      (directRef growth source 2) ⟨growth, source, 3⟩ .left hraw2 hcont2
      outer2 (by simpa [outer2] using hreach2) with
    ⟨d2, _hgap2, hreach3⟩
  let outer3 := (outer2.moveN (orient growth .left) d2).move
    (orient growth .left)
  have hraw3 := hcommands
    (.boundaryNavigation ⟨growth, source, 3⟩ 0 .left
      (directRef growth source 3) .preserve) (by
      simp [validationCommands, routeCommandsAux, MarkerValidation.sweep,
        validationSearchBase, validationDirectBase, directRef])
  have hcont3 := hrules
    (RawDirectRule.mk growth (directRef growth source 3) (.boundary 0)
      (.search ⟨growth, source, 4⟩) .right) (by
      simp [validationRules, routeEntryRules, routeContinuationRules,
        routeContinuationRulesFrom, MarkerValidation.sweep,
        validationSearchBase, validationDirectBase, directRef, searchRef])
  rcases CounterControlArbitraryMortality.reaches_nextSearch_of_immortal_boundary_preserve
      base c hmortal himmortal ⟨growth, source, 3⟩ 0 .left
      (directRef growth source 3) ⟨growth, source, 4⟩ .right hraw3 hcont3
      outer3 (by simpa [outer3] using hreach3) with
    ⟨d3, hgap3, hreach4⟩
  let T := outer3.moveN (orient growth .left) d3
  have hread : T.read = boundarySymbol 0 := by
    simpa [T, FullTM0.Tape.read, Target.Matches] using hgap3.marked
  refine ⟨T, hread, ?_⟩
  have hone : T.move (orient growth .right) = atLogical growth T 1 := by
    simpa [atLogical, orient_eq_orientDirection] using
      (atLogical_move_right growth T 0)
  change FullTM0.Reaches _ _
    ⟨searchState base c ⟨growth, source, 4⟩,
      T.move (orient growth .right)⟩ at hreach4
  rw [hone] at hreach4
  exact hreach4

/-- A reached first validation search on an immortal orbit reconstructs the
finite counter core and reaches the exact instruction body. -/
theorem validation_reconstructs_of_immortal
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    {start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) start)
    (growth : Turing.Dir) (source : Nat)
    (instruction : CounterMachine.Instruction)
    (hrule : (source, instruction) ∈ GlobalSourceProgram.program)
    (outer : FullTM0.Tape (Symbol numTags))
    (hreach : FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      start ⟨searchState base c ⟨growth, source, 0⟩, outer⟩) :
    ∃ (registers : Registers) (T : FullTM0.Tape (Symbol numTags)),
      CounterControlValidationConverse.BoundaryZeroRepresents
          registers growth T ∧
        CounterControlCoreFrame.CoreRepresents registers growth
          (T.move (orient growth .left)) ∧
        FullTM0.Reaches (CounterControlNestingBridge.machine base c) start
          ⟨resolve base c (bodyEntry growth source instruction),
            atLogical growth T
              (RegisterLayout.clockBoundary registers)⟩ := by
  rcases reaches_outward_validation_of_immortal base c hmortal himmortal
      growth source instruction hrule outer hreach with
    ⟨T, hsource, houtward⟩
  rcases outward_validation_reconstructs_of_immortal base c hmortal
      himmortal growth source instruction hrule T
      (by simpa [atLogical] using hsource) houtward with
    ⟨registers, hboundary, hcore, hfinish⟩
  exact ⟨registers, T, hboundary, hcore, hfinish⟩

end

end CounterControlValidationMortality
end Hooper
end Kari
end LeanWang
