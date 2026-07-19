/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlLongSearchMortality
import LeanWang.Kari.Hooper.CounterControlInstructionSemantics
import LeanWang.Kari.Hooper.CounterControlTerminalSemantics
import LeanWang.Kari.Hooper.CounterControlCoreFrame

/-!
# Large represented clocks force concrete mortality

Every compiled counter instruction starts by validating the clock gap from
boundary `4` to boundary `3`.  Thus the uniform mortality bound for long
compiled searches immediately rules out an immortal represented logical
configuration with a sufficiently large clock.  This argument uses only the
tag-free five-boundary core; it does not assume a saved return tag or an outer
Hooper frame.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlLargeClock

open Turing CounterMachine
open BoundedMarkerProgram FramedMarkerTape
open CounterControlPlan CounterControlCoreFrame
open CounterControlCommandAt CounterControlSearchSystem

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-- The first bounded command of every validation sweep. -/
def validationFirst (growth : Turing.Dir) (source : Nat) : RawCommand :=
  .boundaryNavigation
    ⟨growth, source, validationSearchBase⟩ 3 .left
    (directRef growth source validationDirectBase) .preserve

/-- The first validation command belongs to the global command enumeration
whenever the corresponding abstract instruction exists. -/
theorem validationFirst_mem
    (growth : Turing.Dir) (source : Nat)
    (instruction : CounterMachine.Instruction)
    (hrule : (source, instruction) ∈ GlobalSourceProgram.program) :
    validationFirst growth source ∈ rawCommands := by
  apply CounterControlPlan.command_mem_rawCommands_of_rule
    growth hrule
  cases instruction <;>
    simp [validationFirst, commandsForRule, validationCommands,
      routeCommandsAux, MarkerValidation.sweep]

/-- Enter the first validation search using only the boundary-`4` fact of a
tag-free represented core. -/
theorem reaches_validationFirst
    (base : Nat) (c : Nat.Partrec.Code) (growth : Turing.Dir)
    (source : Nat) (instruction : CounterMachine.Instruction)
    (hrule : (source, instruction) ∈ GlobalSourceProgram.program)
    (registers : Registers) (T : FullTM0.Tape (Symbol numTags))
    (hcore : CoreRepresents registers growth T) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      ⟨logicalState base c growth source,
        atLogical growth T (layoutEnd registers)⟩
      ⟨searchState base c
          ⟨growth, source, validationSearchBase⟩,
        atLogical growth T (lastGapOffset registers 3)⟩ := by
  let entry : RawDirectRule :=
    ⟨growth, .logical growth source, .boundary 4,
      searchRef growth source validationSearchBase, .left⟩
  have hentry : entry ∈ rawDirectRules := by
    apply CounterControlPlan.directRule_mem_rawDirectRules_of_rule
      growth hrule
    cases instruction <;>
      simp [entry, directRulesForRule, validationRules,
        routeEntryRules, MarkerValidation.sweep]
  have hmatch : entry.read.Matches
      (atLogical growth T (layoutEnd registers)).read := by
    change (atLogical growth T (layoutEnd registers)).read = boundarySymbol 4
    exact hcore.read_boundary_four
  have hstep := CounterControlDirectSemantics.reaches_directRule base c entry
    hentry (atLogical growth T (layoutEnd registers)) hmatch
  have hcoordinate : lastGapOffset registers 3 + 1 = layoutEnd registers := by
    simp [lastGapOffset, layoutEnd, RegisterLayout.clockBoundary_eq,
      CounterLayout.boundaryPos]
    omega
  change FullTM0.Reaches (CounterControlNestingBridge.machine base c)
    ⟨logicalState base c growth source,
      atLogical growth T (layoutEnd registers)⟩
    ⟨searchState base c ⟨growth, source, validationSearchBase⟩,
      (atLogical growth T (layoutEnd registers)).move
        (orient growth .left)⟩ at hstep
  rw [hcoordinate.symm, CounterControlBridge.orient_eq_orientDirection,
    CounterControlBridge.atLogical_move_left] at hstep
  exact hstep

/-- With a mortal designated source computation, a represented logical state
whose clock exceeds the uniform search bound reaches a concrete halt. -/
theorem haltsFrom_logical_of_rule_clock_gt
    (base : Nat) (c : Nat.Partrec.Code)
    (bound : Nat)
    (hbound : ∀ {search : Search}
        {outer : FullTM0.Tape (Symbol numTags)} {distance : Nat},
      bound < distance →
      SearchGap (fun symbol => symbol = blankSymbol)
        (command base c search).target.Matches outer
        (command base c search).searchDirection distance →
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ((searchSystem base c).startCfg search outer))
    (growth : Turing.Dir) (source : Nat)
    (instruction : CounterMachine.Instruction)
    (hrule : (source, instruction) ∈ GlobalSourceProgram.program)
    (registers : Registers) (T : FullTM0.Tape (Symbol numTags))
    (hcore : CoreRepresents registers growth T)
    (hclock : bound < registers.clock) :
    FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
      ⟨logicalState base c growth source,
        atLogical growth T (layoutEnd registers)⟩ := by
  let raw := validationFirst growth source
  have hraw : raw ∈ rawCommands :=
    validationFirst_mem growth source instruction hrule
  let search : Search := CounterControlCommandAt.rawTag raw hraw
  let outer := atLogical growth T (lastGapOffset registers 3)
  have hget : rawCommands.get search = raw := by
    exact CounterControlCommandAt.rawCommands_get_rawTag raw hraw
  have hcommand : command base c search =
      compileRawCommand base c raw hraw := by
    rfl
  have hspec := CounterControlCommandAt.compileRawCommand_spec
    base c raw hraw
  have hgap0 := hcore.searchGap_adjacent_left (3 : Fin 4)
  have hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (command base c search).target.Matches outer
      (command base c search).searchDirection registers.clock := by
    rw [hcommand, hspec]
    change SearchGap (fun symbol => symbol = blankSymbol)
      (fun symbol => symbol = boundarySymbol (3 : Fin 5)) outer
      (orient growth .left) registers.clock
    simpa [outer, CounterControlBridge.orient_eq_orientDirection] using hgap0
  have hhalts := hbound hclock hgap
  have hprefix := reaches_validationFirst base c growth source instruction
    hrule registers T hcore
  apply FullTM0.HaltsFrom.of_reaches hprefix
  change FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
    ⟨CounterControlSearchSystem.commandOffset base c search, outer⟩ at hhalts
  have hoffset : CounterControlSearchSystem.commandOffset base c search =
      searchState base c ⟨growth, source, validationSearchBase⟩ := by
    unfold CounterControlSearchSystem.commandOffset
    rw [hget]
    rfl
  simpa [hoffset, outer, searchSystem, SearchSystem.startCfg] using hhalts

/-- One uniform clock bound rules out every sufficiently large represented
logical core when the designated computation is mortal. -/
theorem exists_bound_halts_logical_of_core_clock
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c) :
    ∃ bound : Nat,
      ∀ (growth : Turing.Dir) (cfg : CounterMachine.Cfg)
          (T : FullTM0.Tape (Symbol numTags)),
        cfg.state < logicalSpan →
        CoreRepresents cfg.registers growth T →
        bound < cfg.registers.clock →
        FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
          ⟨logicalState base c growth cfg.state,
            atLogical growth T (layoutEnd cfg.registers)⟩ := by
  rcases CounterControlLongSearchMortality.exists_bound_halts_search
      base c hmortal with ⟨bound, hbound⟩
  refine ⟨bound, ?_⟩
  intro growth cfg T hstate hcore hclock
  cases hlookup : lookupInstruction GlobalSourceProgram.program cfg.state with
  | none =>
      refine ⟨⟨logicalState base c growth cfg.state,
          atLogical growth T (layoutEnd cfg.registers)⟩,
        Relation.ReflTransGen.refl, ?_⟩
      apply CounterControlTerminalSemantics.machine_step_eq_none_of_counter_step_none
        base c growth cfg
          (atLogical growth T (layoutEnd cfg.registers)) hstate
      simp [CounterMachine.step, hlookup]
  | some instruction =>
      have hrule : (cfg.state, instruction) ∈
          GlobalSourceProgram.program :=
        CounterProgram.rule_mem_of_lookupInstruction_eq_some hlookup
      exact haltsFrom_logical_of_rule_clock_gt base c bound hbound
        growth cfg.state instruction hrule cfg.registers T hcore hclock

end

end CounterControlLargeClock
end Hooper
end Kari
end LeanWang
