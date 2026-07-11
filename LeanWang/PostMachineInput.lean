/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.PostMachine

/-!
# Post-machine simulation from an arbitrary supported configuration

`PostProgram.toTableProgram` was originally proved correct only for the blank
initial configuration.  Direct input rows need the same stuttering simulation
from a supplied finite-tape configuration.
-/

namespace LeanWang
namespace PostMachineInput

def postRun (program : PostProgram) (initial : PostID) (steps : Nat) : PostID :=
  Nat.iterate program.nextID steps initial

def postHalts (program : PostProgram) (initial : PostID) : Prop :=
  ∃ steps, (postRun program initial steps).state = none

def tableRun (program : PostProgram) (initial : PostID) (steps : Nat) : ID :=
  Nat.iterate program.toTableProgram.toMachine.nextID steps
    (PostProgram.tableIDOfPostID initial)

def tableHalts (program : PostProgram) (initial : PostID) : Prop :=
  ∃ steps, (tableRun program initial steps).state = program.toTableProgram.halt

@[simp] theorem postRun_zero (program : PostProgram) (initial : PostID) :
    postRun program initial 0 = initial :=
  rfl

@[simp] theorem postRun_succ (program : PostProgram) (initial : PostID)
    (steps : Nat) :
    postRun program initial (steps + 1) =
      program.nextID (postRun program initial steps) := by
  unfold postRun
  rw [Function.iterate_succ_apply']

@[simp] theorem tableRun_zero (program : PostProgram) (initial : PostID) :
    tableRun program initial 0 = PostProgram.tableIDOfPostID initial :=
  rfl

@[simp] theorem tableRun_succ (program : PostProgram) (initial : PostID)
    (steps : Nat) :
    tableRun program initial (steps + 1) =
      program.toTableProgram.toMachine.nextID (tableRun program initial steps) := by
  unfold tableRun
  rw [Function.iterate_succ_apply']

theorem postRun_tapeSupported {program : PostProgram} {initial : PostID}
    (supported : PostProgram.TapeSupported program initial) (steps : Nat) :
    PostProgram.TapeSupported program (postRun program initial steps) := by
  induction steps with
  | zero => simpa using supported
  | succ steps ih =>
      rw [postRun_succ]
      exact PostProgram.tapeSupported_nextID ih

theorem table_sync_or_halts
    (program : PostProgram) (initial : PostID)
    (supported : PostProgram.TapeSupported program initial) (steps : Nat) :
    (∃ tableSteps, tableRun program initial tableSteps =
        PostProgram.tableIDOfPostID (postRun program initial steps)) ∨
      tableHalts program initial := by
  induction steps with
  | zero => exact Or.inl ⟨0, rfl⟩
  | succ steps ih =>
      rcases ih with ⟨tableSteps, hsync⟩ | hhalts
      · let configuration := postRun program initial steps
        cases hstate : configuration.state with
        | none =>
            right
            have hstateRun : (postRun program initial steps).state = none := by
              simpa [configuration] using hstate
            exact ⟨tableSteps, by
              rw [hsync]
              rw [PostProgram.tableIDOfPostID_state_halt hstateRun]
              rfl⟩
        | some state =>
            cases hstep : program.step state
                (configuration.tape configuration.head) with
            | none =>
                right
                refine ⟨tableSteps + 1, ?_⟩
                rw [tableRun_succ, hsync]
                have hhalt :=
                  PostProgram.toTableProgram_toMachine_nextID_state_of_post_step_none
                    (P := program) (c := configuration) hstate hstep
                simpa [PostProgram.toTableProgram_halt] using hhalt
            | some action =>
                rcases action with ⟨next, statement⟩
                cases statement with
                | move direction =>
                    left
                    refine ⟨tableSteps + 1, ?_⟩
                    rw [tableRun_succ, hsync, postRun_succ]
                    exact
                      PostProgram.toTableProgram_toMachine_nextID_of_post_move_exact
                        (P := program) (c := configuration) hstate hstep
                | write symbol =>
                    left
                    refine ⟨tableSteps + 2, ?_⟩
                    rw [show tableSteps + 2 = tableSteps + 1 + 1 by omega,
                      tableRun_succ, tableRun_succ, hsync, postRun_succ]
                    exact
                      PostProgram.toTableProgram_toMachine_nextID_two_of_post_write_exact
                        (P := program) (c := configuration)
                        (postRun_tapeSupported supported steps) hstate hstep
      · exact Or.inr hhalts

theorem tableHalts_of_postHalts
    {program : PostProgram} {initial : PostID}
    (supported : PostProgram.TapeSupported program initial)
    (halts : postHalts program initial) : tableHalts program initial := by
  rcases halts with ⟨steps, hhalt⟩
  rcases table_sync_or_halts program initial supported steps with
    ⟨tableSteps, hsync⟩ | hhalts
  · exact ⟨tableSteps, by
      rw [hsync]
      simp [PostProgram.tableIDOfPostID_state_halt hhalt,
        PostProgram.toTableProgram_halt]⟩
  · exact hhalts

def TableRunRel (program : PostProgram) (initial : PostID) (id : ID) : Prop :=
  (∃ steps, id = PostProgram.tableIDOfPostID (postRun program initial steps)) ∨
    ∃ steps state next symbol,
      (postRun program initial steps).state = some state ∧
        program.step state
          ((postRun program initial steps).tape
            (postRun program initial steps).head) =
          some (next, PostStmt.write symbol) ∧
        id =
          { tape := Function.update (postRun program initial steps).tape
              (postRun program initial steps).head symbol
            head := (postRun program initial steps).head + 1
            state := PostProgram.tableWriteState next }

theorem tableRunRel_initial (program : PostProgram) (initial : PostID) :
    TableRunRel program initial (PostProgram.tableIDOfPostID initial) :=
  Or.inl ⟨0, rfl⟩

theorem tableRunRel_state_ne_halt_of_not_postHalts
    {program : PostProgram} {initial : PostID} {id : ID}
    (notHalts : ¬ postHalts program initial)
    (relation : TableRunRel program initial id) :
    id.state ≠ program.toTableProgram.toMachine.halt := by
  rcases relation with ⟨steps, rfl⟩ |
    ⟨steps, state, next, symbol, hstate, _hstep, rfl⟩
  · have hnotState : (postRun program initial steps).state ≠ none := by
      intro hhalt
      exact notHalts ⟨steps, hhalt⟩
    cases hrun : (postRun program initial steps).state with
    | none => exact False.elim (hnotState hrun)
    | some state =>
        simp [PostProgram.tableIDOfPostID_state_running hrun,
          PostProgram.toTableProgram_halt,
          (PostProgram.tableHalt_ne_tableRunState state).symm]
  · simp [PostProgram.toTableProgram_halt,
      (PostProgram.tableHalt_ne_tableWriteState next).symm]

theorem tableRunRel_next_of_not_postHalts
    {program : PostProgram} {initial : PostID} {id : ID}
    (supported : PostProgram.TapeSupported program initial)
    (notHalts : ¬ postHalts program initial)
    (relation : TableRunRel program initial id) :
    TableRunRel program initial (program.toTableProgram.toMachine.nextID id) := by
  rcases relation with ⟨steps, rfl⟩ |
    ⟨steps, state, next, symbol, hstate, hstep, rfl⟩
  · let configuration := postRun program initial steps
    have hnotState : configuration.state ≠ none := by
      intro hhalt
      exact notHalts ⟨steps, by simpa [configuration] using hhalt⟩
    cases hstate : configuration.state with
    | none => exact False.elim (hnotState hstate)
    | some state =>
        cases hstep : program.step state
            (configuration.tape configuration.head) with
        | none =>
            have hnextHalt : (postRun program initial (steps + 1)).state = none := by
              rw [postRun_succ]
              change (program.nextID configuration).state = none
              rw [PostProgram.nextID_of_running hstate]
              simp [hstep]
            exact False.elim (notHalts ⟨steps + 1, hnextHalt⟩)
        | some action =>
            rcases action with ⟨next, statement⟩
            cases statement with
            | move direction =>
                left
                refine ⟨steps + 1, ?_⟩
                rw [postRun_succ]
                exact
                  PostProgram.toTableProgram_toMachine_nextID_of_post_move_exact
                    (P := program) (c := configuration) hstate hstep
            | write symbol =>
                right
                exact ⟨steps, state, next, symbol, by simpa [configuration] using hstate,
                  by simpa [configuration] using hstep,
                  PostProgram.toTableProgram_toMachine_nextID_of_post_write_start
                    (P := program) (c := configuration) hstate hstep⟩
  · left
    refine ⟨steps + 1, ?_⟩
    rw [postRun_succ]
    have hsymbol : symbol ∈ PostProgram.tableSupportedSymbols program :=
      PostProgram.symbol_mem_tableSupportedSymbols
        (PostProgram.symbol_mem_of_step_eq_some_write hstep)
    have hreturn :
        (Function.update (postRun program initial steps).tape
          (postRun program initial steps).head symbol)
          ((postRun program initial steps).head + 1) ∈
            PostProgram.tableSupportedSymbols program :=
      PostProgram.tapeSupported_update
        (postRun_tapeSupported supported steps) hsymbol _
    rw [PostProgram.toTableProgram_toMachine_nextID_of_post_write_return
      (P := program) (q := state)
      (a := (postRun program initial steps).tape
        (postRun program initial steps).head)
      (b := symbol) hstep hreturn]
    rw [PostProgram.nextID_of_running hstate]
    simp [hstep, PostProgram.applyStmt, PostProgram.tableIDOfPostID]

theorem tableRunRel_run_of_not_postHalts
    {program : PostProgram} {initial : PostID}
    (supported : PostProgram.TapeSupported program initial)
    (notHalts : ¬ postHalts program initial) (steps : Nat) :
    TableRunRel program initial (tableRun program initial steps) := by
  induction steps with
  | zero => exact tableRunRel_initial program initial
  | succ steps ih =>
      rw [tableRun_succ]
      exact tableRunRel_next_of_not_postHalts supported notHalts ih

theorem postHalts_of_tableHalts
    {program : PostProgram} {initial : PostID}
    (supported : PostProgram.TapeSupported program initial)
    (halts : tableHalts program initial) : postHalts program initial := by
  by_contra notHalts
  rcases halts with ⟨steps, hhalt⟩
  exact tableRunRel_state_ne_halt_of_not_postHalts notHalts
    (tableRunRel_run_of_not_postHalts supported notHalts steps) hhalt

theorem tableHalts_iff_postHalts
    {program : PostProgram} {initial : PostID}
    (supported : PostProgram.TapeSupported program initial) :
    tableHalts program initial ↔ postHalts program initial :=
  ⟨postHalts_of_tableHalts supported, tableHalts_of_postHalts supported⟩

end PostMachineInput
end LeanWang
