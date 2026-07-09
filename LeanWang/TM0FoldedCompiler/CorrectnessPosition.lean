/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedCompiler.CorrectnessHalting
import LeanWang.TM0FoldedProgram.ProgramData

/-!
Semantic correctness for the generated position-coded folded program.
-/

namespace LeanWang

namespace TM0FoldedCompiler

open TM0Route

private theorem nextID_of_step_eq_some {P : PostProgram} {c : PostID}
    {q q' : Nat} {stmt : PostStmt}
    (hstate : c.state = some q)
    (hstep : P.step q (c.tape c.head) = some (q', stmt)) :
    P.nextID c =
      let r := PostProgram.applyStmt stmt c.tape c.head
      { tape := r.1, head := r.2, state := some q' } := by
  rw [PostProgram.nextID_of_running (P := P) (c := c) (q := q) hstate, hstep]

theorem positionProgramData_step_initReturn_zero
    (tc : Turing.ToPartrec.Code) {read : Nat}
    (hread : read ∈ foldedSymbolList) :
    (positionProgramData tc).step (initReturnState 0) read =
      some (foldedSimStartState tc, PostStmt.write read) := by
  have horigin :
      initWriteOriginRow.matchesInput (initReturnState 0) read = false := by
    unfold initWriteOriginRow
    exact mkRow_matchesInput_of_state_ne_data
      (initWriteOriginState_ne_initReturnState 0)
  have hmove := initMoveRightRows_find?_eq_none_of_initReturnState_data 0 read
  have hwrite := initWriteRightRows_find?_eq_none_of_initReturnState_data 0 read
  have hreturn := initReturnRowsData_find?_of_mem
    (i := 0) (read := read)
    (by
      unfold initReturnIndexList
      exact List.mem_cons_self)
    hread
  have hfind :
      (positionProgramData tc).transition? (initReturnState 0) read =
        some (initReturnRow tc 0 read) := by
    unfold PostProgram.transition?
    change (initRowsData ++
        simRowsOfStepData (simStepDataByLabelIndexWithPositionCode tc)).find?
          (fun e => e.matchesInput (initReturnState 0) read) =
        some (initReturnRow tc 0 read)
    apply program_find?_append_of_eq_some
    unfold initRowsData
    simp only [List.find?_cons]
    rw [horigin]
    have htail :
        (initMoveRightRows ++ (initWriteRightRows ++ initReturnRowsData)).find?
            (fun e => e.matchesInput (initReturnState 0) read) =
          some (initReturnRow tc 0 read) := by
      rw [program_find?_append_of_eq_none hmove]
      rw [program_find?_append_of_eq_none hwrite]
      exact hreturn
    exact htail
  have hnext : foldedSimStartState tc ∈ foldedStateList tc :=
    foldedSimStartState_mem_states tc
  have hnextCode : foldedSimStartStateCode ∈ foldedStateList tc := by
    simpa [foldedSimStartState] using hnext
  simp [PostProgram.step, hfind, initReturnRow, mkRow, foldedSimStartState,
    hnextCode, hread]

theorem positionProgramData_nextID_initial (tc : Turing.ToPartrec.Code) :
    (positionProgramData tc).nextID (positionProgramData tc).initialID =
      { tape := Function.update (fun _ => foldedBlank) 0
          (foldedOriginSymbol (inputSymbol 0)),
        head := 0,
        state := some (initReturnState 0) } := by
  let id := (positionProgramData tc).initialID
  have hstate : id.state = some foldedStartState := rfl
  have hstep :
      (positionProgramData tc).step foldedStartState (id.tape id.head) =
        some (nextAfterOrigin, PostStmt.write (foldedOriginSymbol (inputSymbol 0))) := by
    exact positionProgramData_step_start_blank tc
  change (positionProgramData tc).nextID id =
      { tape := Function.update (fun _ => foldedBlank) 0
          (foldedOriginSymbol (inputSymbol 0)),
        head := 0,
        state := some (initReturnState 0) }
  rw [nextID_of_step_eq_some hstate hstep]
  dsimp [id, PostProgram.initialID, PostProgram.applyStmt]
  simp [nextAfterOrigin_eq_initReturnState_zero]

theorem positionProgramData_runEmpty_one (tc : Turing.ToPartrec.Code) :
    (positionProgramData tc).runEmpty 1 =
      { tape := Function.update (fun _ => foldedBlank) 0
          (foldedOriginSymbol (inputSymbol 0)),
        head := 0,
        state := some (initReturnState 0) } := by
  rw [show 1 = 0 + 1 by rfl, PostProgram.runEmpty_succ, PostProgram.runEmpty_zero]
  exact positionProgramData_nextID_initial tc

theorem positionProgramData_nextID_after_origin (tc : Turing.ToPartrec.Code) :
    (positionProgramData tc).nextID
        { tape := Function.update (fun _ => foldedBlank) 0
            (foldedOriginSymbol (inputSymbol 0)),
          head := 0,
          state := some (initReturnState 0) } =
      { tape := Function.update (fun _ => foldedBlank) 0
          (foldedOriginSymbol (inputSymbol 0)),
        head := 0,
        state := some (foldedSimStartState tc) } := by
  let id : PostID :=
    { tape := Function.update (fun _ => foldedBlank) 0
        (foldedOriginSymbol (inputSymbol 0)),
      head := 0,
      state := some (initReturnState 0) }
  have hstate : id.state = some (initReturnState 0) := rfl
  have hread :
      id.tape id.head = foldedOriginSymbol (inputSymbol 0) := by
    simp [id]
  have hmem :
      foldedOriginSymbol (inputSymbol 0) ∈ foldedSymbolList :=
    foldedSymbolCode_mem_symbols true default (inputSymbol 0)
  have hstep :
      (positionProgramData tc).step (initReturnState 0) (id.tape id.head) =
        some (foldedSimStartState tc, PostStmt.write (id.tape id.head)) := by
    rw [hread]
    exact positionProgramData_step_initReturn_zero tc hmem
  change (positionProgramData tc).nextID id =
      { tape := Function.update (fun _ => foldedBlank) 0
          (foldedOriginSymbol (inputSymbol 0)),
        head := 0,
        state := some (foldedSimStartState tc) }
  rw [nextID_of_step_eq_some hstate hstep]
  simp [id, PostProgram.applyStmt]

theorem positionProgramData_runEmpty_two (tc : Turing.ToPartrec.Code) :
    (positionProgramData tc).runEmpty 2 =
      { tape := Function.update (fun _ => foldedBlank) 0
          (foldedOriginSymbol (inputSymbol 0)),
        head := 0,
        state := some (foldedSimStartState tc) } := by
  rw [show 2 = 1 + 1 by rfl, PostProgram.runEmpty_succ,
    positionProgramData_runEmpty_one]
  exact positionProgramData_nextID_after_origin tc

theorem FoldedConfigRel_runEmpty_two_position (tc : Turing.ToPartrec.Code) :
    FoldedConfigRel tc
      (Turing.TM0.init (Λ := SourceLabel tc) TM0Route.partrecStartedTM0Input)
      ((positionProgramData tc).runEmpty 2) := by
  rw [positionProgramData_runEmpty_two]
  refine ⟨FoldSide.right, ?_, ?_, ?_⟩
  · simpa [Turing.TM0.init] using default_mem_partrecStartedTM0LabelList tc
  · simp [foldedSimStartState, foldedSimStartStateCode, foldedSimStateCode,
      foldedSimStateOfCode, TM0Route.partrecStartedTM0Start,
      TM0FiniteCompiler.stateCode_default tc, Turing.TM0.init]
  · exact FoldedTapeRel_init_right_zero tc

theorem positionProgramData_nextID_eq_program_nextID_of_step
    {tc : Turing.ToPartrec.Code}
    {cfg cfg' : Turing.TM0.Cfg SourceSymbol (SourceLabel tc)} {id : PostID}
    (hrel : FoldedConfigRel tc cfg id)
    (hstep :
      Turing.TM0.step (TM0Route.partrecStartedTM0Machine tc) cfg = some cfg') :
    (positionProgramData tc).nextID id = (program tc).nextID id := by
  rcases hrel with ⟨side, hq, hstate, htape⟩
  let marked := decide (id.head = 0)
  let left := cfg.Tape.nth (sourceOffset side id.head (leftAbs id.head))
  let right := cfg.Tape.nth (sourceOffset side id.head (rightAbs id.head))
  let read := foldedSymbolCode marked left right
  have hread :
      foldedRead side left right = cfg.Tape.head := by
    unfold left right
    exact foldedRead_active_cell cfg.Tape side id.head
  have hcell : id.tape id.head = read := by
    rw [htape id.head]
    simp [foldedCellOfTapeAt, marked, left, right, read]
  cases hM :
      TM0Route.partrecStartedTM0Machine tc cfg.q cfg.Tape.head with
  | none =>
      simp [Turing.TM0.step, hM] at hstep
  | some next =>
      rcases next with ⟨q', stmt⟩
      have hstep' :
          TM0Route.partrecStartedTM0Machine tc cfg.q (foldedRead side left right) =
            some (q', stmt) := by
        simpa [hread] using hM
      have hpos := positionProgramData_step_sim_of_step
        (tc := tc) (q := cfg.q) (q' := q') (side := side)
        (marked := marked) (left := left) (right := right)
        (stmt := stmt) hq hstep'
      have hprog := program_step_sim_of_step
        (tc := tc) (q := cfg.q) (q' := q') (side := side)
        (marked := marked) (left := left) (right := right)
        (stmt := stmt) hq hstep'
      simp [PostProgram.nextID, hstate, hcell, hpos, hprog, read]

theorem FoldedConfigRel_step_position
    {tc : Turing.ToPartrec.Code}
    {cfg cfg' : Turing.TM0.Cfg SourceSymbol (SourceLabel tc)} {id : PostID}
    (hrel : FoldedConfigRel tc cfg id)
    (hstep :
      Turing.TM0.step (TM0Route.partrecStartedTM0Machine tc) cfg = some cfg') :
    FoldedConfigRel tc cfg' ((positionProgramData tc).nextID id) := by
  have hcanonical := FoldedConfigRel_step (tc := tc) (cfg := cfg) (cfg' := cfg')
    (id := id) hrel hstep
  have hnext := positionProgramData_nextID_eq_program_nextID_of_step
    (tc := tc) (cfg := cfg) (cfg' := cfg') (id := id) hrel hstep
  simpa [hnext] using hcanonical

theorem FoldedConfigRel_halt_step_position
    {tc : Turing.ToPartrec.Code}
    {cfg : Turing.TM0.Cfg SourceSymbol (SourceLabel tc)} {id : PostID}
    (hrel : FoldedConfigRel tc cfg id)
    (hstep :
      Turing.TM0.step (TM0Route.partrecStartedTM0Machine tc) cfg = none) :
    ((positionProgramData tc).nextID id).state = none := by
  rcases hrel with ⟨side, hq, hstate, htape⟩
  let marked := decide (id.head = 0)
  let left := cfg.Tape.nth (sourceOffset side id.head (leftAbs id.head))
  let right := cfg.Tape.nth (sourceOffset side id.head (rightAbs id.head))
  let read := foldedSymbolCode marked left right
  have hread :
      foldedRead side left right = cfg.Tape.head := by
    unfold left right
    exact foldedRead_active_cell cfg.Tape side id.head
  have hmachine :
      TM0Route.partrecStartedTM0Machine tc cfg.q cfg.Tape.head = none := by
    cases hM : TM0Route.partrecStartedTM0Machine tc cfg.q cfg.Tape.head with
    | none => simp
    | some next =>
        simp [Turing.TM0.step, hM] at hstep
  have hmachine' :
      TM0Route.partrecStartedTM0Machine tc cfg.q (foldedRead side left right) =
        none := by
    simpa [hread] using hmachine
  have hcell : id.tape id.head = read := by
    rw [htape id.head]
    simp [foldedCellOfTapeAt, marked, left, right, read]
  have hprogramStep := positionProgramData_step_sim_eq_none_of_no_step
    (tc := tc) (q := cfg.q) (side := side) (marked := marked)
    (left := left) (right := right) hq hmachine'
  simp [PostProgram.nextID, hstate, hcell, hprogramStep, read]

theorem FoldedConfigRel_reaches_position
    {tc : Turing.ToPartrec.Code}
    {cfg cfg' : Turing.TM0.Cfg SourceSymbol (SourceLabel tc)} {id : PostID}
    (hrel : FoldedConfigRel tc cfg id)
    (hreach :
      StateTransition.Reaches
        (Turing.TM0.step (TM0Route.partrecStartedTM0Machine tc)) cfg cfg') :
    ∃ n : Nat,
      FoldedConfigRel tc cfg' (Nat.iterate (positionProgramData tc).nextID n id) := by
  induction hreach with
  | refl =>
      exact ⟨0, hrel⟩
  | tail _ hstep ih =>
      rcases ih with ⟨n, hn⟩
      refine ⟨n + 1, ?_⟩
      rw [Function.iterate_succ_apply']
      exact FoldedConfigRel_step_position hn (by simpa using hstep)

theorem FoldedConfigRel_reaches_halt_position
    {tc : Turing.ToPartrec.Code}
    {cfg cfg' : Turing.TM0.Cfg SourceSymbol (SourceLabel tc)} {id : PostID}
    (hrel : FoldedConfigRel tc cfg id)
    (hreach :
      StateTransition.Reaches
        (Turing.TM0.step (TM0Route.partrecStartedTM0Machine tc)) cfg cfg')
    (hhalt :
      Turing.TM0.step (TM0Route.partrecStartedTM0Machine tc) cfg' = none) :
    ∃ n : Nat, (Nat.iterate (positionProgramData tc).nextID n id).state = none := by
  rcases FoldedConfigRel_reaches_position (tc := tc) hrel hreach with ⟨n, hn⟩
  refine ⟨n + 1, ?_⟩
  rw [Function.iterate_succ_apply']
  exact FoldedConfigRel_halt_step_position hn hhalt

theorem positionProgramData_runEmpty_add_two
    (tc : Turing.ToPartrec.Code) (n : Nat) :
    (positionProgramData tc).runEmpty (n + 2) =
      Nat.iterate (positionProgramData tc).nextID n
        ((positionProgramData tc).runEmpty 2) := by
  unfold PostProgram.runEmpty
  rw [Function.iterate_add_apply]

theorem positionProgramData_haltsEmpty_of_tm0_eval_dom
    (tc : Turing.ToPartrec.Code) :
    (Turing.TM0.eval (TM0Route.partrecStartedTM0Machine tc)
      TM0Route.partrecStartedTM0Input).Dom →
      (positionProgramData tc).HaltsEmpty := by
  intro hdomEval
  let step :=
    Turing.TM0.step (TM0Route.partrecStartedTM0Machine tc)
  let initCfg :=
    Turing.TM0.init (Λ := SourceLabel tc) TM0Route.partrecStartedTM0Input
  have hdomState : (StateTransition.eval step initCfg).Dom := by
    dsimp [step, initCfg] at *
    rw [Turing.TM0.eval] at hdomEval
    exact (TM0Route.part_dom_map_iff (fun c => c.Tape.right₀)
      (StateTransition.eval
        (Turing.TM0.step (TM0Route.partrecStartedTM0Machine tc))
        (Turing.TM0.init (Λ := SourceLabel tc)
          TM0Route.partrecStartedTM0Input))).1 hdomEval
  let haltCfg := (StateTransition.eval step initCfg).get hdomState
  have hmem : haltCfg ∈ StateTransition.eval step initCfg :=
    Part.get_mem hdomState
  rcases StateTransition.mem_eval.1 hmem with ⟨hreach, hhalt⟩
  rcases FoldedConfigRel_reaches_halt_position
      (tc := tc) (cfg := initCfg) (cfg' := haltCfg)
      (id := (positionProgramData tc).runEmpty 2)
      (FoldedConfigRel_runEmpty_two_position tc) hreach hhalt with
    ⟨n, hn⟩
  refine ⟨n + 2, ?_⟩
  rw [positionProgramData_runEmpty_add_two]
  exact hn

theorem tm0_reaches_halt_of_positionProgramData_halts
    {tc : Turing.ToPartrec.Code}
    {cfg : Turing.TM0.Cfg SourceSymbol (SourceLabel tc)} {id : PostID}
    (hrel : FoldedConfigRel tc cfg id) :
    ∀ n : Nat,
      (Nat.iterate (positionProgramData tc).nextID n id).state = none →
        ∃ cfg' : Turing.TM0.Cfg SourceSymbol (SourceLabel tc),
          StateTransition.Reaches
            (Turing.TM0.step (TM0Route.partrecStartedTM0Machine tc)) cfg cfg' ∧
          Turing.TM0.step (TM0Route.partrecStartedTM0Machine tc) cfg' = none
  | 0, hhalt => by
      rcases hrel with ⟨side, _hq, hstate, _htape⟩
      simp [hstate] at hhalt
  | n + 1, hhalt => by
      cases hstep :
          Turing.TM0.step (TM0Route.partrecStartedTM0Machine tc) cfg with
      | none =>
          exact ⟨cfg, Relation.ReflTransGen.refl, hstep⟩
      | some cfg₁ =>
          have hrel₁ := FoldedConfigRel_step_position hrel hstep
          have hhalt₁ :
              (Nat.iterate (positionProgramData tc).nextID n
                  ((positionProgramData tc).nextID id)).state =
                none := by
            simpa [Function.iterate_succ_apply] using hhalt
          rcases tm0_reaches_halt_of_positionProgramData_halts hrel₁ n hhalt₁ with
            ⟨cfg', hreach, hterminal⟩
          refine ⟨cfg', ?_, hterminal⟩
          exact Relation.ReflTransGen.head (by simpa using hstep) hreach

theorem tm0_eval_dom_of_positionProgramData_haltsEmpty (tc : Turing.ToPartrec.Code) :
    (positionProgramData tc).HaltsEmpty →
      (Turing.TM0.eval (TM0Route.partrecStartedTM0Machine tc)
        TM0Route.partrecStartedTM0Input).Dom := by
  rintro ⟨k, hhalt⟩
  cases k with
  | zero =>
      simp [PostProgram.runEmpty_zero, PostProgram.initialID] at hhalt
  | succ k =>
      cases k with
      | zero =>
          rw [show 1 = 1 by rfl, positionProgramData_runEmpty_one] at hhalt
          simp at hhalt
      | succ n =>
          have hhalt' : ((positionProgramData tc).runEmpty (n + 2)).state = none := by
            rw [show n + 2 = Nat.succ (Nat.succ n) by omega]
            exact hhalt
          have hhaltIter :
              (Nat.iterate (positionProgramData tc).nextID n
                  ((positionProgramData tc).runEmpty 2)).state =
                none := by
            rw [positionProgramData_runEmpty_add_two] at hhalt'
            exact hhalt'
          let step :=
            Turing.TM0.step (TM0Route.partrecStartedTM0Machine tc)
          let initCfg :=
            Turing.TM0.init (Λ := SourceLabel tc) TM0Route.partrecStartedTM0Input
          rcases tm0_reaches_halt_of_positionProgramData_halts
              (tc := tc) (cfg := initCfg)
              (id := (positionProgramData tc).runEmpty 2)
              (FoldedConfigRel_runEmpty_two_position tc) n hhaltIter with
            ⟨cfg', hreach, hterminal⟩
          have hmem : cfg' ∈ StateTransition.eval step initCfg := by
            exact StateTransition.mem_eval.2 ⟨hreach, hterminal⟩
          have hdomState : (StateTransition.eval step initCfg).Dom :=
            Part.dom_iff_mem.2 ⟨cfg', hmem⟩
          rw [Turing.TM0.eval]
          exact (TM0Route.part_dom_map_iff (fun c => c.Tape.right₀)
            (StateTransition.eval
              (Turing.TM0.step (TM0Route.partrecStartedTM0Machine tc))
              (Turing.TM0.init (Λ := SourceLabel tc)
                TM0Route.partrecStartedTM0Input))).2 hdomState

theorem positionProgramData_haltsEmpty_iff_tm0_eval_dom
    (tc : Turing.ToPartrec.Code) :
    (positionProgramData tc).HaltsEmpty ↔
      (Turing.TM0.eval (TM0Route.partrecStartedTM0Machine tc)
        TM0Route.partrecStartedTM0Input).Dom := by
  exact ⟨tm0_eval_dom_of_positionProgramData_haltsEmpty tc,
    positionProgramData_haltsEmpty_of_tm0_eval_dom tc⟩

end TM0FoldedCompiler

end LeanWang
