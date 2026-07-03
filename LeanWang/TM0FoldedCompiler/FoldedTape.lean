/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedCompiler.ProgramSteps

/-!
Folded tape/configuration relation and one-step simulation lemmas.
-/

namespace LeanWang

namespace TM0FoldedCompiler

open TM0Route

/-!
## Folded semantic relation

Mathlib's `TM0.Cfg.Tape` is centered at the simulated head, while the local
one-sided program keeps a fixed folded origin. The local head and folded side
therefore determine the simulated head's absolute position in the fixed folded
coordinate system.
-/
def rightAbs (i : Nat) : Int :=
  i

def leftAbs (i : Nat) : Int :=
  -((i : Int) + 1)

def activeAbs : FoldSide → Nat → Int
  | FoldSide.right, h => rightAbs h
  | FoldSide.left, h => leftAbs h

def sourceOffset (side : FoldSide) (head : Nat) (abs : Int) : Int :=
  abs - activeAbs side head

def foldedCellOfTapeAt (T : Turing.Tape SourceSymbol)
    (side : FoldSide) (head i : Nat) : Nat :=
  foldedSymbolCode (decide (i = 0))
    (T.nth (sourceOffset side head (leftAbs i)))
    (T.nth (sourceOffset side head (rightAbs i)))

def FoldedTapeRel (T : Turing.Tape SourceSymbol)
    (side : FoldSide) (head : Nat) (tape : Nat → Nat) : Prop :=
  ∀ i : Nat, tape i = foldedCellOfTapeAt T side head i

def FoldedConfigRel (tc : Turing.ToPartrec.Code)
    (cfg : Turing.TM0.Cfg SourceSymbol (SourceLabel tc)) (id : PostID) : Prop :=
  ∃ side : FoldSide,
    cfg.q ∈ TM0Route.partrecStartedTM0LabelList tc ∧
      id.state = some (foldedSimStateCode tc side cfg.q) ∧
      FoldedTapeRel cfg.Tape side id.head id.tape

@[simp]
theorem sourceOffset_right_head (h : Nat) :
    sourceOffset FoldSide.right h (rightAbs h) = 0 := by
  simp [sourceOffset, activeAbs, rightAbs]

@[simp]
theorem sourceOffset_left_head (h : Nat) :
    sourceOffset FoldSide.left h (leftAbs h) = 0 := by
  simp [sourceOffset, activeAbs, leftAbs]

theorem foldedRead_active_cell (T : Turing.Tape SourceSymbol)
    (side : FoldSide) (head : Nat) :
    foldedRead side
        (T.nth (sourceOffset side head (leftAbs head)))
        (T.nth (sourceOffset side head (rightAbs head))) =
      T.head := by
  cases side <;> simp [foldedRead, Turing.Tape.nth_zero]

theorem sourceOffset_right_left_head_ne_zero (head : Nat) :
    sourceOffset FoldSide.right head (leftAbs head) ≠ 0 := by
  simp [sourceOffset, activeAbs, rightAbs, leftAbs]
  omega

theorem sourceOffset_left_right_head_ne_zero (head : Nat) :
    sourceOffset FoldSide.left head (rightAbs head) ≠ 0 := by
  simp [sourceOffset, activeAbs, rightAbs, leftAbs]
  omega

set_option linter.flexible false in
set_option linter.unusedSimpArgs false in
theorem foldedCellOfTapeAt_write_active (T : Turing.Tape SourceSymbol)
    (side : FoldSide) (head : Nat) (new : SourceSymbol) :
    foldedCellOfTapeAt (T.write new) side head head =
      foldedWriteForStmt side (decide (head = 0)) new
        (T.nth (sourceOffset side head (leftAbs head)))
        (T.nth (sourceOffset side head (rightAbs head))) := by
  cases side
  · by_cases h : head = 0
    · simp [foldedCellOfTapeAt, foldedWriteForStmt, foldedWrite, foldedWriteMarked,
        sourceOffset_left_head, sourceOffset_left_right_head_ne_zero, h]
      change foldedSymbolCode true new
          (T.nth (sourceOffset FoldSide.left 0 (rightAbs 0))) =
        foldedSymbolCode true new
          (T.nth (sourceOffset FoldSide.left 0 (rightAbs 0)))
      rfl
    · simp [foldedCellOfTapeAt, foldedWriteForStmt, foldedWrite, foldedWriteMarked,
        sourceOffset_left_head, sourceOffset_left_right_head_ne_zero, h]
      change foldedSymbolCode false new
          (T.nth (sourceOffset FoldSide.left head (rightAbs head))) =
        foldedSymbolCode false new
          (T.nth (sourceOffset FoldSide.left head (rightAbs head)))
      rfl
  · by_cases h : head = 0
    · simp [foldedCellOfTapeAt, foldedWriteForStmt, foldedWrite, foldedWriteMarked,
        sourceOffset_right_head, sourceOffset_right_left_head_ne_zero, h]
      change foldedSymbolCode true
          (T.nth (sourceOffset FoldSide.right 0 (leftAbs 0))) new =
        foldedSymbolCode true
          (T.nth (sourceOffset FoldSide.right 0 (leftAbs 0))) new
      rfl
    · simp [foldedCellOfTapeAt, foldedWriteForStmt, foldedWrite, foldedWriteMarked,
        sourceOffset_right_head, sourceOffset_right_left_head_ne_zero, h]
      change foldedSymbolCode false
          (T.nth (sourceOffset FoldSide.right head (leftAbs head))) new =
        foldedSymbolCode false
          (T.nth (sourceOffset FoldSide.right head (leftAbs head))) new
      rfl

theorem sourceOffset_left_ne_zero_of_ne_head
    (side : FoldSide) {head i : Nat} (h : i ≠ head) :
    sourceOffset side head (leftAbs i) ≠ 0 := by
  cases side
  · simp [sourceOffset, activeAbs, leftAbs]
    omega
  · simp [sourceOffset, activeAbs, leftAbs, rightAbs]
    omega

theorem sourceOffset_right_ne_zero_of_ne_head
    (side : FoldSide) {head i : Nat} (h : i ≠ head) :
    sourceOffset side head (rightAbs i) ≠ 0 := by
  cases side
  · simp [sourceOffset, activeAbs, rightAbs, leftAbs]
    omega
  · simp [sourceOffset, activeAbs, rightAbs]
    omega

theorem foldedCellOfTapeAt_write_inactive (T : Turing.Tape SourceSymbol)
    (side : FoldSide) {head i : Nat} (new : SourceSymbol) (h : i ≠ head) :
    foldedCellOfTapeAt (T.write new) side head i =
      foldedCellOfTapeAt T side head i := by
  have hleft := sourceOffset_left_ne_zero_of_ne_head side h
  have hright := sourceOffset_right_ne_zero_of_ne_head side h
  simp [foldedCellOfTapeAt, hleft, hright]

theorem FoldedTapeRel_write
    {T : Turing.Tape SourceSymbol} {side : FoldSide} {head : Nat} {tape : Nat → Nat}
    (new : SourceSymbol)
    (hrel : FoldedTapeRel T side head tape) :
    FoldedTapeRel (T.write new) side head
      (Function.update tape head
        (foldedWriteForStmt side (decide (head = 0)) new
          (T.nth (sourceOffset side head (leftAbs head)))
          (T.nth (sourceOffset side head (rightAbs head))))) := by
  intro i
  by_cases hi : i = head
  · subst i
    simp [Function.update_self, foldedCellOfTapeAt_write_active]
  · rw [Function.update_of_ne hi]
    rw [hrel i]
    exact (foldedCellOfTapeAt_write_inactive T side new hi).symm

set_option linter.flexible false in
theorem FoldedConfigRel_write_step
    {tc : Turing.ToPartrec.Code}
    {cfg : Turing.TM0.Cfg SourceSymbol (SourceLabel tc)} {id : PostID}
    {q' : SourceLabel tc} {new : SourceSymbol}
    (hrel : FoldedConfigRel tc cfg id)
    (hstep :
      TM0Route.partrecStartedTM0Machine tc cfg.q cfg.Tape.head =
        some (q', Turing.TM0.Stmt.write new)) :
    FoldedConfigRel tc
      { q := q', Tape := cfg.Tape.write new }
      ((program tc).nextID id) := by
  rcases hrel with ⟨side, hq, hstate, htape⟩
  let left := cfg.Tape.nth (sourceOffset side id.head (leftAbs id.head))
  let right := cfg.Tape.nth (sourceOffset side id.head (rightAbs id.head))
  have hread :
      foldedRead side left right = cfg.Tape.head := by
    unfold left right
    exact foldedRead_active_cell cfg.Tape side id.head
  have hstep' :
      TM0Route.partrecStartedTM0Machine tc cfg.q (foldedRead side left right) =
        some (q', Turing.TM0.Stmt.write new) := by
    simpa [hread] using hstep
  have hcell :
      id.tape id.head = foldedSymbolCode (decide (id.head = 0)) left right := by
    rw [htape id.head]
    simp [foldedCellOfTapeAt, left, right]
  have hprogramStep := program_step_sim_of_step
    (tc := tc) (q := cfg.q) (q' := q') (side := side)
    (marked := decide (id.head = 0)) (left := left) (right := right)
    (stmt := Turing.TM0.Stmt.write new) hq hstep'
  simp [PostProgram.nextID, hstate, hcell, hprogramStep, PostProgram.applyStmt,
    simRowOfStep, left, right]
  refine ⟨side, ?_, rfl, ?_⟩
  · have hqset : cfg.q ∈ TM0Route.partrecStartedTM0Labels tc :=
      (TM0Route.mem_partrecStartedTM0LabelList tc cfg.q).1 hq
    have hq'set : q' ∈ TM0Route.partrecStartedTM0Labels tc :=
      TM0FiniteCompiler.next_label_mem_of_step hqset hstep
    exact (TM0Route.mem_partrecStartedTM0LabelList tc q').2 hq'set
  · exact FoldedTapeRel_write new htape

theorem activeAbs_move_right_regular {head : Nat} (h : head ≠ 0) :
    activeAbs FoldSide.left (head - 1) =
      activeAbs FoldSide.left head + 1 := by
  cases head with
  | zero => exact False.elim (h rfl)
  | succ n =>
      simp [activeAbs, leftAbs]

theorem activeAbs_move_left_regular (head : Nat) :
    activeAbs FoldSide.left (head + 1) =
      activeAbs FoldSide.left head - 1 := by
  simp [activeAbs, leftAbs]
  omega

theorem activeAbs_move_right_from_origin :
    activeAbs FoldSide.right 0 =
      activeAbs FoldSide.left 0 + 1 := by
  simp [activeAbs, leftAbs, rightAbs]

theorem activeAbs_move_left_from_origin :
    activeAbs FoldSide.left 0 =
      activeAbs FoldSide.right 0 - 1 := by
  simp [activeAbs, leftAbs, rightAbs]

theorem activeAbs_move_right_right (head : Nat) :
    activeAbs FoldSide.right (head + 1) =
      activeAbs FoldSide.right head + 1 := by
  simp [activeAbs, rightAbs]

theorem activeAbs_move_left_right {head : Nat} (h : head ≠ 0) :
    activeAbs FoldSide.right (head - 1) =
      activeAbs FoldSide.right head - 1 := by
  cases head with
  | zero => exact False.elim (h rfl)
  | succ n =>
      simp [activeAbs, rightAbs]

theorem activeAbs_foldedMoveHead
    (side : FoldSide) (head : Nat) (dir : Turing.Dir) :
    activeAbs (foldedMoveNextSide side (decide (head = 0)) dir)
        (foldedMoveHead side (decide (head = 0)) head dir) =
      activeAbs side head + match dir with
        | Turing.Dir.left => -1
        | Turing.Dir.right => 1 := by
  cases side <;> cases dir <;> by_cases h : head = 0
  all_goals
    subst_vars
    simp_all [foldedMoveNextSide, foldedMoveHead, activeAbs, leftAbs, rightAbs]
    try omega

theorem sourceOffset_foldedMoveHead
    (side : FoldSide) (head : Nat) (dir : Turing.Dir) (abs : Int) :
    sourceOffset (foldedMoveNextSide side (decide (head = 0)) dir)
        (foldedMoveHead side (decide (head = 0)) head dir) abs =
      sourceOffset side head abs -
        match dir with
        | Turing.Dir.left => -1
        | Turing.Dir.right => 1 := by
  unfold sourceOffset
  rw [activeAbs_foldedMoveHead]
  cases dir <;> omega

theorem foldedCellOfTapeAt_move (T : Turing.Tape SourceSymbol)
    (side : FoldSide) (head i : Nat) (dir : Turing.Dir) :
    foldedCellOfTapeAt (T.move dir)
        (foldedMoveNextSide side (decide (head = 0)) dir)
        (foldedMoveHead side (decide (head = 0)) head dir) i =
      foldedCellOfTapeAt T side head i := by
  cases dir
  · simp [foldedCellOfTapeAt, sourceOffset_foldedMoveHead]
  · simp [foldedCellOfTapeAt, sourceOffset_foldedMoveHead]

theorem FoldedTapeRel_move
    {T : Turing.Tape SourceSymbol} {side : FoldSide} {head : Nat} {tape : Nat → Nat}
    (dir : Turing.Dir)
    (hrel : FoldedTapeRel T side head tape) :
    FoldedTapeRel (T.move dir)
      (foldedMoveNextSide side (decide (head = 0)) dir)
      (foldedMoveHead side (decide (head = 0)) head dir) tape := by
  intro i
  rw [hrel i, foldedCellOfTapeAt_move]

set_option linter.flexible false in
theorem FoldedConfigRel_move_step
    {tc : Turing.ToPartrec.Code}
    {cfg : Turing.TM0.Cfg SourceSymbol (SourceLabel tc)} {id : PostID}
    {q' : SourceLabel tc} {dir : Turing.Dir}
    (hrel : FoldedConfigRel tc cfg id)
    (hstep :
      TM0Route.partrecStartedTM0Machine tc cfg.q cfg.Tape.head =
        some (q', Turing.TM0.Stmt.move dir)) :
    FoldedConfigRel tc
      { q := q', Tape := cfg.Tape.move dir }
      ((program tc).nextID id) := by
  rcases hrel with ⟨side, hq, hstate, htape⟩
  let marked := decide (id.head = 0)
  let left := cfg.Tape.nth (sourceOffset side id.head (leftAbs id.head))
  let right := cfg.Tape.nth (sourceOffset side id.head (rightAbs id.head))
  let read := foldedSymbolCode marked left right
  have hread :
      foldedRead side left right = cfg.Tape.head := by
    unfold left right
    exact foldedRead_active_cell cfg.Tape side id.head
  have hstep' :
      TM0Route.partrecStartedTM0Machine tc cfg.q (foldedRead side left right) =
        some (q', Turing.TM0.Stmt.move dir) := by
    simpa [hread] using hstep
  have hcell : id.tape id.head = read := by
    rw [htape id.head]
    simp [foldedCellOfTapeAt, marked, left, right, read]
  have hprogramStep := program_step_sim_of_step
    (tc := tc) (q := cfg.q) (q' := q') (side := side)
    (marked := marked) (left := left) (right := right)
    (stmt := Turing.TM0.Stmt.move dir) hq hstep'
  have hq'list : q' ∈ TM0Route.partrecStartedTM0LabelList tc := by
    have hqset : cfg.q ∈ TM0Route.partrecStartedTM0Labels tc :=
      (TM0Route.mem_partrecStartedTM0LabelList tc cfg.q).1 hq
    have hq'set : q' ∈ TM0Route.partrecStartedTM0Labels tc :=
      TM0FiniteCompiler.next_label_mem_of_step hqset hstep
    exact (TM0Route.mem_partrecStartedTM0LabelList tc q').2 hq'set
  have htapeApply :
      (PostProgram.applyStmt (foldedMoveStmt side marked read dir) id.tape id.head).1 =
        id.tape := by
    exact foldedMoveStmt_applyStmt_tape side marked read dir hcell
  have hheadApply :
      (PostProgram.applyStmt (foldedMoveStmt side marked read dir) id.tape id.head).2 =
        foldedMoveHead side marked id.head dir := by
    exact foldedMoveStmt_applyStmt_head side marked read dir id.tape id.head
  simp [PostProgram.nextID, hstate, hcell, hprogramStep, simRowOfStep, marked, read]
  refine ⟨foldedMoveNextSide side marked dir, hq'list, ?_, ?_⟩
  · simp [mkRow, marked]
  · simpa [mkRow, marked, read, htapeApply, hheadApply]
      using FoldedTapeRel_move (T := cfg.Tape) (side := side)
      (head := id.head) (tape := id.tape) dir htape

theorem FoldedConfigRel_step
    {tc : Turing.ToPartrec.Code}
    {cfg cfg' : Turing.TM0.Cfg SourceSymbol (SourceLabel tc)} {id : PostID}
    (hrel : FoldedConfigRel tc cfg id)
    (hstep :
      Turing.TM0.step (TM0Route.partrecStartedTM0Machine tc) cfg = some cfg') :
    FoldedConfigRel tc cfg' ((program tc).nextID id) := by
  cases hM :
      TM0Route.partrecStartedTM0Machine tc cfg.q cfg.Tape.head with
  | none =>
      simp [Turing.TM0.step, hM] at hstep
  | some next =>
      rcases next with ⟨q', stmt⟩
      cases stmt with
      | move dir =>
          have hcfg' : cfg' = { q := q', Tape := cfg.Tape.move dir } := by
            simpa [Turing.TM0.step, hM] using hstep.symm
          subst cfg'
          exact FoldedConfigRel_move_step (tc := tc) (cfg := cfg) (id := id)
            (q' := q') (dir := dir) hrel hM
      | write new =>
          have hcfg' : cfg' = { q := q', Tape := cfg.Tape.write new } := by
            simpa [Turing.TM0.step, hM] using hstep.symm
          subst cfg'
          exact FoldedConfigRel_write_step (tc := tc) (cfg := cfg) (id := id)
            (q' := q') (new := new) hrel hM

theorem FoldedConfigRel_halt_step
    {tc : Turing.ToPartrec.Code}
    {cfg : Turing.TM0.Cfg SourceSymbol (SourceLabel tc)} {id : PostID}
    (hrel : FoldedConfigRel tc cfg id)
    (hstep :
      Turing.TM0.step (TM0Route.partrecStartedTM0Machine tc) cfg = none) :
    ((program tc).nextID id).state = none := by
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
  have hprogramStep := program_step_sim_eq_none_of_no_step
    (tc := tc) (q := cfg.q) (side := side) (marked := marked)
    (left := left) (right := right) hq hmachine'
  simp [PostProgram.nextID, hstate, hcell, hprogramStep, read]

theorem FoldedConfigRel_reaches
    {tc : Turing.ToPartrec.Code}
    {cfg cfg' : Turing.TM0.Cfg SourceSymbol (SourceLabel tc)} {id : PostID}
    (hrel : FoldedConfigRel tc cfg id)
    (hreach :
      StateTransition.Reaches
        (Turing.TM0.step (TM0Route.partrecStartedTM0Machine tc)) cfg cfg') :
    ∃ n : Nat,
      FoldedConfigRel tc cfg' (Nat.iterate (program tc).nextID n id) := by
  induction hreach with
  | refl =>
      exact ⟨0, hrel⟩
  | tail _ hstep ih =>
      rcases ih with ⟨n, hn⟩
      refine ⟨n + 1, ?_⟩
      rw [Function.iterate_succ_apply']
      exact FoldedConfigRel_step hn (by simpa using hstep)

theorem FoldedConfigRel_reaches_halt
    {tc : Turing.ToPartrec.Code}
    {cfg cfg' : Turing.TM0.Cfg SourceSymbol (SourceLabel tc)} {id : PostID}
    (hrel : FoldedConfigRel tc cfg id)
    (hreach :
      StateTransition.Reaches
        (Turing.TM0.step (TM0Route.partrecStartedTM0Machine tc)) cfg cfg')
    (hhalt :
      Turing.TM0.step (TM0Route.partrecStartedTM0Machine tc) cfg' = none) :
    ∃ n : Nat, (Nat.iterate (program tc).nextID n id).state = none := by
  rcases FoldedConfigRel_reaches (tc := tc) hrel hreach with ⟨n, hn⟩
  refine ⟨n + 1, ?_⟩
  rw [Function.iterate_succ_apply']
  exact FoldedConfigRel_halt_step hn hhalt

end TM0FoldedCompiler

end LeanWang
