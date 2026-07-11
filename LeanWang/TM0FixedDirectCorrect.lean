/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FixedDirectExecution

/-!
# Correctness of the direct fixed-TM0 program

The direct finite table takes exactly the corresponding semantic TM0 step on
every related folded configuration.  The proof uses only the folded-tape
geometry and the direct table lookup theorem; it does not pass through the
generated position-coded compiler.
-/

noncomputable section

namespace LeanWang
namespace TM0FixedDirectCorrect

open TM0Route TM0FoldedCompiler TM0FixedDirectProgram TM0FixedDirectGeometry
  TM0FixedDirectExecution

set_option maxRecDepth 20000

theorem FoldedConfigRel_direct_write_step
    {tc : Turing.ToPartrec.Code}
    {cfg : Turing.TM0.Cfg SourceSymbol (SourceLabel tc)} {id : PostID}
    {q' : SourceLabel tc} {new : SourceSymbol}
    (hrel : FoldedConfigRel tc cfg id)
    (hstep : partrecStartedTM0Machine tc cfg.q cfg.Tape.head =
      some (q', Turing.TM0.Stmt.write new)) :
    FoldedConfigRel tc { q := q', Tape := cfg.Tape.write new }
      ((program tc).nextID id) := by
  rcases hrel with ⟨side, hq, hstate, htape⟩
  let left := cfg.Tape.nth (sourceOffset side id.head (leftAbs id.head))
  let right := cfg.Tape.nth (sourceOffset side id.head (rightAbs id.head))
  have hread : foldedRead side left right = cfg.Tape.head := by
    unfold left right
    exact foldedRead_active_cell cfg.Tape side id.head
  have hstep' : partrecStartedTM0Machine tc cfg.q (foldedRead side left right) =
      some (q', Turing.TM0.Stmt.write new) := by
    simpa [hread] using hstep
  have hcell : id.tape id.head =
      foldedSymbolCode (decide (id.head = 0)) left right := by
    rw [htape id.head]
    simp [foldedCellOfTapeAt, left, right]
  rw [nextID_write hstate hcell hq hstep']
  refine ⟨side, ?_, rfl, FoldedTapeRel_write new htape⟩
  have hqset := (mem_partrecStartedTM0LabelList tc cfg.q).1 hq
  exact (mem_partrecStartedTM0LabelList tc q').2
    (TM0FiniteCompiler.next_label_mem_of_step hqset hstep)

theorem FoldedConfigRel_direct_move_step
    {tc : Turing.ToPartrec.Code}
    {cfg : Turing.TM0.Cfg SourceSymbol (SourceLabel tc)} {id : PostID}
    {q' : SourceLabel tc} {dir : Turing.Dir}
    (hrel : FoldedConfigRel tc cfg id)
    (hstep : partrecStartedTM0Machine tc cfg.q cfg.Tape.head =
      some (q', Turing.TM0.Stmt.move dir)) :
    FoldedConfigRel tc { q := q', Tape := cfg.Tape.move dir }
      ((program tc).nextID id) := by
  rcases hrel with ⟨side, hq, hstate, htape⟩
  let marked := decide (id.head = 0)
  let left := cfg.Tape.nth (sourceOffset side id.head (leftAbs id.head))
  let right := cfg.Tape.nth (sourceOffset side id.head (rightAbs id.head))
  have hread : foldedRead side left right = cfg.Tape.head := by
    unfold left right
    exact foldedRead_active_cell cfg.Tape side id.head
  have hstep' : partrecStartedTM0Machine tc cfg.q (foldedRead side left right) =
      some (q', Turing.TM0.Stmt.move dir) := by
    simpa [hread] using hstep
  have hcell : id.tape id.head = foldedSymbolCode marked left right := by
    rw [htape id.head]
    simp [foldedCellOfTapeAt, marked, left, right]
  have hq' : q' ∈ partrecStartedTM0LabelList tc := by
    have hqset := (mem_partrecStartedTM0LabelList tc cfg.q).1 hq
    exact (mem_partrecStartedTM0LabelList tc q').2
      (TM0FiniteCompiler.next_label_mem_of_step hqset hstep)
  rw [nextID_move hstate hcell hq hstep']
  refine ⟨foldedMoveNextSide side marked dir, hq', ?_, ?_⟩
  · rfl
  · exact FoldedTapeRel_move (T := cfg.Tape) (side := side) (head := id.head)
      (tape := id.tape) dir htape

theorem FoldedConfigRel_direct_step
    {tc : Turing.ToPartrec.Code}
    {cfg cfg' : Turing.TM0.Cfg SourceSymbol (SourceLabel tc)} {id : PostID}
    (hrel : FoldedConfigRel tc cfg id)
    (hstep : Turing.TM0.step (partrecStartedTM0Machine tc) cfg = some cfg') :
    FoldedConfigRel tc cfg'
      ((programWithTable tc (rows tc)).nextID id) := by
  cases hM : partrecStartedTM0Machine tc cfg.q cfg.Tape.head with
  | none => simp [Turing.TM0.step, hM] at hstep
  | some next =>
      rcases next with ⟨q', stmt⟩
      cases stmt with
      | move dir =>
          have : cfg' = { q := q', Tape := cfg.Tape.move dir } := by
            simpa [Turing.TM0.step, hM] using hstep.symm
          subst cfg'
          exact FoldedConfigRel_direct_move_step hrel hM
      | write new =>
          have : cfg' = { q := q', Tape := cfg.Tape.write new } := by
            simpa [Turing.TM0.step, hM] using hstep.symm
          subst cfg'
          exact FoldedConfigRel_direct_write_step hrel hM

theorem FoldedConfigRel_direct_halt_step
    {tc : Turing.ToPartrec.Code}
    {cfg : Turing.TM0.Cfg SourceSymbol (SourceLabel tc)} {id : PostID}
    (hrel : FoldedConfigRel tc cfg id)
    (hstep : Turing.TM0.step (partrecStartedTM0Machine tc) cfg = none) :
    ((programWithTable tc (rows tc)).nextID id).state = none := by
  rcases hrel with ⟨side, hq, hstate, htape⟩
  let marked := decide (id.head = 0)
  let left := cfg.Tape.nth (sourceOffset side id.head (leftAbs id.head))
  let right := cfg.Tape.nth (sourceOffset side id.head (rightAbs id.head))
  have hread : foldedRead side left right = cfg.Tape.head := by
    unfold left right
    exact foldedRead_active_cell cfg.Tape side id.head
  have hmachine : partrecStartedTM0Machine tc cfg.q cfg.Tape.head = none := by
    cases hM : partrecStartedTM0Machine tc cfg.q cfg.Tape.head with
    | none => rfl
    | some next => simp [Turing.TM0.step, hM] at hstep
  have hmachine' : partrecStartedTM0Machine tc cfg.q
      (foldedRead side left right) = none := by
    simpa [hread] using hmachine
  have hcell : id.tape id.head = foldedSymbolCode marked left right := by
    rw [htape id.head]
    simp [foldedCellOfTapeAt, marked, left, right]
  exact nextID_halt hstate hcell hq hmachine'

theorem FoldedConfigRel_direct_reaches
    {tc : Turing.ToPartrec.Code}
    {cfg cfg' : Turing.TM0.Cfg SourceSymbol (SourceLabel tc)} {id : PostID}
    (hrel : FoldedConfigRel tc cfg id)
    (hreach : StateTransition.Reaches
      (Turing.TM0.step (partrecStartedTM0Machine tc)) cfg cfg') :
    ∃ n, FoldedConfigRel tc cfg'
      (Nat.iterate (programWithTable tc (rows tc)).nextID n id) := by
  induction hreach with
  | refl => exact ⟨0, hrel⟩
  | tail _ hstep ih =>
      rcases ih with ⟨n, hn⟩
      refine ⟨n + 1, ?_⟩
      rw [Function.iterate_succ_apply']
      exact FoldedConfigRel_direct_step hn (by simpa using hstep)

theorem FoldedConfigRel_direct_reaches_halt
    {tc : Turing.ToPartrec.Code}
    {cfg cfg' : Turing.TM0.Cfg SourceSymbol (SourceLabel tc)} {id : PostID}
    (hrel : FoldedConfigRel tc cfg id)
    (hreach : StateTransition.Reaches
      (Turing.TM0.step (partrecStartedTM0Machine tc)) cfg cfg')
    (hhalt : Turing.TM0.step (partrecStartedTM0Machine tc) cfg' = none) :
    ∃ n, (Nat.iterate (programWithTable tc (rows tc)).nextID n id).state = none := by
  rcases FoldedConfigRel_direct_reaches hrel hreach with ⟨n, hn⟩
  refine ⟨n + 1, ?_⟩
  rw [Function.iterate_succ_apply']
  exact FoldedConfigRel_direct_halt_step hn hhalt

theorem tm0_reaches_halt_of_direct_halts
    {tc : Turing.ToPartrec.Code}
    {cfg : Turing.TM0.Cfg SourceSymbol (SourceLabel tc)} {id : PostID}
    (hrel : FoldedConfigRel tc cfg id) :
    ∀ n,
      (Nat.iterate (programWithTable tc (rows tc)).nextID n id).state = none →
        ∃ cfg', StateTransition.Reaches
          (Turing.TM0.step (partrecStartedTM0Machine tc)) cfg cfg' ∧
          Turing.TM0.step (partrecStartedTM0Machine tc) cfg' = none
  | 0, hhalt => by
      rcases hrel with ⟨side, _hq, hstate, _htape⟩
      simp [hstate] at hhalt
  | n + 1, hhalt => by
      cases hstep : Turing.TM0.step (partrecStartedTM0Machine tc) cfg with
      | none => exact ⟨cfg, Relation.ReflTransGen.refl, hstep⟩
      | some cfg₁ =>
          have hrel₁ := FoldedConfigRel_direct_step hrel hstep
          have hhalt₁ :
              (Nat.iterate (programWithTable tc (rows tc)).nextID n
                ((programWithTable tc (rows tc)).nextID id)).state = none := by
            simpa [Function.iterate_succ_apply] using hhalt
          rcases tm0_reaches_halt_of_direct_halts hrel₁ n hhalt₁ with
            ⟨cfg', hreach, hterminal⟩
          exact ⟨cfg', Relation.ReflTransGen.head (by simpa using hstep) hreach,
            hterminal⟩

end TM0FixedDirectCorrect
end LeanWang
