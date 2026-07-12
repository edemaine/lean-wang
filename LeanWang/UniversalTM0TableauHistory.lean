/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.UniversalTM0TableauTiles

/-!
# Actual direct-tableau histories
-/

noncomputable section

namespace LeanWang
namespace UniversalTM0Tableau

open UniversalTM0Semantic

def Config.next (config : Config) : Config := config.step.getD config

def Config.run (input : List Symbol) (time : Nat) : Config :=
  (Config.next^[time]) (Config.initial input)

@[simp] theorem Config.run_zero (input : List Symbol) :
    Config.run input 0 = Config.initial input := rfl

theorem Config.run_succ (input : List Symbol) (time : Nat) :
    Config.run input (time + 1) = (Config.run input time).next := by
  simp [Config.run, Function.iterate_succ_apply']

theorem Config.step_eq_none_iff (config : Config) :
    config.step = none ↔ Turing.TM0.step tm0 config.source = none := by
  rcases config with ⟨⟨q, tape⟩, side, head⟩
  unfold Config.step Turing.TM0.step
  cases hstep : tm0 q tape.head with
  | none => simp [hstep]
  | some result =>
      rcases result with ⟨q', stmt⟩
      cases stmt <;> simp [hstep, Config.afterWrite, Config.afterMove]

theorem Config.source_reaches_run (input : List Symbol) (time : Nat) :
    StateTransition.Reaches (Turing.TM0.step tm0)
      (Config.initial input).source (Config.run input time).source := by
  induction time with
  | zero => exact Relation.ReflTransGen.refl
  | succ time ih =>
      rw [Config.run_succ]
      unfold Config.next
      cases hstep : (Config.run input time).step with
      | none => simp [hstep]; exact ih
      | some next =>
          simp only [hstep, Option.getD_some]
          exact Relation.ReflTransGen.tail ih (Config.step_source hstep)

private theorem part_dom_map_iff {alpha beta : Type} (f : alpha → beta) (p : Part alpha) :
    (f <$> p).Dom ↔ p.Dom := by
  rw [Part.map_eq_map]
  rfl

theorem Config.step_run_some_of_not_dom {input : List Symbol}
    (hdom : ¬ (Turing.TM0.eval tm0 input).Dom) (time : Nat) :
    ∃ next, (Config.run input time).step = some next := by
  cases hstep : (Config.run input time).step with
  | some next => exact ⟨next, rfl⟩
  | none =>
      exfalso
      apply hdom
      rw [Turing.TM0.eval]
      apply (part_dom_map_iff (fun c => c.Tape.right₀)
        (StateTransition.eval (Turing.TM0.step tm0)
          (Turing.TM0.init input))).2
      apply Part.dom_iff_mem.2
      refine ⟨(Config.run input time).source, StateTransition.mem_eval.2 ⟨?_, ?_⟩⟩
      · simpa [Config.initial] using Config.source_reaches_run input time
      · exact (Config.step_eq_none_iff _).1 hstep

theorem Config.run_succ_of_not_dom {input : List Symbol}
    (hdom : ¬ (Turing.TM0.eval tm0 input).Dom) (time : Nat) :
    ∃ next, (Config.run input time).step = some next ∧
      Config.run input (time + 1) = next := by
  rcases Config.step_run_some_of_not_dom hdom time with ⟨next, hnext⟩
  refine ⟨next, hnext, ?_⟩
  rw [Config.run_succ]
  simp [Config.next, hnext]

def Config.Mem (config : Config) : Prop := config.source.q ∈ labels

theorem Config.initial_mem (input : List Symbol) : (Config.initial input).Mem := by
  exact default_mem_labels

theorem Config.next_mem {config next : Config} (hconfig : config.Mem)
    (hstep : config.step = some next) : next.Mem := by
  unfold Config.step at hstep
  cases hm : tm0 config.source.q config.source.Tape.head with
  | none => simp [hm] at hstep
  | some result =>
      rcases result with ⟨q', stmt⟩
      have hq' := next_mem_labels hconfig hm
      cases stmt <;> simp [hm] at hstep <;> cases hstep <;> exact hq'

theorem Config.run_mem (input : List Symbol) (time : Nat) :
    (Config.run input time).Mem := by
  induction time with
  | zero => exact Config.initial_mem input
  | succ time ih =>
      rw [Config.run_succ]
      unfold Config.next
      cases hstep : (Config.run input time).step with
      | none => simpa [hstep] using ih
      | some next =>
          simpa [hstep] using Config.next_mem ih hstep

theorem Config.cellAt_mem {config : Config} (hconfig : config.Mem)
    (position : Nat) : (config.cellAt position).Mem := by
  unfold Config.cellAt Cell.Mem
  split
  · exact hconfig
  · trivial

theorem Config.cellAtLeft_mem {config : Config} (hconfig : config.Mem)
    (position : Nat) : (config.cellAtLeft position).Mem := by
  cases position with
  | zero => exact blankCell_mem
  | succ position => exact Config.cellAt_mem hconfig position

def runHistoryTile (input : List Symbol) (time position : Nat) : HistoryTile :=
  let current := Config.run input time
  let next := Config.run input (time + 1)
  { atOrigin := decide (position = 0)
    prevLeft := current.cellAtLeft position
    prevCenter := current.cellAt position
    prevRight := current.cellAt (position + 1)
    nextLeft := next.cellAtLeft position
    nextCenter := next.cellAt position
    nextRight := next.cellAt (position + 1) }

theorem runHistoryTile_valid {input : List Symbol}
    (hdom : ¬ (Turing.TM0.eval tm0 input).Dom) (time position : Nat) :
    (runHistoryTile input time position).Valid := by
  rcases Config.run_succ_of_not_dom hdom time with ⟨next, hstep, hnext⟩
  have hcurrentMem := Config.run_mem input time
  have hnextMem := Config.run_mem input (time + 1)
  refine ⟨Config.cellAtLeft_mem hcurrentMem position,
    Config.cellAt_mem hcurrentMem position,
    Config.cellAt_mem hcurrentMem (position + 1),
    Config.cellAtLeft_mem hnextMem position,
    Config.cellAt_mem hnextMem position,
    Config.cellAt_mem hnextMem (position + 1), ?_, ?_⟩
  · intro horigin
    have hposition : position = 0 := of_decide_eq_true horigin
    subst position
    simp [runHistoryTile, Config.cellAtLeft]
  · simpa [runHistoryTile, hnext] using
      localNextCell_of_step hstep position

theorem runHistoryTile_mem {input : List Symbol}
    (hdom : ¬ (Turing.TM0.eval tm0 input).Dom) (time position : Nat) :
    runHistoryTile input time position ∈ historyTiles :=
  (mem_historyTiles_iff _).2 (runHistoryTile_valid hdom time position)

theorem runHistoryTile_hMatches (input : List Symbol) (time position : Nat) :
    WangTile.HMatches
      ((runHistoryTile input time position).toWangTile normalRowTag normalRowTag)
      ((runHistoryTile input time (position + 1)).toWangTile
        normalRowTag normalRowTag) := by
  rw [HistoryTile.hMatches_toWangTile_iff]
  simp [runHistoryTile, HistoryTile.leftMachineCell, Config.cellAtLeft]

theorem runHistoryTile_hOverlap (input : List Symbol) (time position : Nat) :
    let left := runHistoryTile input time position
    let right := runHistoryTile input time (position + 1)
    left.prevCenter.toMachineCell =
        HistoryTile.leftMachineCell right.atOrigin right.prevLeft ∧
      left.prevRight.toMachineCell = right.prevCenter.toMachineCell ∧
      left.nextCenter.toMachineCell =
        HistoryTile.leftMachineCell right.atOrigin right.nextLeft ∧
      left.nextRight.toMachineCell = right.nextCenter.toMachineCell := by
  have h := (HistoryTile.hMatches_toWangTile_iff
    (runHistoryTile input time position)
    (runHistoryTile input time (position + 1))
    normalRowTag normalRowTag normalRowTag normalRowTag).1
      (runHistoryTile_hMatches input time position)
  exact ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

theorem runHistoryTile_vMatches (input : List Symbol) (time position : Nat) :
    WangTile.VMatches
      ((runHistoryTile input time position).toWangTile normalRowTag normalRowTag)
      ((runHistoryTile input (time + 1) position).toWangTile
        normalRowTag normalRowTag) := by
  rw [HistoryTile.vMatches_toWangTile_iff]
  simp [runHistoryTile]

theorem runHistoryTile_vOverlap (input : List Symbol) (time position : Nat) :
    let lower := runHistoryTile input time position
    let upper := runHistoryTile input (time + 1) position
    HistoryTile.leftMachineCell lower.atOrigin lower.nextLeft =
        HistoryTile.leftMachineCell upper.atOrigin upper.prevLeft ∧
      lower.nextCenter.toMachineCell = upper.prevCenter.toMachineCell ∧
      lower.nextRight.toMachineCell = upper.prevRight.toMachineCell := by
  have h := (HistoryTile.vMatches_toWangTile_iff
    (runHistoryTile input time position)
    (runHistoryTile input (time + 1) position)
    normalRowTag normalRowTag normalRowTag normalRowTag).1
      (runHistoryTile_vMatches input time position)
  exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩

end UniversalTM0Tableau
end LeanWang
