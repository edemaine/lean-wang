/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Kari.Hooper.FiniteTM0
import LeanWang.Kari.Hooper.SearchGeometry

/-!
# Reflection of finite full-tape machines

Hooper launches a right-growing canonical computation inside a failed
rightward search and its mirror image inside a failed leftward search.  This
file packages that symmetry once: reflect tape coordinates through the head
and interchange left- and right-moving table actions.  Lookup, one-step
execution, finite reachability, and immortality all commute with reflection.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace FiniteTM0Mirror

open Turing

/-- Reverse a head direction. -/
def mirrorDir : Turing.Dir → Turing.Dir
  | .left => .right
  | .right => .left

@[simp] theorem mirrorDir_left : mirrorDir .left = .right := rfl
@[simp] theorem mirrorDir_right : mirrorDir .right = .left := rfl

@[simp]
theorem mirrorDir_mirrorDir (direction : Turing.Dir) :
    mirrorDir (mirrorDir direction) = direction := by
  cases direction <;> rfl

namespace Tape

universe u

/-- Reflect a head-relative tape through its scanned cell. -/
def mirror {Γ : Type u} (T : FullTM0.Tape Γ) : FullTM0.Tape Γ :=
  fun position => T (-position)

@[simp]
theorem mirror_apply {Γ : Type u} (T : FullTM0.Tape Γ) (position : Int) :
    mirror T position = T (-position) :=
  rfl

@[simp]
theorem mirror_mirror {Γ : Type u} (T : FullTM0.Tape Γ) :
    mirror (mirror T) = T := by
  funext position
  simp [mirror]

@[simp]
theorem mirror_read {Γ : Type u} (T : FullTM0.Tape Γ) :
    (mirror T).read = T.read := by
  simp [mirror, FullTM0.Tape.read]

@[simp]
theorem mirror_write {Γ : Type u} (T : FullTM0.Tape Γ) (a : Γ) :
    mirror (T.write a) = (mirror T).write a := by
  funext position
  by_cases hposition : position = 0
  · subst position
    simp [mirror, FullTM0.Tape.write]
  · have hneg : -position ≠ 0 := by omega
    simp [mirror, FullTM0.Tape.write, hposition, hneg]

@[simp]
theorem mirror_move {Γ : Type u} (T : FullTM0.Tape Γ)
    (direction : Turing.Dir) :
    mirror (T.move direction) = (mirror T).move (mirrorDir direction) := by
  funext position
  cases direction <;>
    simp [mirror, FullTM0.Tape.move] <;> ring

@[simp]
theorem mirror_moveN {Γ : Type u} (T : FullTM0.Tape Γ)
    (direction : Turing.Dir) (distance : Nat) :
    mirror (T.moveN direction distance) =
      (mirror T).moveN (mirrorDir direction) distance := by
  funext position
  cases direction <;>
    simp [mirror, FullTM0.Tape.moveN, FullTM0.Tape.offset] <;> ring

end Tape

/-! ## Explicit table reflection -/

/-- Interchange left and right actions, leaving writes unchanged. -/
def mirrorAction {numSymbols : Nat} :
    FiniteTM0.Action numSymbols → FiniteTM0.Action numSymbols
  | .moveLeft => .moveRight
  | .moveRight => .moveLeft
  | .write a => .write a

@[simp]
theorem mirrorAction_mirrorAction {numSymbols : Nat}
    (action : FiniteTM0.Action numSymbols) :
    mirrorAction (mirrorAction action) = action := by
  cases action <;> rfl

/-- Reflect the motion of one explicit rule without changing its key or
control states. -/
def mirrorRule {numSymbols : Nat} (rule : FiniteTM0.Rule numSymbols) :
    FiniteTM0.Rule numSymbols :=
  FiniteTM0.Rule.mk rule.1.1 rule.1.2 rule.2.1
    (mirrorAction rule.2.2)

/-- Reflect every action in a finite table. -/
def mirrorTable {numSymbols : Nat} (rules : FiniteTM0.Table numSymbols) :
    FiniteTM0.Table numSymbols :=
  rules.map mirrorRule

/-- Reflect the action component of a lookup result. -/
def mirrorResult {numSymbols : Nat}
    (result : FiniteTM0.Result numSymbols) : FiniteTM0.Result numSymbols :=
  (result.1, mirrorAction result.2)

@[simp]
theorem mirrorRule_fst {numSymbols : Nat}
    (rule : FiniteTM0.Rule numSymbols) :
    (mirrorRule rule).1 = rule.1 :=
  rfl

@[simp]
theorem mirrorRule_mirrorRule {numSymbols : Nat}
    (rule : FiniteTM0.Rule numSymbols) :
    mirrorRule (mirrorRule rule) = rule := by
  rcases rule with ⟨⟨source, read⟩, ⟨target, action⟩⟩
  cases action <;> rfl

@[simp]
theorem mirrorTable_mirrorTable {numSymbols : Nat}
    (rules : FiniteTM0.Table numSymbols) :
    mirrorTable (mirrorTable rules) = rules := by
  simp [mirrorTable, List.map_map, Function.comp_def]

theorem lookupAction_mirrorTable {numSymbols : Nat}
    (rules : FiniteTM0.Table numSymbols) (state : FiniteTM0.State)
    (a : FiniteTM0.Symbol numSymbols) :
    FiniteTM0.lookupAction (mirrorTable rules) state a =
      (FiniteTM0.lookupAction rules state a).map mirrorResult := by
  induction rules with
  | nil => rfl
  | cons rule rules ih =>
      rcases rule with ⟨⟨source, read⟩, ⟨target, action⟩⟩
      by_cases hkey : (state, a) = (source, read)
      · rcases hkey with ⟨rfl, rfl⟩
        simp [mirrorTable, mirrorRule, mirrorResult,
          FiniteTM0.lookupAction, FiniteTM0.Rule.mk]
      · change FiniteTM0.lookupAction
          (FiniteTM0.Rule.mk source read target (mirrorAction action) ::
            mirrorTable rules) state a =
          (FiniteTM0.lookupAction
            (FiniteTM0.Rule.mk source read target action :: rules)
            state a).map mirrorResult
        rw [FiniteTM0.lookupAction_cons_ne hkey]
        rw [FiniteTM0.lookupAction_cons_ne hkey]
        exact ih

theorem mirrorTable_deterministic {numSymbols : Nat}
    {rules : FiniteTM0.Table numSymbols}
    (hdeterministic : FiniteTM0.Deterministic rules) :
    FiniteTM0.Deterministic (mirrorTable rules) := by
  simpa [FiniteTM0.Deterministic, mirrorTable, List.map_map,
    Function.comp_def] using hdeterministic

/-! ## Full-tape semantic reflection -/

/-- Reflect only the tape coordinates of a full configuration. -/
def mirrorCfg {numSymbols : Nat}
    (cfg : FullTM0.Cfg (FiniteTM0.Symbol numSymbols) FiniteTM0.State) :
    FullTM0.Cfg (FiniteTM0.Symbol numSymbols) FiniteTM0.State :=
  ⟨cfg.q, Tape.mirror cfg.tape⟩

@[simp]
theorem mirrorCfg_mirrorCfg {numSymbols : Nat}
    (cfg : FullTM0.Cfg (FiniteTM0.Symbol numSymbols) FiniteTM0.State) :
    mirrorCfg (mirrorCfg cfg) = cfg := by
  rcases cfg with ⟨state, tape⟩
  simp [mirrorCfg]

/-- One full-tape step commutes with reflection. -/
theorem step_mirrorTable {numSymbols : Nat}
    (rules : FiniteTM0.Table numSymbols)
    (cfg : FullTM0.Cfg (FiniteTM0.Symbol numSymbols) FiniteTM0.State) :
    FullTM0.step (FiniteTM0.machine (mirrorTable rules)) (mirrorCfg cfg) =
      (FullTM0.step (FiniteTM0.machine rules) cfg).map mirrorCfg := by
  simp only [FullTM0.step, FiniteTM0.machine, mirrorCfg, Tape.mirror_read]
  rw [lookupAction_mirrorTable]
  cases hlookup : FiniteTM0.lookupAction rules cfg.q cfg.tape.read with
  | none => simp
  | some result =>
      rcases result with ⟨target, action⟩
      cases action <;>
        simp [mirrorResult, mirrorAction, mirrorCfg, Tape.mirror_move,
          Tape.mirror_write]

/-- Every finite execution reflects pointwise. -/
theorem reaches_mirrorTable {numSymbols : Nat}
    (rules : FiniteTM0.Table numSymbols)
    {start finish :
      FullTM0.Cfg (FiniteTM0.Symbol numSymbols) FiniteTM0.State}
    (hreach : FullTM0.Reaches (FiniteTM0.machine rules) start finish) :
    FullTM0.Reaches (FiniteTM0.machine (mirrorTable rules))
      (mirrorCfg start) (mirrorCfg finish) := by
  induction hreach with
  | refl => exact Relation.ReflTransGen.refl
  | tail hpath hstep ih =>
      apply Relation.ReflTransGen.tail ih
      rw [step_mirrorTable]
      simpa using Option.mem_map_of_mem mirrorCfg hstep

theorem iterate_step_mirrorTable {numSymbols : Nat}
    (rules : FiniteTM0.Table numSymbols) (iterations : Nat)
    (cfg : FullTM0.Cfg (FiniteTM0.Symbol numSymbols) FiniteTM0.State) :
    Dynamics.iterate
        (FullTM0.step (FiniteTM0.machine (mirrorTable rules))) iterations
        (mirrorCfg cfg) =
      (Dynamics.iterate
        (FullTM0.step (FiniteTM0.machine rules)) iterations cfg).map
          mirrorCfg := by
  induction iterations with
  | zero => rfl
  | succ iterations ih =>
      rw [Dynamics.iterate_succ, Dynamics.iterate_succ, ih]
      cases hiterate : Dynamics.iterate
          (FullTM0.step (FiniteTM0.machine rules)) iterations cfg with
      | none => simp
      | some current =>
          simp only [Option.map_some, Option.bind_some]
          exact step_mirrorTable rules current

/-- Reflection preserves immortality from a designated full configuration. -/
theorem immortalFrom_mirrorTable_iff {numSymbols : Nat}
    (rules : FiniteTM0.Table numSymbols)
    (cfg : FullTM0.Cfg (FiniteTM0.Symbol numSymbols) FiniteTM0.State) :
    FullTM0.ImmortalFrom (FiniteTM0.machine (mirrorTable rules))
        (mirrorCfg cfg) ↔
      FullTM0.ImmortalFrom (FiniteTM0.machine rules) cfg := by
  constructor
  · intro himmortal iterations
    rcases himmortal iterations with ⟨mirrored, hmirrored⟩
    rw [iterate_step_mirrorTable] at hmirrored
    cases horiginal : Dynamics.iterate
        (FullTM0.step (FiniteTM0.machine rules)) iterations cfg with
    | none => simp [horiginal] at hmirrored
    | some original => exact ⟨original, horiginal⟩
  · intro himmortal iterations
    rcases himmortal iterations with ⟨original, horiginal⟩
    refine ⟨mirrorCfg original, ?_⟩
    rw [iterate_step_mirrorTable, horiginal]
    rfl

/-- A finite table is immortal exactly when its reflected table is. -/
theorem immortal_mirrorTable_iff {numSymbols : Nat}
    (rules : FiniteTM0.Table numSymbols) :
    FullTM0.Immortal (FiniteTM0.machine (mirrorTable rules)) ↔
      FullTM0.Immortal (FiniteTM0.machine rules) := by
  constructor
  · rintro ⟨start, hstart⟩
    change FullTM0.ImmortalFrom
      (FiniteTM0.machine (mirrorTable rules)) start at hstart
    refine ⟨mirrorCfg start, ?_⟩
    apply (immortalFrom_mirrorTable_iff rules (mirrorCfg start)).1
    simpa using hstart
  · rintro ⟨start, hstart⟩
    exact ⟨mirrorCfg start,
      (immortalFrom_mirrorTable_iff rules start).2 hstart⟩

/-! ## Search geometry under reflection -/

@[simp]
theorem searchGap_mirror_iff {Γ : Type*} {IsBlank IsMark : Γ → Prop}
    (T : FullTM0.Tape Γ) (direction : Turing.Dir) (distance : Nat) :
    SearchGap IsBlank IsMark (Tape.mirror T) (mirrorDir direction) distance ↔
      SearchGap IsBlank IsMark T direction distance := by
  cases direction <;>
    simp only [SearchGap, mirrorDir_left, mirrorDir_right,
      FullTM0.Tape.offset_left, FullTM0.Tape.offset_right,
      Tape.mirror_apply, neg_neg]

end FiniteTM0Mirror
end Hooper
end Kari
end LeanWang
