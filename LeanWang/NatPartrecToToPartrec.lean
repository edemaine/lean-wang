/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.ToPartrecHelpers

/-!
A syntactic translation from Mathlib's unary `Nat.Partrec.Code` language to
Mathlib's list-based `Turing.ToPartrec.Code` language.

The intended invariant is that `translate c` maps a singleton input `[n]` to a
singleton output `[x]` exactly when `Nat.Partrec.Code.eval c n = x`. This file
starts by making the translation itself explicit. The hard proof work is the
semantic correctness theorem for the recursive and minimization constructors.
-/

noncomputable section

namespace LeanWang

namespace NatPartrecToToPartrec

namespace TCode

open Turing.ToPartrec

/-- The constant-one singleton function. -/
def one : Code :=
  Code.succ.comp Code.zero

@[simp]
theorem one_eval (v : List Nat) :
    one.eval v = pure [1] := by
  simp [one]

/--
The body used to implement `Nat.Partrec.Code.rfind'`.

On state `[n, m, a]`, the body evaluates the translated predicate at
`[Nat.pair a (n + m)]`. If the predicate returns zero, `Code.fix` stops with
state `[n, m, a]`; otherwise the next state is `[n + 1, m, a]`.
-/
def rfindBody (test : Code) : Code :=
  let condition := test.comp Code.rfindTestArg
  let found := Code.zero'
  let nextState := Code.cons (Code.succ.comp Code.second) (Code.tail.comp Code.tail)
  let step := Code.cons one nextState
  (Code.case found step).comp (Code.cons condition Code.id)

theorem rfindBody_eval_zero {test : Code} {n m a : Nat}
    (htest : test.eval [Nat.pair a (n + m)] = pure [0]) :
    (rfindBody test).eval [n, m, a] = pure [0, n, m, a] := by
  simp [rfindBody, htest]

theorem rfindBody_eval_succ {test : Code} {n m a k : Nat}
    (htest : test.eval [Nat.pair a (n + m)] = pure [k.succ]) :
    (rfindBody test).eval [n, m, a] = pure [1, n.succ, m, a] := by
  simp [rfindBody, htest]

/--
Implementation of the `Nat.Partrec.Code.rfind'` constructor from a translated
predicate.

The input `[Nat.pair a m]` is first rearranged to `[m, a]`, then `0` is prepended
to start the search state `[0, m, a]`. The final state `[n, m, a]` is mapped to
the singleton `[n + m]`, matching the offset minimization semantics.
-/
def rfindFrom (test : Code) : Code :=
  Code.addFirstSecond.comp
    ((Code.fix (rfindBody test)).comp (Code.zero'.comp Code.unpairListSwap))

end TCode

open Turing.ToPartrec

/--
Translate unary `Nat.Partrec.Code` syntax to list-based `Turing.ToPartrec.Code`
syntax.
-/
def translate : Nat.Partrec.Code → Code
  | .zero => Code.zero
  | .succ => Code.succ
  | .left => Code.unpairLeft
  | .right => Code.unpairRight
  | .pair cf cg => Code.singletonPair (translate cf) (translate cg)
  | .comp cf cg => (translate cf).comp (translate cg)
  | .prec cf cg =>
      (Code.prec (translate cf) ((translate cg).comp Code.precStepArg)).comp
        Code.unpairListSwap
  | .rfind' cf => TCode.rfindFrom (translate cf)

@[simp]
theorem translate_zero : translate .zero = Code.zero :=
  rfl

@[simp]
theorem translate_succ : translate .succ = Code.succ :=
  rfl

@[simp]
theorem translate_left : translate .left = Code.unpairLeft :=
  rfl

@[simp]
theorem translate_right : translate .right = Code.unpairRight :=
  rfl

@[simp]
theorem translate_pair (cf cg : Nat.Partrec.Code) :
    translate (.pair cf cg) = Code.singletonPair (translate cf) (translate cg) :=
  rfl

@[simp]
theorem translate_comp (cf cg : Nat.Partrec.Code) :
    translate (.comp cf cg) = (translate cf).comp (translate cg) :=
  rfl

@[simp]
theorem translate_prec (cf cg : Nat.Partrec.Code) :
    translate (.prec cf cg) =
      (Code.prec (translate cf) ((translate cg).comp Code.precStepArg)).comp
        Code.unpairListSwap :=
  rfl

@[simp]
theorem translate_rfind' (cf : Nat.Partrec.Code) :
    translate (.rfind' cf) = TCode.rfindFrom (translate cf) :=
  rfl

/--
Semantic correctness predicate for a translated unary partial-recursive code.

`Translates c tc` says that every translated output is a singleton list `[x]`,
and those singleton outputs are exactly the values of `Nat.Partrec.Code.eval c`.
-/
def Translates (c : Nat.Partrec.Code) (tc : Code) : Prop :=
  ∀ n : Nat, ∀ v : List Nat, v ∈ tc.eval [n] ↔
    ∃ x : Nat, x ∈ Nat.Partrec.Code.eval c n ∧ v = [x]

private theorem part_mem_pure_iff {α : Type} {a b : α} :
    a ∈ (pure b : Part α) ↔ a = b := by
  rw [Part.pure_eq_some, Part.mem_some_iff]

private theorem part_dom_map_iff {α β : Type} (f : α → β) (p : Part α) :
    (f <$> p).Dom ↔ p.Dom := by
  rw [Part.map_eq_map]
  rfl

theorem Translates.dom {c : Nat.Partrec.Code} {tc : Code}
    (h : Translates c tc) (n : Nat) :
    (tc.eval [n]).Dom ↔ (Nat.Partrec.Code.eval c n).Dom := by
  constructor
  · intro htc
    rcases Part.dom_iff_mem.1 htc with ⟨v, hv⟩
    rcases (h n v).1 hv with ⟨x, hx, _⟩
    exact Part.dom_iff_mem.2 ⟨x, hx⟩
  · intro hc
    rcases Part.dom_iff_mem.1 hc with ⟨x, hx⟩
    exact Part.dom_iff_mem.2 ⟨[x], (h n [x]).2 ⟨x, hx, rfl⟩⟩

theorem Translates.tm2_dom {c : Nat.Partrec.Code} {tc : Code}
    (h : Translates c tc) :
    (StateTransition.eval
      (Turing.TM2.step Turing.PartrecToTM2.tr)
      (Turing.PartrecToTM2.init tc [0])).Dom ↔
        (Nat.Partrec.Code.eval c 0).Dom := by
  rw [Turing.PartrecToTM2.tr_eval tc [0]]
  exact (part_dom_map_iff Turing.PartrecToTM2.halt (tc.eval [0])).trans (h.dom 0)

theorem translates_zero : Translates .zero (translate .zero) := by
  intro n v
  rw [translate_zero]
  simp only [Turing.ToPartrec.Code.zero_eval]
  constructor
  · intro hv
    exact ⟨0, by simp [Nat.Partrec.Code.eval, pure, PFun.pure], part_mem_pure_iff.1 hv⟩
  · rintro ⟨x, hx, hv⟩
    have hx0 : x = 0 := by
      simpa [Nat.Partrec.Code.eval, pure, PFun.pure] using hx
    simpa [hx0] using hv

theorem translates_succ : Translates .succ (translate .succ) := by
  intro n v
  rw [translate_succ]
  simp only [Turing.ToPartrec.Code.succ_eval, List.headI_cons]
  constructor
  · intro hv
    exact ⟨n.succ, by simp [Nat.Partrec.Code.eval], part_mem_pure_iff.1 hv⟩
  · rintro ⟨x, hx, hv⟩
    have hx0 : x = n.succ := by
      simpa [Nat.Partrec.Code.eval] using hx
    simpa [hx0] using hv

theorem translates_left : Translates .left (translate .left) := by
  intro n v
  rw [translate_left]
  simp only [Code.unpairLeft_eval]
  constructor
  · intro hv
    exact ⟨n.unpair.1, by simp [Nat.Partrec.Code.eval], part_mem_pure_iff.1 hv⟩
  · rintro ⟨x, hx, hv⟩
    have hx0 : x = n.unpair.1 := by
      simpa [Nat.Partrec.Code.eval] using hx
    simpa [hx0] using hv

theorem translates_right : Translates .right (translate .right) := by
  intro n v
  rw [translate_right]
  simp only [Code.unpairRight_eval]
  constructor
  · intro hv
    exact ⟨n.unpair.2, by simp [Nat.Partrec.Code.eval], part_mem_pure_iff.1 hv⟩
  · rintro ⟨x, hx, hv⟩
    have hx0 : x = n.unpair.2 := by
      simpa [Nat.Partrec.Code.eval] using hx
    simpa [hx0] using hv

set_option linter.flexible false in
theorem translates_pair {cf cg : Nat.Partrec.Code}
    (hf : Translates cf (translate cf)) (hg : Translates cg (translate cg)) :
    Translates (.pair cf cg) (translate (.pair cf cg)) := by
  intro n v
  simp [Nat.Partrec.Code.eval, Code.singletonPair, Code.listPair,
    hf n, hg n, Seq.seq, Part.mem_bind_iff, Part.mem_map_iff]
  constructor
  · rintro ⟨x, y, ⟨hx, hy⟩, hv⟩
    exact ⟨x, hx, y, hy, hv⟩
  · rintro ⟨x, hx, y, hy, hv⟩
    exact ⟨x, y, ⟨hx, hy⟩, hv⟩

theorem translates_comp {cf cg : Nat.Partrec.Code}
    (hf : Translates cf (translate cf)) (hg : Translates cg (translate cg)) :
    Translates (.comp cf cg) (translate (.comp cf cg)) := by
  intro n v
  constructor
  · intro hv
    rw [translate_comp, Turing.ToPartrec.Code.comp_eval] at hv
    change v ∈ ((translate cg).eval [n] >>= (translate cf).eval) at hv
    simp only [Part.bind_eq_bind, Part.mem_bind_iff] at hv
    rcases hv with ⟨w, hwg, hvf⟩
    rcases (hg n w).1 hwg with ⟨y, hyg, rfl⟩
    rcases (hf y v).1 hvf with ⟨x, hxf, hv⟩
    refine ⟨x, ?_, hv⟩
    change x ∈ (Nat.Partrec.Code.eval cg n >>= fun a => Nat.Partrec.Code.eval cf a)
    simp only [Part.bind_eq_bind, Part.mem_bind_iff]
    exact ⟨y, hyg, hxf⟩
  · rintro ⟨x, hx, rfl⟩
    change x ∈ (Nat.Partrec.Code.eval cg n >>= fun a => Nat.Partrec.Code.eval cf a) at hx
    simp only [Part.bind_eq_bind, Part.mem_bind_iff] at hx
    rcases hx with ⟨y, hyg, hxf⟩
    rw [translate_comp, Turing.ToPartrec.Code.comp_eval]
    change [x] ∈ ((translate cg).eval [n] >>= (translate cf).eval)
    simp only [Part.bind_eq_bind, Part.mem_bind_iff]
    exact ⟨[y], (hg n [y]).2 ⟨y, hyg, rfl⟩,
      (hf y [x]).2 ⟨x, hxf, rfl⟩⟩

end NatPartrecToToPartrec

end LeanWang
