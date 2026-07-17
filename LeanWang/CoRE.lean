/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import Mathlib.Computability.Reduce

/-!
# Co-r.e. predicates and many-one completeness

Mathlib defines recursively enumerable predicates and computable many-one
reductions, but does not currently package their co-r.e. counterparts.  This
module supplies the small missing interface, the universal fixed-input halting
reduction, and closure under computable preimages and existential search.
-/

noncomputable section

namespace LeanWang

universe u

/-- A predicate is co-r.e. when its complement is recursively enumerable. -/
def CoREPred {α : Type*} [Primcodable α] (p : α → Prop) : Prop :=
  REPred fun a => ¬ p a

/-- Every co-r.e. predicate computably many-one reduces to `q`. -/
def CoREHard {β : Type u} [Primcodable β] (q : β → Prop) : Prop :=
  ∀ {α : Type u} [Primcodable α] (p : α → Prop), CoREPred p → p ≤₀ q

/-- A predicate is co-r.e.-complete when it is both co-r.e. and co-r.e.-hard. -/
def CoREComplete {α : Type u} [Primcodable α] (p : α → Prop) : Prop :=
  CoREPred p ∧ CoREHard p

namespace REPred

/-- Recursively enumerable predicates are closed under computable preimages. -/
theorem comp {α β : Type*} [Primcodable α] [Primcodable β]
    {p : β → Prop} (hp : REPred p) {f : α → β} (hf : Computable f) :
    REPred fun a => p (f a) := by
  unfold _root_.REPred at hp ⊢
  exact hp.comp hf

/-- Existential quantification over naturals preserves recursive enumerability. -/
theorem exists_nat {α : Type*} [Primcodable α]
    {p : α → Nat → Prop}
    (hp : ComputablePred fun a : α × Nat => p a.1 a.2) :
    REPred fun a => ∃ n, p a n := by
  rcases hp with ⟨decision, htest⟩
  letI : DecidableRel p := fun a n => decision (a, n)
  have htest₂ : Computable₂ fun a n => decide (p a n) := htest.to₂
  have hsearch : Partrec fun a => Nat.rfind fun n => Part.some (decide (p a n)) :=
    Partrec.rfind htest₂.partrec₂
  exact (Partrec.dom_re hsearch).of_eq fun a => by
    simp

end REPred

open Encodable
open Nat.Partrec (Code)

/-- Every r.e. predicate reduces to universal fixed-input halting. -/
theorem re_manyOneReducible_fixedHalting
    {α : Type*} [Primcodable α] (p : α → Prop) (hp : REPred p) :
    p ≤₀ fun c : Code => (Code.eval c 0).Dom := by
  unfold REPred at hp
  have hnat := Partrec.bind_decode₂_iff.1 hp
  obtain ⟨c, hc⟩ := Code.exists_code.1 hnat
  let reduce : α → Code := fun a =>
    Code.comp c (Code.const (encode a))
  refine ⟨reduce, ?_, ?_⟩
  · exact Code.primrec₂_comp.to_comp.comp
      (Computable.const c)
      (Code.primrec_const.to_comp.comp Computable.encode)
  · intro a
    change p a ↔ (Code.eval (Code.comp c (Code.const (encode a))) 0).Dom
    simp only [Code.eval, Code.eval_const]
    rw [hc]
    simp [Part.dom_iff_mem]

/-- Every co-r.e. predicate reduces to universal fixed-input nonhalting. -/
theorem coRE_manyOneReducible_fixedNonhalting
    {α : Type*} [Primcodable α] (p : α → Prop) (hp : CoREPred p) :
    p ≤₀ fun c : Code => ¬ (Code.eval c 0).Dom := by
  obtain ⟨f, hf, hcorrect⟩ :=
    re_manyOneReducible_fixedHalting (fun a => ¬ p a) hp
  exact ⟨f, hf, fun a => by
    simpa only [not_not] using not_congr (hcorrect a)⟩

end LeanWang

end
