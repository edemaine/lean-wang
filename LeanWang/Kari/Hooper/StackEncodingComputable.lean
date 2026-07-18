/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Kari.Hooper.StackEncoding
import Mathlib.Computability.Primrec.List

/-!
# Effectiveness of the fixed stack encoding

The generic stack code chooses a pointed enumeration of a finite alphabet
noncomputably.  Once the alphabet is fixed, that finite digit map is still a
primitive-recursive function.  This file records that effectiveness and, in
particular, proves that the numeric registers used for the source input are
computable from its program code.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace StackEncoding

universe u

noncomputable section

variable {Γ : Type u} [Fintype Γ] [Inhabited Γ] [Primcodable Γ]

/-- The fixed digit assignment on a finite alphabet is primitive recursive. -/
theorem digit_primrec : Primrec (digit : Γ → Nat) :=
  Primrec.dom_finite _

/-- Arithmetic push is primitive recursive in the symbol and old stack. -/
theorem push_primrec : Primrec fun input : Γ × Nat ↦
    push input.1 input.2 := by
  exact Primrec.nat_add.comp
    (digit_primrec.comp Primrec.fst)
    (Primrec.nat_mul.comp (Primrec.const (base Γ)) Primrec.snd)

/-- Encoding a finite list by least-significant-first radix folding is
primitive recursive. -/
theorem encodeList_primrec : Primrec (encodeList : List Γ → Nat) := by
  let step : List Γ → Γ × Nat → Nat :=
    fun _ pair => push pair.1 pair.2
  have hstep : Primrec₂ step := by
    apply Primrec₂.mk
    exact push_primrec.comp Primrec.snd
  exact (Primrec.list_foldr Primrec.id (Primrec.const 0) hstep).of_eq
    fun list => by
      induction list with
      | nil => rfl
      | cons head tail ih =>
          change push head (tail.foldr push 0) =
            push head (encodeList tail)
          exact congrArg (push head) ih

end

/-! ## The code-dependent universal source input -/

/-- The left source stack is the constant empty code. -/
theorem sourceInitialRegisters_left_primrec :
    Primrec fun c : Nat.Partrec.Code ↦
      (sourceInitialRegisters c).left := by
  exact (Primrec.const 0).of_eq fun _ => rfl

/-- The potentially large right-stack numeral used to initialize a nested
canonical computation is primitive recursive in the source code. -/
theorem sourceInitialRegisters_right_primrec :
    Primrec fun c : Nat.Partrec.Code ↦
      (sourceInitialRegisters c).right := by
  change Primrec fun c : Nat.Partrec.Code ↦
    encodeList (UniversalTM0Semantic.input c).tail
  exact encodeList_primrec.comp
    (Primrec.list_tail.comp UniversalTM0Semantic.input_primrec)

theorem sourceInitialRegisters_right_computable :
    Computable fun c : Nat.Partrec.Code ↦
      (sourceInitialRegisters c).right :=
  sourceInitialRegisters_right_primrec.to_comp

end StackEncoding
end Hooper
end Kari
end LeanWang
