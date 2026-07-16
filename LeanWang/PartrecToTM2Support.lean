/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import Mathlib.Computability.TuringMachine.ToPartrec

/-!
Finite-control support facts for Mathlib's `PartrecToTM2` evaluator.

The machine-side reduction uses Mathlib's finite reachable-label set
`Turing.PartrecToTM2.codeSupp`, followed by the TM2-to-TM1-to-TM0 translations.
This file supplies the finite/primitive-codable instances needed by those
translations and packages the evaluator's two support facts used downstream.
-/

namespace LeanWang
namespace PartrecToTM2Support

open Turing
open Turing.PartrecToTM2

/-- The evaluator label used by `PartrecToTM2.init tc [0]`. -/
def startLabel (tc : ToPartrec.Code) : Λ' :=
  trNormal tc Cont'.halt

/-- Finite set of TM2 labels reachable from the evaluator start label. -/
def labels (tc : ToPartrec.Code) : Finset Λ' :=
  codeSupp tc Cont'.halt

private def stackNameToBits : K' → Bool × Bool
  | .main => (false, false)
  | .rev => (false, true)
  | .aux => (true, false)
  | .stack => (true, true)

private def stackNameOfBits : Bool × Bool → K'
  | (false, false) => .main
  | (false, true) => .rev
  | (true, false) => .aux
  | (true, true) => .stack

private def stackNameEquivBits : K' ≃ Bool × Bool where
  toFun := stackNameToBits
  invFun := stackNameOfBits
  left_inv := by
    intro k
    cases k <;> rfl
  right_inv := by
    intro bits
    rcases bits with ⟨b0, b1⟩
    cases b0 <;> cases b1 <;> rfl

instance : Fintype K' :=
  Fintype.ofEquiv (Bool × Bool) stackNameEquivBits.symm

instance : Primcodable K' :=
  Primcodable.ofEquiv (Bool × Bool) stackNameEquivBits

private def stackSymbolToBits : Γ' → Bool × Bool
  | .consₗ => (false, false)
  | .cons => (false, true)
  | .bit0 => (true, false)
  | .bit1 => (true, true)

private def stackSymbolOfBits : Bool × Bool → Γ'
  | (false, false) => .consₗ
  | (false, true) => .cons
  | (true, false) => .bit0
  | (true, true) => .bit1

private def stackSymbolEquivBits : Γ' ≃ Bool × Bool where
  toFun := stackSymbolToBits
  invFun := stackSymbolOfBits
  left_inv := by
    intro symbol
    cases symbol <;> rfl
  right_inv := by
    intro bits
    rcases bits with ⟨b0, b1⟩
    cases b0 <;> cases b1 <;> rfl

instance : Primcodable Γ' :=
  Primcodable.ofEquiv (Bool × Bool) stackSymbolEquivBits

/-- The evaluator's start label belongs to its finite reachable support. -/
theorem startLabel_mem_labels (tc : ToPartrec.Code) :
    startLabel tc ∈ labels tc :=
  codeSupp_self tc Cont'.halt (trStmts₁_self _)

/-- Mathlib's support theorem specialized to the evaluator label set. -/
theorem tr_supports_labels (tc : ToPartrec.Code) :
    @TM2.Supports _ _ _ _ ⟨startLabel tc⟩ tr (labels tc) := by
  change @TM2.Supports _ _ _ _ ⟨trNormal tc Cont'.halt⟩ tr
    (codeSupp tc Cont'.halt)
  exact tr_supports tc Cont'.halt

end PartrecToTM2Support
end LeanWang
