/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.NatPartrecToToPartrec
import LeanWang.TM0Route
import LeanWang.UniversalCode

/-!
# One fixed universal TM0 machine

This is the semantic core of the simplified machine reduction.  Instead of
compiling every source program into new finite control, translate the single
universal code once.  The varying source code is supplied as ordinary input to
that fixed machine.
-/

noncomputable section

namespace LeanWang

namespace UniversalTM0

open Encodable

/-- Input to the universal evaluator for running `c` on `0`. -/
def sourceInput (c : Nat.Partrec.Code) : Nat :=
  Nat.pair (encode c) 0

theorem sourceInput_primrec : Primrec sourceInput := by
  unfold sourceInput
  exact Primrec₂.natPair.comp Primrec.encode (Primrec.const 0)

theorem sourceInput_computable : Computable sourceInput :=
  sourceInput_primrec.to_comp

/-- The fixed list-language code compiled by the machine reduction. -/
def code : Turing.ToPartrec.Code :=
  NatPartrecToToPartrec.translate UniversalCode.universalCode

/-- The fixed TM0 control used for every source program. -/
def machine :=
  TM0Route.partrecStartedTM0Machine code

/-- Only the initial tape depends on the source program. -/
def input (c : Nat.Partrec.Code) :=
  TM0Route.partrecStartedTM0InputFor (sourceInput c)

/--
The varying initial tape is computable from the source code.  This is now a
standalone binary-encoding lemma; it does not inspect or compile source syntax.
-/
theorem input_computable : Computable input := by
  sorry

theorem eval_dom_iff (c : Nat.Partrec.Code) :
    (Turing.TM0.eval machine (input c)).Dom ↔
      (Nat.Partrec.Code.eval c 0).Dom := by
  rw [machine, input]
  rw [TM0Route.partrecStartedTM0_eval_dom_iff_tm2_for]
  rw [TM0Route.partrecStartedTM2_eval_dom_iff_partrec_for]
  change
    (StateTransition.eval
      (Turing.TM2.step Turing.PartrecToTM2.tr)
      (Turing.PartrecToTM2.init
        (NatPartrecToToPartrec.translate UniversalCode.universalCode)
        [sourceInput c])).Dom ↔
      (Nat.Partrec.Code.eval c 0).Dom
  rw [NatPartrecToToPartrec.translate_tm2_dom_at]
  rw [sourceInput, UniversalCode.universalCode_eval]

/-- Complemented form used by the Wang-tiling construction. -/
theorem not_eval_dom_iff (c : Nat.Partrec.Code) :
    ¬ (Turing.TM0.eval machine (input c)).Dom ↔
      ¬ (Nat.Partrec.Code.eval c 0).Dom := by
  rw [eval_dom_iff]

end UniversalTM0

end LeanWang
