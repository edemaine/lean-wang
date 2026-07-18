/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Kari.AffineTM

/-!
# Compile a finite TM0 table to Kari's affine system

`AffineTM.lean` compiles one fully specified local rule: besides a rule of the
source machine, it records the symbols visible at the tops of both side
stacks.  This module performs the finite outer enumeration.  Every table rule
is combined with every pair of tape symbols, and the resulting affine branches
are packaged as an `AffineSystem`.

The tags used by `AffineTM.LocalRule` encode the complete triple consisting of
the table rule and the two visible symbols.  Their injectivity supplies the
tag-uniqueness condition needed to force each transducer row to use one affine
branch.
-/

namespace LeanWang
namespace Kari
namespace AffineTMSystem

open Hooper
open Hooper.FiniteTM0
open AffineTM

variable {numSymbols : Nat}

/-- Fully specified local rules are effectively just triples. -/
def localRuleEquiv (numSymbols : Nat) :
    LocalRule numSymbols ≃
      Rule numSymbols × Symbol numSymbols × Symbol numSymbols where
  toFun spec := (spec.rule, spec.leftTop, spec.rightTop)
  invFun data :=
    { rule := data.1, leftTop := data.2.1, rightTop := data.2.2 }
  left_inv := by
    intro spec
    cases spec
    rfl
  right_inv := by
    rintro ⟨rule, leftTop, rightTop⟩
    rfl

instance instPrimcodableLocalRule : Primcodable (LocalRule numSymbols) :=
  Primcodable.ofEquiv
    (Rule numSymbols × Symbol numSymbols × Symbol numSymbols)
    (localRuleEquiv numSymbols)

/-- Constructing a local rule from its effective tuple is primitive recursive. -/
theorem localRuleOfTuple_primrec :
    Primrec (localRuleEquiv numSymbols).symm := by
  simpa using
    (Primrec.of_equiv_symm (e := localRuleEquiv numSymbols) :
      Primrec (localRuleEquiv numSymbols).symm)

theorem localRuleEquiv_primrec :
    Primrec (localRuleEquiv numSymbols) := by
  simpa [localRuleEquiv] using
    (Primrec.of_equiv (e := localRuleEquiv numSymbols) :
      Primrec (localRuleEquiv numSymbols))

theorem localRule_rule_primrec :
    Primrec (LocalRule.rule : LocalRule numSymbols → Rule numSymbols) :=
  Primrec.fst.comp localRuleEquiv_primrec

theorem localRule_leftTop_primrec :
    Primrec (LocalRule.leftTop :
      LocalRule numSymbols → Symbol numSymbols) :=
  Primrec.fst.comp (Primrec.snd.comp localRuleEquiv_primrec)

theorem localRule_rightTop_primrec :
    Primrec (LocalRule.rightTop :
      LocalRule numSymbols → Symbol numSymbols) :=
  Primrec.snd.comp (Primrec.snd.comp localRuleEquiv_primrec)

theorem localRule_source_primrec :
    Primrec (LocalRule.source : LocalRule numSymbols → State) :=
  Primrec.fst.comp (Primrec.fst.comp localRule_rule_primrec)

theorem localRule_read_primrec :
    Primrec (LocalRule.read :
      LocalRule numSymbols → Symbol numSymbols) :=
  Primrec.snd.comp (Primrec.fst.comp localRule_rule_primrec)

theorem localRule_target_primrec :
    Primrec (LocalRule.target : LocalRule numSymbols → State) :=
  Primrec.fst.comp (Primrec.snd.comp localRule_rule_primrec)

theorem localRule_action_primrec :
    Primrec (LocalRule.action :
      LocalRule numSymbols → Action numSymbols) :=
  Primrec.snd.comp (Primrec.snd.comp localRule_rule_primrec)

/-- Even symbol interval codes are primitive recursive. -/
theorem symbolValue_primrec :
    Primrec (AffineTM.symbolValue : Symbol numSymbols → Int) := by
  exact (SignedPrimrec.intMul.comp (Primrec.const 2)
    (SignedPrimrec.intOfNat.comp Primrec.fin_val)).of_eq fun a => by
      simp [AffineTM.symbolValue]

/-- Center tags are primitive recursive in the state and scanned symbol. -/
theorem centerValue_primrec :
    Primrec fun input : State × Symbol numSymbols =>
      AffineTM.centerValue input.1 input.2 := by
  exact (SignedPrimrec.intOfNat.comp
    (Primrec₂.natPair.comp Primrec.fst
      (Primrec.fin_val.comp Primrec.snd))).of_eq fun _ => rfl

/-- The two Beatty digits of an integer unit interval are primitive recursive. -/
theorem intervalDigits_primrec :
    Primrec AffineTM.intervalDigits := by
  unfold AffineTM.intervalDigits
  exact Primrec.list_cons.comp Primrec.id
    (Primrec.list_cons.comp
      (SignedPrimrec.intAdd.comp Primrec.id (Primrec.const 1))
      (Primrec.const []))

/-- The finite componentwise digit box is primitive recursive in its two
visible symbols and center tag. -/
theorem digitBox_primrec :
    Primrec fun input : Symbol numSymbols × Symbol numSymbols × Int =>
      AffineTM.digitBox input.1 input.2.1 input.2.2 := by
  unfold AffineTM.digitBox
  refine Primrec.list_flatMap
    (intervalDigits_primrec.comp
      (symbolValue_primrec.comp Primrec.fst)) ?_
  apply Primrec₂.mk
  refine Primrec.list_map
    (intervalDigits_primrec.comp
      (symbolValue_primrec.comp
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))) ?_
  apply Primrec₂.mk
  have hx : Primrec fun input :
      ((Symbol numSymbols × Symbol numSymbols × Int) × Int) × Int =>
        input.1.2 :=
    Primrec.snd.comp Primrec.fst
  have hy : Primrec fun input :
      ((Symbol numSymbols × Symbol numSymbols × Int) × Int) × Int =>
        input.2 :=
    Primrec.snd
  have hz : Primrec fun input :
      ((Symbol numSymbols × Symbol numSymbols × Int) × Int) × Int =>
        input.1.1.2.2 :=
    Primrec.snd.comp
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  exact IntVector3.ofTuple_primrec.comp
    (hx.pair (hy.pair hz))

/-- The explicit action-code equivalence is primitive recursive. -/
theorem actionEquivCode_primrec :
    Primrec (Action.equivCode :
      Action numSymbols → Bool ⊕ Symbol numSymbols) := by
  simpa [Action.equivCode] using
    (Primrec.of_equiv (e := Action.equivCode) :
      Primrec (Action.equivCode :
        Action numSymbols → Bool ⊕ Symbol numSymbols))

/-- Fully specified local-rule tags are primitive recursive. -/
theorem localRule_tag_primrec :
    Primrec (LocalRule.tag : LocalRule numSymbols → Nat) := by
  exact Primrec₂.natPair.comp
    (Primrec.encode.comp localRule_rule_primrec)
    (Primrec₂.natPair.comp
      (Primrec.fin_val.comp localRule_leftTop_primrec)
      (Primrec.fin_val.comp localRule_rightTop_primrec))

/-- Affine branch denominators are primitive recursive. -/
theorem localRule_denominator_primrec :
    Primrec (LocalRule.denominator :
      LocalRule numSymbols → Nat) := by
  have hcode : Primrec fun spec : LocalRule numSymbols =>
      (Action.equivCode spec.action :
        Bool ⊕ Symbol numSymbols) :=
    (@actionEquivCode_primrec numSymbols).comp
      (@localRule_action_primrec numSymbols)
  exact (Primrec.sumCasesOn hcode
    (Primrec.const (AffineTM.sideBase numSymbols)).to₂
    (Primrec.const 1).to₂).of_eq fun spec => by
      cases haction : spec.action <;>
        simp [LocalRule.denominator, haction, Action.equivCode]

/-- Affine numerator matrices are primitive recursive. -/
theorem localRule_linearNumerator_primrec :
    Primrec (LocalRule.linearNumerator :
      LocalRule numSymbols → IntMatrix3) := by
  let B : Int := AffineTM.sideBase numSymbols
  let writeMatrix : IntMatrix3 :=
    ⟨1, 0, 0, 0, 1, 0, 0, 0, 0⟩
  let leftMatrix : IntMatrix3 :=
    ⟨B * B, 0, 0, 0, 1, 0, 0, 0, 0⟩
  let rightMatrix : IntMatrix3 :=
    ⟨1, 0, 0, 0, B * B, 0, 0, 0, 0⟩
  have hcode : Primrec fun spec : LocalRule numSymbols =>
      (Action.equivCode spec.action :
        Bool ⊕ Symbol numSymbols) :=
    (@actionEquivCode_primrec numSymbols).comp
      (@localRule_action_primrec numSymbols)
  have hmove : Primrec₂ fun (_spec : LocalRule numSymbols) (right : Bool) =>
      bif right then rightMatrix else leftMatrix := by
    apply Primrec₂.mk
    exact (Primrec.dom_bool fun right =>
      bif right then rightMatrix else leftMatrix).comp Primrec.snd
  exact (Primrec.sumCasesOn hcode hmove
    (Primrec.const writeMatrix).to₂).of_eq fun spec => by
      cases haction : spec.action <;>
        simp [LocalRule.linearNumerator, haction, Action.equivCode,
          B, writeMatrix, leftMatrix, rightMatrix]

/-- Input digit alphabets of fully specified local rules are primitive
recursive. -/
theorem localRule_inputs_primrec :
    Primrec (LocalRule.inputs :
      LocalRule numSymbols → List IntVector3) := by
  have hcenter : Primrec fun spec : LocalRule numSymbols =>
      AffineTM.centerValue spec.source spec.read :=
    centerValue_primrec.comp
      (localRule_source_primrec.pair localRule_read_primrec)
  exact digitBox_primrec.comp
    (localRule_leftTop_primrec.pair
      (localRule_rightTop_primrec.pair hcenter))

private theorem intVector3_mk_primrec
    {α : Type*} [Primcodable α]
    {x y z : α → Int}
    (hx : Primrec x) (hy : Primrec y) (hz : Primrec z) :
    Primrec fun input => (⟨x input, y input, z input⟩ : IntVector3) :=
  IntVector3.ofTuple_primrec.comp (hx.pair (hy.pair hz))

set_option maxHeartbeats 1000000 in
-- The three action cases generate a large primitive-recursion closure term.
/-- Affine numerator offsets are primitive recursive. -/
theorem localRule_offsetNumerator_primrec :
    Primrec (LocalRule.offsetNumerator :
      LocalRule numSymbols → IntVector3) := by
  let B : Int := AffineTM.sideBase numSymbols
  have hBmul : ∀ {f : LocalRule numSymbols → Int},
      Primrec f → Primrec fun input => B * f input :=
    fun hf => SignedPrimrec.intMul.comp (Primrec.const B) hf
  have hB2mul : ∀ {f : LocalRule numSymbols → Int},
      Primrec f → Primrec fun input => B * B * f input :=
    fun hf => SignedPrimrec.intMul.comp
      (SignedPrimrec.intMul.comp (Primrec.const B) (Primrec.const B)) hf
  have hread : Primrec fun spec : LocalRule numSymbols =>
      AffineTM.symbolValue spec.read :=
    symbolValue_primrec.comp localRule_read_primrec
  have hleftTop : Primrec fun spec : LocalRule numSymbols =>
      AffineTM.symbolValue spec.leftTop :=
    symbolValue_primrec.comp localRule_leftTop_primrec
  have hrightTop : Primrec fun spec : LocalRule numSymbols =>
      AffineTM.symbolValue spec.rightTop :=
    symbolValue_primrec.comp localRule_rightTop_primrec
  have htargetLeft : Primrec fun spec : LocalRule numSymbols =>
      AffineTM.centerValue spec.target spec.leftTop :=
    centerValue_primrec.comp
      (localRule_target_primrec.pair localRule_leftTop_primrec)
  have htargetRight : Primrec fun spec : LocalRule numSymbols =>
      AffineTM.centerValue spec.target spec.rightTop :=
    centerValue_primrec.comp
      (localRule_target_primrec.pair localRule_rightTop_primrec)
  have hleft : Primrec fun spec : LocalRule numSymbols =>
      (⟨-(B * B * AffineTM.symbolValue spec.leftTop),
        B * AffineTM.symbolValue spec.read,
        B * AffineTM.centerValue spec.target spec.leftTop⟩ : IntVector3) :=
    intVector3_mk_primrec
      (SignedPrimrec.intNeg.comp (hB2mul hleftTop))
      (hBmul hread) (hBmul htargetLeft)
  have hright : Primrec fun spec : LocalRule numSymbols =>
      (⟨B * AffineTM.symbolValue spec.read,
        -(B * B * AffineTM.symbolValue spec.rightTop),
        B * AffineTM.centerValue spec.target spec.rightTop⟩ : IntVector3) :=
    intVector3_mk_primrec
      (hBmul hread)
      (SignedPrimrec.intNeg.comp (hB2mul hrightTop))
      (hBmul htargetRight)
  have hwrite : Primrec₂ fun (spec : LocalRule numSymbols)
      (written : Symbol numSymbols) =>
      (⟨0, 0, AffineTM.centerValue spec.target written⟩ : IntVector3) := by
    apply Primrec₂.mk
    apply intVector3_mk_primrec (Primrec.const 0) (Primrec.const 0)
    exact centerValue_primrec.comp
      ((localRule_target_primrec.comp Primrec.fst).pair Primrec.snd)
  have hmove : Primrec₂ fun (spec : LocalRule numSymbols) (right : Bool) =>
      bif right then
        (⟨B * AffineTM.symbolValue spec.read,
          -(B * B * AffineTM.symbolValue spec.rightTop),
          B * AffineTM.centerValue spec.target spec.rightTop⟩ : IntVector3)
      else
        (⟨-(B * B * AffineTM.symbolValue spec.leftTop),
          B * AffineTM.symbolValue spec.read,
          B * AffineTM.centerValue spec.target spec.leftTop⟩ : IntVector3) := by
    apply Primrec₂.mk
    exact Primrec.cond Primrec.snd
      (hright.comp Primrec.fst) (hleft.comp Primrec.fst)
  have hcode : Primrec fun spec : LocalRule numSymbols =>
      (Action.equivCode spec.action : Bool ⊕ Symbol numSymbols) :=
    (@actionEquivCode_primrec numSymbols).comp
      (@localRule_action_primrec numSymbols)
  exact (Primrec.sumCasesOn hcode hmove hwrite).of_eq fun spec => by
    cases haction : spec.action <;>
      simp [LocalRule.offsetNumerator, haction, Action.equivCode, B]

set_option maxHeartbeats 1000000 in
-- Nested finite-list closure produces a large typeclass-normalization term.
/-- Output digit alphabets of fully specified local rules are primitive
recursive. -/
theorem localRule_outputs_primrec :
    Primrec (LocalRule.outputs :
      LocalRule numSymbols → List IntVector3) := by
  have hwrite : Primrec₂ fun (spec : LocalRule numSymbols)
      (written : Symbol numSymbols) =>
      AffineTM.digitBox spec.leftTop spec.rightTop
        (AffineTM.centerValue spec.target written) := by
    apply Primrec₂.mk
    exact digitBox_primrec.comp
      ((localRule_leftTop_primrec.comp Primrec.fst).pair
        ((localRule_rightTop_primrec.comp Primrec.fst).pair
          (centerValue_primrec.comp
            ((localRule_target_primrec.comp Primrec.fst).pair Primrec.snd))))
  have hleft : Primrec fun spec : LocalRule numSymbols =>
      (List.finRange numSymbols).flatMap fun newLeftTop =>
        AffineTM.digitBox newLeftTop spec.read
          (AffineTM.centerValue spec.target spec.leftTop) := by
    have hcenter : Primrec fun spec : LocalRule numSymbols =>
        AffineTM.centerValue spec.target spec.leftTop :=
      centerValue_primrec.comp
        (localRule_target_primrec.pair localRule_leftTop_primrec)
    refine Primrec.list_flatMap
      (Primrec.const (List.finRange numSymbols)) ?_
    apply Primrec₂.mk
    exact digitBox_primrec.comp
      (Primrec.snd.pair
        ((localRule_read_primrec.comp Primrec.fst).pair
          (hcenter.comp Primrec.fst)))
  have hright : Primrec fun spec : LocalRule numSymbols =>
      (List.finRange numSymbols).flatMap fun newRightTop =>
        AffineTM.digitBox spec.read newRightTop
          (AffineTM.centerValue spec.target spec.rightTop) := by
    have hcenter : Primrec fun spec : LocalRule numSymbols =>
        AffineTM.centerValue spec.target spec.rightTop :=
      centerValue_primrec.comp
        (localRule_target_primrec.pair localRule_rightTop_primrec)
    refine Primrec.list_flatMap
      (Primrec.const (List.finRange numSymbols)) ?_
    apply Primrec₂.mk
    exact digitBox_primrec.comp
      ((localRule_read_primrec.comp Primrec.fst).pair
        (Primrec.snd.pair (hcenter.comp Primrec.fst)))
  have hmove : Primrec₂ fun (spec : LocalRule numSymbols) (right : Bool) =>
      bif right then
        (List.finRange numSymbols).flatMap fun newRightTop =>
          AffineTM.digitBox spec.read newRightTop
            (AffineTM.centerValue spec.target spec.rightTop)
      else
        (List.finRange numSymbols).flatMap fun newLeftTop =>
          AffineTM.digitBox newLeftTop spec.read
            (AffineTM.centerValue spec.target spec.leftTop) := by
    apply Primrec₂.mk
    exact Primrec.cond Primrec.snd
      (hright.comp Primrec.fst) (hleft.comp Primrec.fst)
  have hcode : Primrec fun spec : LocalRule numSymbols =>
      (Action.equivCode spec.action : Bool ⊕ Symbol numSymbols) :=
    (@actionEquivCode_primrec numSymbols).comp
      (@localRule_action_primrec numSymbols)
  exact (Primrec.sumCasesOn hcode hmove hwrite).of_eq fun spec => by
    cases haction : spec.action <;>
      simp [LocalRule.outputs, haction, Action.equivCode]

/-- Absolute value from signed integers to naturals is primitive recursive. -/
theorem intNatAbs_primrec : Primrec Int.natAbs := by
  exact (SignedPrimrec.intCasesOn Primrec.id
    Primrec.snd.to₂
    (Primrec.succ.comp Primrec.snd).to₂).of_eq fun z => by
      cases z <;> rfl

set_option maxHeartbeats 1000000 in
-- Nine matrix projections and additions produce a large closure term.
/-- Kari's uniform carry bound is primitive recursive in a local rule. -/
theorem localRule_carryBound_primrec :
    Primrec fun spec : LocalRule numSymbols =>
      AffineBeatty.carryBound spec.branch := by
  have hmatrix : Primrec fun spec : LocalRule numSymbols =>
      spec.linearNumerator :=
    @localRule_linearNumerator_primrec numSymbols
  have hrows : Primrec fun spec : LocalRule numSymbols =>
      IntMatrix3.equivRows spec.linearNumerator :=
    IntMatrix3.equivRows_primrec.comp hmatrix
  have hrowX : Primrec fun spec : LocalRule numSymbols =>
      (⟨spec.linearNumerator.xx, spec.linearNumerator.xy,
        spec.linearNumerator.xz⟩ : IntVector3) :=
    Primrec.fst.comp hrows
  have hrowY : Primrec fun spec : LocalRule numSymbols =>
      (⟨spec.linearNumerator.yx, spec.linearNumerator.yy,
        spec.linearNumerator.yz⟩ : IntVector3) :=
    Primrec.fst.comp (Primrec.snd.comp hrows)
  have hrowZ : Primrec fun spec : LocalRule numSymbols =>
      (⟨spec.linearNumerator.zx, spec.linearNumerator.zy,
        spec.linearNumerator.zz⟩ : IntVector3) :=
    Primrec.snd.comp (Primrec.snd.comp hrows)
  have hxx := intNatAbs_primrec.comp (IntVector3.x_primrec.comp hrowX)
  have hxy := intNatAbs_primrec.comp (IntVector3.y_primrec.comp hrowX)
  have hxz := intNatAbs_primrec.comp (IntVector3.z_primrec.comp hrowX)
  have hyx := intNatAbs_primrec.comp (IntVector3.x_primrec.comp hrowY)
  have hyy := intNatAbs_primrec.comp (IntVector3.y_primrec.comp hrowY)
  have hyz := intNatAbs_primrec.comp (IntVector3.z_primrec.comp hrowY)
  have hzx := intNatAbs_primrec.comp (IntVector3.x_primrec.comp hrowZ)
  have hzy := intNatAbs_primrec.comp (IntVector3.y_primrec.comp hrowZ)
  have hzz := intNatAbs_primrec.comp (IntVector3.z_primrec.comp hrowZ)
  exact (Primrec.nat_add.comp
    (Primrec.nat_add.comp
      (Primrec.nat_add.comp
        (Primrec.nat_add.comp
          (Primrec.nat_add.comp
            (Primrec.nat_add.comp
              (Primrec.nat_add.comp
                (Primrec.nat_add.comp
                  (Primrec.nat_add.comp localRule_denominator_primrec hxx)
                  hxy)
                hxz)
              hyx)
            hyy)
          hyz)
        hzx)
      hzy)
    hzz).of_eq fun spec => by
      rfl

/-- Mathlib's total conversion of naturals to positive naturals is primitive
recursive under the predecessor encoding of `PNat`. -/
theorem natToPNat'_primrec : Primrec Nat.toPNat' := by
  rw [← Primrec.encode_iff]
  exact Primrec.pred.of_eq fun _ => rfl

/-- Effective raw data of the rational affine branch for a local rule. -/
def branchData (spec : LocalRule numSymbols) :
    IntegerAffineBranch.BranchData :=
  (spec.tag, Nat.toPNat' spec.denominator,
    spec.linearNumerator, spec.offsetNumerator)

/-- Interpreting the raw branch data recovers the mathematical local branch. -/
theorem ofData_branchData (spec : LocalRule numSymbols) :
    IntegerAffineBranch.ofData (branchData spec) = spec.branch := by
  apply IntegerAffineBranch.equivTuple.injective
  change (spec.tag, Nat.toPNat' spec.denominator,
      spec.linearNumerator, spec.offsetNumerator) =
    (spec.tag, (⟨spec.denominator, spec.denominator_pos⟩ : PNat),
      spec.linearNumerator, spec.offsetNumerator)
  have hp : Nat.toPNat' spec.denominator =
      (⟨spec.denominator, spec.denominator_pos⟩ : PNat) :=
    PNat.eq (PNat.toPNat'_coe spec.denominator_pos)
  exact congrArg
    (fun denominator : PNat =>
      (spec.tag, denominator, spec.linearNumerator, spec.offsetNumerator)) hp

set_option maxHeartbeats 1000000 in
-- Packaging the proof-bearing denominator requires normalizing the tuple code.
/-- Raw affine branch data is primitive recursive in a local rule. -/
theorem branchData_primrec :
    Primrec (branchData : LocalRule numSymbols →
      IntegerAffineBranch.BranchData) := by
  have hdenominator : Primrec fun spec : LocalRule numSymbols =>
      Nat.toPNat' spec.denominator :=
    natToPNat'_primrec.comp localRule_denominator_primrec
  exact (localRule_tag_primrec.pair
    (hdenominator.pair
      (localRule_linearNumerator_primrec.pair
        localRule_offsetNumerator_primrec))).of_eq fun _ => rfl

/-- Enumerate both visible side symbols for one source rule. -/
def instantiateRule (rule : Rule numSymbols) :
    List (LocalRule numSymbols) :=
  (List.finRange numSymbols).flatMap fun leftTop =>
    (List.finRange numSymbols).map fun rightTop =>
      { rule := rule, leftTop := leftTop, rightTop := rightTop }

/-- All fully specified local rules arising from a finite TM0 table. -/
def localRules (table : Table numSymbols) : List (LocalRule numSymbols) :=
  table.flatMap instantiateRule

/-- The finite instantiation of one source rule is primitive recursive. -/
theorem instantiateRule_primrec :
    Primrec (instantiateRule :
      Rule numSymbols → List (LocalRule numSymbols)) := by
  unfold instantiateRule
  refine Primrec.list_flatMap (Primrec.const (List.finRange numSymbols)) ?_
  apply Primrec₂.mk
  refine Primrec.list_map (Primrec.const (List.finRange numSymbols)) ?_
  apply Primrec₂.mk
  exact localRuleOfTuple_primrec.comp
    ((Primrec.fst.comp Primrec.fst).pair
      ((Primrec.snd.comp Primrec.fst).pair Primrec.snd))

/-- Enumerating all fully specified local rules is primitive recursive in the
finite source table. -/
theorem localRules_primrec :
    Primrec (localRules :
      Table numSymbols → List (LocalRule numSymbols)) := by
  unfold localRules
  exact Primrec.list_flatMap Primrec.id
    (Primrec₂.mk (instantiateRule_primrec.comp Primrec.snd))

/-- Computable form of `localRules_primrec`. -/
theorem localRules_computable :
    Computable (localRules :
      Table numSymbols → List (LocalRule numSymbols)) :=
  localRules_primrec.to_comp

/-! ## Effective compiled-branch containers -/

/-- A compiled affine branch is effectively its four data fields. -/
def compiledBranchEquiv : CompiledAffineBranch ≃
    IntegerAffineBranch × List IntVector3 × List IntVector3 × Nat where
  toFun compiled :=
    (compiled.branch, compiled.inputs, compiled.outputs, compiled.carryBound)
  invFun data :=
    { branch := data.1
      inputs := data.2.1
      outputs := data.2.2.1
      carryBound := data.2.2.2 }
  left_inv := by
    intro compiled
    cases compiled
    rfl
  right_inv := by
    rintro ⟨branch, inputs, outputs, carryBound⟩
    rfl

instance instPrimcodableCompiledAffineBranch :
    Primcodable CompiledAffineBranch :=
  Primcodable.ofEquiv
    (IntegerAffineBranch × List IntVector3 × List IntVector3 × Nat)
    compiledBranchEquiv

theorem compiledBranchEquiv_primrec :
    Primrec compiledBranchEquiv := by
  simpa [compiledBranchEquiv] using
    (Primrec.of_equiv (e := compiledBranchEquiv) :
      Primrec compiledBranchEquiv)

theorem compiledBranchOfTuple_primrec :
    Primrec compiledBranchEquiv.symm := by
  simpa using
    (Primrec.of_equiv_symm (e := compiledBranchEquiv) :
      Primrec compiledBranchEquiv.symm)

/-- Extracting raw branch data from an integer affine branch is primitive
recursive. -/
theorem integerAffineBranchData_primrec :
    Primrec IntegerAffineBranch.equivTuple := by
  simpa [IntegerAffineBranch.equivTuple] using
    (Primrec.of_equiv (e := IntegerAffineBranch.equivTuple) :
      Primrec IntegerAffineBranch.equivTuple)

/-- Compile every fully specified local rule to an affine branch. -/
def branches (table : Table numSymbols) : List CompiledAffineBranch :=
  (localRules table).map LocalRule.compiled

/-- The executable data consumed by the raw affine transducer compiler. -/
def localTransducerInput (spec : LocalRule numSymbols) :
    IntegerAffineBranch.BranchData ×
      List IntVector3 × List IntVector3 × Nat :=
  (branchData spec, spec.inputs, spec.outputs,
    AffineBeatty.carryBound spec.branch)

set_option maxHeartbeats 1000000 in
-- Combining the four separately verified fields creates a large product code.
/-- The complete raw input for one local transducer is primitive recursive. -/
theorem localTransducerInput_primrec :
    Primrec (localTransducerInput : LocalRule numSymbols →
      IntegerAffineBranch.BranchData ×
        List IntVector3 × List IntVector3 × Nat) := by
  exact (branchData_primrec.pair
    (localRule_inputs_primrec.pair
      (localRule_outputs_primrec.pair
        localRule_carryBound_primrec))).of_eq fun _ => rfl

/-- The raw effective transducer for one fully specified local rule. -/
def localTransducer (spec : LocalRule numSymbols) : Transducer :=
  IntegerAffineBranch.transducerData (localTransducerInput spec).1
    (localTransducerInput spec).2.1
    (localTransducerInput spec).2.2.1
    (localTransducerInput spec).2.2.2

/-- The raw effective implementation agrees with the mathematical compiled
branch transducer. -/
theorem localTransducer_eq (spec : LocalRule numSymbols) :
    localTransducer spec = spec.compiled.transducer := by
  rw [localTransducer, localTransducerInput,
    IntegerAffineBranch.transducerData_eq_transducer,
    ofData_branchData]
  rfl

set_option maxHeartbeats 1000000 in
-- Combining the raw branch data with three finite enumerations is a large term.
/-- The local affine transducer compiler is primitive recursive. -/
theorem localTransducer_primrec :
    Primrec (localTransducer :
      LocalRule numSymbols → Transducer) := by
  exact IntegerAffineBranch.transducerData_primrec.comp
    localTransducerInput_primrec

/-- Raw finite union used to exhibit the effective table transducer. -/
def rawTransducer (table : Table numSymbols) : Transducer :=
  (localRules table).flatMap localTransducer

set_option maxHeartbeats 1000000 in
-- The nested table and symbol enumerations create a large list-recursion term.
/-- The raw table transducer is primitive recursive. -/
theorem rawTransducer_primrec :
    Primrec (rawTransducer : Table numSymbols → Transducer) := by
  unfold rawTransducer
  exact Primrec.list_flatMap localRules_primrec
    (Primrec₂.mk (localTransducer_primrec.comp Primrec.snd))

/-- Proof-free effective output of the whole affine branch compiler. -/
def compilerData (table : Table numSymbols) : List
    (IntegerAffineBranch.BranchData ×
      List IntVector3 × List IntVector3 × Nat) :=
  (localRules table).map localTransducerInput

set_option maxHeartbeats 1000000 in
-- Mapping the nested raw branch tuple over all local rules is a large term.
/-- The proof-free affine branch compiler is primitive recursive. -/
theorem compilerData_primrec :
    Primrec (compilerData : Table numSymbols → List
      (IntegerAffineBranch.BranchData ×
        List IntVector3 × List IntVector3 × Nat)) := by
  unfold compilerData
  exact Primrec.list_map localRules_primrec
    (Primrec₂.mk (localTransducerInput_primrec.comp Primrec.snd))

/-- Computable form of `compilerData_primrec`. -/
theorem compilerData_computable :
    Computable (compilerData : Table numSymbols → List
      (IntegerAffineBranch.BranchData ×
        List IntVector3 × List IntVector3 × Nat)) :=
  compilerData_primrec.to_comp

/-- A local rule occurs in the enumeration exactly when its underlying TM0
rule occurs in the source table. -/
theorem mem_localRules_iff (table : Table numSymbols)
    (spec : LocalRule numSymbols) :
    spec ∈ localRules table ↔ spec.rule ∈ table := by
  constructor
  · intro hspec
    simp only [localRules, instantiateRule, List.mem_flatMap,
      List.mem_map] at hspec
    rcases hspec with
      ⟨rule, hrule, leftTop, _, rightTop, _, hspec⟩
    cases hspec
    exact hrule
  · intro hrule
    simp only [localRules, instantiateRule, List.mem_flatMap, List.mem_map]
    exact ⟨spec.rule, hrule, spec.leftTop, List.mem_finRange spec.leftTop,
      spec.rightTop, List.mem_finRange spec.rightTop, rfl⟩

/-- Membership in the local-rule enumeration, with all three enumerated
values exposed explicitly. -/
theorem mem_localRules_iff_exists (table : Table numSymbols)
    (spec : LocalRule numSymbols) :
    spec ∈ localRules table ↔
      ∃ rule ∈ table, ∃ leftTop rightTop,
        spec = { rule := rule, leftTop := leftTop, rightTop := rightTop } := by
  constructor
  · intro hspec
    simp only [localRules, instantiateRule, List.mem_flatMap,
      List.mem_map] at hspec
    rcases hspec with
      ⟨rule, hrule, leftTop, _, rightTop, _, hspec⟩
    exact ⟨rule, hrule, leftTop, rightTop, hspec.symm⟩
  · rintro ⟨rule, hrule, leftTop, rightTop, rfl⟩
    exact (mem_localRules_iff table _).2 hrule

/-- The nested branch tag determines the source rule and both visible side
symbols. -/
theorem localRule_tag_injective :
    Function.Injective
      (LocalRule.tag : LocalRule numSymbols → Nat) := by
  rintro ⟨ruleA, leftA, rightA⟩ ⟨ruleB, leftB, rightB⟩ htag
  simp only [LocalRule.tag, Nat.pair_eq_pair, Encodable.encode_inj,
    Fin.val_inj] at htag
  rcases htag with ⟨rfl, rfl, rfl⟩
  rfl

/-- Consequently the compiled branch tag still determines its complete local
rule specification. -/
theorem compiled_tag_injective :
    Function.Injective fun spec : LocalRule numSymbols =>
      (spec.compiled.branch.tag) := by
  intro a b htag
  exact localRule_tag_injective htag

/-- Membership in the compiled branch list exposes a fully specified local
rule from the source table. -/
theorem mem_branches_iff (table : Table numSymbols)
    (compiled : CompiledAffineBranch) :
    compiled ∈ branches table ↔
      ∃ spec : LocalRule numSymbols,
        spec.rule ∈ table ∧ spec.compiled = compiled := by
  simp only [branches, List.mem_map]
  constructor
  · rintro ⟨spec, hspec, rfl⟩
    exact ⟨spec, (mem_localRules_iff table spec).1 hspec, rfl⟩
  · rintro ⟨spec, hrule, rfl⟩
    exact ⟨spec, (mem_localRules_iff table spec).2 hrule, rfl⟩

/-- Expanded membership inversion exposing the source table rule and the two
visible side-stack symbols. -/
theorem mem_branches_iff_exists (table : Table numSymbols)
    (compiled : CompiledAffineBranch) :
    compiled ∈ branches table ↔
      ∃ rule ∈ table, ∃ leftTop rightTop,
        (LocalRule.compiled
          { rule := rule, leftTop := leftTop, rightTop := rightTop }) =
            compiled := by
  constructor
  · intro hcompiled
    rcases (mem_branches_iff table compiled).1 hcompiled with
      ⟨spec, hrule, rfl⟩
    exact ⟨spec.rule, hrule, spec.leftTop, spec.rightTop, rfl⟩
  · rintro ⟨rule, hrule, leftTop, rightTop, rfl⟩
    exact (mem_branches_iff table _).2
      ⟨{ rule := rule, leftTop := leftTop, rightTop := rightTop }, hrule, rfl⟩

/-- Every explicitly chosen source rule and pair of visible symbols occurs in
the compiled list. -/
theorem compiled_mem_branches (table : Table numSymbols)
    {rule : Rule numSymbols} (hrule : rule ∈ table)
    (leftTop rightTop : Symbol numSymbols) :
    LocalRule.compiled
      { rule := rule, leftTop := leftTop, rightTop := rightTop } ∈
        branches table := by
  exact (mem_branches_iff table _).2
    ⟨{ rule := rule, leftTop := leftTop, rightTop := rightTop }, hrule, rfl⟩

/-- The branch list produced from a table has unique tags, even if the source
table itself contains duplicate rules. -/
theorem branches_tagsUnique (table : Table numSymbols) :
    AffineBranchTagsUnique (branches table) := by
  intro a b ha hb htag
  rcases (mem_branches_iff table a).1 ha with ⟨specA, _, rfl⟩
  rcases (mem_branches_iff table b).1 hb with ⟨specB, _, rfl⟩
  have hspec : specA = specB := compiled_tag_injective htag
  cases hspec
  rfl

/-- The finite piecewise-affine system compiled from a finite TM0 table. -/
def system (table : Table numSymbols) : AffineSystem where
  branches := branches table
  tagsUnique := branches_tagsUnique table

@[simp]
theorem system_branches (table : Table numSymbols) :
    (system table).branches = branches table :=
  rfl

/-- The complete finite transducer compiled from a finite TM0 table. -/
def transducer (table : Table numSymbols) : Transducer :=
  (system table).transducer

/-- The proof-free effective union is extensionally the transducer of the
mathematical affine system. -/
theorem rawTransducer_eq_transducer (table : Table numSymbols) :
    rawTransducer table = transducer table := by
  change (localRules table).flatMap localTransducer =
    ((localRules table).map LocalRule.compiled).flatMap
      CompiledAffineBranch.transducer
  induction localRules table with
  | nil => rfl
  | cons spec specs ih =>
      simp only [List.flatMap_cons, List.map_cons]
      rw [localTransducer_eq spec, ih]

/-- Compiling a finite TM0 table to its affine transducer is primitive
recursive. -/
theorem transducer_primrec :
    Primrec (transducer : Table numSymbols → Transducer) :=
  rawTransducer_primrec.of_eq rawTransducer_eq_transducer

/-- Computable form of `transducer_primrec`. -/
theorem transducer_computable :
    Computable (transducer : Table numSymbols → Transducer) :=
  transducer_primrec.to_comp

/-- The Wang tiles obtained from the compiled finite transducer. -/
def tiles (table : Table numSymbols) : TileSet :=
  (transducer table).tiles

/-- The complete finite-table-to-Wang-tiles compiler is primitive recursive. -/
theorem tiles_primrec :
    Primrec (tiles : Table numSymbols → TileSet) := by
  exact (Transducer.tiles_primrec.comp transducer_primrec).of_eq fun _ => rfl

/-- Computable form of `tiles_primrec`. -/
theorem tiles_computable :
    Computable (tiles : Table numSymbols → TileSet) :=
  tiles_primrec.to_comp

/-- A transition in the table transducer exposes its source rule, both visible
side symbols, and the corresponding local affine transducer. -/
theorem mem_transducer_iff (table : Table numSymbols) (t : Transition) :
    t ∈ transducer table ↔
      ∃ rule ∈ table, ∃ leftTop rightTop,
        t ∈ (LocalRule.compiled
          { rule := rule, leftTop := leftTop,
            rightTop := rightTop }).transducer := by
  rw [transducer, AffineSystem.mem_transducer_iff]
  constructor
  · rintro ⟨compiled, hcompiled, ht⟩
    rcases (mem_branches_iff_exists table compiled).1 hcompiled with
      ⟨rule, hrule, leftTop, rightTop, rfl⟩
    exact ⟨rule, hrule, leftTop, rightTop, ht⟩
  · rintro ⟨rule, hrule, leftTop, rightTop, ht⟩
    refine ⟨LocalRule.compiled
      { rule := rule, leftTop := leftTop, rightTop := rightTop }, ?_, ht⟩
    exact compiled_mem_branches table hrule leftTop rightTop

end AffineTMSystem
end Kari
end LeanWang
