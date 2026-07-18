/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Kari.AffineTM
import LeanWang.Kari.AffineLimit
import Mathlib.Tactic.Linarith

/-!
# Beatty rows for finite-TM0 affine branches

The local affine compiler assigns each visible tape symbol the closed interval
`[2a, 2a+1]`, while the center coordinate is an exact integer.  This module
proves that every componentwise Beatty digit of such a real configuration lies
in the finite input alphabet emitted by `AffineTM.LocalRule.compiled`.

The main scalar lemma is pleasantly short: the length-one discrepancy theorem
for Beatty sequences says that a digit differs from the represented real by
less than one.  An integer lying within one of a real in `[m,m+1]` must be
either `m` or `m+1`.
-/

namespace LeanWang
namespace Kari
namespace AffineTM

open Hooper.FiniteTM0

noncomputable section

variable {numSymbols : Nat}

/-- Every Beatty digit of a real in `[m,m+1]` is one of the two interval
endpoints. -/
theorem beatty_digit_eq_or_eq_add_one (alpha : ℝ) (m : Int)
    (hlower : (m : ℝ) ≤ alpha) (hupper : alpha ≤ (m : ℝ) + 1)
    (i : Int) :
    Beatty.digit alpha i = m ∨ Beatty.digit alpha i = m + 1 := by
  have hdiscrepancy :
      |(Beatty.digit alpha i : ℝ) - alpha| < 1 := by
    simpa using Beatty.abs_sum_digit_sub alpha i 1
  rw [abs_lt] at hdiscrepancy
  have hlower' : ((m - 1 : Int) : ℝ) < (Beatty.digit alpha i : ℝ) := by
    push_cast
    linarith [hdiscrepancy.1]
  have hupper' : (Beatty.digit alpha i : ℝ) < ((m + 2 : Int) : ℝ) := by
    push_cast
    linarith [hdiscrepancy.2]
  have hlowerInt : m - 1 < Beatty.digit alpha i := by
    exact_mod_cast hlower'
  have hupperInt : Beatty.digit alpha i < m + 2 := by
    exact_mod_cast hupper'
  omega

/-- A real side-stack coordinate currently exposes symbol `a`. -/
def InSymbolInterval (a : Symbol numSymbols) (x : ℝ) : Prop :=
  (symbolValue a : ℝ) ≤ x ∧ x ≤ (symbolValue a : ℝ) + 1

/-- The separated unit intervals identify their tape symbol uniquely. -/
theorem eq_of_inSymbolInterval {a b : Symbol numSymbols} {x : ℝ}
    (ha : InSymbolInterval a x) (hb : InSymbolInterval b x) :
    a = b := by
  have habReal : (symbolValue a : ℝ) ≤ (symbolValue b : ℝ) + 1 := by
    linarith [ha.1, hb.2]
  have hbaReal : (symbolValue b : ℝ) ≤ (symbolValue a : ℝ) + 1 := by
    linarith [hb.1, ha.2]
  have hab : symbolValue a ≤ symbolValue b + 1 := by
    exact_mod_cast habReal
  have hba : symbolValue b ≤ symbolValue a + 1 := by
    exact_mod_cast hbaReal
  apply Fin.ext
  simp only [symbolValue] at hab hba
  omega

/-- Pushing a symbol onto any valid side stack puts the result in that
symbol's separated unit interval. -/
theorem inSymbolInterval_push (a b : Symbol numSymbols) (x : ℝ)
    (hx : InSymbolInterval b x) :
    InSymbolInterval a (LocalRule.push a x) := by
  have hbase : (0 : ℝ) < sideBase numSymbols := by
    exact_mod_cast sideBase_pos numSymbols
  have hsymbolNonneg : (0 : ℝ) ≤ symbolValue b := by
    simp [symbolValue]
  have hxNonneg : 0 ≤ x := hsymbolNonneg.trans hx.1
  have htopNat : 2 * b.val + 1 < sideBase numSymbols := by
    simp only [sideBase]
    omega
  have htop : (symbolValue b : ℝ) + 1 < sideBase numSymbols := by
    simp only [symbolValue]
    push_cast
    exact_mod_cast htopNat
  have hxBase : x < sideBase numSymbols := hx.2.trans_lt htop
  have hquotNonneg : 0 ≤ x / sideBase numSymbols :=
    div_nonneg hxNonneg hbase.le
  have hquotLt : x / sideBase numSymbols < 1 :=
    (div_lt_one hbase).2 hxBase
  simp only [LocalRule.push]
  constructor <;> linarith

@[simp]
theorem centerValue_eq_centerValue
    (q r : State) (a b : Symbol numSymbols) :
    centerValue q a = centerValue r b ↔ q = r ∧ a = b := by
  constructor
  · intro h
    change ((Nat.pair q a.val : Nat) : Int) =
      ((Nat.pair r b.val : Nat) : Int) at h
    have hnat : Nat.pair q a.val = Nat.pair r b.val := by
      exact_mod_cast h
    rw [Nat.pair_eq_pair] at hnat
    exact ⟨hnat.1, Fin.ext hnat.2⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Beatty digits of a valid side-stack coordinate belong to its two-element
integer digit alphabet. -/
theorem beatty_digit_mem_intervalDigits (a : Symbol numSymbols) (x : ℝ)
    (hinterval : InSymbolInterval a x) (i : Int) :
    Beatty.digit x i ∈ intervalDigits (symbolValue a) := by
  rw [mem_intervalDigits]
  exact beatty_digit_eq_or_eq_add_one x (symbolValue a)
    hinterval.1 hinterval.2 i

/-- The Beatty row representing an integer is the constant row at that
integer. -/
@[simp]
theorem beatty_digit_intCast (z i : Int) :
    Beatty.digit (z : ℝ) i = z := by
  have hsucc : ((i : ℝ) + 1) * (z : ℝ) = (((i + 1) * z : Int) : ℝ) := by
    push_cast
    ring
  have hbase : (i : ℝ) * (z : ℝ) = ((i * z : Int) : ℝ) := by
    push_cast
    ring
  simp only [Beatty.digit, Beatty.sequence, Int.cast_add, Int.cast_one]
  rw [hsucc, hbase, Int.floor_intCast, Int.floor_intCast]
  ring

/-- Real source-domain condition selected by one local machine branch. -/
def LocalRule.InInputRegion (spec : LocalRule numSymbols)
    (v : Fin 3 → ℝ) : Prop :=
  InSymbolInterval spec.leftTop (v 0) ∧
    InSymbolInterval spec.rightTop (v 1) ∧
    v 2 = centerValue spec.source spec.read

/-- Componentwise interval membership is sufficient for every Beatty digit
to belong to the corresponding finite three-dimensional box. -/
theorem digitVector_mem_digitBox
    (leftTop rightTop : Symbol numSymbols) (center : Int)
    (v : Fin 3 → ℝ)
    (hleft : InSymbolInterval leftTop (v 0))
    (hright : InSymbolInterval rightTop (v 1))
    (hcenter : v 2 = center) (i : Int) :
    AffineBeatty.digitVector v i ∈ digitBox leftTop rightTop center := by
  rw [mem_digitBox_iff]
  constructor
  · change Beatty.digit (v 0) i = symbolValue leftTop ∨
      Beatty.digit (v 0) i = symbolValue leftTop + 1
    exact beatty_digit_eq_or_eq_add_one _ _ hleft.1 hleft.2 i
  constructor
  · change Beatty.digit (v 1) i = symbolValue rightTop ∨
      Beatty.digit (v 1) i = symbolValue rightTop + 1
    exact beatty_digit_eq_or_eq_add_one _ _ hright.1 hright.2 i
  · change Beatty.digit (v 2) i = center
    rw [hcenter]
    exact beatty_digit_intCast _ _

/-- Every componentwise Beatty digit of a point in the branch's source region
is one of the explicitly enumerated input vectors. -/
theorem LocalRule.digitVector_mem_inputs (spec : LocalRule numSymbols)
    (v : Fin 3 → ℝ) (hregion : spec.InInputRegion v) (i : Int) :
    AffineBeatty.digitVector v i ∈ spec.inputs := by
  change AffineBeatty.digitVector v i ∈
    digitBox spec.leftTop spec.rightTop
      (centerValue spec.source spec.read)
  exact digitVector_mem_digitBox spec.leftTop spec.rightTop
    (centerValue spec.source spec.read) v hregion.1 hregion.2.1
    hregion.2.2 i

/-- Conversely, the coordinatewise closed envelope of a local branch's input
alphabet is exactly strong enough to recover its source-region constraints.
This is the bridge used for affine orbits extracted analytically from
transducer diagrams. -/
theorem LocalRule.inInputRegion_of_inInputEnvelope
    (spec : LocalRule numSymbols) (v : Fin 3 → ℝ)
    (henvelope : AffineLimit.InInputEnvelope spec.compiled v) :
    spec.InInputRegion v := by
  have hbox (digit : IntVector3) (hdigit : digit ∈ spec.inputs) :
      (digit.x = symbolValue spec.leftTop ∨
          digit.x = symbolValue spec.leftTop + 1) ∧
        (digit.y = symbolValue spec.rightTop ∨
          digit.y = symbolValue spec.rightTop + 1) ∧
        digit.z = centerValue spec.source spec.read := by
    exact (mem_digitBox_iff spec.leftTop spec.rightTop
      (centerValue spec.source spec.read) digit).1 hdigit
  have hleft := henvelope (0 : Fin 3)
    (symbolValue spec.leftTop : ℝ)
    ((symbolValue spec.leftTop : ℝ) + 1) (by
      intro digit hdigit
      have hx := (hbox digit hdigit).1
      simp only [AffineBeatty.toReal]
      rcases hx with hx | hx <;> rw [hx] <;> norm_num)
  have hright := henvelope (1 : Fin 3)
    (symbolValue spec.rightTop : ℝ)
    ((symbolValue spec.rightTop : ℝ) + 1) (by
      intro digit hdigit
      have hy := (hbox digit hdigit).2.1
      simp only [AffineBeatty.toReal]
      rcases hy with hy | hy <;> rw [hy] <;> norm_num)
  have hcenter := henvelope (2 : Fin 3)
    (centerValue spec.source spec.read : ℝ)
    (centerValue spec.source spec.read : ℝ) (by
      intro digit hdigit
      have hz := (hbox digit hdigit).2.2
      simp only [AffineBeatty.toReal]
      rw [hz]
      exact ⟨le_rfl, le_rfl⟩)
  exact ⟨hleft, hright,
    le_antisymm hcenter.2 hcenter.1⟩

/-- A point in the rectangular source region belongs to the coordinatewise
closed envelope of the branch's endpoint digit box. -/
theorem LocalRule.inInputEnvelope_of_inInputRegion
    (spec : LocalRule numSymbols) (v : Fin 3 → ℝ)
    (hregion : spec.InInputRegion v) :
    AffineLimit.InInputEnvelope spec.compiled v := by
  intro j lower upper hbounds
  let base : IntVector3 :=
    ⟨symbolValue spec.leftTop, symbolValue spec.rightTop,
      centerValue spec.source spec.read⟩
  have hbase : base ∈ spec.inputs := by
    change base ∈ digitBox spec.leftTop spec.rightTop
      (centerValue spec.source spec.read)
    rw [mem_digitBox_iff]
    exact ⟨Or.inl rfl, Or.inl rfl, rfl⟩
  fin_cases j
  · let high : IntVector3 :=
      ⟨symbolValue spec.leftTop + 1, symbolValue spec.rightTop,
        centerValue spec.source spec.read⟩
    have hhigh : high ∈ spec.inputs := by
      change high ∈ digitBox spec.leftTop spec.rightTop
        (centerValue spec.source spec.read)
      rw [mem_digitBox_iff]
      exact ⟨Or.inr rfl, Or.inl rfl, rfl⟩
    have hlo := (hbounds base hbase).1
    have hhi := (hbounds high hhigh).2
    change lower ≤ (base.x : ℝ) at hlo
    change (high.x : ℝ) ≤ upper at hhi
    change lower ≤ v 0 ∧ v 0 ≤ upper
    dsimp only [base] at hlo
    dsimp only [high] at hhi
    push_cast at hhi
    exact ⟨hlo.trans hregion.1.1, hregion.1.2.trans hhi⟩
  · let high : IntVector3 :=
      ⟨symbolValue spec.leftTop, symbolValue spec.rightTop + 1,
        centerValue spec.source spec.read⟩
    have hhigh : high ∈ spec.inputs := by
      change high ∈ digitBox spec.leftTop spec.rightTop
        (centerValue spec.source spec.read)
      rw [mem_digitBox_iff]
      exact ⟨Or.inl rfl, Or.inr rfl, rfl⟩
    have hlo := (hbounds base hbase).1
    have hhi := (hbounds high hhigh).2
    change lower ≤ (base.y : ℝ) at hlo
    change (high.y : ℝ) ≤ upper at hhi
    change lower ≤ v 1 ∧ v 1 ≤ upper
    dsimp only [base] at hlo
    dsimp only [high] at hhi
    push_cast at hhi
    exact ⟨hlo.trans hregion.2.1.1, hregion.2.1.2.trans hhi⟩
  · have hb := hbounds base hbase
    change lower ≤ (base.z : ℝ) ∧ (base.z : ℝ) ≤ upper at hb
    change lower ≤ v 2 ∧ v 2 ≤ upper
    dsimp only [base] at hb
    rw [hregion.2.2]
    exact hb

/-- Discrete compatibility of two consecutive local branches.  These are
exactly the state, scanned-symbol, and visible-stack equalities imposed by
one Post-Turing action. -/
def LocalRule.Follows (spec next : LocalRule numSymbols) : Prop :=
  match spec.action with
  | .write written =>
      spec.target = next.source ∧ written = next.read ∧
        spec.leftTop = next.leftTop ∧ spec.rightTop = next.rightTop
  | .moveLeft =>
      spec.target = next.source ∧ spec.leftTop = next.read ∧
        spec.read = next.rightTop
  | .moveRight =>
      spec.target = next.source ∧ spec.rightTop = next.read ∧
        spec.read = next.leftTop

theorem LocalRule.target_eq_source_of_follows
    {spec next : LocalRule numSymbols} (h : spec.Follows next) :
    spec.target = next.source := by
  cases haction : spec.action <;>
    simp only [Follows, haction] at h <;>
    exact h.1

/-- Source-region membership at two consecutive orbit points, together with
the exact affine update, forces the corresponding discrete local rules to
follow one another. -/
theorem LocalRule.follows_of_regions_realStep
    (spec next : LocalRule numSymbols) (input output : Fin 3 → ℝ)
    (hinput : spec.InInputRegion input)
    (houtput : next.InInputRegion output)
    (hstep : output = spec.realStep input) :
    spec.Follows next := by
  cases haction : spec.action with
  | write written =>
      have hcenter : (centerValue spec.target written : ℝ) =
          (centerValue next.source next.read : ℝ) := by
        calc
          (centerValue spec.target written : ℝ) = spec.realStep input 2 := by
            simp [LocalRule.realStep, haction]
          _ = output 2 := (congrFun hstep 2).symm
          _ = centerValue next.source next.read := houtput.2.2
      have hcenterDiscrete :=
        (centerValue_eq_centerValue spec.target next.source written next.read).1
          (by exact_mod_cast hcenter)
      have hleftAt : InSymbolInterval spec.leftTop (output 0) := by
        rw [hstep]
        simpa [LocalRule.realStep, haction] using hinput.1
      have hrightAt : InSymbolInterval spec.rightTop (output 1) := by
        rw [hstep]
        simpa [LocalRule.realStep, haction] using hinput.2.1
      simp only [Follows, haction]
      exact ⟨hcenterDiscrete.1, hcenterDiscrete.2,
        eq_of_inSymbolInterval hleftAt houtput.1,
        eq_of_inSymbolInterval hrightAt houtput.2.1⟩
  | moveLeft =>
      have hcenter : (centerValue spec.target spec.leftTop : ℝ) =
          (centerValue next.source next.read : ℝ) := by
        calc
          (centerValue spec.target spec.leftTop : ℝ) =
              spec.realStep input 2 := by
            simp [LocalRule.realStep, haction]
          _ = output 2 := (congrFun hstep 2).symm
          _ = centerValue next.source next.read := houtput.2.2
      have hcenterDiscrete :=
        (centerValue_eq_centerValue spec.target next.source
          spec.leftTop next.read).1 (by exact_mod_cast hcenter)
      have hrightAt : InSymbolInterval spec.read (output 1) := by
        rw [hstep]
        simpa [LocalRule.realStep, haction] using
          inSymbolInterval_push spec.read spec.rightTop (input 1) hinput.2.1
      simp only [Follows, haction]
      exact ⟨hcenterDiscrete.1, hcenterDiscrete.2,
        eq_of_inSymbolInterval hrightAt houtput.2.1⟩
  | moveRight =>
      have hcenter : (centerValue spec.target spec.rightTop : ℝ) =
          (centerValue next.source next.read : ℝ) := by
        calc
          (centerValue spec.target spec.rightTop : ℝ) =
              spec.realStep input 2 := by
            simp [LocalRule.realStep, haction]
          _ = output 2 := (congrFun hstep 2).symm
          _ = centerValue next.source next.read := houtput.2.2
      have hcenterDiscrete :=
        (centerValue_eq_centerValue spec.target next.source
          spec.rightTop next.read).1 (by exact_mod_cast hcenter)
      have hleftAt : InSymbolInterval spec.read (output 0) := by
        rw [hstep]
        simpa [LocalRule.realStep, haction] using
          inSymbolInterval_push spec.read spec.leftTop (input 0) hinput.1
      simp only [Follows, haction]
      exact ⟨hcenterDiscrete.1, hcenterDiscrete.2,
        eq_of_inSymbolInterval hleftAt houtput.1⟩

/-- Real target-domain condition emitted by one local machine branch.  A
moving branch leaves the newly exposed top symbol existential, matching the
finite union used in `LocalRule.outputs`. -/
def LocalRule.InOutputRegion (spec : LocalRule numSymbols)
    (v : Fin 3 → ℝ) : Prop :=
  match spec.action with
  | .write written =>
      InSymbolInterval spec.leftTop (v 0) ∧
        InSymbolInterval spec.rightTop (v 1) ∧
        v 2 = centerValue spec.target written
  | .moveLeft =>
      ∃ newLeftTop : Symbol numSymbols,
        InSymbolInterval newLeftTop (v 0) ∧
          InSymbolInterval spec.read (v 1) ∧
          v 2 = centerValue spec.target spec.leftTop
  | .moveRight =>
      ∃ newRightTop : Symbol numSymbols,
        InSymbolInterval spec.read (v 0) ∧
          InSymbolInterval newRightTop (v 1) ∧
          v 2 = centerValue spec.target spec.rightTop

/-- Every componentwise Beatty digit of a point in the advertised target
region belongs to the branch's explicitly enumerated output alphabet. -/
theorem LocalRule.digitVector_mem_outputs (spec : LocalRule numSymbols)
    (v : Fin 3 → ℝ) (hregion : spec.InOutputRegion v) (i : Int) :
    AffineBeatty.digitVector v i ∈ spec.outputs := by
  cases haction : spec.action with
  | write written =>
      simp only [InOutputRegion, haction] at hregion
      simp only [outputs, haction]
      exact digitVector_mem_digitBox spec.leftTop spec.rightTop
        (centerValue spec.target written) v hregion.1 hregion.2.1
        hregion.2.2 i
  | moveLeft =>
      simp only [InOutputRegion, haction] at hregion
      rcases hregion with ⟨newLeftTop, hleft, hright, hcenter⟩
      simp only [outputs, haction, List.mem_flatMap]
      refine ⟨newLeftTop, by simp, ?_⟩
      exact digitVector_mem_digitBox newLeftTop spec.read
        (centerValue spec.target spec.leftTop) v hleft hright hcenter i
  | moveRight =>
      simp only [InOutputRegion, haction] at hregion
      rcases hregion with ⟨newRightTop, hleft, hright, hcenter⟩
      simp only [outputs, haction, List.mem_flatMap]
      refine ⟨newRightTop, by simp, ?_⟩
      exact digitVector_mem_digitBox spec.read newRightTop
        (centerValue spec.target spec.rightTop) v hleft hright hcenter i

end

end AffineTM
end Kari
end LeanWang
