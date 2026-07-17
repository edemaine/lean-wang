/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Kari.AffineTM
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
