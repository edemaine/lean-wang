/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Kari.AffineBeatty
import LeanWang.Kari.AffineSystem
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

/-!
# Limits of affine transducer diagrams

The converse direction of Kari's affine-transducer lemma is a limiting
argument.  Average longer and longer prefixes of the bottom digit row and
choose a convergent subsequence.  The exact carry telescope shows that the
same subsequence converges on every later row: the two endpoint carries are
uniformly bounded, so their contribution divided by the prefix length tends
to zero.  The successive limits therefore form a forward orbit of the affine
branches selected by the rows.

This file makes that argument independent of the later machine-specific
choice of affine branches.  Prefixes have length `n + 1`, avoiding a special
case at zero.
-/

namespace LeanWang
namespace Kari

open Filter Topology
open scoped BigOperators

noncomputable section

namespace AffineLimit

/-- Interpret a rational vector as a real vector. -/
def ratToReal (v : Fin 3 → ℚ) : Fin 3 → ℝ :=
  fun j => (v j : ℝ)

/-- Real interpretation of a vertical digit color. -/
def digitValue (color : Nat) : Fin 3 → ℝ :=
  ratToReal (IntegerAffineBranch.digitValue color)

@[simp] theorem digitValue_code (v : IntVector3) :
    digitValue v.code = AffineBeatty.toReal v := by
  funext j
  fin_cases j <;>
    simp [digitValue, ratToReal, AffineBeatty.toReal, IntVector3.toRat]

/-- Real interpretation of a horizontal carry color for one branch. -/
def carryValue (branch : IntegerAffineBranch) (color : Nat) : Fin 3 → ℝ :=
  ratToReal (branch.carryValue color)

/-- Average of the first `n + 1` decoded digit vectors in row `y`. -/
def prefixAverage (digits : Int × Nat → Nat) (y n : Nat) : Fin 3 → ℝ :=
  fun j =>
    (∑ i ∈ Finset.range (n + 1),
      digitValue (digits ((i : Int), y)) j) / (n + 1 : Nat)

/-- The real affine map encoded by an integer branch. -/
def branchMap (branch : IntegerAffineBranch) (v : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun j =>
    (AffineBeatty.mulReal branch.linearNumerator v j +
      AffineBeatty.toReal branch.offsetNumerator j) /
        branch.denominator

/-- `branchMap` satisfies the scaled real affine equation used by the Beatty
construction. -/
theorem realizes_branchMap (branch : IntegerAffineBranch) (v : Fin 3 → ℝ) :
    AffineBeatty.Realizes branch v (branchMap branch v) := by
  intro j
  have hden : (branch.denominator : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt branch.denominator_pos
  rw [branchMap]
  exact (mul_div_cancel₀ _ hden)

/-- The real affine map of one branch is continuous. -/
theorem continuous_branchMap (branch : IntegerAffineBranch) :
    Continuous (branchMap branch) := by
  apply continuous_pi
  intro j
  fin_cases j <;>
    simp only [branchMap, AffineBeatty.mulReal, AffineBeatty.toReal] <;>
    fun_prop

private theorem abs_int_div_denominator_le (z : Int) (bound denominator : Nat)
    (hz : -(bound : Int) ≤ z ∧ z ≤ bound) (hden : 0 < denominator) :
    |(((z : ℚ) / denominator : ℚ) : ℝ)| ≤ (bound : ℝ) := by
  rw [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < denominator)]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < denominator)).2
  have hz' : |(z : ℝ)| ≤ (bound : ℝ) := by
    rw [abs_le]
    constructor
    · exact_mod_cast hz.1
    · exact_mod_cast hz.2
  have hden' : (1 : ℝ) ≤ denominator := by
    exact_mod_cast hden
  nlinarith [show (0 : ℝ) ≤ bound by positivity]

/-- Carries occurring in a row compiled with `compiled` are uniformly
bounded after real interpretation.  This is where finiteness of the carry
alphabet enters the limiting argument. -/
theorem abs_carryValue_le_of_row
    {digits carries : Int × Nat → Nat} {y : Nat}
    (compiled : CompiledAffineBranch)
    (hrow : ∀ x : Int,
      ∃ t ∈ compiled.transducer,
        AffineSystem.TransitionMatchesCell t digits carries (x, y) ∧
          t.SatisfiesAffine compiled.branch.rationalMap
            IntegerAffineBranch.digitValue compiled.branch.carryValue)
    (x : Int) (j : Fin 3) :
    |carryValue compiled.branch (carries (x, y)) j| ≤
      (compiled.carryBound : ℝ) := by
  rcases hrow x with ⟨t, ht, hmatches, _⟩
  rcases (compiled.branch.mem_transducer_iff compiled.inputs compiled.outputs
      compiled.carryBound t).1 ht with
    ⟨input, output, left, right, _, _, hleft, _, _, rfl⟩
  have hcarries :
      carries (x, y) = compiled.branch.carryColor left := by
    simpa [IntegerAffineBranch.transition] using hmatches.2.2.1.symm
  rw [hcarries]
  simp only [carryValue, ratToReal,
    IntegerAffineBranch.carryValue_carryColor]
  have hbounds := (IntVector3.mem_bounded left compiled.carryBound).1 hleft
  fin_cases j
  · exact abs_int_div_denominator_le left.x compiled.carryBound
      compiled.branch.denominator ⟨hbounds.1, hbounds.2.1⟩
      compiled.branch.denominator_pos
  · change |(((left.y : ℚ) / compiled.branch.denominator : ℚ) : ℝ)| ≤
      (compiled.carryBound : ℝ)
    exact abs_int_div_denominator_le left.y compiled.carryBound
      compiled.branch.denominator ⟨hbounds.2.2.1, hbounds.2.2.2.1⟩
      compiled.branch.denominator_pos
  · change |(((left.z : ℚ) / compiled.branch.denominator : ℚ) : ℝ)| ≤
      (compiled.carryBound : ℝ)
    exact abs_int_div_denominator_le left.z compiled.carryBound
      compiled.branch.denominator ⟨hbounds.2.2.2.2.1, hbounds.2.2.2.2.2⟩
      compiled.branch.denominator_pos

/-- Every vertical digit in a compiled row comes from that branch's declared
finite input alphabet. -/
theorem exists_inputVector_of_row
    {digits carries : Int × Nat → Nat} {y : Nat}
    (compiled : CompiledAffineBranch)
    (hrow : ∀ x : Int,
      ∃ t ∈ compiled.transducer,
        AffineSystem.TransitionMatchesCell t digits carries (x, y) ∧
          t.SatisfiesAffine compiled.branch.rationalMap
            IntegerAffineBranch.digitValue compiled.branch.carryValue)
    (x : Int) :
    ∃ v ∈ compiled.inputs,
      digitValue (digits (x, y)) = AffineBeatty.toReal v := by
  rcases hrow x with ⟨t, ht, hmatches, _⟩
  rcases (compiled.branch.mem_transducer_iff compiled.inputs compiled.outputs
      compiled.carryBound t).1 ht with
    ⟨input, output, left, right, hinput, _, _, _, _, rfl⟩
  refine ⟨input, hinput, ?_⟩
  have hdigit : digits (x, y) = input.code := by
    simpa [IntegerAffineBranch.transition] using hmatches.1.symm
  simp only [hdigit, digitValue_code]

/-- A convenient explicit bound for the real norms of a compiled branch's
finite input alphabet. -/
def inputBound (compiled : CompiledAffineBranch) : ℝ :=
  (compiled.inputs.map fun v => ‖AffineBeatty.toReal v‖).sum

private theorem sum_norm_toReal_nonneg (inputs : List IntVector3) :
    0 ≤ (inputs.map fun v => ‖AffineBeatty.toReal v‖).sum := by
  induction inputs with
  | nil => simp
  | cons head tail ih =>
      simpa only [List.map_cons, List.sum_cons] using
        add_nonneg (norm_nonneg (AffineBeatty.toReal head)) ih

private theorem norm_toReal_le_sum_of_mem (v : IntVector3)
    (inputs : List IntVector3) (hv : v ∈ inputs) :
    ‖AffineBeatty.toReal v‖ ≤
      (inputs.map fun w => ‖AffineBeatty.toReal w‖).sum := by
  induction inputs with
  | nil => simp at hv
  | cons head tail ih =>
      simp only [List.mem_cons] at hv
      simp only [List.map_cons, List.sum_cons]
      rcases hv with rfl | hv
      · exact le_add_of_nonneg_right (sum_norm_toReal_nonneg tail)
      · exact (ih hv).trans (le_add_of_nonneg_left (norm_nonneg _))

/-- Every decoded digit in a compiled row has norm at most `inputBound`. -/
theorem norm_digitValue_le_inputBound_of_row
    {digits carries : Int × Nat → Nat} {y : Nat}
    (compiled : CompiledAffineBranch)
    (hrow : ∀ x : Int,
      ∃ t ∈ compiled.transducer,
        AffineSystem.TransitionMatchesCell t digits carries (x, y) ∧
          t.SatisfiesAffine compiled.branch.rationalMap
            IntegerAffineBranch.digitValue compiled.branch.carryValue)
    (x : Int) :
    ‖digitValue (digits (x, y))‖ ≤ inputBound compiled := by
  rcases exists_inputVector_of_row compiled hrow x with ⟨v, hv, heq⟩
  rw [heq, inputBound]
  exact norm_toReal_le_sum_of_mem v compiled.inputs hv

/-- Prefix averages of one compiled row remain in the closed norm ball whose
radius is the finite input-alphabet bound. -/
theorem norm_prefixAverage_le_inputBound_of_row
    {digits carries : Int × Nat → Nat} {y : Nat}
    (compiled : CompiledAffineBranch)
    (hrow : ∀ x : Int,
      ∃ t ∈ compiled.transducer,
        AffineSystem.TransitionMatchesCell t digits carries (x, y) ∧
          t.SatisfiesAffine compiled.branch.rationalMap
            IntegerAffineBranch.digitValue compiled.branch.carryValue)
    (n : Nat) :
    ‖prefixAverage digits y n‖ ≤ inputBound compiled := by
  let rowDigit : Nat → Fin 3 → ℝ := fun i =>
    digitValue (digits ((i : Int), y))
  have haverage : prefixAverage digits y n =
      ((n + 1 : Nat) : ℝ)⁻¹ •
        ∑ i ∈ Finset.range (n + 1), rowDigit i := by
    funext j
    simp only [prefixAverage, rowDigit, Pi.smul_apply, smul_eq_mul,
      inv_mul_eq_div, Finset.sum_apply]
  have hsum :
      ‖∑ i ∈ Finset.range (n + 1), rowDigit i‖ ≤
        ((n + 1 : Nat) : ℝ) * inputBound compiled := by
    calc
      ‖∑ i ∈ Finset.range (n + 1), rowDigit i‖ ≤
          ∑ i ∈ Finset.range (n + 1), ‖rowDigit i‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _i ∈ Finset.range (n + 1), inputBound compiled := by
        exact Finset.sum_le_sum fun i _ =>
          norm_digitValue_le_inputBound_of_row compiled hrow (i : Int)
      _ = ((n + 1 : Nat) : ℝ) * inputBound compiled := by
        simp [Nat.cast_add]
  rw [haverage, norm_smul]
  have hlength : (0 : ℝ) < (n + 1 : Nat) := by positivity
  have hinvNorm : ‖(((n + 1 : Nat) : ℝ)⁻¹)‖ =
      (((n + 1 : Nat) : ℝ)⁻¹) := by
    exact Real.norm_of_nonneg (inv_nonneg.mpr hlength.le)
  rw [hinvNorm]
  calc
    (((n + 1 : Nat) : ℝ)⁻¹) *
          ‖∑ i ∈ Finset.range (n + 1), rowDigit i‖ ≤
        (((n + 1 : Nat) : ℝ)⁻¹) *
          (((n + 1 : Nat) : ℝ) * inputBound compiled) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hlength.le)
    _ = inputBound compiled := by
      rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hlength), one_mul]

/-- The entire sequence of prefix averages of one compiled row is bounded. -/
theorem isBounded_range_prefixAverage_of_row
    {digits carries : Int × Nat → Nat} {y : Nat}
    (compiled : CompiledAffineBranch)
    (hrow : ∀ x : Int,
      ∃ t ∈ compiled.transducer,
        AffineSystem.TransitionMatchesCell t digits carries (x, y) ∧
          t.SatisfiesAffine compiled.branch.rationalMap
            IntegerAffineBranch.digitValue compiled.branch.carryValue) :
    Bornology.IsBounded (Set.range (prefixAverage digits y)) := by
  rw [isBounded_iff_forall_norm_le]
  refine ⟨inputBound compiled, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact norm_prefixAverage_le_inputBound_of_row compiled hrow n

/-- Bolzano--Weierstrass supplies a convergent subsequence of prefix averages
from the finite input alphabet of any compiled row. -/
theorem exists_tendsto_subseq_prefixAverage_of_row
    {digits carries : Int × Nat → Nat} {y : Nat}
    (compiled : CompiledAffineBranch)
    (hrow : ∀ x : Int,
      ∃ t ∈ compiled.transducer,
        AffineSystem.TransitionMatchesCell t digits carries (x, y) ∧
          t.SatisfiesAffine compiled.branch.rationalMap
            IntegerAffineBranch.digitValue compiled.branch.carryValue) :
    ∃ (φ : Nat → Nat) (limit : Fin 3 → ℝ),
      StrictMono φ ∧
        Tendsto (prefixAverage digits y ∘ φ) atTop (𝓝 limit) := by
  have hbounded := isBounded_range_prefixAverage_of_row compiled hrow
  rcases tendsto_subseq_of_bounded hbounded
      (fun n => Set.mem_range_self n) with
    ⟨limit, _hclosure, φ, hφ, hlimit⟩
  exact ⟨φ, limit, hφ, hlimit⟩

/-- Any sequence of carries taken from one compiled row, divided by prefix
lengths along a strictly increasing subsequence, tends to zero. -/
theorem carryValue_div_tendsto_zero_of_row
    {digits carries : Int × Nat → Nat} {y : Nat}
    (compiled : CompiledAffineBranch)
    (hrow : ∀ x : Int,
      ∃ t ∈ compiled.transducer,
        AffineSystem.TransitionMatchesCell t digits carries (x, y) ∧
          t.SatisfiesAffine compiled.branch.rationalMap
            IntegerAffineBranch.digitValue compiled.branch.carryValue)
    (φ : Nat → Nat) (hφ : StrictMono φ) (position : Nat → Int)
    (j : Fin 3) :
    Tendsto (fun n =>
        carryValue compiled.branch (carries (position n, y)) j /
          (φ n + 1 : Nat)) atTop (𝓝 0) := by
  have habs (n : Nat) :
      |carryValue compiled.branch (carries (position n, y)) j| ≤
        (compiled.carryBound : ℝ) :=
    abs_carryValue_le_of_row compiled hrow (position n) j
  have hlower : ∀ᶠ n in atTop,
      -(compiled.carryBound : ℝ) ≤
        carryValue compiled.branch (carries (position n, y)) j :=
    Filter.Eventually.of_forall fun n => (abs_le.mp (habs n)).1
  have hupper : ∀ᶠ n in atTop,
      carryValue compiled.branch (carries (position n, y)) j ≤
        (compiled.carryBound : ℝ) :=
    Filter.Eventually.of_forall fun n => (abs_le.mp (habs n)).2
  have hφtop : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hdenom : Tendsto (fun n => ((φ n + 1 : Nat) : ℝ)) atTop atTop := by
    have hcast : Tendsto (fun n => (φ n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hφtop
    simpa only [Nat.cast_add, Nat.cast_one] using
      tendsto_atTop_add_const_right atTop (1 : ℝ) hcast
  exact tendsto_bdd_div_atTop_nhds_zero hlower hupper hdenom

/-- The exact rational carry telescope, divided by prefix length and cast to
the reals.  It expresses the next-row prefix average as the affine image of
the current average plus the two endpoint carries. -/
theorem prefixAverage_next_eq
    {digits carries : Int × Nat → Nat} {y n : Nat}
    (compiled : CompiledAffineBranch)
    (hrow : ∀ x : Int,
      ∃ t ∈ compiled.transducer,
        AffineSystem.TransitionMatchesCell t digits carries (x, y) ∧
          t.SatisfiesAffine compiled.branch.rationalMap
            IntegerAffineBranch.digitValue compiled.branch.carryValue) :
    prefixAverage digits (y + 1) n =
      branchMap compiled.branch (prefixAverage digits y n) +
        fun j =>
          (carryValue compiled.branch (carries (0, y)) j -
              carryValue compiled.branch
                (carries (((n + 1 : Nat) : Int), y)) j) /
            (n + 1 : Nat) := by
  let input : Nat → Fin 3 → ℚ := fun i =>
    IntegerAffineBranch.digitValue (digits ((i : Int), y))
  let output : Nat → Fin 3 → ℚ := fun i =>
    IntegerAffineBranch.digitValue (digits ((i : Int), y + 1))
  let carry : Nat → Fin 3 → ℚ := fun i =>
    compiled.branch.carryValue (carries ((i : Int), y))
  have hlocal : ∀ i < n + 1,
      carry i + compiled.branch.rationalMap (input i) =
        output i + carry (i + 1) := by
    intro i hi
    rcases hrow (i : Int) with ⟨t, ht, hmatches, hsatisfies⟩
    rw [Transition.SatisfiesAffine] at hsatisfies
    rcases hmatches with ⟨hinput, houtput, hleft, hright⟩
    rw [hinput, houtput, hleft, hright] at hsatisfies
    simpa [input, output, carry, Nat.cast_succ] using hsatisfies
  have htel := compiled.branch.rationalMap.telescope input output carry
    (n + 1) hlocal
  funext j
  have hj := congrFun htel j
  have hjReal := congrArg (fun q : ℚ => (q : ℝ)) hj
  fin_cases j <;>
    simp [prefixAverage, branchMap, Pi.add_apply, input, output, carry,
      carryValue, digitValue, ratToReal, IntegerAffineBranch.rationalMap,
      IntMatrix3.toLinearMap, AffineBeatty.mulReal, AffineBeatty.toReal,
      Pi.smul_apply, smul_eq_mul, Finset.sum_apply, Nat.cast_add,
      Nat.cast_one, IntVector3.toRat] at hjReal ⊢ <;>
    simp only [← Finset.sum_div, Finset.sum_add_distrib,
      ← Finset.mul_sum] at hjReal <;>
    field_simp at hjReal ⊢ <;>
    linarith

/-- A convergent subsequence of prefix averages propagates through one row,
along the same subsequence, to the affine image under the row-selected branch.
-/
theorem tendsto_prefixAverage_next
    {digits carries : Int × Nat → Nat} {y : Nat}
    (compiled : CompiledAffineBranch)
    (hrow : ∀ x : Int,
      ∃ t ∈ compiled.transducer,
        AffineSystem.TransitionMatchesCell t digits carries (x, y) ∧
          t.SatisfiesAffine compiled.branch.rationalMap
            IntegerAffineBranch.digitValue compiled.branch.carryValue)
    (φ : Nat → Nat) (hφ : StrictMono φ) (v : Fin 3 → ℝ)
    (hlimit : Tendsto (prefixAverage digits y ∘ φ) atTop (𝓝 v)) :
    Tendsto (prefixAverage digits (y + 1) ∘ φ) atTop
      (𝓝 (branchMap compiled.branch v)) := by
  have haffine : Tendsto
      (branchMap compiled.branch ∘ prefixAverage digits y ∘ φ) atTop
      (𝓝 (branchMap compiled.branch v)) :=
    (continuous_branchMap compiled.branch).continuousAt.tendsto.comp hlimit
  let error : Nat → Fin 3 → ℝ := fun n j =>
    (carryValue compiled.branch (carries (0, y)) j -
        carryValue compiled.branch
          (carries (((φ n + 1 : Nat) : Int), y)) j) /
      (φ n + 1 : Nat)
  have herror : Tendsto error atTop (𝓝 0) := by
    rw [tendsto_pi_nhds]
    intro j
    have hleft := carryValue_div_tendsto_zero_of_row compiled hrow φ hφ
      (fun _ => 0) j
    have hright := carryValue_div_tendsto_zero_of_row compiled hrow φ hφ
      (fun n => ((φ n + 1 : Nat) : Int)) j
    simpa [error, sub_div] using hleft.sub hright
  have hsum : Tendsto
      (fun n => branchMap compiled.branch (prefixAverage digits y (φ n)) +
        error n) atTop (𝓝 (branchMap compiled.branch v)) := by
    simpa only [Function.comp_apply, add_zero] using haffine.add herror
  apply hsum.congr'
  exact Filter.Eventually.of_forall fun n => by
    simpa only [Function.comp_apply, error] using
      (prefixAverage_next_eq (n := φ n) compiled hrow).symm

/-- A forward affine orbit records both the limiting points and the compiled
branch selected at each time step. -/
structure ForwardOrbit (system : AffineSystem) where
  state : Nat → Fin 3 → ℝ
  branch : Nat → CompiledAffineBranch
  branch_mem : ∀ y, branch y ∈ system.branches
  realizes : ∀ y,
    AffineBeatty.Realizes (branch y).branch (state y) (state (y + 1))

/-- The finite affine system has an infinite forward orbit. -/
def HasForwardOrbit (system : AffineSystem) : Prop :=
  Nonempty (ForwardOrbit system)

/-- Starting from one convergent subsequence on row zero, choose the branch
used by each row and propagate the limit inductively.  A single subsequence is
used for every time step; no countable diagonal argument is needed. -/
def forwardOrbitOfBottomTendsto
    (system : AffineSystem) {digits carries : Int × Nat → Nat}
    (hdiagram : system.transducer.IsUpperHalfDiagram digits carries)
    (φ : Nat → Nat) (hφ : StrictMono φ) (initial : Fin 3 → ℝ)
    (hinitial : Tendsto (prefixAverage digits 0 ∘ φ) atTop (𝓝 initial)) :
    ForwardOrbit system := by
  classical
  let branchAt : Nat → CompiledAffineBranch := fun y =>
    Classical.choose (system.exists_branch_for_row hdiagram y)
  have hbranchAt (y : Nat) :
      branchAt y ∈ system.branches ∧
        ∀ x : Int,
          ∃ t ∈ (branchAt y).transducer,
            AffineSystem.TransitionMatchesCell t digits carries (x, y) ∧
              t.SatisfiesAffine (branchAt y).branch.rationalMap
                IntegerAffineBranch.digitValue
                (branchAt y).branch.carryValue :=
    Classical.choose_spec (system.exists_branch_for_row hdiagram y)
  let state : Nat → Fin 3 → ℝ := Nat.rec initial fun y previous =>
    branchMap (branchAt y).branch previous
  have hstate_zero : state 0 = initial := rfl
  have hstate_succ (y : Nat) :
      state (y + 1) = branchMap (branchAt y).branch (state y) := by
    rfl
  have hstate_limit (y : Nat) :
      Tendsto (prefixAverage digits y ∘ φ) atTop (𝓝 (state y)) := by
    induction y with
    | zero => simpa only [hstate_zero] using hinitial
    | succ y ih =>
        rw [hstate_succ]
        exact tendsto_prefixAverage_next (branchAt y) (hbranchAt y).2
          φ hφ (state y) ih
  exact
    { state := state
      branch := branchAt
      branch_mem := fun y => (hbranchAt y).1
      realizes := fun y => by
        rw [hstate_succ]
        exact realizes_branchMap (branchAt y).branch (state y) }

/-- Existential packaging of `forwardOrbitOfBottomTendsto`. -/
theorem hasForwardOrbit_of_bottom_tendsto
    (system : AffineSystem) {digits carries : Int × Nat → Nat}
    (hdiagram : system.transducer.IsUpperHalfDiagram digits carries)
    (φ : Nat → Nat) (hφ : StrictMono φ) (initial : Fin 3 → ℝ)
    (hinitial : Tendsto (prefixAverage digits 0 ∘ φ) atTop (𝓝 initial)) :
  HasForwardOrbit system :=
  ⟨forwardOrbitOfBottomTendsto system hdiagram φ hφ initial hinitial⟩

/-- Every upper-half diagram has a convergent subsequence of bottom-row
prefix averages.  Finiteness of the selected branch's digit alphabet gives
boundedness; finite-dimensional Bolzano--Weierstrass gives convergence. -/
theorem exists_bottom_tendsto_of_upperHalfDiagram
    (system : AffineSystem) {digits carries : Int × Nat → Nat}
    (hdiagram : system.transducer.IsUpperHalfDiagram digits carries) :
    ∃ (φ : Nat → Nat) (initial : Fin 3 → ℝ),
      StrictMono φ ∧
        Tendsto (prefixAverage digits 0 ∘ φ) atTop (𝓝 initial) := by
  rcases system.exists_branch_for_row hdiagram 0 with
    ⟨compiled, _hcompiled, hrow⟩
  exact exists_tendsto_subseq_prefixAverage_of_row compiled hrow

/-- The analytic converse of Kari's affine-transducer construction: every
upper-half-plane diagram determines an infinite forward affine orbit. -/
theorem hasForwardOrbit_of_hasUpperHalfDiagram (system : AffineSystem) :
    system.transducer.HasUpperHalfDiagram → HasForwardOrbit system := by
  rintro ⟨digits, carries, hdiagram⟩
  rcases exists_bottom_tendsto_of_upperHalfDiagram system hdiagram with
    ⟨φ, initial, hφ, hinitial⟩
  exact hasForwardOrbit_of_bottom_tendsto system hdiagram φ hφ initial hinitial

end AffineLimit

end

end Kari
end LeanWang
