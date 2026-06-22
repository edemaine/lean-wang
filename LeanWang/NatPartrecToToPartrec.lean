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

/-- The partial step function used by `Code.fix (rfindBody test)`. -/
def rfindBodyStep (test : Code) (v : List Nat) : Part (List Nat ⊕ List Nat) :=
  ((rfindBody test).eval v).map fun out =>
    if out.headI = 0 then Sum.inl out.tail else Sum.inr out.tail

theorem rfindBody_eval_zero {test : Code} {n m a : Nat}
    (htest : test.eval [Nat.pair a (n + m)] = pure [0]) :
    (rfindBody test).eval [n, m, a] = pure [0, n, m, a] := by
  simp [rfindBody, htest]

theorem rfindBody_eval_succ {test : Code} {n m a k : Nat}
    (htest : test.eval [Nat.pair a (n + m)] = pure [k.succ]) :
    (rfindBody test).eval [n, m, a] = pure [1, n.succ, m, a] := by
  simp [rfindBody, htest]

theorem rfindBody_fix_stop {test : Code} {n m a : Nat}
    (htest : test.eval [Nat.pair a (n + m)] = pure [0]) :
    [n, m, a] ∈ (Code.fix (rfindBody test)).eval [n, m, a] := by
  rw [Turing.ToPartrec.Code.fix_eval]
  refine PFun.fix_stop ?_
  simp [rfindBody_eval_zero htest]

theorem rfindBody_fix_fwd {test : Code} {n m a k : Nat} {v : List Nat}
    (htest : test.eval [Nat.pair a (n + m)] = pure [k.succ])
    (hnext : v ∈ (Code.fix (rfindBody test)).eval [n.succ, m, a]) :
    v ∈ (Code.fix (rfindBody test)).eval [n, m, a] := by
  rw [Turing.ToPartrec.Code.fix_eval] at hnext ⊢
  refine PFun.mem_fix_iff.2 (Or.inr ⟨[n.succ, m, a], ?_, hnext⟩)
  simp [rfindBody_eval_succ htest]

set_option linter.flexible false in
theorem rfindBodyStep_stop_shape {test : Code} {i n m a : Nat}
    (hsingle : ∀ v : List Nat, v ∈ test.eval [Nat.pair a (i + m)] → ∃ x : Nat, v = [x])
    (hstop : Sum.inl [n, m, a] ∈ rfindBodyStep test [i, m, a]) :
    i = n ∧ [0] ∈ test.eval [Nat.pair a (i + m)] := by
  unfold rfindBodyStep at hstop
  rw [Part.mem_map_iff] at hstop
  rcases hstop with ⟨w, hw, hwmap⟩
  simp [rfindBody] at hw
  rcases hw with ⟨cond, hcond, hwcase⟩
  rcases hsingle cond hcond with ⟨x, rfl⟩
  cases x with
  | zero =>
      simp at hwcase
      subst w
      simp at hwmap
      exact ⟨by simpa using hwmap, hcond⟩
  | succ _ =>
      simp at hwcase
      subst w
      simp at hwmap

set_option linter.flexible false in
theorem rfindBodyStep_fwd_shape {test : Code} {i m a : Nat} {next : List Nat}
    (hsingle : ∀ v : List Nat, v ∈ test.eval [Nat.pair a (i + m)] → ∃ x : Nat, v = [x])
    (hfwd : Sum.inr next ∈ rfindBodyStep test [i, m, a]) :
    next = [i.succ, m, a] ∧
      ∃ k : Nat, [k.succ] ∈ test.eval [Nat.pair a (i + m)] := by
  unfold rfindBodyStep at hfwd
  rw [Part.mem_map_iff] at hfwd
  rcases hfwd with ⟨w, hw, hwmap⟩
  simp [rfindBody] at hw
  rcases hw with ⟨cond, hcond, hwcase⟩
  rcases hsingle cond hcond with ⟨x, rfl⟩
  cases x with
  | zero =>
      simp at hwcase
      subst w
      simp at hwmap
  | succ k =>
      simp at hwcase
      subst w
      simp at hwmap
      exact ⟨by simpa using hwmap.symm, ⟨k, hcond⟩⟩

set_option linter.flexible false in
theorem rfindBodyStep_stop_shape_any {test : Code} {i m a : Nat} {out : List Nat}
    (hsingle : ∀ v : List Nat, v ∈ test.eval [Nat.pair a (i + m)] → ∃ x : Nat, v = [x])
    (hstop : Sum.inl out ∈ rfindBodyStep test [i, m, a]) :
    out = [i, m, a] ∧ [0] ∈ test.eval [Nat.pair a (i + m)] := by
  unfold rfindBodyStep at hstop
  rw [Part.mem_map_iff] at hstop
  rcases hstop with ⟨w, hw, hwmap⟩
  simp [rfindBody] at hw
  rcases hw with ⟨cond, hcond, hwcase⟩
  rcases hsingle cond hcond with ⟨x, rfl⟩
  cases x with
  | zero =>
      simp at hwcase
      subst w
      simp at hwmap
      exact ⟨by simpa using hwmap.symm, hcond⟩
  | succ _ =>
      simp at hwcase
      subst w
      simp at hwmap

theorem rfindBody_fix_of_first_zeroFrom {test : Code} {a m : Nat}
    (start len : Nat)
    (hzero : test.eval [Nat.pair a ((start + len) + m)] = pure [0])
    (hprev : ∀ i : Nat, i < len →
      ∃ k : Nat, test.eval [Nat.pair a ((start + i) + m)] = pure [k.succ]) :
    [start + len, m, a] ∈ (Code.fix (rfindBody test)).eval [start, m, a] := by
  induction len generalizing start with
  | zero =>
      simpa using rfindBody_fix_stop (test := test) (n := start) (m := m) (a := a)
        (by simpa using hzero)
  | succ len IH =>
      rcases hprev 0 (Nat.zero_lt_succ len) with ⟨k, hstart⟩
      have hnext :
          [start.succ + len, m, a] ∈
            (Code.fix (rfindBody test)).eval [start.succ, m, a] := by
        refine IH start.succ ?_ ?_
        · simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            using hzero
        · intro i hi
          rcases hprev (i.succ) (Nat.succ_lt_succ hi) with ⟨k', hk'⟩
          refine ⟨k', ?_⟩
          simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            using hk'
      have hstep :
          [start.succ + len, m, a] ∈
            (Code.fix (rfindBody test)).eval [start, m, a] :=
        rfindBody_fix_fwd (test := test) (n := start) (m := m) (a := a) (k := k)
          (by simpa [Nat.add_assoc] using hstart) hnext
      simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hstep

theorem rfindBody_first_zeroFrom_of_fix_mem {test : Code} {start n m a : Nat}
    (hsingle : ∀ t : Nat, ∀ v : List Nat,
      v ∈ test.eval [Nat.pair a (t + m)] → ∃ x : Nat, v = [x])
    (hfix : [n, m, a] ∈ (Code.fix (rfindBody test)).eval [start, m, a]) :
    start ≤ n ∧ [0] ∈ test.eval [Nat.pair a (n + m)] ∧
      ∀ i : Nat, start ≤ i → i < n →
        ∃ k : Nat, [k.succ] ∈ test.eval [Nat.pair a (i + m)] := by
  rw [Turing.ToPartrec.Code.fix_eval] at hfix
  change [n, m, a] ∈ PFun.fix (rfindBodyStep test) [start, m, a] at hfix
  let C : List Nat → Prop := fun state =>
    ∀ i : Nat, state = [i, m, a] →
      i ≤ n ∧ [0] ∈ test.eval [Nat.pair a (n + m)] ∧
        ∀ j : Nat, i ≤ j → j < n →
          ∃ k : Nat, [k.succ] ∈ test.eval [Nat.pair a (j + m)]
  have hC : C [start, m, a] := by
    refine PFun.fixInduction' (f := rfindBodyStep test) hfix ?_ ?_
    · intro final hstop i hstate
      subst final
      have hstop' : Sum.inl [n, m, a] ∈ rfindBodyStep test [i, m, a] := by
        simpa using hstop
      rcases rfindBodyStep_stop_shape (test := test) (i := i) (n := n)
          (m := m) (a := a) (hsingle i) hstop' with ⟨hin, hzero⟩
      refine ⟨by omega, ?_, ?_⟩
      · simpa [hin] using hzero
      · intro j hij hjn
        omega
    · intro state next _hnext hfwd ih i hstate
      subst state
      have hfwd' : Sum.inr next ∈ rfindBodyStep test [i, m, a] := by
        simpa using hfwd
      rcases rfindBodyStep_fwd_shape (test := test) (i := i) (m := m)
          (a := a) (hsingle i) hfwd' with ⟨hnext_eq, hnonzero⟩
      rcases ih i.succ hnext_eq with ⟨hin_le, hzero, hprev⟩
      refine ⟨by omega, hzero, ?_⟩
      intro j hij hjn
      by_cases hji : j = i
      · subst j
        simpa using hnonzero
      · exact hprev j (by omega) hjn
  exact hC start rfl

theorem rfindBody_fix_mem_trace {test : Code} {start m a : Nat} {out : List Nat}
    (hsingle : ∀ t : Nat, ∀ v : List Nat,
      v ∈ test.eval [Nat.pair a (t + m)] → ∃ x : Nat, v = [x])
    (hfix : out ∈ (Code.fix (rfindBody test)).eval [start, m, a]) :
    ∃ n : Nat, out = [n, m, a] ∧ start ≤ n ∧
      [0] ∈ test.eval [Nat.pair a (n + m)] ∧
      ∀ i : Nat, start ≤ i → i < n →
        ∃ k : Nat, [k.succ] ∈ test.eval [Nat.pair a (i + m)] := by
  rw [Turing.ToPartrec.Code.fix_eval] at hfix
  change out ∈ PFun.fix (rfindBodyStep test) [start, m, a] at hfix
  let C : List Nat → Prop := fun state =>
    ∀ i : Nat, state = [i, m, a] →
      ∃ n : Nat, out = [n, m, a] ∧ i ≤ n ∧
        [0] ∈ test.eval [Nat.pair a (n + m)] ∧
        ∀ j : Nat, i ≤ j → j < n →
          ∃ k : Nat, [k.succ] ∈ test.eval [Nat.pair a (j + m)]
  have hC : C [start, m, a] := by
    refine PFun.fixInduction' (f := rfindBodyStep test) hfix ?_ ?_
    · intro final hstop i hstate
      subst final
      have hstop' : Sum.inl out ∈ rfindBodyStep test [i, m, a] := by
        simpa using hstop
      rcases rfindBodyStep_stop_shape_any (test := test) (i := i) (m := m)
          (a := a) (hsingle i) hstop' with ⟨hout, hzero⟩
      refine ⟨i, hout, by omega, hzero, ?_⟩
      intro j hij hji
      omega
    · intro state next _hnext hfwd ih i hstate
      subst state
      have hfwd' : Sum.inr next ∈ rfindBodyStep test [i, m, a] := by
        simpa using hfwd
      rcases rfindBodyStep_fwd_shape (test := test) (i := i) (m := m)
          (a := a) (hsingle i) hfwd' with ⟨hnext_eq, hnonzero⟩
      rcases ih i.succ hnext_eq with ⟨n, hout, hin_le, hzero, hprev⟩
      refine ⟨n, hout, by omega, hzero, ?_⟩
      intro j hij hjn
      by_cases hji : j = i
      · subst j
        simpa using hnonzero
      · exact hprev j (by omega) hjn
  exact hC start rfl

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

theorem rfindFrom_mem_of_fix_state {test : Code} {a m n : Nat}
    (hfix : [n, m, a] ∈ (Code.fix (rfindBody test)).eval [0, m, a]) :
    [n + m] ∈ (rfindFrom test).eval [Nat.pair a m] := by
  have hstart :
      [0, m, a] ∈ (Code.zero'.comp Code.unpairListSwap).eval [Nat.pair a m] := by
    simp [Part.bind_eq_bind]
  have hinner :
      [n, m, a] ∈ ((Code.fix (rfindBody test)).comp
        (Code.zero'.comp Code.unpairListSwap)).eval [Nat.pair a m] := by
    rw [Turing.ToPartrec.Code.comp_eval]
    simp only [Part.bind_eq_bind, Part.mem_bind_iff]
    exact ⟨[0, m, a], hstart, hfix⟩
  rw [rfindFrom, Turing.ToPartrec.Code.comp_eval]
  simp only [Part.bind_eq_bind, Part.mem_bind_iff]
  exact ⟨[n, m, a], hinner, by simp⟩

theorem rfindFrom_mem_of_first_zero {test : Code} {a m n : Nat}
    (hzero : test.eval [Nat.pair a (n + m)] = pure [0])
    (hprev : ∀ i : Nat, i < n →
      ∃ k : Nat, test.eval [Nat.pair a (i + m)] = pure [k.succ]) :
    [n + m] ∈ (rfindFrom test).eval [Nat.pair a m] := by
  refine rfindFrom_mem_of_fix_state (test := test) (a := a) (m := m) (n := n) ?_
  simpa using
    rfindBody_fix_of_first_zeroFrom (test := test) (a := a) (m := m)
      0 n (by simpa using hzero) (by simpa using hprev)

theorem rfindFrom_mem_trace {test : Code} {a m : Nat} {v : List Nat}
    (hsingle : ∀ t : Nat, ∀ v : List Nat,
      v ∈ test.eval [Nat.pair a (t + m)] → ∃ x : Nat, v = [x])
    (hv : v ∈ (rfindFrom test).eval [Nat.pair a m]) :
    ∃ n : Nat, v = [n + m] ∧
      [0] ∈ test.eval [Nat.pair a (n + m)] ∧
      ∀ i : Nat, i < n →
        ∃ k : Nat, [k.succ] ∈ test.eval [Nat.pair a (i + m)] := by
  rw [rfindFrom, Turing.ToPartrec.Code.comp_eval] at hv
  simp only [Part.bind_eq_bind, Part.mem_bind_iff] at hv
  rcases hv with ⟨state, hinner, hout⟩
  rw [Turing.ToPartrec.Code.comp_eval] at hinner
  simp only [Part.bind_eq_bind, Part.mem_bind_iff] at hinner
  rcases hinner with ⟨start, hstart, hfix⟩
  have hstart_eq : start = [0, m, a] := by
    simpa [Part.bind_eq_bind] using hstart
  subst start
  rcases rfindBody_fix_mem_trace (test := test) (start := 0) (m := m) (a := a)
      hsingle hfix with ⟨n, hstate, _h0n, hzero, hprev⟩
  subst state
  have hv_eq : v = [n + m] := by
    simpa using hout
  refine ⟨n, hv_eq, hzero, ?_⟩
  intro i hi
  exact hprev i (Nat.zero_le i) hi

end TCode

namespace TCode

open Turing.ToPartrec

/-- The internal step code used by Mathlib's `Turing.ToPartrec.Code.prec`. -/
def precG (g : Code) : Code :=
  Code.cons Code.tail <|
    Code.cons Code.succ <|
      Code.cons (Code.comp Code.pred Code.tail) <|
        Code.cons (Code.comp g <| Code.cons Code.id <| Code.comp Code.tail Code.tail) <|
          Code.comp Code.tail <| Code.comp Code.tail Code.tail

theorem prec_eq (f g : Code) :
    Code.prec f g =
      let G := precG g
      let F := Code.case Code.id <|
        Code.comp (Code.comp (Code.comp Code.tail Code.tail) (Code.fix G)) Code.zero'
      Code.cons (Code.comp F (Code.cons Code.head <| Code.cons (Code.comp f Code.tail) Code.tail))
        Code.nil := by
  rfl

theorem precG_eval {g : Code} {i b ih a x : Nat}
    (hg : g.eval [i, ih, a] = pure [x]) :
    (precG g).eval [i, b, ih, a] = pure [b, i.succ, b.pred, x, a] := by
  simp [precG, hg]

/-- The partial step function used by `Code.fix (precG g)`. -/
def precGStep (g : Code) (v : List Nat) : Part (List Nat ⊕ List Nat) :=
  ((precG g).eval v).map fun out =>
    if out.headI = 0 then Sum.inl out.tail else Sum.inr out.tail

theorem precG_fix_stop {g : Code} {i ih a x : Nat}
    (hg : g.eval [i, ih, a] = pure [x]) :
    [i.succ, 0, x, a] ∈ (Code.fix (precG g)).eval [i, 0, ih, a] := by
  rw [Turing.ToPartrec.Code.fix_eval]
  refine PFun.fix_stop ?_
  simp [precG_eval hg]

theorem precG_fix_fwd {g : Code} {i b ih a x : Nat} {v : List Nat}
    (hg : g.eval [i, ih, a] = pure [x])
    (hnext : v ∈ (Code.fix (precG g)).eval [i.succ, b, x, a]) :
    v ∈ (Code.fix (precG g)).eval [i, b.succ, ih, a] := by
  rw [Turing.ToPartrec.Code.fix_eval] at hnext ⊢
  refine PFun.mem_fix_iff.2 (Or.inr ⟨[i.succ, b, x, a], ?_, hnext⟩)
  simp [precG_eval hg]

set_option linter.flexible false in
theorem precGStep_stop_shape {g : Code} {i ih a : Nat} {out : List Nat}
    (hsingle : ∀ v : List Nat, v ∈ g.eval [i, ih, a] → ∃ x : Nat, v = [x])
    (hstop : Sum.inl out ∈ precGStep g [i, 0, ih, a]) :
    ∃ x : Nat, out = [i.succ, 0, x, a] ∧ [x] ∈ g.eval [i, ih, a] := by
  unfold precGStep at hstop
  rw [Part.mem_map_iff] at hstop
  rcases hstop with ⟨w, hw, hwmap⟩
  simp [precG] at hw
  rcases hw with ⟨gv, hgv, hw⟩
  rcases hsingle gv hgv with ⟨x, rfl⟩
  simp at hw
  subst w
  simp at hwmap
  exact ⟨x, by simpa using hwmap.symm, hgv⟩

set_option linter.flexible false in
theorem precGStep_fwd_shape {g : Code} {i b ih a : Nat} {next : List Nat}
    (hsingle : ∀ v : List Nat, v ∈ g.eval [i, ih, a] → ∃ x : Nat, v = [x])
    (hfwd : Sum.inr next ∈ precGStep g [i, b.succ, ih, a]) :
    ∃ x : Nat, next = [i.succ, b, x, a] ∧ [x] ∈ g.eval [i, ih, a] := by
  unfold precGStep at hfwd
  rw [Part.mem_map_iff] at hfwd
  rcases hfwd with ⟨w, hw, hwmap⟩
  simp [precG] at hw
  rcases hw with ⟨gv, hgv, hw⟩
  rcases hsingle gv hgv with ⟨x, rfl⟩
  simp at hw
  subst w
  simp at hwmap
  exact ⟨x, by simpa using hwmap.symm, hgv⟩

set_option linter.flexible false in
theorem precGStep_no_fwd_zero {g : Code} {i ih a : Nat} {next : List Nat}
    (hsingle : ∀ v : List Nat, v ∈ g.eval [i, ih, a] → ∃ x : Nat, v = [x])
    (hfwd : Sum.inr next ∈ precGStep g [i, 0, ih, a]) :
    False := by
  unfold precGStep at hfwd
  rw [Part.mem_map_iff] at hfwd
  rcases hfwd with ⟨w, hw, hwmap⟩
  simp [precG] at hw
  rcases hw with ⟨gv, hgv, hw⟩
  rcases hsingle gv hgv with ⟨x, rfl⟩
  simp at hw
  subst w
  simp at hwmap

set_option linter.flexible false in
theorem precGStep_no_stop_succ {g : Code} {i b ih a : Nat} {out : List Nat}
    (hsingle : ∀ v : List Nat, v ∈ g.eval [i, ih, a] → ∃ x : Nat, v = [x])
    (hstop : Sum.inl out ∈ precGStep g [i, b.succ, ih, a]) :
    False := by
  unfold precGStep at hstop
  rw [Part.mem_map_iff] at hstop
  rcases hstop with ⟨w, hw, hwmap⟩
  simp [precG] at hw
  rcases hw with ⟨gv, hgv, hw⟩
  rcases hsingle gv hgv with ⟨x, rfl⟩
  simp at hw
  subst w
  simp at hwmap

/-- Successful traces through the internal loop used by `Code.prec`. -/
def precRun (g : Code) (a : Nat) : Nat → Nat → Nat → Nat → Prop
  | i, 0, ih, x => [x] ∈ g.eval [i, ih, a]
  | i, b + 1, ih, x => ∃ y : Nat, [y] ∈ g.eval [i, ih, a] ∧ precRun g a i.succ b y x

set_option linter.flexible false in
theorem precG_fix_of_precRun {g : Code} {a i b ih x : Nat}
    (h : precRun g a i b ih x) :
    [i + b.succ, 0, x, a] ∈ (Code.fix (precG g)).eval [i, b, ih, a] := by
  induction b generalizing i ih with
  | zero =>
      simp [precRun] at h
      exact precG_fix_stop (g := g) (i := i) (ih := ih) (a := a) (x := x)
        (Part.eq_some_iff.2 h)
  | succ b IH =>
      simp [precRun] at h
      rcases h with ⟨y, hy, hrest⟩
      have hnext : [i.succ + b.succ, 0, x, a] ∈
          (Code.fix (precG g)).eval [i.succ, b, y, a] :=
        IH hrest
      have hmem : [i.succ + b.succ, 0, x, a] ∈
          (Code.fix (precG g)).eval [i, b.succ, ih, a] :=
        precG_fix_fwd (g := g) (i := i) (b := b) (ih := ih) (a := a) (x := y)
          (Part.eq_some_iff.2 hy) hnext
      simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hmem

theorem precRun_of_precG_fix_mem {g : Code} {a i b ih x : Nat}
    (hsingle : ∀ i ih, ∀ v : List Nat, v ∈ g.eval [i, ih, a] → ∃ x : Nat, v = [x])
    (hfix : [i + b.succ, 0, x, a] ∈ (Code.fix (precG g)).eval [i, b, ih, a]) :
    precRun g a i b ih x := by
  induction b generalizing i ih with
  | zero =>
      rw [Turing.ToPartrec.Code.fix_eval] at hfix
      change [i.succ, 0, x, a] ∈ PFun.fix (precGStep g) [i, 0, ih, a] at hfix
      rcases PFun.mem_fix_iff.1 hfix with hstop | ⟨next, hfwd, _hnext⟩
      · rcases precGStep_stop_shape (g := g) (i := i) (ih := ih) (a := a)
            (hsingle i ih) hstop with ⟨y, hout, hy⟩
        have hyx : y = x := by
          simpa using hout.symm
        simpa [precRun, hyx] using hy
      · exact (precGStep_no_fwd_zero (g := g) (i := i) (ih := ih) (a := a)
          (hsingle i ih) hfwd).elim
  | succ b IH =>
      rw [Turing.ToPartrec.Code.fix_eval] at hfix
      change [i + (b.succ).succ, 0, x, a] ∈
        PFun.fix (precGStep g) [i, b.succ, ih, a] at hfix
      rcases PFun.mem_fix_iff.1 hfix with hstop | ⟨next, hfwd, hnext⟩
      · exact (precGStep_no_stop_succ (g := g) (i := i) (b := b) (ih := ih) (a := a)
          (hsingle i ih) hstop).elim
      · rcases precGStep_fwd_shape (g := g) (i := i) (b := b) (ih := ih) (a := a)
            (hsingle i ih) hfwd with ⟨y, hnext_eq, hy⟩
        have hnext' : [i.succ + b.succ, 0, x, a] ∈
            (Code.fix (precG g)).eval [i.succ, b, y, a] := by
          rw [Turing.ToPartrec.Code.fix_eval]
          change [i.succ + b.succ, 0, x, a] ∈
            PFun.fix (precGStep g) [i.succ, b, y, a]
          simpa [hnext_eq, Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            using hnext
        have hrun : precRun g a i.succ b y x := IH (i := i.succ) (ih := y) hnext'
        exact ⟨y, hy, hrun⟩

theorem precG_fix_mem_trace {g : Code} {a i b ih : Nat} {out : List Nat}
    (hsingle : ∀ i ih, ∀ v : List Nat, v ∈ g.eval [i, ih, a] → ∃ x : Nat, v = [x])
    (hfix : out ∈ (Code.fix (precG g)).eval [i, b, ih, a]) :
    ∃ x : Nat, out = [i + b.succ, 0, x, a] ∧ precRun g a i b ih x := by
  induction b generalizing i ih with
  | zero =>
      rw [Turing.ToPartrec.Code.fix_eval] at hfix
      change out ∈ PFun.fix (precGStep g) [i, 0, ih, a] at hfix
      rcases PFun.mem_fix_iff.1 hfix with hstop | ⟨next, hfwd, _hnext⟩
      · rcases precGStep_stop_shape (g := g) (i := i) (ih := ih) (a := a)
            (hsingle i ih) hstop with ⟨x, hout, hx⟩
        exact ⟨x, by simpa using hout, by simpa [precRun] using hx⟩
      · exact (precGStep_no_fwd_zero (g := g) (i := i) (ih := ih) (a := a)
          (hsingle i ih) hfwd).elim
  | succ b IH =>
      rw [Turing.ToPartrec.Code.fix_eval] at hfix
      change out ∈ PFun.fix (precGStep g) [i, b.succ, ih, a] at hfix
      rcases PFun.mem_fix_iff.1 hfix with hstop | ⟨next, hfwd, hnext⟩
      · exact (precGStep_no_stop_succ (g := g) (i := i) (b := b) (ih := ih) (a := a)
          (hsingle i ih) hstop).elim
      · rcases precGStep_fwd_shape (g := g) (i := i) (b := b) (ih := ih) (a := a)
            (hsingle i ih) hfwd with ⟨y, hnext_eq, hy⟩
        have hnext' : out ∈ (Code.fix (precG g)).eval [i.succ, b, y, a] := by
          rw [Turing.ToPartrec.Code.fix_eval]
          change out ∈ PFun.fix (precGStep g) [i.succ, b, y, a]
          simpa [hnext_eq] using hnext
        rcases IH (i := i.succ) (ih := y) hnext' with ⟨x, hout, hrun⟩
        refine ⟨x, ?_, ⟨y, hy, hrun⟩⟩
        simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using hout

set_option linter.flexible false in
theorem precRun_snoc {g : Code} {a i b ih y x : Nat}
    (hrun : precRun g a i b ih y)
    (hstep : [x] ∈ g.eval [i + b.succ, y, a]) :
    precRun g a i b.succ ih x := by
  induction b generalizing i ih with
  | zero =>
      simp [precRun] at hrun ⊢
      exact ⟨y, hrun, by simpa [Nat.succ_eq_add_one] using hstep⟩
  | succ b IH =>
      simp [precRun] at hrun ⊢
      rcases hrun with ⟨z, hz, hrest⟩
      refine ⟨z, hz, ?_⟩
      refine IH hrest ?_
      simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hstep

set_option linter.flexible false in
theorem prec_mem_of_precRun {f g : Code} {a k base x : Nat}
    (hbase : f.eval [a] = pure [base])
    (hrun : precRun g a 0 k base x) :
    [x] ∈ (Code.prec f g).eval [k.succ, a] := by
  have hfix : [k.succ, 0, x, a] ∈ (Code.fix (precG g)).eval [0, k, base, a] := by
    simpa using precG_fix_of_precRun hrun
  rw [Turing.ToPartrec.Code.fix_eval] at hfix
  rw [prec_eq]
  simp [hbase]
  exact ⟨[k.succ, 0, x, a], hfix, by simp⟩

set_option linter.flexible false in
theorem precRun_of_prec_mem {f g : Code} {a k x : Nat}
    (hsingleF : ∀ v : List Nat, v ∈ f.eval [a] → ∃ base : Nat, v = [base])
    (hsingleG : ∀ i ih, ∀ v : List Nat, v ∈ g.eval [i, ih, a] → ∃ x : Nat, v = [x])
    (hv : [x] ∈ (Code.prec f g).eval [k.succ, a]) :
    ∃ base : Nat, [base] ∈ f.eval [a] ∧ precRun g a 0 k base x := by
  rw [prec_eq] at hv
  simp at hv
  rcases hv with ⟨baseOut, final, ⟨hbaseOut, hfix⟩, hx⟩
  rcases hsingleF baseOut hbaseOut with ⟨base, rfl⟩
  have hfix' : final ∈ (Code.fix (precG g)).eval [0, k, base, a] := by
    rw [Turing.ToPartrec.Code.fix_eval]
    change final ∈ PFun.fix (precGStep g) [0, k, base, a]
    exact hfix
  rcases precG_fix_mem_trace (g := g) (a := a) (i := 0) (b := k) (ih := base)
      hsingleG hfix' with ⟨y, hfinal, hrun⟩
  have hxy : x = y := by
    simpa [hfinal] using hx
  exact ⟨base, hbaseOut, by simpa [hxy] using hrun⟩

set_option linter.flexible false in
theorem prec_mem_trace {f g : Code} {a k : Nat} {v : List Nat}
    (hsingleF : ∀ v : List Nat, v ∈ f.eval [a] → ∃ base : Nat, v = [base])
    (hsingleG : ∀ i ih, ∀ v : List Nat, v ∈ g.eval [i, ih, a] → ∃ x : Nat, v = [x])
    (hv : v ∈ (Code.prec f g).eval [k.succ, a]) :
    ∃ base x : Nat, v = [x] ∧ [base] ∈ f.eval [a] ∧ precRun g a 0 k base x := by
  rw [prec_eq] at hv
  simp at hv
  rcases hv with ⟨baseOut, final, ⟨hbaseOut, hfix⟩, hv⟩
  rcases hsingleF baseOut hbaseOut with ⟨base, rfl⟩
  have hfix' : final ∈ (Code.fix (precG g)).eval [0, k, base, a] := by
    rw [Turing.ToPartrec.Code.fix_eval]
    change final ∈ PFun.fix (precGStep g) [0, k, base, a]
    exact hfix
  rcases precG_fix_mem_trace (g := g) (a := a) (i := 0) (b := k) (ih := base)
      hsingleG hfix' with ⟨x, hfinal, hrun⟩
  refine ⟨base, x, ?_, hbaseOut, hrun⟩
  simpa [hfinal] using hv

theorem primrec_precG : Primrec precG := by
  unfold precG
  exact Code.primrec₂_cons.comp (Primrec.const Code.tail)
    (Code.primrec₂_cons.comp (Primrec.const Code.succ)
      (Code.primrec₂_cons.comp (Primrec.const (Code.comp Code.pred Code.tail))
        (Code.primrec₂_cons.comp
          (Code.primrec₂_comp.comp Primrec.id
            (Primrec.const (Code.cons Code.id (Code.comp Code.tail Code.tail))))
          (Primrec.const (Code.comp Code.tail (Code.comp Code.tail Code.tail))))))

theorem primrec₂_prec : Primrec (fun p : Code × Code => Code.prec p.1 p.2) := by
  have hF : Primrec (fun g : Code =>
      Code.case Code.id <|
        Code.comp (Code.comp (Code.comp Code.tail Code.tail) (Code.fix (precG g))) Code.zero') := by
    exact Code.primrec₂_case.comp (Primrec.const Code.id)
      (Code.primrec₂_comp.comp
        (Code.primrec₂_comp.comp (Primrec.const (Code.comp Code.tail Code.tail))
          (Code.primrec_fix.comp primrec_precG))
        (Primrec.const Code.zero'))
  rw [show (fun p : Code × Code => Code.prec p.1 p.2) =
      (fun p : Code × Code =>
        let F := Code.case Code.id <|
          Code.comp (Code.comp (Code.comp Code.tail Code.tail) (Code.fix (precG p.2))) Code.zero'
        Code.cons (Code.comp F (Code.cons Code.head <|
          Code.cons (Code.comp p.1 Code.tail) Code.tail)) Code.nil) by
    funext p
    rw [prec_eq]]
  exact Code.primrec₂_cons.comp
    (Code.primrec₂_comp.comp (hF.comp Primrec.snd)
      (Code.primrec₂_cons.comp (Primrec.const Code.head)
        (Code.primrec₂_cons.comp
          (Code.primrec₂_comp.comp Primrec.fst (Primrec.const Code.tail))
          (Primrec.const Code.tail))))
    (Primrec.const Code.nil)

theorem primrec_rfindBody : Primrec rfindBody := by
  unfold rfindBody
  exact Code.primrec₂_comp.comp
    (Code.primrec₂_case.comp (Primrec.const Code.zero')
      (Primrec.const
        (Code.cons one (Code.cons (Code.succ.comp Code.second) (Code.tail.comp Code.tail)))))
    (Code.primrec₂_cons.comp
      (Code.primrec₂_comp.comp Primrec.id (Primrec.const Code.rfindTestArg))
      (Primrec.const Code.id))

theorem primrec_rfindFrom : Primrec rfindFrom := by
  unfold rfindFrom
  exact Code.primrec₂_comp.comp (Primrec.const Code.addFirstSecond)
    (Code.primrec₂_comp.comp
      (Code.primrec_fix.comp primrec_rfindBody)
      (Primrec.const (Code.zero'.comp Code.unpairListSwap)))

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

theorem translate_eq_rec (c : Nat.Partrec.Code) :
    translate c =
      Nat.Partrec.Code.rec Code.zero Code.succ Code.unpairLeft Code.unpairRight
        (fun _ _ hf hg => Code.singletonPair hf hg)
        (fun _ _ hf hg => hf.comp hg)
        (fun _ _ hf hg => (Code.prec hf (hg.comp Code.precStepArg)).comp
          Code.unpairListSwap)
        (fun _ hf => TCode.rfindFrom hf) c := by
  induction c <;> simp [translate, *]

theorem translate_primrec : Primrec translate := by
  have hListPair : Primrec (fun p : Code × Code => Code.listPair p.1 p.2) := by
    unfold Code.listPair
    exact Code.primrec₂_cons.comp Primrec.fst
      (Code.primrec₂_cons.comp Primrec.snd (Primrec.const Code.nil))
  have hSingletonPair :
      Primrec (fun p : Code × Code => Code.singletonPair p.1 p.2) := by
    unfold Code.singletonPair
    exact Code.primrec₂_comp.comp (Primrec.const Code.pairNat) hListPair
  have hrec := Nat.Partrec.Code.primrec_recOn (α := Nat.Partrec.Code)
    (σ := Code)
    (c := fun c : Nat.Partrec.Code => c) Primrec.id
    (z := fun _ : Nat.Partrec.Code => Code.zero) (Primrec.const Code.zero)
    (s := fun _ : Nat.Partrec.Code => Code.succ) (Primrec.const Code.succ)
    (l := fun _ : Nat.Partrec.Code => Code.unpairLeft) (Primrec.const Code.unpairLeft)
    (r := fun _ : Nat.Partrec.Code => Code.unpairRight) (Primrec.const Code.unpairRight)
    (pr := fun _ _ _ hf hg => Code.singletonPair hf hg)
    (by
      exact hSingletonPair.comp
        (Primrec.pair
          (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
          (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))
    (co := fun _ _ _ hf hg => hf.comp hg)
    (by
      exact Code.primrec₂_comp.comp
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
    (pc := fun _ _ _ hf hg =>
      (Code.prec hf (hg.comp Code.precStepArg)).comp Code.unpairListSwap)
    (by
      exact Code.primrec₂_comp.comp
        (TCode.primrec₂_prec.comp
          (Primrec.pair
            (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
            (Code.primrec₂_comp.comp
              (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
              (Primrec.const Code.precStepArg))))
        (Primrec.const Code.unpairListSwap))
    (rf := fun _ _ hf => TCode.rfindFrom hf)
    (by
      exact TCode.primrec_rfindFrom.comp
        (Primrec.snd.comp Primrec.snd))
  exact hrec.of_eq fun c => (translate_eq_rec c).symm

theorem translate_computable : Computable translate :=
  translate_primrec.to_comp

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

theorem translates_prec_zero {cf cg : Nat.Partrec.Code}
    (hf : Translates cf (translate cf)) (_hg : Translates cg (translate cg))
    (a : Nat) (v : List Nat) :
    v ∈ (translate (.prec cf cg)).eval [Nat.pair a 0] ↔
      ∃ x : Nat, x ∈ Nat.Partrec.Code.eval cf a ∧ v = [x] := by
  simp [translate_prec, Turing.ToPartrec.Code.prec, hf a, Part.bind_eq_bind,
    Part.mem_bind_iff]

theorem translates_precStepArg {cg : Nat.Partrec.Code}
    (hg : Translates cg (translate cg)) (y ih a : Nat) (v : List Nat) :
    v ∈ (((translate cg).comp Code.precStepArg).eval [y, ih, a]) ↔
      ∃ x : Nat, x ∈ Nat.Partrec.Code.eval cg (Nat.pair a (Nat.pair y ih)) ∧ v = [x] := by
  rw [Turing.ToPartrec.Code.comp_eval]
  simpa [Part.bind_eq_bind] using hg (Nat.pair a (Nat.pair y ih)) v

theorem precRun_of_nat_prec_succ {cf cg : Nat.Partrec.Code}
    (_hf : Translates cf (translate cf)) (hg : Translates cg (translate cg))
    {a k base x : Nat}
    (hbase : base ∈ Nat.Partrec.Code.eval cf a)
    (hx : x ∈ Nat.Partrec.Code.eval (.prec cf cg) (Nat.pair a k.succ)) :
    TCode.precRun ((translate cg).comp Code.precStepArg) a 0 k base x := by
  induction k generalizing x with
  | zero =>
      rw [Nat.Partrec.Code.eval_prec_succ] at hx
      simp only [Part.bind_eq_bind, Part.mem_bind_iff] at hx
      rcases hx with ⟨ih, hih, hxg⟩
      have hih_base : ih = base := by
        rw [Nat.Partrec.Code.eval_prec_zero] at hih
        exact Part.mem_unique hih hbase
      subst ih
      change [x] ∈ (((translate cg).comp Code.precStepArg).eval [0, base, a])
      exact (translates_precStepArg hg 0 base a [x]).2 ⟨x, hxg, rfl⟩
  | succ k IH =>
      rw [Nat.Partrec.Code.eval_prec_succ] at hx
      simp only [Part.bind_eq_bind, Part.mem_bind_iff] at hx
      rcases hx with ⟨ih, hih, hxg⟩
      have hrun : TCode.precRun ((translate cg).comp Code.precStepArg) a 0 k base ih :=
        IH hih
      have hstep : [x] ∈ (((translate cg).comp Code.precStepArg).eval [0 + k.succ, ih, a]) := by
        simpa using (translates_precStepArg hg k.succ ih a [x]).2 ⟨x, hxg, rfl⟩
      exact TCode.precRun_snoc hrun hstep

theorem exists_precRun_of_nat_prec_succ {cf cg : Nat.Partrec.Code}
    (hg : Translates cg (translate cg)) {a k x : Nat}
    (hx : x ∈ Nat.Partrec.Code.eval (.prec cf cg) (Nat.pair a k.succ)) :
    ∃ base : Nat, base ∈ Nat.Partrec.Code.eval cf a ∧
      TCode.precRun ((translate cg).comp Code.precStepArg) a 0 k base x := by
  induction k generalizing x with
  | zero =>
      rw [Nat.Partrec.Code.eval_prec_succ] at hx
      simp only [Part.bind_eq_bind, Part.mem_bind_iff] at hx
      rcases hx with ⟨base, hbase, hxg⟩
      rw [Nat.Partrec.Code.eval_prec_zero] at hbase
      refine ⟨base, hbase, ?_⟩
      change [x] ∈ (((translate cg).comp Code.precStepArg).eval [0, base, a])
      exact (translates_precStepArg hg 0 base a [x]).2 ⟨x, hxg, rfl⟩
  | succ k IH =>
      rw [Nat.Partrec.Code.eval_prec_succ] at hx
      simp only [Part.bind_eq_bind, Part.mem_bind_iff] at hx
      rcases hx with ⟨ih, hih, hxg⟩
      rcases IH hih with ⟨base, hbase, hrun⟩
      refine ⟨base, hbase, ?_⟩
      have hstep : [x] ∈ (((translate cg).comp Code.precStepArg).eval [0 + k.succ, ih, a]) := by
        simpa using (translates_precStepArg hg k.succ ih a [x]).2 ⟨x, hxg, rfl⟩
      exact TCode.precRun_snoc hrun hstep

theorem translate_prec_mem_of_nat_eval {cf cg : Nat.Partrec.Code}
    (hf : Translates cf (translate cf)) (hg : Translates cg (translate cg))
    {a n x : Nat}
    (hx : x ∈ Nat.Partrec.Code.eval (.prec cf cg) (Nat.pair a n)) :
    [x] ∈ (translate (.prec cf cg)).eval [Nat.pair a n] := by
  cases n with
  | zero =>
      exact (translates_prec_zero hf hg a [x]).2
        ⟨x, by simpa [Nat.Partrec.Code.eval_prec_zero] using hx, rfl⟩
  | succ k =>
      rcases exists_precRun_of_nat_prec_succ (cf := cf) (cg := cg) hg hx with
        ⟨base, hbase, hrun⟩
      have hbase_trans : [base] ∈ (translate cf).eval [a] :=
        (hf a [base]).2 ⟨base, hbase, rfl⟩
      have hbase_eq : (translate cf).eval [a] = pure [base] :=
        Part.eq_some_iff.2 hbase_trans
      have hprec : [x] ∈
          (Code.prec (translate cf) ((translate cg).comp Code.precStepArg)).eval [k.succ, a] :=
        TCode.prec_mem_of_precRun (f := translate cf)
          (g := (translate cg).comp Code.precStepArg) hbase_eq hrun
      rw [translate_prec, Turing.ToPartrec.Code.comp_eval]
      simp only [Part.bind_eq_bind, Part.mem_bind_iff]
      exact ⟨[k.succ, a], by simp, hprec⟩

set_option linter.flexible false in
theorem nat_eval_mem_of_precRun {cf cg : Nat.Partrec.Code}
    (hg : Translates cg (translate cg)) {a i b ih x : Nat}
    (hih : ih ∈ Nat.Partrec.Code.eval (.prec cf cg) (Nat.pair a i))
    (hrun : TCode.precRun ((translate cg).comp Code.precStepArg) a i b ih x) :
    x ∈ Nat.Partrec.Code.eval (.prec cf cg) (Nat.pair a (i + b.succ)) := by
  induction b generalizing i ih with
  | zero =>
      rw [show i + Nat.succ 0 = i.succ by omega]
      rw [Nat.Partrec.Code.eval_prec_succ]
      simp only [Part.bind_eq_bind, Part.mem_bind_iff]
      change [x] ∈ (((translate cg).comp Code.precStepArg).eval [i, ih, a]) at hrun
      rcases (translates_precStepArg hg i ih a [x]).1 hrun with ⟨x', hxg, hxv⟩
      have hx' : x' = x := by
        simpa using hxv.symm
      exact ⟨ih, hih, by simpa [hx'] using hxg⟩
  | succ b IH =>
      simp [TCode.precRun] at hrun
      rcases hrun with ⟨y, hy, hrest⟩
      have hyNat : y ∈ Nat.Partrec.Code.eval (.prec cf cg) (Nat.pair a i.succ) := by
        rw [Nat.Partrec.Code.eval_prec_succ]
        simp only [Part.bind_eq_bind, Part.mem_bind_iff]
        rcases (hg (Nat.pair a (Nat.pair i ih)) [y]).1 hy with ⟨y', hyg, hyv⟩
        have hy' : y' = y := by
          simpa using hyv.symm
        exact ⟨ih, hih, by simpa [hy'] using hyg⟩
      have hxNat : x ∈ Nat.Partrec.Code.eval (.prec cf cg)
          (Nat.pair a (i.succ + b.succ)) :=
        IH hyNat hrest
      simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hxNat

theorem nat_eval_mem_of_translate_prec_mem {cf cg : Nat.Partrec.Code}
    (hf : Translates cf (translate cf)) (hg : Translates cg (translate cg))
    {a n : Nat} {v : List Nat}
    (hv : v ∈ (translate (.prec cf cg)).eval [Nat.pair a n]) :
    ∃ x : Nat, x ∈ Nat.Partrec.Code.eval (.prec cf cg) (Nat.pair a n) ∧ v = [x] := by
  cases n with
  | zero =>
      rcases (translates_prec_zero hf hg a v).1 hv with ⟨x, hx, hvx⟩
      exact ⟨x, by simpa [Nat.Partrec.Code.eval_prec_zero] using hx, hvx⟩
  | succ k =>
      rw [translate_prec, Turing.ToPartrec.Code.comp_eval] at hv
      simp only [Part.bind_eq_bind, Part.mem_bind_iff] at hv
      rcases hv with ⟨arg, harg, hprec⟩
      have harg_eq : arg = [k.succ, a] := by
        simpa [Part.bind_eq_bind] using harg
      subst arg
      have hsingleF :
          ∀ v : List Nat, v ∈ (translate cf).eval [a] → ∃ base : Nat, v = [base] := by
        intro v hvf
        rcases (hf a v).1 hvf with ⟨base, _hbase, hv⟩
        exact ⟨base, hv⟩
      have hsingleG : ∀ i ih, ∀ v : List Nat,
          v ∈ (((translate cg).comp Code.precStepArg).eval [i, ih, a]) → ∃ x : Nat, v = [x] := by
        intro i ih v hvg
        rcases (translates_precStepArg hg i ih a v).1 hvg with ⟨x, _hx, hv⟩
        exact ⟨x, hv⟩
      rcases TCode.prec_mem_trace (f := translate cf)
          (g := (translate cg).comp Code.precStepArg) (a := a) (k := k)
          hsingleF hsingleG hprec with ⟨base, x, hvx, hbaseTrans, hrun⟩
      rcases (hf a [base]).1 hbaseTrans with ⟨base', hbase, hbasev⟩
      have hbase' : base' = base := by
        simpa using hbasev.symm
      have hbaseNat : base ∈ Nat.Partrec.Code.eval cf a := by
        simpa [hbase'] using hbase
      have hbasePrec : base ∈ Nat.Partrec.Code.eval (.prec cf cg) (Nat.pair a 0) := by
        simpa [Nat.Partrec.Code.eval_prec_zero] using hbaseNat
      have hxNat : x ∈ Nat.Partrec.Code.eval (.prec cf cg) (Nat.pair a (0 + k.succ)) :=
        nat_eval_mem_of_precRun (cf := cf) (cg := cg) hg hbasePrec hrun
      refine ⟨x, ?_, hvx⟩
      simpa using hxNat

theorem translates_prec_mp {cf cg : Nat.Partrec.Code}
    (hf : Translates cf (translate cf)) (hg : Translates cg (translate cg))
    (n : Nat) (v : List Nat) :
    v ∈ (translate (.prec cf cg)).eval [n] →
      ∃ x : Nat, x ∈ Nat.Partrec.Code.eval (.prec cf cg) n ∧ v = [x] := by
  intro hv
  let a := n.unpair.1
  let k := n.unpair.2
  have hn : Nat.pair a k = n := by
    simp [a, k, Nat.pair_unpair]
  rw [← hn] at hv ⊢
  exact nat_eval_mem_of_translate_prec_mem hf hg hv

theorem translates_prec_mpr {cf cg : Nat.Partrec.Code}
    (hf : Translates cf (translate cf)) (hg : Translates cg (translate cg))
    (n : Nat) (v : List Nat) :
    (∃ x : Nat, x ∈ Nat.Partrec.Code.eval (.prec cf cg) n ∧ v = [x]) →
      v ∈ (translate (.prec cf cg)).eval [n] := by
  rintro ⟨x, hx, rfl⟩
  let a := n.unpair.1
  let k := n.unpair.2
  have hn : Nat.pair a k = n := by
    simp [a, k, Nat.pair_unpair]
  rw [← hn] at hx ⊢
  exact translate_prec_mem_of_nat_eval hf hg hx

theorem translates_prec {cf cg : Nat.Partrec.Code}
    (hf : Translates cf (translate cf)) (hg : Translates cg (translate cg)) :
    Translates (.prec cf cg) (translate (.prec cf cg)) := by
  intro n v
  constructor
  · exact translates_prec_mp hf hg n v
  · exact translates_prec_mpr hf hg n v

theorem rfindFrom_mem_of_nat_rfind {cf : Nat.Partrec.Code}
    (hf : Translates cf (translate cf)) {a m n : Nat}
    (hrfind : n ∈ Nat.rfind fun i =>
      (fun x : Nat => x = 0) <$> Nat.Partrec.Code.eval cf (Nat.pair a (i + m))) :
    [n + m] ∈ (translate (.rfind' cf)).eval [Nat.pair a m] := by
  rw [translate_rfind']
  refine TCode.rfindFrom_mem_of_first_zero (test := translate cf) (a := a) (m := m)
    (n := n) ?_ ?_
  · have hzero_mem :
        0 ∈ Nat.Partrec.Code.eval cf (Nat.pair a (n + m)) := by
      have htrue := (Nat.mem_rfind.1 hrfind).1
      rw [Part.map_eq_map, Part.mem_map_iff] at htrue
      rcases htrue with ⟨x, hx, hxtrue⟩
      have hx0 : x = 0 := by
        simpa using hxtrue.symm
      simpa [hx0] using hx
    have htest_mem : [0] ∈ (translate cf).eval [Nat.pair a (n + m)] :=
      (hf (Nat.pair a (n + m)) [0]).2 ⟨0, hzero_mem, rfl⟩
    exact Part.eq_some_iff.2 htest_mem
  · intro i hi
    have hfalse := (Nat.mem_rfind.1 hrfind).2 hi
    rw [Part.map_eq_map, Part.mem_map_iff] at hfalse
    rcases hfalse with ⟨x, hx, hxfalse⟩
    have hxne : x ≠ 0 := by
      intro hx0
      subst x
      cases hxfalse
    cases x with
    | zero => exact (hxne rfl).elim
    | succ k =>
        refine ⟨k, ?_⟩
        have htest_mem : [k.succ] ∈ (translate cf).eval [Nat.pair a (i + m)] :=
          (hf (Nat.pair a (i + m)) [k.succ]).2 ⟨k.succ, hx, rfl⟩
        exact Part.eq_some_iff.2 htest_mem

theorem translate_rfind'_mem_of_nat_eval {cf : Nat.Partrec.Code}
    (hf : Translates cf (translate cf)) {a m x : Nat}
    (hx : x ∈ Nat.Partrec.Code.eval (.rfind' cf) (Nat.pair a m)) :
    [x] ∈ (translate (.rfind' cf)).eval [Nat.pair a m] := by
  rw [Nat.Partrec.Code.eval, Nat.unpaired, Nat.unpair_pair] at hx
  change x ∈ (Nat.rfind (fun n =>
    (fun z : Nat => z = 0) <$> Nat.Partrec.Code.eval cf (Nat.pair a (n + m)))).map
      (fun n => n + m) at hx
  rw [Part.mem_map_iff] at hx
  rcases hx with ⟨n, hn, rfl⟩
  exact rfindFrom_mem_of_nat_rfind hf hn

theorem nat_eval_mem_of_translate_rfind'_mem {cf : Nat.Partrec.Code}
    (hf : Translates cf (translate cf)) {a m : Nat} {v : List Nat}
    (hv : v ∈ (translate (.rfind' cf)).eval [Nat.pair a m]) :
    ∃ x : Nat, x ∈ Nat.Partrec.Code.eval (.rfind' cf) (Nat.pair a m) ∧ v = [x] := by
  rw [translate_rfind'] at hv
  have hsingle : ∀ t : Nat, ∀ v : List Nat,
      v ∈ (translate cf).eval [Nat.pair a (t + m)] → ∃ x : Nat, v = [x] := by
    intro t v hvtest
    rcases (hf (Nat.pair a (t + m)) v).1 hvtest with ⟨x, _hx, hv⟩
    exact ⟨x, hv⟩
  rcases TCode.rfindFrom_mem_trace (test := translate cf) (a := a) (m := m)
      hsingle hv with ⟨n, rfl, hzero, hprev⟩
  have hzeroNat : 0 ∈ Nat.Partrec.Code.eval cf (Nat.pair a (n + m)) := by
    rcases (hf (Nat.pair a (n + m)) [0]).1 hzero with ⟨x, hx, hxv⟩
    have hx0 : x = 0 := by
      simpa using hxv.symm
    simpa [hx0] using hx
  have htrue : true ∈ (fun z : Nat => decide (z = 0)) <$>
      Nat.Partrec.Code.eval cf (Nat.pair a (n + m)) := by
    rw [Part.map_eq_map, Part.mem_map_iff]
    exact ⟨0, hzeroNat, by simp⟩
  have hfalse : ∀ {i : Nat}, i < n → false ∈ (fun z : Nat => decide (z = 0)) <$>
      Nat.Partrec.Code.eval cf (Nat.pair a (i + m)) := by
    intro i hi
    rcases hprev i hi with ⟨k, hk⟩
    rcases (hf (Nat.pair a (i + m)) [k.succ]).1 hk with ⟨x, hx, hxv⟩
    have hxk : x = k.succ := by
      simpa using hxv.symm
    rw [Part.map_eq_map, Part.mem_map_iff]
    exact ⟨k.succ, by simpa [hxk] using hx, by simp⟩
  have hn : n ∈ Nat.rfind fun i =>
      (fun z : Nat => decide (z = 0)) <$> Nat.Partrec.Code.eval cf (Nat.pair a (i + m)) := by
    exact Nat.mem_rfind.2 ⟨htrue, hfalse⟩
  have hnat : n + m ∈ Nat.Partrec.Code.eval (.rfind' cf) (Nat.pair a m) := by
    rw [Nat.Partrec.Code.eval, Nat.unpaired, Nat.unpair_pair]
    change n + m ∈ (Nat.rfind (fun i =>
      (fun z : Nat => decide (z = 0)) <$>
        Nat.Partrec.Code.eval cf (Nat.pair a (i + m)))).map (fun i => i + m)
    rw [Part.mem_map_iff]
    exact ⟨n, hn, rfl⟩
  exact ⟨n + m, hnat, rfl⟩

theorem translates_rfind'_mp {cf : Nat.Partrec.Code}
    (hf : Translates cf (translate cf)) (n : Nat) (v : List Nat) :
    v ∈ (translate (.rfind' cf)).eval [n] →
      ∃ x : Nat, x ∈ Nat.Partrec.Code.eval (.rfind' cf) n ∧ v = [x] := by
  intro hv
  let a := n.unpair.1
  let m := n.unpair.2
  have hn : Nat.pair a m = n := by
    simp [a, m, Nat.pair_unpair]
  rw [← hn] at hv ⊢
  exact nat_eval_mem_of_translate_rfind'_mem hf hv

theorem translates_rfind'_mpr {cf : Nat.Partrec.Code}
    (hf : Translates cf (translate cf)) (n : Nat) (v : List Nat) :
    (∃ x : Nat, x ∈ Nat.Partrec.Code.eval (.rfind' cf) n ∧ v = [x]) →
      v ∈ (translate (.rfind' cf)).eval [n] := by
  rintro ⟨x, hx, rfl⟩
  let a := n.unpair.1
  let m := n.unpair.2
  have hn : Nat.pair a m = n := by
    simp [a, m, Nat.pair_unpair]
  rw [← hn] at hx ⊢
  exact translate_rfind'_mem_of_nat_eval hf hx

theorem translates_rfind' {cf : Nat.Partrec.Code}
    (hf : Translates cf (translate cf)) :
    Translates (.rfind' cf) (translate (.rfind' cf)) := by
  intro n v
  constructor
  · exact translates_rfind'_mp hf n v
  · exact translates_rfind'_mpr hf n v

theorem translate_correct (c : Nat.Partrec.Code) : Translates c (translate c) := by
  induction c with
  | zero => exact translates_zero
  | succ => exact translates_succ
  | left => exact translates_left
  | right => exact translates_right
  | pair _ _ ihf ihg => exact translates_pair ihf ihg
  | comp _ _ ihf ihg => exact translates_comp ihf ihg
  | prec _ _ ihf ihg => exact translates_prec ihf ihg
  | rfind' _ ih => exact translates_rfind' ih

/--
The source-code translation preserves the halting domain of Mathlib's
`PartrecToTM2` evaluator.
-/
theorem translate_tm2_dom (c : Nat.Partrec.Code) :
    (StateTransition.eval
      (Turing.TM2.step Turing.PartrecToTM2.tr)
      (Turing.PartrecToTM2.init (translate c) [0])).Dom ↔
        (Nat.Partrec.Code.eval c 0).Dom := by
  exact (translate_correct c).tm2_dom

end NatPartrecToToPartrec

end LeanWang
