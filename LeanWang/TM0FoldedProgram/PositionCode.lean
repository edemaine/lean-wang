/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedProgram.SimSemantics

/-!
Position-coded label lookup and primitive-recursive row descriptors.
-/

namespace LeanWang

namespace TM0FoldedCompiler

open TM0Route

/--
Descriptor rows for a source-label index. This is a numeric outer enumeration
of the same semantic labels used by `simStepData`, avoiding a dependent label
as the externally visible iterator.
-/
def simStepDataForLabelIndex (tc : Turing.ToPartrec.Code) (i : Nat) :
    List SimStepData :=
  ((TM0Route.partrecStartedTM0LabelList tc)[i]?).elim [] (simStepDataForLabel tc)

/--
Offset form of `simStepDataForLabelIndex`, using the statement-decoder-based
label index from `TM0Route`. The extra `fuel` and statement offset `k` expose
the recursive state needed for the eventual primitive-recursive proof of the
descriptor list.
-/
def simStepDataForLabelIndexFrom
    (tc : Turing.ToPartrec.Code) (fuel k i : Nat) :
    List SimStepData :=
  (TM0Route.partrecStartedTM0LabelAtByStatementFrom? tc fuel k i).elim []
    (simStepDataForLabel tc)

/--
Label lookup for the offset descriptor decoder, paired with the numeric finite
state code of the decoded current label.
-/
def labelAtByStatementFromWithStateCode?
    (tc : Turing.ToPartrec.Code) (fuel k i : Nat) :
    Option (SourceLabel tc × Nat) :=
  (TM0Route.partrecStartedTM0LabelAtByStatementFrom? tc fuel k i).map
    fun q => (q, TM0FiniteCompiler.stateCode tc q)

/--
Position-code for the rectangular statement/variable label decoder.

The support list is `default :: labelList`, while the rectangular label list
itself starts with the same default label `(none, default)`.  To agree with the
forced start/default state, that duplicated label is coded as `0`; all other
rectangular positions use the shifted support-list position.
-/
def labelPositionCode {tc : Turing.ToPartrec.Code}
    (k i : Nat) (stmt : Option (SourceStmt tc)) (v : PartrecVar) : Nat :=
  if ((stmt, v) : SourceLabel tc) = sourceDefaultLabel tc then
    0
  else
    1 + k * TM0Route.partrecVarList.length + i

theorem labelPositionCode_primrec_fixed (tc : Turing.ToPartrec.Code)
    [Primcodable (Turing.TM1.Stmt
      (Turing.TM2to1.Γ' PartrecStack PartrecStackSymbol)
      (Turing.TM2to1.Λ' PartrecStack PartrecStackSymbol (StartedLabel tc) PartrecVar)
      PartrecVar)] :
    Primrec (fun p : Nat × Nat × Option (SourceStmt tc) × PartrecVar =>
      labelPositionCode p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  let rect : Nat × Nat × Option (SourceStmt tc) × PartrecVar → Nat := fun p =>
    1 + p.1 * TM0Route.partrecVarList.length + p.2.1
  have hrect : Primrec rect := by
    exact Primrec.nat_add.comp
      (Primrec.nat_add.comp (Primrec.const 1)
        (Primrec.nat_mul.comp Primrec.fst
          (Primrec.const TM0Route.partrecVarList.length)))
      (Primrec.fst.comp Primrec.snd)
  have hdefault : PrimrecPred
      (fun p : Nat × Nat × Option (SourceStmt tc) × PartrecVar =>
        ((p.2.2.1, p.2.2.2) : SourceLabel tc) = sourceDefaultLabel tc) :=
    Primrec.eq.comp
      (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.const (sourceDefaultLabel tc))
  exact (Primrec.ite hdefault
    (Primrec.const 0) hrect).of_eq fun p => by
      unfold labelPositionCode rect
      rfl

/-- One step of the position-coded offset label lookup. -/
def labelAtByStatementFromWithPositionCodeStep?
    (tc : Turing.ToPartrec.Code)
    (s : Option (SourceLabel tc × Nat) × Nat × Nat) :
    Option (SourceLabel tc × Nat) × Nat × Nat :=
  match s.1 with
  | some r => (some r, s.2)
  | none =>
      match TM0Route.partrecVarList[s.2.2]? with
      | some v =>
          ((TM0Route.partrecStartedTM0StatementAt? tc s.2.1).map fun stmt =>
            ((stmt, v), labelPositionCode s.2.1 s.2.2 stmt v),
            s.2.1, s.2.2)
      | none =>
          (none, s.2.1 + 1, s.2.2 - TM0Route.partrecVarList.length)

/--
Offset label lookup paired with the numeric position in the rectangular
statement-by-variable enumeration, including the leading default state.

The duplicated default label is mapped to state `0`; all other decoded
statement/variable positions use their support-list position.
-/
def labelAtByStatementFromWithPositionCode?
    (tc : Turing.ToPartrec.Code) (fuel k i : Nat) :
    Option (SourceLabel tc × Nat) :=
  ((labelAtByStatementFromWithPositionCodeStep? tc)^[fuel] (none, k, i)).1

theorem labelAtByStatementFromWithPositionCodeStep?_primrec_fixed
    (tc : Turing.ToPartrec.Code)
    [Primcodable (Turing.TM1.Stmt
      (Turing.TM2to1.Γ' PartrecStack PartrecStackSymbol)
      (Turing.TM2to1.Λ' PartrecStack PartrecStackSymbol (StartedLabel tc) PartrecVar)
      PartrecVar)] :
    Primrec (labelAtByStatementFromWithPositionCodeStep? tc) := by
  let State := Option (SourceLabel tc × Nat) × Nat × Nat
  let found : State → Option (SourceLabel tc × Nat) := fun s => s.1
  let offset : State → Nat := fun s => s.2.1
  let index : State → Nat := fun s => s.2.2
  have hfound : Primrec found := Primrec.fst
  have hoffset : Primrec offset := Primrec.fst.comp Primrec.snd
  have hindex : Primrec index := Primrec.snd.comp Primrec.snd
  have hstmt : Primrec (TM0Route.partrecStartedTM0StatementAt? tc) :=
    TM0Route.partrecStartedTM0StatementAt?_primrec_fixed tc
  have hnoneStep : Primrec (fun s : State =>
      ((none : Option (SourceLabel tc × Nat)),
        (offset s + 1, index s - TM0Route.partrecVarList.length))) := by
    exact Primrec.pair (Primrec.const (none : Option (SourceLabel tc × Nat)))
      (Primrec.pair (Primrec.succ.comp hoffset)
        (Primrec.nat_sub.comp hindex (Primrec.const TM0Route.partrecVarList.length)))
  have hsomeBlock : Primrec₂ (fun s : State => fun v : PartrecVar =>
      ((TM0Route.partrecStartedTM0StatementAt? tc (offset s)).map fun stmt =>
        ((stmt, v), labelPositionCode (offset s) (index s) stmt v),
        offset s, index s)) := by
    apply Primrec₂.mk
    let base : State × PartrecVar → State := fun p => p.1
    let vArg : State × PartrecVar → PartrecVar := fun p => p.2
    have hbase : Primrec base := Primrec.fst
    have hvArg : Primrec vArg := Primrec.snd
    have hoffsetBase : Primrec (fun p : State × PartrecVar => offset (base p)) :=
      hoffset.comp hbase
    have hindexBase : Primrec (fun p : State × PartrecVar => index (base p)) :=
      hindex.comp hbase
    have hget : Primrec (fun p : State × PartrecVar =>
        TM0Route.partrecStartedTM0StatementAt? tc (offset (base p))) :=
      hstmt.comp hoffsetBase
    have hpair : Primrec₂ (fun p : State × PartrecVar =>
        fun stmt : Option (SourceStmt tc) =>
          ((stmt, vArg p), labelPositionCode (offset (base p)) (index (base p)) stmt
            (vArg p))) := by
      apply Primrec₂.mk
      have hcode : Primrec (fun p : (State × PartrecVar) × Option (SourceStmt tc) =>
          labelPositionCode (offset (base p.1)) (index (base p.1)) p.2 (vArg p.1)) := by
        exact (labelPositionCode_primrec_fixed tc).comp
          (Primrec.pair
            (hoffsetBase.comp Primrec.fst)
            (Primrec.pair
              (hindexBase.comp Primrec.fst)
              (Primrec.pair Primrec.snd (hvArg.comp Primrec.fst))))
      exact Primrec.pair
        (Primrec.pair Primrec.snd (hvArg.comp Primrec.fst))
        hcode
    have hmap : Primrec (fun p : State × PartrecVar =>
        (TM0Route.partrecStartedTM0StatementAt? tc (offset (base p))).map
          fun stmt =>
            ((stmt, vArg p), labelPositionCode (offset (base p)) (index (base p)) stmt
              (vArg p))) :=
      Primrec.option_map hget hpair
    exact Primrec.pair hmap (Primrec.pair hoffsetBase hindexBase)
  have hnone : Primrec (fun s : State =>
      match TM0Route.partrecVarList[index s]? with
      | some v =>
          ((TM0Route.partrecStartedTM0StatementAt? tc (offset s)).map fun stmt =>
            ((stmt, v), labelPositionCode (offset s) (index s) stmt v),
            offset s, index s)
      | none =>
          ((none : Option (SourceLabel tc × Nat)),
            (offset s + 1, index s - TM0Route.partrecVarList.length))) := by
    have hlookup : Primrec (fun s : State => TM0Route.partrecVarList[index s]?) :=
      (Primrec.list_getElem?₁ TM0Route.partrecVarList).comp hindex
    exact (Primrec.option_casesOn hlookup hnoneStep hsomeBlock).of_eq fun s => by
      cases TM0Route.partrecVarList[index s]? <;> rfl
  have hsomeFound : Primrec₂ (fun s : State => fun r : SourceLabel tc × Nat =>
      (some r, s.2)) := by
    apply Primrec₂.mk
    exact Primrec.pair (Primrec.option_some.comp Primrec.snd)
      (Primrec.snd.comp Primrec.fst)
  exact (Primrec.option_casesOn hfound hnone hsomeFound).of_eq fun s => by
    rcases s with ⟨r, k, i⟩
    cases r <;> rfl

theorem labelAtByStatementFromWithPositionCode?_primrec_fixed
    (tc : Turing.ToPartrec.Code)
    [Primcodable (Turing.TM1.Stmt
      (Turing.TM2to1.Γ' PartrecStack PartrecStackSymbol)
      (Turing.TM2to1.Λ' PartrecStack PartrecStackSymbol (StartedLabel tc) PartrecVar)
      PartrecVar)] :
    Primrec (fun p : Nat × Nat × Nat =>
      labelAtByStatementFromWithPositionCode? tc p.1 p.2.1 p.2.2) := by
  let step := labelAtByStatementFromWithPositionCodeStep? tc
  let init : Nat × Nat × Nat → Option (SourceLabel tc × Nat) × Nat × Nat :=
    fun p => (none, p.2.1, p.2.2)
  have hstep : Primrec step :=
    labelAtByStatementFromWithPositionCodeStep?_primrec_fixed tc
  have hinit : Primrec init :=
    Primrec.pair (Primrec.const (none : Option (SourceLabel tc × Nat))) Primrec.snd
  have hiter : Primrec (fun p : Nat × Nat × Nat => (step^[p.1]) (init p)) := by
    exact Primrec.nat_iterate Primrec.fst hinit ((hstep.comp Primrec.snd).to₂)
  exact (Primrec.fst.comp hiter).of_eq fun p => by
    rfl

theorem labelAtByStatementFromWithPositionCodeStep?_fixed_of_found
    (tc : Turing.ToPartrec.Code) (r : SourceLabel tc × Nat) (k i : Nat) :
    labelAtByStatementFromWithPositionCodeStep? tc (some r, k, i) =
      (some r, k, i) := by
  rfl

theorem labelAtByStatementFromWithPositionCodeStep?_fixed_of_stmt_none
    (tc : Turing.ToPartrec.Code) {k i : Nat} {v : PartrecVar}
    (hv : TM0Route.partrecVarList[i]? = some v)
    (hstmt : TM0Route.partrecStartedTM0StatementAt? tc k = none) :
    labelAtByStatementFromWithPositionCodeStep? tc (none, k, i) =
      (none, k, i) := by
  unfold labelAtByStatementFromWithPositionCodeStep?
  simp [hv, hstmt]

theorem labelAtByStatementFromWithPositionCode?_zero
    (tc : Turing.ToPartrec.Code) (k i : Nat) :
    labelAtByStatementFromWithPositionCode? tc 0 k i = none := by
  rfl

theorem labelAtByStatementFromWithPositionCode?_succ_of_var_none
    (tc : Turing.ToPartrec.Code) {fuel k i : Nat}
    (hv : TM0Route.partrecVarList[i]? = none) :
    labelAtByStatementFromWithPositionCode? tc (fuel + 1) k i =
      labelAtByStatementFromWithPositionCode? tc fuel
        (k + 1) (i - TM0Route.partrecVarList.length) := by
  unfold labelAtByStatementFromWithPositionCode?
  rw [Function.iterate_succ_apply]
  unfold labelAtByStatementFromWithPositionCodeStep?
  simp [hv]

theorem labelAtByStatementFromWithPositionCode?_succ_of_stmt_none
    (tc : Turing.ToPartrec.Code) {fuel k i : Nat} {v : PartrecVar}
    (hv : TM0Route.partrecVarList[i]? = some v)
    (hstmt : TM0Route.partrecStartedTM0StatementAt? tc k = none) :
    labelAtByStatementFromWithPositionCode? tc (fuel + 1) k i = none := by
  unfold labelAtByStatementFromWithPositionCode?
  rw [Function.iterate_succ_apply]
  have hfixed := labelAtByStatementFromWithPositionCodeStep?_fixed_of_stmt_none
    tc hv hstmt
  rw [hfixed]
  rw [Function.iterate_fixed hfixed fuel]

theorem labelAtByStatementFromWithPositionCode?_succ_of_stmt_some
    (tc : Turing.ToPartrec.Code) {fuel k i : Nat} {v : PartrecVar}
    {stmt : Option (SourceStmt tc)}
    (hv : TM0Route.partrecVarList[i]? = some v)
    (hstmt : TM0Route.partrecStartedTM0StatementAt? tc k = some stmt) :
    labelAtByStatementFromWithPositionCode? tc (fuel + 1) k i =
      some ((((stmt, v) : SourceLabel tc),
        labelPositionCode k i stmt v)) := by
  unfold labelAtByStatementFromWithPositionCode?
  rw [Function.iterate_succ_apply]
  unfold labelAtByStatementFromWithPositionCodeStep?
  simp only [hv, hstmt, Option.map_some]
  have hfixed := labelAtByStatementFromWithPositionCodeStep?_fixed_of_found
    tc ((((stmt, v) : SourceLabel tc),
      labelPositionCode k i stmt v)) k i
  change ((labelAtByStatementFromWithPositionCodeStep? tc)^[fuel]
      (some ((((stmt, v) : SourceLabel tc),
        labelPositionCode k i stmt v)), k, i)).1 =
    some ((((stmt, v) : SourceLabel tc),
      labelPositionCode k i stmt v))
  rw [Function.iterate_fixed hfixed fuel]
  rfl

theorem labelAtByStatementFromWithPositionCode?_of_div_mod
    (tc : Turing.ToPartrec.Code) {fuel k i : Nat}
    {stmt : Option (SourceStmt tc)} {v : PartrecVar}
    (hblock : i / TM0Route.partrecVarList.length < fuel)
    (hv : TM0Route.partrecVarList[i % TM0Route.partrecVarList.length]? = some v)
    (hstmt : TM0Route.partrecStartedTM0StatementAt? tc
        (k + i / TM0Route.partrecVarList.length) = some stmt) :
    labelAtByStatementFromWithPositionCode? tc fuel k i =
      some ((((stmt, v) : SourceLabel tc),
        labelPositionCode (k + i / TM0Route.partrecVarList.length)
          (i % TM0Route.partrecVarList.length) stmt v)) := by
  induction fuel generalizing k i with
  | zero =>
      exact False.elim (Nat.not_lt_zero _ hblock)
  | succ fuel ih =>
      by_cases hi : i < TM0Route.partrecVarList.length
      · have hdiv : i / TM0Route.partrecVarList.length = 0 := Nat.div_eq_of_lt hi
        have hmod : i % TM0Route.partrecVarList.length = i := Nat.mod_eq_of_lt hi
        have hvi : TM0Route.partrecVarList[i]? = some v := by
          simpa [hmod] using hv
        rw [labelAtByStatementFromWithPositionCode?_succ_of_stmt_some
          (tc := tc) (fuel := fuel) (k := k) (i := i) (v := v)
          (stmt := stmt) hvi (by simpa [hdiv] using hstmt)]
        · simp [hdiv, hmod]
      · have hle : TM0Route.partrecVarList.length ≤ i := le_of_not_gt hi
        have hvnone : TM0Route.partrecVarList[i]? = none := by
          rw [List.getElem?_eq_none_iff]
          exact hle
        rw [labelAtByStatementFromWithPositionCode?_succ_of_var_none tc hvnone]
        have hlen : 0 < TM0Route.partrecVarList.length := by
          simp [TM0Route.partrecVarList]
        have hdiv :
            i / TM0Route.partrecVarList.length =
              (i - TM0Route.partrecVarList.length) /
                  TM0Route.partrecVarList.length + 1 := by
          calc
            i / TM0Route.partrecVarList.length =
                ((i - TM0Route.partrecVarList.length) +
                    TM0Route.partrecVarList.length) /
                  TM0Route.partrecVarList.length := by
              rw [Nat.sub_add_cancel hle]
            _ = (i - TM0Route.partrecVarList.length) /
                  TM0Route.partrecVarList.length + 1 := by
              rw [Nat.add_div_right _ hlen]
        have hblock' :
            (i - TM0Route.partrecVarList.length) /
                TM0Route.partrecVarList.length < fuel := by
          have hsucc :
              (i - TM0Route.partrecVarList.length) /
                  TM0Route.partrecVarList.length + 1 < fuel + 1 := by
            simpa [hdiv] using hblock
          exact Nat.succ_lt_succ_iff.1 hsucc
        have hmod :
            (i - TM0Route.partrecVarList.length) %
                TM0Route.partrecVarList.length =
              i % TM0Route.partrecVarList.length := by
          rw [← Nat.add_mod_right (i - TM0Route.partrecVarList.length)
            TM0Route.partrecVarList.length]
          have hsum :
              i - TM0Route.partrecVarList.length +
                  TM0Route.partrecVarList.length = i :=
            Nat.sub_add_cancel hle
          rw [hsum]
        have hv' :
            TM0Route.partrecVarList[
              (i - TM0Route.partrecVarList.length) %
                TM0Route.partrecVarList.length]? = some v := by
          simpa [hmod] using hv
        have hstmt' :
            TM0Route.partrecStartedTM0StatementAt? tc
                (k + 1 +
                  (i - TM0Route.partrecVarList.length) /
                    TM0Route.partrecVarList.length) = some stmt := by
          simpa [hdiv, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hstmt
        simpa [hdiv, hmod, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          ih (k := k + 1) hblock' hv' hstmt'

theorem labelPositionCode_mem_states_of_statementAt?
    (tc : Turing.ToPartrec.Code) {k i : Nat} {stmt : Option (SourceStmt tc)}
    {v : PartrecVar}
    (hstmt : TM0Route.partrecStartedTM0StatementAt? tc k = some stmt)
    (hv : TM0Route.partrecVarList[i]? = some v) :
    labelPositionCode k i stmt v ∈ TM0Route.partrecStartedTM0States tc := by
  by_cases hdefault : ((stmt, v) : SourceLabel tc) = sourceDefaultLabel tc
  · simpa [labelPositionCode, hdefault, TM0Route.partrecStartedTM0Start] using
      TM0Route.partrecStartedTM0Start_mem_states tc
  · rw [show labelPositionCode k i stmt v =
        1 + k * TM0Route.partrecVarList.length + i by
      simp [labelPositionCode, hdefault]]
    exact TM0Route.partrecStartedTM0_position_mem_states_of_statementAt?
      tc hstmt hv

theorem labelPositionCode_support_get?_of_statementAt?
    (tc : Turing.ToPartrec.Code) {k i : Nat} {stmt : Option (SourceStmt tc)}
    {v : PartrecVar}
    (hstmt : TM0Route.partrecStartedTM0StatementAt? tc k = some stmt)
    (hv : TM0Route.partrecVarList[i]? = some v) :
    (TM0Route.partrecStartedTM0LabelSupportList tc)[labelPositionCode k i stmt v]? =
      some ((stmt, v) : SourceLabel tc) := by
  by_cases hdefault : ((stmt, v) : SourceLabel tc) = sourceDefaultLabel tc
  · rw [show labelPositionCode k i stmt v = 0 by simp [labelPositionCode, hdefault]]
    rw [TM0Route.partrecStartedTM0LabelSupportList_get_zero]
    rw [← sourceDefaultLabel_eq_default tc]
    exact congrArg some hdefault.symm
  · rw [show labelPositionCode k i stmt v =
        1 + k * TM0Route.partrecVarList.length + i by
      simp [labelPositionCode, hdefault]]
    exact TM0Route.partrecStartedTM0LabelSupportList_get_position_of_statementAt?
      tc hstmt hv

/--
If the statement-support list has no duplicates, the rectangular
statement/variable position is the first occurrence of its label in the support
list.
-/
theorem labelPositionCode_minimal_of_statementList_nodup
    (tc : Turing.ToPartrec.Code) {k i : Nat} {stmt : Option (SourceStmt tc)}
    {v : PartrecVar}
    (hnodup : (TM0Route.partrecStartedTM0StatementList tc).Nodup)
    (hstmt : TM0Route.partrecStartedTM0StatementAt? tc k = some stmt)
    (hv : TM0Route.partrecVarList[i]? = some v) :
    ∀ m, m < labelPositionCode k i stmt v →
      (TM0Route.partrecStartedTM0LabelSupportList tc)[m]? ≠
        some ((stmt, v) : SourceLabel tc) := by
  by_cases hdefault : ((stmt, v) : SourceLabel tc) = sourceDefaultLabel tc
  · simp [labelPositionCode, hdefault]
  · intro m hm hget
    have hcode :
        labelPositionCode k i stmt v = 1 + k * TM0Route.partrecVarList.length + i := by
      simp [labelPositionCode, hdefault]
    rw [hcode] at hm
    cases m with
    | zero =>
        rw [TM0Route.partrecStartedTM0LabelSupportList_get_zero] at hget
        have hq : (default : SourceLabel tc) = ((stmt, v) : SourceLabel tc) :=
          Option.some.inj hget
        have hqDefault : ((stmt, v) : SourceLabel tc) = (default : SourceLabel tc) :=
          hq.symm
        exact hdefault (hqDefault.trans (sourceDefaultLabel_eq_default tc).symm)
    | succ m =>
        unfold TM0Route.partrecStartedTM0LabelSupportList at hget
        simp only [List.getElem?_cons_succ] at hget
        unfold TM0Route.partrecStartedTM0LabelList at hget
        have hstmtList :
            (TM0Route.partrecStartedTM0StatementList tc)[k]? = some stmt := by
          simpa [TM0Route.partrecStartedTM0StatementAt?_eq_getElem? tc k] using hstmt
        have hrectGet :
            ((TM0Route.partrecStartedTM0StatementList tc).flatMap fun stmt =>
              TM0Route.partrecVarList.map fun v =>
                ((stmt, v) : SourceLabel tc))[k * TM0Route.partrecVarList.length + i]? =
              some ((stmt, v) : SourceLabel tc) := by
          exact TM0Route.flatMap_constMap_getElem?_of_getElem?
            (TM0Route.partrecStartedTM0StatementList tc) TM0Route.partrecVarList
            hstmtList hv
        have hrectNodup :
            ((TM0Route.partrecStartedTM0StatementList tc).flatMap fun stmt =>
              TM0Route.partrecVarList.map fun v =>
                ((stmt, v) : SourceLabel tc)).Nodup := by
          simpa only [SProd.sprod, List.product] using
            hnodup.product TM0Route.partrecVarList_nodup
        rcases List.getElem?_eq_some_iff.1 hget with ⟨hmLen, hmGet⟩
        rcases List.getElem?_eq_some_iff.1 hrectGet with ⟨hposLen, hposGet⟩
        have hmEq : m = k * TM0Route.partrecVarList.length + i := by
          exact (hrectNodup.getElem_inj_iff
            (i := m) (hi := hmLen)
            (j := k * TM0Route.partrecVarList.length + i) (hj := hposLen)).1 (by
              exact hmGet.trans hposGet.symm)
        omega

private theorem idxOf_eq_of_getElem?_eq_some_of_forall_lt_ne
    {α : Type} [DecidableEq α] (xs : List α) {n : Nat} {x : α}
    (hget : xs[n]? = some x)
    (hmin : ∀ m, m < n → xs[m]? ≠ some x) :
    xs.idxOf x = n := by
  induction xs generalizing n with
  | nil =>
      simp at hget
  | cons y ys ih =>
      cases n with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
          subst y
          simp
      | succ n =>
          simp only [List.getElem?_cons_succ] at hget
          have hyne : y ≠ x := by
            have h0 := hmin 0 (Nat.succ_pos n)
            simp only [List.getElem?_cons_zero] at h0
            intro hy
            subst y
            exact h0 rfl
          have hminTail : ∀ m, m < n → ys[m]? ≠ some x := by
            intro m hm
            have hs := hmin (m + 1) (Nat.succ_lt_succ hm)
            simpa only [List.getElem?_cons_succ] using hs
          rw [List.idxOf_cons_ne ys hyne, ih hget hminTail]

theorem stateCode_eq_of_support_get?_minimal
    {tc : Turing.ToPartrec.Code} {q : SourceLabel tc} {n : Nat}
    (hget : (TM0Route.partrecStartedTM0LabelSupportList tc)[n]? = some q)
    (hmin : ∀ m, m < n →
      (TM0Route.partrecStartedTM0LabelSupportList tc)[m]? ≠ some q) :
    TM0FiniteCompiler.stateCode tc q = n := by
  unfold TM0FiniteCompiler.stateCode
  exact idxOf_eq_of_getElem?_eq_some_of_forall_lt_ne
    (TM0Route.partrecStartedTM0LabelSupportList tc) hget hmin

theorem labelPositionCode_eq_stateCode_of_minimal
    (tc : Turing.ToPartrec.Code) {k i : Nat} {stmt : Option (SourceStmt tc)}
    {v : PartrecVar}
    (hstmt : TM0Route.partrecStartedTM0StatementAt? tc k = some stmt)
    (hv : TM0Route.partrecVarList[i]? = some v)
    (hmin : ∀ m, m < labelPositionCode k i stmt v →
      (TM0Route.partrecStartedTM0LabelSupportList tc)[m]? ≠
        some ((stmt, v) : SourceLabel tc)) :
    labelPositionCode k i stmt v = TM0FiniteCompiler.stateCode tc ((stmt, v) : SourceLabel tc) := by
  symm
  exact stateCode_eq_of_support_get?_minimal
    (labelPositionCode_support_get?_of_statementAt? tc hstmt hv) hmin

theorem labelAtByStatementFromWithPositionCode?_fst_eq
    (tc : Turing.ToPartrec.Code) (fuel k i : Nat) :
    (labelAtByStatementFromWithPositionCode? tc fuel k i).map Prod.fst =
      TM0Route.partrecStartedTM0LabelAtByStatementFrom? tc fuel k i := by
  induction fuel generalizing k i with
  | zero =>
      simp [labelAtByStatementFromWithPositionCode?_zero,
        TM0Route.partrecStartedTM0LabelAtByStatementFrom?_zero]
  | succ fuel ih =>
      rw [TM0Route.partrecStartedTM0LabelAtByStatementFrom?_succ]
      cases hv : TM0Route.partrecVarList[i]? with
      | none =>
          rw [labelAtByStatementFromWithPositionCode?_succ_of_var_none tc hv]
          exact ih (k + 1) (i - TM0Route.partrecVarList.length)
      | some v =>
          cases hstmt : TM0Route.partrecStartedTM0StatementAt? tc k with
          | none =>
              rw [labelAtByStatementFromWithPositionCode?_succ_of_stmt_none tc hv hstmt]
              simp
          | some stmt =>
              rw [labelAtByStatementFromWithPositionCode?_succ_of_stmt_some tc hv hstmt]
              rfl

theorem labelAtByStatementFromWithPositionCode?_code_mem_states
    (tc : Turing.ToPartrec.Code) {fuel k i : Nat} {q : SourceLabel tc × Nat}
    (h : labelAtByStatementFromWithPositionCode? tc fuel k i = some q) :
    q.2 ∈ TM0Route.partrecStartedTM0States tc := by
  induction fuel generalizing k i with
  | zero =>
      simp [labelAtByStatementFromWithPositionCode?_zero] at h
  | succ fuel ih =>
      cases hv : TM0Route.partrecVarList[i]? with
      | none =>
          rw [labelAtByStatementFromWithPositionCode?_succ_of_var_none tc hv] at h
          exact ih h
      | some v =>
          cases hstmt : TM0Route.partrecStartedTM0StatementAt? tc k with
          | none =>
              rw [labelAtByStatementFromWithPositionCode?_succ_of_stmt_none tc hv hstmt] at h
              simp at h
          | some stmt =>
              rw [labelAtByStatementFromWithPositionCode?_succ_of_stmt_some tc hv hstmt] at h
              cases h
              exact labelPositionCode_mem_states_of_statementAt? tc hstmt hv

theorem labelAtByStatementFromWithPositionCode?_code_eq_zero_or_rect
    (tc : Turing.ToPartrec.Code) {fuel k i : Nat} {q : SourceLabel tc × Nat}
    (h : labelAtByStatementFromWithPositionCode? tc fuel k i = some q) :
    q.2 = 0 ∨ q.2 = 1 + k * TM0Route.partrecVarList.length + i := by
  induction fuel generalizing k i with
  | zero =>
      simp [labelAtByStatementFromWithPositionCode?_zero] at h
  | succ fuel ih =>
      cases hv : TM0Route.partrecVarList[i]? with
      | none =>
          rw [labelAtByStatementFromWithPositionCode?_succ_of_var_none tc hv] at h
          rcases ih h with hzero | hrect
          · exact Or.inl hzero
          · right
            have hle : TM0Route.partrecVarList.length ≤ i := by
              rw [List.getElem?_eq_none_iff] at hv
              exact hv
            have hlen : 0 < TM0Route.partrecVarList.length := by
              simp [TM0Route.partrecVarList]
            calc
              q.2 = 1 + (k + 1) * TM0Route.partrecVarList.length +
                  (i - TM0Route.partrecVarList.length) := hrect
              _ = 1 + (k * TM0Route.partrecVarList.length +
                    TM0Route.partrecVarList.length) +
                  (i - TM0Route.partrecVarList.length) := by
                    rw [Nat.succ_mul]
              _ = 1 + k * TM0Route.partrecVarList.length + i := by
                    omega
      | some v =>
          cases hstmt : TM0Route.partrecStartedTM0StatementAt? tc k with
          | none =>
              rw [labelAtByStatementFromWithPositionCode?_succ_of_stmt_none tc hv hstmt] at h
              simp at h
          | some stmt =>
              rw [labelAtByStatementFromWithPositionCode?_succ_of_stmt_some tc hv hstmt] at h
              cases h
              by_cases hdefault : ((stmt, v) : SourceLabel tc) = sourceDefaultLabel tc
              · left
                simp [labelPositionCode, hdefault]
              · right
                simp [labelPositionCode, hdefault]

theorem labelAtByStatementFromWithPositionCode?_start_code_eq_zero_or_succ
    (tc : Turing.ToPartrec.Code) {fuel i : Nat} {q : SourceLabel tc × Nat}
    (h : labelAtByStatementFromWithPositionCode? tc fuel 0 i = some q) :
    q.2 = 0 ∨ q.2 = i + 1 := by
  rcases labelAtByStatementFromWithPositionCode?_code_eq_zero_or_rect tc h with
    hzero | hrect
  · exact Or.inl hzero
  · right
    omega

theorem labelAtByStatementFromWithPositionCode?_start_currentCode_ne_succ_of_lt
    (tc : Turing.ToPartrec.Code) {fuel i n : Nat} {q : SourceLabel tc × Nat}
    (hi : i < n)
    (h : labelAtByStatementFromWithPositionCode? tc fuel 0 i = some q) :
    q.2 ≠ n + 1 := by
  rcases labelAtByStatementFromWithPositionCode?_start_code_eq_zero_or_succ tc h with
    hzero | hsucc
  · omega
  · omega

theorem labelAtByStatementFromWithPositionCode?_code_eq_zero_of_sourceDefault
    (tc : Turing.ToPartrec.Code) {fuel k i : Nat} {q : SourceLabel tc × Nat}
    (h : labelAtByStatementFromWithPositionCode? tc fuel k i = some q)
    (hq : q.1 = sourceDefaultLabel tc) :
    q.2 = 0 := by
  induction fuel generalizing k i with
  | zero =>
      simp [labelAtByStatementFromWithPositionCode?_zero] at h
  | succ fuel ih =>
      cases hv : TM0Route.partrecVarList[i]? with
      | none =>
          rw [labelAtByStatementFromWithPositionCode?_succ_of_var_none tc hv] at h
          exact ih h
      | some v =>
          cases hstmt : TM0Route.partrecStartedTM0StatementAt? tc k with
          | none =>
              rw [labelAtByStatementFromWithPositionCode?_succ_of_stmt_none tc hv hstmt] at h
              simp at h
          | some stmt =>
              rw [labelAtByStatementFromWithPositionCode?_succ_of_stmt_some tc hv hstmt] at h
              cases h
              simpa [labelPositionCode, hq]

theorem labelAtByStatementFromWithPositionCode?_support_get?
    (tc : Turing.ToPartrec.Code) {fuel k i : Nat} {q : SourceLabel tc × Nat}
    (h : labelAtByStatementFromWithPositionCode? tc fuel k i = some q) :
    (TM0Route.partrecStartedTM0LabelSupportList tc)[q.2]? = some q.1 := by
  induction fuel generalizing k i with
  | zero =>
      simp [labelAtByStatementFromWithPositionCode?_zero] at h
  | succ fuel ih =>
      cases hv : TM0Route.partrecVarList[i]? with
      | none =>
          rw [labelAtByStatementFromWithPositionCode?_succ_of_var_none tc hv] at h
          exact ih h
      | some v =>
          cases hstmt : TM0Route.partrecStartedTM0StatementAt? tc k with
          | none =>
              rw [labelAtByStatementFromWithPositionCode?_succ_of_stmt_none tc hv hstmt] at h
              simp at h
          | some stmt =>
              rw [labelAtByStatementFromWithPositionCode?_succ_of_stmt_some tc hv hstmt] at h
              cases h
              exact labelPositionCode_support_get?_of_statementAt? tc hstmt hv

theorem labelAtByStatementFromWithPositionCode?_start_of_support_succ_stateCode
    (tc : Turing.ToPartrec.Code) {n : Nat} {target : SourceLabel tc}
    (hsupport :
      (TM0Route.partrecStartedTM0LabelSupportList tc)[n + 1]? = some target)
    (hstate : TM0FiniteCompiler.stateCode tc target = n + 1) :
    ∃ q : SourceLabel tc × Nat,
      labelAtByStatementFromWithPositionCode? tc
          (TM0Route.partrecStartedTM0StatementCount tc) 0 n = some q ∧
        q.1 = target ∧ q.2 = TM0FiniteCompiler.stateCode tc target := by
  have hlabelList :
      (TM0Route.partrecStartedTM0LabelList tc)[n]? = some target := by
    unfold TM0Route.partrecStartedTM0LabelSupportList at hsupport
    simpa using hsupport
  have hlabel :
      TM0Route.partrecStartedTM0LabelAtByStatementFrom? tc
          (TM0Route.partrecStartedTM0StatementCount tc) 0 n = some target := by
    rw [TM0Route.partrecStartedTM0LabelAtByStatementFrom?_zero_eq,
      TM0Route.partrecStartedTM0LabelAtByStatement?_eq_labelAt,
      TM0Route.partrecStartedTM0LabelAt?_eq_getElem?]
    exact hlabelList
  cases hdecode : labelAtByStatementFromWithPositionCode? tc
      (TM0Route.partrecStartedTM0StatementCount tc) 0 n with
  | none =>
      have hfst := labelAtByStatementFromWithPositionCode?_fst_eq tc
        (TM0Route.partrecStartedTM0StatementCount tc) 0 n
      rw [hdecode] at hfst
      simp [hlabel] at hfst
  | some q =>
      have hfst := labelAtByStatementFromWithPositionCode?_fst_eq tc
        (TM0Route.partrecStartedTM0StatementCount tc) 0 n
      rw [hdecode] at hfst
      rw [hlabel] at hfst
      have hqtarget : q.1 = target := Option.some.inj hfst
      have hqcode : q.2 = TM0FiniteCompiler.stateCode tc target := by
        rcases labelAtByStatementFromWithPositionCode?_start_code_eq_zero_or_succ
            tc hdecode with hzero | hsucc
        · have hget := labelAtByStatementFromWithPositionCode?_support_get? tc hdecode
          rw [hzero] at hget
          rw [TM0Route.partrecStartedTM0LabelSupportList_get_zero] at hget
          have hqdefault : q.1 =
              (default : Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc)) := by
            exact (Option.some.inj hget).symm
          have htargetDefault :
              target =
                (default : Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc)) := by
            rw [← hqtarget]
            exact hqdefault
          have hstate0 := TM0FiniteCompiler.stateCode_default tc
          rw [htargetDefault] at hstate
          rw [hstate0] at hstate
          unfold TM0Route.partrecStartedTM0Start at hstate
          omega
        · rw [hsucc, hstate]
      exact ⟨q, rfl, hqtarget, hqcode⟩

theorem exists_labelAtByStatementFromWithPositionCode?_sourceDefault
    (tc : Turing.ToPartrec.Code) :
    ∃ n, n < TM0Route.partrecStartedTM0LabelCount tc ∧
      labelAtByStatementFromWithPositionCode? tc
          (TM0Route.partrecStartedTM0StatementCount tc) 0 n =
        some (sourceDefaultLabel tc, 0) := by
  rcases exists_partrecStartedTM0LabelList_get?_default tc with
    ⟨n, hnlt, hlabelList⟩
  have hlabel :
      TM0Route.partrecStartedTM0LabelAtByStatementFrom? tc
          (TM0Route.partrecStartedTM0StatementCount tc) 0 n =
        some (default : SourceLabel tc) := by
    rw [TM0Route.partrecStartedTM0LabelAtByStatementFrom?_zero_eq,
      TM0Route.partrecStartedTM0LabelAtByStatement?_eq_labelAt,
      TM0Route.partrecStartedTM0LabelAt?_eq_getElem?]
    exact hlabelList
  cases hdecode : labelAtByStatementFromWithPositionCode? tc
      (TM0Route.partrecStartedTM0StatementCount tc) 0 n with
  | none =>
      have hfst := labelAtByStatementFromWithPositionCode?_fst_eq tc
        (TM0Route.partrecStartedTM0StatementCount tc) 0 n
      rw [hdecode] at hfst
      simp [hlabel] at hfst
  | some q =>
      have hfst := labelAtByStatementFromWithPositionCode?_fst_eq tc
        (TM0Route.partrecStartedTM0StatementCount tc) 0 n
      rw [hdecode] at hfst
      rw [hlabel] at hfst
      have hqdefault : q.1 = (default : SourceLabel tc) :=
        Option.some.inj hfst
      have hqsource : q.1 = sourceDefaultLabel tc := by
        simpa [sourceDefaultLabel_eq_default tc] using hqdefault
      have hqcode :
          q.2 = 0 :=
        labelAtByStatementFromWithPositionCode?_code_eq_zero_of_sourceDefault
          tc hdecode hqsource
      have hqeq : q = (sourceDefaultLabel tc, 0) := by
        exact Prod.ext hqsource hqcode
      exact ⟨n, hnlt, hdecode.trans (congrArg some hqeq)⟩

/-- First generated label-list index whose label is the forced source default. -/
def sourceDefaultLabelIndex (tc : Turing.ToPartrec.Code) : Nat :=
  (TM0Route.partrecStartedTM0LabelList tc).idxOf (default : SourceLabel tc)

theorem sourceDefaultLabelIndex_lt_labelCount (tc : Turing.ToPartrec.Code) :
    sourceDefaultLabelIndex tc < TM0Route.partrecStartedTM0LabelCount tc := by
  unfold sourceDefaultLabelIndex
  rw [← TM0Route.partrecStartedTM0LabelList_length tc]
  exact List.idxOf_lt_length_iff.2 (default_mem_partrecStartedTM0LabelList tc)

theorem exists_support_succ_of_labelList_ne_sourceDefault
    {tc : Turing.ToPartrec.Code} {q : SourceLabel tc}
    (hq : q ∈ TM0Route.partrecStartedTM0LabelList tc)
    (hneq : q ≠ sourceDefaultLabel tc) :
    ∃ n, n < TM0Route.partrecStartedTM0LabelCount tc ∧
      (TM0Route.partrecStartedTM0LabelSupportList tc)[n + 1]? = some q ∧
        TM0FiniteCompiler.stateCode tc q = n + 1 := by
  have hqset : q ∈ TM0Route.partrecStartedTM0Labels tc :=
    (TM0Route.mem_partrecStartedTM0LabelList tc q).1 hq
  have hqSupport : q ∈ TM0Route.partrecStartedTM0LabelSupportList tc :=
    TM0Route.mem_partrecStartedTM0LabelSupportList_of_mem_labels hqset
  have hget :
      (TM0Route.partrecStartedTM0LabelSupportList tc)[
          TM0FiniteCompiler.stateCode tc q]? = some q := by
    unfold TM0FiniteCompiler.stateCode
    exact List.getElem?_idxOf hqSupport
  have hneqDefault : q ≠ (default : SourceLabel tc) := by
    intro hqDefault
    exact hneq (by simpa [sourceDefaultLabel_eq_default tc] using hqDefault)
  have hcodeNeZero : TM0FiniteCompiler.stateCode tc q ≠ 0 := by
    have hneStart := TM0FiniteCompiler.stateCode_ne_start_of_mem_labels_ne_default
      hqset hneqDefault
    simpa [TM0Route.partrecStartedTM0Start] using hneStart
  let n := TM0FiniteCompiler.stateCode tc q - 1
  have hstate : TM0FiniteCompiler.stateCode tc q = n + 1 := by
    unfold n
    omega
  have hcodeLt :
      TM0FiniteCompiler.stateCode tc q < TM0Route.partrecStartedTM0StateCount tc := by
    have hmem := TM0FiniteCompiler.stateCode_mem_states tc q hqset
    simpa [TM0Route.partrecStartedTM0States] using hmem
  have hn : n < TM0Route.partrecStartedTM0LabelCount tc := by
    rw [TM0Route.partrecStartedTM0StateCount,
      TM0Route.partrecStartedTM0LabelSupportCount] at hcodeLt
    omega
  refine ⟨n, hn, ?_, hstate⟩
  simpa [hstate] using hget

theorem partrecStartedTM0LabelList_get?_sourceDefaultLabelIndex
    (tc : Turing.ToPartrec.Code) :
    (TM0Route.partrecStartedTM0LabelList tc)[sourceDefaultLabelIndex tc]? =
      some (default : SourceLabel tc) := by
  unfold sourceDefaultLabelIndex
  exact List.getElem?_idxOf (default_mem_partrecStartedTM0LabelList tc)

theorem labelAtByStatementFromWithPositionCode?_sourceDefaultLabelIndex
    (tc : Turing.ToPartrec.Code) :
    labelAtByStatementFromWithPositionCode? tc
        (TM0Route.partrecStartedTM0StatementCount tc) 0
          (sourceDefaultLabelIndex tc) =
      some (sourceDefaultLabel tc, 0) := by
  have hlabelList := partrecStartedTM0LabelList_get?_sourceDefaultLabelIndex tc
  have hlabel :
      TM0Route.partrecStartedTM0LabelAtByStatementFrom? tc
          (TM0Route.partrecStartedTM0StatementCount tc) 0
            (sourceDefaultLabelIndex tc) =
        some (default : SourceLabel tc) := by
    rw [TM0Route.partrecStartedTM0LabelAtByStatementFrom?_zero_eq,
      TM0Route.partrecStartedTM0LabelAtByStatement?_eq_labelAt,
      TM0Route.partrecStartedTM0LabelAt?_eq_getElem?]
    exact hlabelList
  cases hdecode : labelAtByStatementFromWithPositionCode? tc
      (TM0Route.partrecStartedTM0StatementCount tc) 0
        (sourceDefaultLabelIndex tc) with
  | none =>
      have hfst := labelAtByStatementFromWithPositionCode?_fst_eq tc
        (TM0Route.partrecStartedTM0StatementCount tc) 0
          (sourceDefaultLabelIndex tc)
      rw [hdecode] at hfst
      simp [hlabel] at hfst
  | some q =>
      have hfst := labelAtByStatementFromWithPositionCode?_fst_eq tc
        (TM0Route.partrecStartedTM0StatementCount tc) 0
          (sourceDefaultLabelIndex tc)
      rw [hdecode] at hfst
      rw [hlabel] at hfst
      have hqdefault : q.1 = (default : SourceLabel tc) :=
        Option.some.inj hfst
      have hqsource : q.1 = sourceDefaultLabel tc := by
        simpa [sourceDefaultLabel_eq_default tc] using hqdefault
      have hqcode :
          q.2 = 0 :=
        labelAtByStatementFromWithPositionCode?_code_eq_zero_of_sourceDefault
          tc hdecode hqsource
      have hqeq : q = (sourceDefaultLabel tc, 0) := by
        exact Prod.ext hqsource hqcode
      exact congrArg some hqeq

theorem labelAtByStatementFromWithPositionCode?_prefix_sourceDefaultLabelIndex_code_ne_zero
    (tc : Turing.ToPartrec.Code) {i : Nat} {q : SourceLabel tc × Nat}
    (hi : i < sourceDefaultLabelIndex tc)
    (hdecode : labelAtByStatementFromWithPositionCode? tc
        (TM0Route.partrecStartedTM0StatementCount tc) 0 i = some q) :
    q.2 ≠ 0 := by
  intro hzero
  have hqget := labelAtByStatementFromWithPositionCode?_support_get? tc hdecode
  rw [hzero] at hqget
  rw [TM0Route.partrecStartedTM0LabelSupportList_get_zero] at hqget
  have hqdefault : q.1 = (default : SourceLabel tc) :=
    (Option.some.inj hqget).symm
  have hlabelAt :
      TM0Route.partrecStartedTM0LabelAtByStatementFrom? tc
          (TM0Route.partrecStartedTM0StatementCount tc) 0 i =
        some q.1 := by
    have hfst := labelAtByStatementFromWithPositionCode?_fst_eq tc
      (TM0Route.partrecStartedTM0StatementCount tc) 0 i
    rw [hdecode] at hfst
    exact hfst.symm
  have hlabelList :
      (TM0Route.partrecStartedTM0LabelList tc)[i]? =
        some (default : SourceLabel tc) := by
    rw [TM0Route.partrecStartedTM0LabelAtByStatementFrom?_zero_eq,
      TM0Route.partrecStartedTM0LabelAtByStatement?_eq_labelAt,
      TM0Route.partrecStartedTM0LabelAt?_eq_getElem?] at hlabelAt
    simpa [hqdefault] using hlabelAt
  have hmemTake :
      (default : SourceLabel tc) ∈
        (TM0Route.partrecStartedTM0LabelList tc).take (i + 1) := by
    rw [List.mem_iff_getElem?]
    exact ⟨i, by simpa [List.getElem?_take, Nat.lt_succ_self] using hlabelList⟩
  have hidxLt :
      sourceDefaultLabelIndex tc < i + 1 := by
    unfold sourceDefaultLabelIndex
    exact (List.mem_take_iff_idxOf_lt (default_mem_partrecStartedTM0LabelList tc)).1 hmemTake
  omega

theorem labelAtByStatementFromWithPositionCode?_label_eq_of_code_eq_stateCode
    (tc : Turing.ToPartrec.Code) {fuel k i : Nat} {q : SourceLabel tc × Nat}
    {target : SourceLabel tc}
    (h : labelAtByStatementFromWithPositionCode? tc fuel k i = some q)
    (htarget : target ∈ TM0Route.partrecStartedTM0LabelSupportList tc)
    (hcode : q.2 = TM0FiniteCompiler.stateCode tc target) :
    q.1 = target := by
  have hqget := labelAtByStatementFromWithPositionCode?_support_get? tc h
  have htargetget :
      (TM0Route.partrecStartedTM0LabelSupportList tc)[
          TM0FiniteCompiler.stateCode tc target]? = some target := by
    unfold TM0FiniteCompiler.stateCode
    exact List.getElem?_idxOf htarget
  rw [hcode] at hqget
  rw [htargetget] at hqget
  exact (Option.some.inj hqget).symm

theorem labelAtByStatementFromWithPositionCode?_minimal_of_statementList_nodup
    (tc : Turing.ToPartrec.Code)
    (hnodup : (TM0Route.partrecStartedTM0StatementList tc).Nodup)
    {fuel k i : Nat} {q : SourceLabel tc × Nat}
    (h : labelAtByStatementFromWithPositionCode? tc fuel k i = some q) :
    ∀ m, m < q.2 →
      (TM0Route.partrecStartedTM0LabelSupportList tc)[m]? ≠ some q.1 := by
  induction fuel generalizing k i with
  | zero =>
      simp [labelAtByStatementFromWithPositionCode?_zero] at h
  | succ fuel ih =>
      cases hv : TM0Route.partrecVarList[i]? with
      | none =>
          rw [labelAtByStatementFromWithPositionCode?_succ_of_var_none tc hv] at h
          exact ih h
      | some v =>
          cases hstmt : TM0Route.partrecStartedTM0StatementAt? tc k with
          | none =>
              rw [labelAtByStatementFromWithPositionCode?_succ_of_stmt_none tc hv hstmt] at h
              simp at h
          | some stmt =>
              rw [labelAtByStatementFromWithPositionCode?_succ_of_stmt_some tc hv hstmt] at h
              cases h
              exact labelPositionCode_minimal_of_statementList_nodup
                tc hnodup hstmt hv

theorem labelAtByStatementFromWithPositionCode?_code_eq_stateCode_of_minimal
    (tc : Turing.ToPartrec.Code) {fuel k i : Nat} {q : SourceLabel tc × Nat}
    (h : labelAtByStatementFromWithPositionCode? tc fuel k i = some q)
    (hmin : ∀ m, m < q.2 →
      (TM0Route.partrecStartedTM0LabelSupportList tc)[m]? ≠ some q.1) :
    q.2 = TM0FiniteCompiler.stateCode tc q.1 := by
  symm
  exact stateCode_eq_of_support_get?_minimal
    (labelAtByStatementFromWithPositionCode?_support_get? tc h) hmin

theorem labelAtByStatementFromWithPositionCode?_eq_stateCode_of_minimal
    (tc : Turing.ToPartrec.Code) {fuel k i : Nat}
    (hmin : ∀ q : SourceLabel tc × Nat,
      labelAtByStatementFromWithPositionCode? tc fuel k i = some q →
        ∀ m, m < q.2 →
          (TM0Route.partrecStartedTM0LabelSupportList tc)[m]? ≠ some q.1) :
    labelAtByStatementFromWithPositionCode? tc fuel k i =
      labelAtByStatementFromWithStateCode? tc fuel k i := by
  unfold labelAtByStatementFromWithStateCode?
  cases hq : labelAtByStatementFromWithPositionCode? tc fuel k i with
  | none =>
      have hnone :
          TM0Route.partrecStartedTM0LabelAtByStatementFrom? tc fuel k i = none := by
        have hmap := congrArg (Option.map Prod.fst) hq
        simpa [labelAtByStatementFromWithPositionCode?_fst_eq tc fuel k i] using hmap
      simp [hnone]
  | some q =>
      have hlabel :
          TM0Route.partrecStartedTM0LabelAtByStatementFrom? tc fuel k i = some q.1 := by
        have hmap := congrArg (Option.map Prod.fst) hq
        simpa [labelAtByStatementFromWithPositionCode?_fst_eq tc fuel k i] using hmap
      have hcode : q.2 = TM0FiniteCompiler.stateCode tc q.1 :=
        labelAtByStatementFromWithPositionCode?_code_eq_stateCode_of_minimal
          tc hq (hmin q hq)
      rcases q with ⟨qLabel, qCode⟩
      change qCode = TM0FiniteCompiler.stateCode tc qLabel at hcode
      subst qCode
      simp [hlabel]

theorem labelAtByStatementFromWithStateCode?_primrec_fixed
    (tc : Turing.ToPartrec.Code)
    [Primcodable (Turing.TM1.Stmt
      (Turing.TM2to1.Γ' PartrecStack PartrecStackSymbol)
      (Turing.TM2to1.Λ' PartrecStack PartrecStackSymbol (StartedLabel tc) PartrecVar)
      PartrecVar)] :
    Primrec (fun p : Nat × Nat × Nat =>
      labelAtByStatementFromWithStateCode? tc p.1 p.2.1 p.2.2) := by
  have hlookup := TM0Route.partrecStartedTM0LabelAtByStatementFrom?_primrec_fixed tc
  have hstate : Primrec (fun q : SourceLabel tc => TM0FiniteCompiler.stateCode tc q) :=
    TM0FiniteCompiler.stateCode_primrec_fixed tc
  have hsome : Primrec₂ (fun _p : Nat × Nat × Nat => fun q : SourceLabel tc =>
      (q, TM0FiniteCompiler.stateCode tc q)) := by
    apply Primrec₂.mk
    exact Primrec.pair Primrec.snd (hstate.comp Primrec.snd)
  exact (Primrec.option_map hlookup hsome).of_eq fun p => by
    unfold labelAtByStatementFromWithStateCode?
    cases TM0Route.partrecStartedTM0LabelAtByStatementFrom? tc p.1 p.2.1 p.2.2 <;> rfl

/--
Offset label lookup paired with the numeric current-state code computed by the
executable support-position search.
-/
def labelAtByStatementFromWithSearchCode?
    (tc : Turing.ToPartrec.Code) (fuel k i : Nat) :
    Option (SourceLabel tc × Nat) :=
  (TM0Route.partrecStartedTM0LabelAtByStatementFrom? tc fuel k i).map
    fun q => (q, TM0FiniteCompiler.stateCodeBySupportSearch tc
      (TM0Route.partrecStartedTM0StatementCount tc) q)

theorem labelAtByStatementFromWithSearchCode?_primrec_fixed
    (tc : Turing.ToPartrec.Code)
    [Primcodable (Turing.TM1.Stmt
      (Turing.TM2to1.Γ' PartrecStack PartrecStackSymbol)
      (Turing.TM2to1.Λ' PartrecStack PartrecStackSymbol (StartedLabel tc) PartrecVar)
      PartrecVar)] :
    Primrec (fun p : Nat × Nat × Nat =>
      labelAtByStatementFromWithSearchCode? tc p.1 p.2.1 p.2.2) := by
  have hlookup := TM0Route.partrecStartedTM0LabelAtByStatementFrom?_primrec_fixed tc
  have hsearch : Primrec (fun q : SourceLabel tc =>
      TM0FiniteCompiler.stateCodeBySupportSearch tc
        (TM0Route.partrecStartedTM0StatementCount tc) q) := by
    exact (TM0FiniteCompiler.stateCodeBySupportSearch_primrec_fixed tc).comp
      (Primrec.pair (Primrec.const (TM0Route.partrecStartedTM0StatementCount tc))
        Primrec.id)
  have hsome : Primrec₂ (fun _p : Nat × Nat × Nat => fun q : SourceLabel tc =>
      (q, TM0FiniteCompiler.stateCodeBySupportSearch tc
        (TM0Route.partrecStartedTM0StatementCount tc) q)) := by
    apply Primrec₂.mk
    exact Primrec.pair Primrec.snd (hsearch.comp Primrec.snd)
  exact (Primrec.option_map hlookup hsome).of_eq fun p => by
    unfold labelAtByStatementFromWithSearchCode?
    cases TM0Route.partrecStartedTM0LabelAtByStatementFrom? tc p.1 p.2.1 p.2.2 <;> rfl

theorem labelAtByStatementFromWithSearchCode?_eq_stateCode
    (tc : Turing.ToPartrec.Code) (fuel k i : Nat) :
    labelAtByStatementFromWithSearchCode? tc fuel k i =
      labelAtByStatementFromWithStateCode? tc fuel k i := by
  unfold labelAtByStatementFromWithSearchCode? labelAtByStatementFromWithStateCode?
  cases h : TM0Route.partrecStartedTM0LabelAtByStatementFrom? tc fuel k i with
  | none =>
      rfl
  | some q =>
      simp only [Option.map_some]
      rw [TM0FiniteCompiler.stateCodeBySupportSearch_eq_stateCode tc q
        (TM0Route.mem_partrecStartedTM0LabelSupportList_of_labelAtByStatementFrom?_eq_some h)]

/--
Offset label-index decoder factored through the numeric folded state code.

This has the same behavior as `simStepDataForLabelIndexFrom`, but its row
generator takes the state code as a separate natural number. This is the shape
needed by the source-level computability proof, where dependent labels should
only be used to decode statements and variables, not to hide the numeric state
fed to the finite program.
-/
def simStepDataForLabelIndexFromWithCode
    (tc : Turing.ToPartrec.Code) (fuel k i : Nat) :
    List SimStepData :=
  (labelAtByStatementFromWithStateCode? tc fuel k i).elim []
    (fun q => simStepDataForStmtLabelWithCode tc q.2 q.1.1 q.1.2)

def simStepDataForLabelIndexFromWithSearchCode
    (tc : Turing.ToPartrec.Code) (fuel k i : Nat) :
    List SimStepData :=
  (labelAtByStatementFromWithSearchCode? tc fuel k i).elim []
    (fun q => simStepDataForStmtLabelWithCode tc q.2 q.1.1 q.1.2)

/--
Offset label-index decoder using the explicit rectangular statement/variable
position as the numeric current-state code.

This is not used by the semantic route yet: it records the cleaner numeric
decoder target where the state code is computed directly from the decoded
statement offset and variable index rather than by searching the finite support
list.
-/
def simStepDataForLabelIndexFromWithPositionCode
    (tc : Turing.ToPartrec.Code) (fuel k i : Nat) :
    List SimStepData :=
  (labelAtByStatementFromWithPositionCode? tc fuel k i).elim []
    (fun q => simStepDataForStmtLabelWithCode tc q.2 q.1.1 q.1.2)

theorem mem_simStepDataForLabelIndexFromWithPositionCode_current_support_get?
    {tc : Turing.ToPartrec.Code} {fuel k i : Nat} {p : SimStepData}
    (h : p ∈ simStepDataForLabelIndexFromWithPositionCode tc fuel k i) :
    ∃ q : SourceLabel tc × Nat,
      labelAtByStatementFromWithPositionCode? tc fuel k i = some q ∧
        p.2.2.1 = q.2 ∧
        (TM0Route.partrecStartedTM0LabelSupportList tc)[p.2.2.1]? = some q.1 := by
  unfold simStepDataForLabelIndexFromWithPositionCode at h
  cases hq : labelAtByStatementFromWithPositionCode? tc fuel k i with
  | none =>
      rw [hq] at h
      cases h
  | some q =>
      have hmem : p ∈ simStepDataForStmtLabelWithCode tc q.2 q.1.1 q.1.2 := by
        simpa [hq] using h
      have hcode : p.2.2.1 = q.2 :=
        mem_simStepDataForStmtLabelWithCode_currentCode hmem
      refine ⟨q, rfl, hcode, ?_⟩
      rw [hcode]
      exact labelAtByStatementFromWithPositionCode?_support_get? tc hq

theorem mem_simStepDataForLabelIndexFromWithPositionCode_currentCode_ne
    {tc : Turing.ToPartrec.Code} {fuel k i : Nat} {target : SourceLabel tc}
    {p : SimStepData}
    (hcode : ∀ q : SourceLabel tc × Nat,
      labelAtByStatementFromWithPositionCode? tc fuel k i = some q →
        q.2 ≠ TM0FiniteCompiler.stateCode tc target)
    (h : p ∈ simStepDataForLabelIndexFromWithPositionCode tc fuel k i) :
    p.2.2.1 ≠ TM0FiniteCompiler.stateCode tc target := by
  rcases mem_simStepDataForLabelIndexFromWithPositionCode_current_support_get?
      (tc := tc) (fuel := fuel) (k := k) (i := i) h with
    ⟨q, hq, hpcode, _hget⟩
  rw [hpcode]
  exact hcode q hq

theorem simRowsOfStepDataForLabelIndexFromWithPositionCode_find?_eq_none_of_currentCode_ne
    {tc : Turing.ToPartrec.Code} {fuel k i : Nat}
    {side : FoldSide} {marked : Bool} {target : SourceLabel tc}
    {left right : SourceSymbol}
    (hcode : ∀ q : SourceLabel tc × Nat,
      labelAtByStatementFromWithPositionCode? tc fuel k i = some q →
        q.2 ≠ TM0FiniteCompiler.stateCode tc target) :
    (simRowsOfStepData
        (simStepDataForLabelIndexFromWithPositionCode tc fuel k i)).find?
        (fun e =>
          e.matchesInput (foldedSimStateCode tc side target)
            (foldedSymbolCode marked left right)) =
      none := by
  exact simRowsOfStepData_find?_eq_none_of_forall_currentCode_ne
    (tc := tc)
    (steps := simStepDataForLabelIndexFromWithPositionCode tc fuel k i)
    (side := side) (marked := marked) (q := target)
    (left := left) (right := right)
    (fun p hp =>
      mem_simStepDataForLabelIndexFromWithPositionCode_currentCode_ne
        (tc := tc) (fuel := fuel) (k := k) (i := i)
        (target := target) hcode hp)

theorem simStepDataForLabelIndexFromWithPositionCode_eq_target_of_currentCode_eq_stateCode
    {tc : Turing.ToPartrec.Code} {fuel k i : Nat}
    {q : SourceLabel tc × Nat} {target : SourceLabel tc}
    (h : labelAtByStatementFromWithPositionCode? tc fuel k i = some q)
    (htarget : target ∈ TM0Route.partrecStartedTM0LabelSupportList tc)
    (hcode : q.2 = TM0FiniteCompiler.stateCode tc target) :
    simStepDataForLabelIndexFromWithPositionCode tc fuel k i =
      simStepDataForStmtLabelWithCode tc
        (TM0FiniteCompiler.stateCode tc target) target.1 target.2 := by
  have hlabel :=
    labelAtByStatementFromWithPositionCode?_label_eq_of_code_eq_stateCode
      tc h htarget hcode
  unfold simStepDataForLabelIndexFromWithPositionCode
  rw [h]
  simp [hlabel, hcode]

theorem simRowsOfStepDataForPositionCode_find?_eq_target
    {tc : Turing.ToPartrec.Code} {fuel k i : Nat}
    {q : SourceLabel tc × Nat} {target : SourceLabel tc}
    {side : FoldSide} {marked : Bool} {left right : SourceSymbol}
    (h : labelAtByStatementFromWithPositionCode? tc fuel k i = some q)
    (htarget : target ∈ TM0Route.partrecStartedTM0LabelSupportList tc)
    (hcode : q.2 = TM0FiniteCompiler.stateCode tc target) :
    (simRowsOfStepData
        (simStepDataForLabelIndexFromWithPositionCode tc fuel k i)).find?
        (fun e =>
          e.matchesInput (foldedSimStateCode tc side target)
            (foldedSymbolCode marked left right)) =
      (simRowsOfStepData
        (simStepDataForStmtLabelWithCode tc
          (TM0FiniteCompiler.stateCode tc target) target.1 target.2)).find?
        (fun e =>
          e.matchesInput (foldedSimStateCode tc side target)
            (foldedSymbolCode marked left right)) := by
  rw [simStepDataForLabelIndexFromWithPositionCode_eq_target_of_currentCode_eq_stateCode
    h htarget hcode]

theorem simStepDataForLabelIndexFromWithSearchCode_eq_withCode
    (tc : Turing.ToPartrec.Code) (fuel k i : Nat) :
    simStepDataForLabelIndexFromWithSearchCode tc fuel k i =
      simStepDataForLabelIndexFromWithCode tc fuel k i := by
  unfold simStepDataForLabelIndexFromWithSearchCode simStepDataForLabelIndexFromWithCode
  rw [labelAtByStatementFromWithSearchCode?_eq_stateCode]

theorem simStepDataForLabelIndexFrom_eq_withCode
    (tc : Turing.ToPartrec.Code) (fuel k i : Nat) :
    simStepDataForLabelIndexFrom tc fuel k i =
      simStepDataForLabelIndexFromWithCode tc fuel k i := by
  unfold simStepDataForLabelIndexFrom simStepDataForLabelIndexFromWithCode
    labelAtByStatementFromWithStateCode?
  cases h : TM0Route.partrecStartedTM0LabelAtByStatementFrom? tc fuel k i with
  | none =>
      simp only [Option.map_none, Option.elim_none]
  | some q =>
      simp only [Option.elim_some, Option.map_some]
      rw [← simStepDataForStmtLabel_eq_of_label tc q,
        simStepDataForStmtLabel_eq_withCode tc q.1 q.2]
      rfl

theorem simStepDataForLabelIndexFromWithPositionCode_eq_withCode_of_minimal
    (tc : Turing.ToPartrec.Code) {fuel k i : Nat}
    (hmin : ∀ q : SourceLabel tc × Nat,
      labelAtByStatementFromWithPositionCode? tc fuel k i = some q →
        ∀ m, m < q.2 →
          (TM0Route.partrecStartedTM0LabelSupportList tc)[m]? ≠ some q.1) :
    simStepDataForLabelIndexFromWithPositionCode tc fuel k i =
      simStepDataForLabelIndexFromWithCode tc fuel k i := by
  unfold simStepDataForLabelIndexFromWithPositionCode simStepDataForLabelIndexFromWithCode
  rw [labelAtByStatementFromWithPositionCode?_eq_stateCode_of_minimal tc hmin]

/--
Canonical offset start for `simStepDataForLabelIndexFrom`: scan from statement
offset `0` with exactly the computed statement-support count as fuel.
-/
def simStepDataForLabelIndexStart (tc : Turing.ToPartrec.Code) (i : Nat) :
    List SimStepData :=
  simStepDataForLabelIndexFrom tc
    (TM0Route.partrecStartedTM0StatementCount tc) 0 i

/-- Canonical offset start for the numeric-state offset decoder. -/
def simStepDataForLabelIndexStartWithCode (tc : Turing.ToPartrec.Code) (i : Nat) :
    List SimStepData :=
  simStepDataForLabelIndexFromWithCode tc
    (TM0Route.partrecStartedTM0StatementCount tc) 0 i

/-- Canonical offset start for the bounded-search numeric-state decoder. -/
def simStepDataForLabelIndexStartWithSearchCode
    (tc : Turing.ToPartrec.Code) (i : Nat) : List SimStepData :=
  simStepDataForLabelIndexFromWithSearchCode tc
    (TM0Route.partrecStartedTM0StatementCount tc) 0 i

/-- Canonical offset start for the position-coded offset decoder. -/
def simStepDataForLabelIndexStartWithPositionCode
    (tc : Turing.ToPartrec.Code) (i : Nat) : List SimStepData :=
  simStepDataForLabelIndexFromWithPositionCode tc
    (TM0Route.partrecStartedTM0StatementCount tc) 0 i

theorem simRowsOfStepDataForPositionCodeStart_find?_eq_target
    {tc : Turing.ToPartrec.Code} {i : Nat}
    {q : SourceLabel tc × Nat} {target : SourceLabel tc}
    {side : FoldSide} {marked : Bool} {left right : SourceSymbol}
    (h : labelAtByStatementFromWithPositionCode? tc
        (TM0Route.partrecStartedTM0StatementCount tc) 0 i = some q)
    (htarget : target ∈ TM0Route.partrecStartedTM0LabelSupportList tc)
    (hcode : q.2 = TM0FiniteCompiler.stateCode tc target) :
    (simRowsOfStepData
        (simStepDataForLabelIndexStartWithPositionCode tc i)).find?
        (fun e =>
          e.matchesInput (foldedSimStateCode tc side target)
            (foldedSymbolCode marked left right)) =
      (simRowsOfStepData
        (simStepDataForStmtLabelWithCode tc
          (TM0FiniteCompiler.stateCode tc target) target.1 target.2)).find?
        (fun e =>
          e.matchesInput (foldedSimStateCode tc side target)
            (foldedSymbolCode marked left right)) := by
  unfold simStepDataForLabelIndexStartWithPositionCode
  exact simRowsOfStepDataForPositionCode_find?_eq_target h htarget hcode

theorem simRowsOfStepDataForPositionCodeIndexRange_find?_eq_none
    {tc : Turing.ToPartrec.Code} {n : Nat} {target : SourceLabel tc}
    {side : FoldSide} {marked : Bool} {left right : SourceSymbol}
    (hcode : ∀ i, i < n → ∀ q : SourceLabel tc × Nat,
      labelAtByStatementFromWithPositionCode? tc
          (TM0Route.partrecStartedTM0StatementCount tc) 0 i = some q →
        q.2 ≠ TM0FiniteCompiler.stateCode tc target) :
    (simRowsOfStepData
        ((List.range n).flatMap
          (simStepDataForLabelIndexStartWithPositionCode tc))).find?
        (fun e =>
          e.matchesInput (foldedSimStateCode tc side target)
            (foldedSymbolCode marked left right)) =
      none := by
  exact simRowsOfStepData_find?_eq_none_of_forall_currentCode_ne
    (tc := tc)
    (steps := (List.range n).flatMap
      (simStepDataForLabelIndexStartWithPositionCode tc))
    (side := side) (marked := marked) (q := target)
    (left := left) (right := right)
    (fun p hp => by
      rw [List.mem_flatMap] at hp
      rcases hp with ⟨i, hiRange, hpBlock⟩
      have hi : i < n := by
        simpa [List.mem_range] using hiRange
      unfold simStepDataForLabelIndexStartWithPositionCode at hpBlock
      exact mem_simStepDataForLabelIndexFromWithPositionCode_currentCode_ne
        (tc := tc) (fuel := TM0Route.partrecStartedTM0StatementCount tc)
        (k := 0) (i := i) (target := target) (hcode i hi) hpBlock)

theorem simRowsOfStepDataForPositionCodeIndexIco_find?_eq_none_of_stateCode_succ
    {tc : Turing.ToPartrec.Code} {n count : Nat} {target : SourceLabel tc}
    {side : FoldSide} {marked : Bool} {left right : SourceSymbol}
    (hstate : TM0FiniteCompiler.stateCode tc target = n + 1) :
    (simRowsOfStepData
        ((List.Ico (n + 1) count).flatMap
          (simStepDataForLabelIndexStartWithPositionCode tc))).find?
        (fun e =>
          e.matchesInput (foldedSimStateCode tc side target)
            (foldedSymbolCode marked left right)) =
      none := by
  exact simRowsOfStepData_find?_eq_none_of_forall_currentCode_ne
    (tc := tc)
    (steps := (List.Ico (n + 1) count).flatMap
      (simStepDataForLabelIndexStartWithPositionCode tc))
    (side := side) (marked := marked) (q := target)
    (left := left) (right := right)
    (fun p hp => by
      rw [List.mem_flatMap] at hp
      rcases hp with ⟨i, hiIco, hpBlock⟩
      have hle : n + 1 ≤ i := by
        have hIco : n + 1 ≤ i ∧ i < count := by
          simpa using hiIco
        exact hIco.1
      unfold simStepDataForLabelIndexStartWithPositionCode at hpBlock
      rcases mem_simStepDataForLabelIndexFromWithPositionCode_current_support_get?
          (tc := tc) (fuel := TM0Route.partrecStartedTM0StatementCount tc)
          (k := 0) (i := i) hpBlock with ⟨q, hq, hpcode, _hget⟩
      rw [hpcode, hstate]
      rcases labelAtByStatementFromWithPositionCode?_start_code_eq_zero_or_succ
          tc hq with hzero | hsucc
      · omega
      · omega)

theorem simRowsOfStepDataForPositionCodeIndexRange_append_find?_eq_some
    {tc : Turing.ToPartrec.Code} {n : Nat} {target : SourceLabel tc}
    {side : FoldSide} {marked : Bool} {left right : SourceSymbol}
    {suffix : List SimStepData} {e : PostTransition}
    (hcode : ∀ i, i < n → ∀ q : SourceLabel tc × Nat,
      labelAtByStatementFromWithPositionCode? tc
          (TM0Route.partrecStartedTM0StatementCount tc) 0 i = some q →
        q.2 ≠ TM0FiniteCompiler.stateCode tc target)
    (hblock :
      (simRowsOfStepData (simStepDataForLabelIndexStartWithPositionCode tc n)).find?
          (fun e =>
            e.matchesInput (foldedSimStateCode tc side target)
              (foldedSymbolCode marked left right)) = some e) :
    (simRowsOfStepData
        (((List.range n).flatMap
          (simStepDataForLabelIndexStartWithPositionCode tc)) ++
            simStepDataForLabelIndexStartWithPositionCode tc n ++ suffix)).find?
        (fun e =>
          e.matchesInput (foldedSimStateCode tc side target)
            (foldedSymbolCode marked left right)) =
      some e := by
  have hpref :=
    simRowsOfStepDataForPositionCodeIndexRange_find?_eq_none
      (tc := tc) (n := n) (target := target) (side := side)
      (marked := marked) (left := left) (right := right) hcode
  rw [show simRowsOfStepData
        (((List.range n).flatMap
          (simStepDataForLabelIndexStartWithPositionCode tc)) ++
            simStepDataForLabelIndexStartWithPositionCode tc n ++ suffix) =
      simRowsOfStepData
        ((List.range n).flatMap
          (simStepDataForLabelIndexStartWithPositionCode tc)) ++
      (simRowsOfStepData
        (simStepDataForLabelIndexStartWithPositionCode tc n) ++
          simRowsOfStepData suffix) by
    simp [simRowsOfStepData, List.map_append]]
  rw [program_find?_append_of_eq_none hpref]
  exact program_find?_append_of_eq_some hblock

theorem simStepDataForLabelIndex_eq_labelAt
    (tc : Turing.ToPartrec.Code) (i : Nat) :
    simStepDataForLabelIndex tc i =
      (TM0Route.partrecStartedTM0LabelAt? tc i).elim [] (simStepDataForLabel tc) := by
  unfold simStepDataForLabelIndex
  rw [TM0Route.partrecStartedTM0LabelAt?_eq_getElem?]

theorem simStepDataForLabelIndex_eq_labelAtByStatement
    (tc : Turing.ToPartrec.Code) (i : Nat) :
    simStepDataForLabelIndex tc i =
      (TM0Route.partrecStartedTM0LabelAtByStatement? tc i).elim []
        (simStepDataForLabel tc) := by
  rw [simStepDataForLabelIndex_eq_labelAt,
    TM0Route.partrecStartedTM0LabelAtByStatement?_eq_labelAt]

theorem simStepDataForLabelIndexFrom_zero_eq
    (tc : Turing.ToPartrec.Code) (i : Nat) :
    simStepDataForLabelIndexFrom tc
        (TM0Route.partrecStartedTM0StatementCount tc) 0 i =
      simStepDataForLabelIndex tc i := by
  unfold simStepDataForLabelIndexFrom
  rw [TM0Route.partrecStartedTM0LabelAtByStatementFrom?_zero_eq]
  rw [simStepDataForLabelIndex_eq_labelAtByStatement]

theorem simStepDataForLabelIndexStart_eq_withCode
    (tc : Turing.ToPartrec.Code) (i : Nat) :
    simStepDataForLabelIndexStart tc i =
      simStepDataForLabelIndexStartWithCode tc i := by
  unfold simStepDataForLabelIndexStart simStepDataForLabelIndexStartWithCode
  exact simStepDataForLabelIndexFrom_eq_withCode
    tc (TM0Route.partrecStartedTM0StatementCount tc) 0 i

theorem simStepDataForLabelIndexStartWithSearchCode_eq_withCode
    (tc : Turing.ToPartrec.Code) (i : Nat) :
    simStepDataForLabelIndexStartWithSearchCode tc i =
      simStepDataForLabelIndexStartWithCode tc i := by
  unfold simStepDataForLabelIndexStartWithSearchCode simStepDataForLabelIndexStartWithCode
  exact simStepDataForLabelIndexFromWithSearchCode_eq_withCode
    tc (TM0Route.partrecStartedTM0StatementCount tc) 0 i

theorem simStepDataForLabelIndexFrom_primrec_fixed_of_trAux
    (tc : Turing.ToPartrec.Code)
    (haux : Primrec (fun p : SourceStmt tc × PartrecVar × SourceSymbol =>
      Turing.TM1to0.trAux (TM0Route.partrecStartedTM1Machine tc) p.2.2 p.1 p.2.1)) :
    Primrec (fun p : Nat × Nat × Nat =>
      simStepDataForLabelIndexFrom tc p.1 p.2.1 p.2.2) := by
  have hlookup := TM0Route.partrecStartedTM0LabelAtByStatementFrom?_primrec_fixed tc
  have hlabel := simStepDataForStmtLabel_primrec_fixed_of_trAux tc haux
  have hnone : Primrec (fun _p : Nat × Nat × Nat => ([] : List SimStepData)) :=
    Primrec.const []
  have hsome : Primrec₂ (fun _p : Nat × Nat × Nat => fun q : SourceLabel tc =>
      simStepDataForStmtLabel tc q.1 q.2) := by
    apply Primrec₂.mk
    exact hlabel.comp
      (Primrec.pair (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
  exact (Primrec.option_casesOn hlookup hnone hsome).of_eq fun p => by
    unfold simStepDataForLabelIndexFrom
    cases h : TM0Route.partrecStartedTM0LabelAtByStatementFrom? tc p.1 p.2.1 p.2.2 with
    | none =>
        rfl
    | some q =>
        exact simStepDataForStmtLabel_eq_of_label tc q

theorem simStepDataForLabelIndexFromWithCode_primrec_fixed_of_trAux
    (tc : Turing.ToPartrec.Code)
    (haux : Primrec (fun p : SourceStmt tc × PartrecVar × SourceSymbol =>
      Turing.TM1to0.trAux (TM0Route.partrecStartedTM1Machine tc) p.2.2 p.1 p.2.1)) :
    Primrec (fun p : Nat × Nat × Nat =>
      simStepDataForLabelIndexFromWithCode tc p.1 p.2.1 p.2.2) := by
  have hlookup := labelAtByStatementFromWithStateCode?_primrec_fixed tc
  have hlabel := simStepDataForStmtLabelWithCode_primrec_fixed_of_trAux tc haux
  have hnone : Primrec (fun _p : Nat × Nat × Nat => ([] : List SimStepData)) :=
    Primrec.const []
  have hsome : Primrec₂ (fun _p : Nat × Nat × Nat => fun q : SourceLabel tc × Nat =>
      simStepDataForStmtLabelWithCode tc q.2 q.1.1 q.1.2) := by
    apply Primrec₂.mk
    exact hlabel.comp
      (Primrec.pair
        (Primrec.snd.comp Primrec.snd)
        (Primrec.pair
          (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
          (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))))
  exact (Primrec.option_casesOn hlookup hnone hsome).of_eq fun p => by
    unfold simStepDataForLabelIndexFromWithCode
    cases labelAtByStatementFromWithStateCode? tc p.1 p.2.1 p.2.2 <;> rfl

theorem simStepDataForLabelIndexFromWithSearchCode_primrec_fixed_of_trAux
    (tc : Turing.ToPartrec.Code)
    (haux : Primrec (fun p : SourceStmt tc × PartrecVar × SourceSymbol =>
      Turing.TM1to0.trAux (TM0Route.partrecStartedTM1Machine tc) p.2.2 p.1 p.2.1)) :
    Primrec (fun p : Nat × Nat × Nat =>
      simStepDataForLabelIndexFromWithSearchCode tc p.1 p.2.1 p.2.2) := by
  have hlookup := labelAtByStatementFromWithSearchCode?_primrec_fixed tc
  have hlabel := simStepDataForStmtLabelWithCode_primrec_fixed_of_trAux tc haux
  have hnone : Primrec (fun _p : Nat × Nat × Nat => ([] : List SimStepData)) :=
    Primrec.const []
  have hsome : Primrec₂ (fun _p : Nat × Nat × Nat => fun q : SourceLabel tc × Nat =>
      simStepDataForStmtLabelWithCode tc q.2 q.1.1 q.1.2) := by
    apply Primrec₂.mk
    exact hlabel.comp
      (Primrec.pair
        (Primrec.snd.comp Primrec.snd)
        (Primrec.pair
          (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
          (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))))
  exact (Primrec.option_casesOn hlookup hnone hsome).of_eq fun p => by
    unfold simStepDataForLabelIndexFromWithSearchCode
    cases labelAtByStatementFromWithSearchCode? tc p.1 p.2.1 p.2.2 <;> rfl

theorem simStepDataForLabelIndexFromWithPositionCode_primrec_fixed_of_trAux
    (tc : Turing.ToPartrec.Code)
    (haux : Primrec (fun p : SourceStmt tc × PartrecVar × SourceSymbol =>
      Turing.TM1to0.trAux (TM0Route.partrecStartedTM1Machine tc) p.2.2 p.1 p.2.1)) :
    Primrec (fun p : Nat × Nat × Nat =>
      simStepDataForLabelIndexFromWithPositionCode tc p.1 p.2.1 p.2.2) := by
  have hlookup := labelAtByStatementFromWithPositionCode?_primrec_fixed tc
  have hlabel := simStepDataForStmtLabelWithCode_primrec_fixed_of_trAux tc haux
  have hnone : Primrec (fun _p : Nat × Nat × Nat => ([] : List SimStepData)) :=
    Primrec.const []
  have hsome : Primrec₂ (fun _p : Nat × Nat × Nat => fun q : SourceLabel tc × Nat =>
      simStepDataForStmtLabelWithCode tc q.2 q.1.1 q.1.2) := by
    apply Primrec₂.mk
    exact hlabel.comp
      (Primrec.pair
        (Primrec.snd.comp Primrec.snd)
        (Primrec.pair
          (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
          (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))))
  exact (Primrec.option_casesOn hlookup hnone hsome).of_eq fun p => by
    unfold simStepDataForLabelIndexFromWithPositionCode
    cases labelAtByStatementFromWithPositionCode? tc p.1 p.2.1 p.2.2 <;> rfl

theorem simStepDataForLabelIndexFromWithCode_primrec_fixed_of_machine
    (tc : Turing.ToPartrec.Code)
    (hmachine : Primrec (TM0Route.partrecStartedTM1Machine tc)) :
    Primrec (fun p : Nat × Nat × Nat =>
      simStepDataForLabelIndexFromWithCode tc p.1 p.2.1 p.2.2) :=
  simStepDataForLabelIndexFromWithCode_primrec_fixed_of_trAux tc
    (trAux_primrec_fixed_of_machine tc hmachine)

theorem simStepDataForLabelIndexFromWithCode_primrec_fixed
    (tc : Turing.ToPartrec.Code) :
    Primrec (fun p : Nat × Nat × Nat =>
      simStepDataForLabelIndexFromWithCode tc p.1 p.2.1 p.2.2) :=
  simStepDataForLabelIndexFromWithCode_primrec_fixed_of_machine tc
    (TM0Route.partrecStartedTM1Machine_primrec tc)

theorem simStepDataForLabelIndexFromWithSearchCode_primrec_fixed_of_machine
    (tc : Turing.ToPartrec.Code)
    (hmachine : Primrec (TM0Route.partrecStartedTM1Machine tc)) :
    Primrec (fun p : Nat × Nat × Nat =>
      simStepDataForLabelIndexFromWithSearchCode tc p.1 p.2.1 p.2.2) :=
  simStepDataForLabelIndexFromWithSearchCode_primrec_fixed_of_trAux tc
    (trAux_primrec_fixed_of_machine tc hmachine)

theorem simStepDataForLabelIndexFromWithSearchCode_primrec_fixed
    (tc : Turing.ToPartrec.Code) :
    Primrec (fun p : Nat × Nat × Nat =>
      simStepDataForLabelIndexFromWithSearchCode tc p.1 p.2.1 p.2.2) :=
  simStepDataForLabelIndexFromWithSearchCode_primrec_fixed_of_machine tc
    (TM0Route.partrecStartedTM1Machine_primrec tc)

theorem simStepDataForLabelIndexFromWithPositionCode_primrec_fixed_of_machine
    (tc : Turing.ToPartrec.Code)
    (hmachine : Primrec (TM0Route.partrecStartedTM1Machine tc)) :
    Primrec (fun p : Nat × Nat × Nat =>
      simStepDataForLabelIndexFromWithPositionCode tc p.1 p.2.1 p.2.2) :=
  simStepDataForLabelIndexFromWithPositionCode_primrec_fixed_of_trAux tc
    (trAux_primrec_fixed_of_machine tc hmachine)

theorem simStepDataForLabelIndexFromWithPositionCode_primrec_fixed
    (tc : Turing.ToPartrec.Code) :
    Primrec (fun p : Nat × Nat × Nat =>
      simStepDataForLabelIndexFromWithPositionCode tc p.1 p.2.1 p.2.2) :=
  simStepDataForLabelIndexFromWithPositionCode_primrec_fixed_of_machine tc
    (TM0Route.partrecStartedTM1Machine_primrec tc)

theorem simStepDataForLabelIndexFrom_primrec_fixed_of_machine
    (tc : Turing.ToPartrec.Code)
    (hmachine : Primrec (TM0Route.partrecStartedTM1Machine tc)) :
    Primrec (fun p : Nat × Nat × Nat =>
      simStepDataForLabelIndexFrom tc p.1 p.2.1 p.2.2) :=
  simStepDataForLabelIndexFrom_primrec_fixed_of_trAux tc
    (trAux_primrec_fixed_of_machine tc hmachine)

theorem simStepDataForLabelIndexFrom_primrec_fixed
    (tc : Turing.ToPartrec.Code) :
    Primrec (fun p : Nat × Nat × Nat =>
      simStepDataForLabelIndexFrom tc p.1 p.2.1 p.2.2) :=
  simStepDataForLabelIndexFrom_primrec_fixed_of_machine tc
    (TM0Route.partrecStartedTM1Machine_primrec tc)

theorem simStepDataForLabelIndexStart_eq
    (tc : Turing.ToPartrec.Code) (i : Nat) :
    simStepDataForLabelIndexStart tc i = simStepDataForLabelIndex tc i := by
  unfold simStepDataForLabelIndexStart
  exact simStepDataForLabelIndexFrom_zero_eq tc i

theorem simStepDataForLabelIndexStartWithCode_eq
    (tc : Turing.ToPartrec.Code) (i : Nat) :
    simStepDataForLabelIndexStartWithCode tc i =
      simStepDataForLabelIndex tc i := by
  rw [← simStepDataForLabelIndexStart_eq_withCode]
  exact simStepDataForLabelIndexStart_eq tc i

theorem simStepDataForLabelIndexStart_primrec_fixed_of_trAux
    (tc : Turing.ToPartrec.Code)
    (haux : Primrec (fun p : SourceStmt tc × PartrecVar × SourceSymbol =>
      Turing.TM1to0.trAux (TM0Route.partrecStartedTM1Machine tc) p.2.2 p.1 p.2.1)) :
    Primrec (simStepDataForLabelIndexStart tc) := by
  unfold simStepDataForLabelIndexStart
  exact (simStepDataForLabelIndexFrom_primrec_fixed_of_trAux tc haux).comp
    (Primrec.pair (Primrec.const (TM0Route.partrecStartedTM0StatementCount tc))
      (Primrec.pair (Primrec.const 0) Primrec.id))

theorem simStepDataForLabelIndexStartWithCode_primrec_fixed_of_trAux
    (tc : Turing.ToPartrec.Code)
    (haux : Primrec (fun p : SourceStmt tc × PartrecVar × SourceSymbol =>
      Turing.TM1to0.trAux (TM0Route.partrecStartedTM1Machine tc) p.2.2 p.1 p.2.1)) :
    Primrec (simStepDataForLabelIndexStartWithCode tc) := by
  unfold simStepDataForLabelIndexStartWithCode
  exact (simStepDataForLabelIndexFromWithCode_primrec_fixed_of_trAux tc haux).comp
    (Primrec.pair (Primrec.const (TM0Route.partrecStartedTM0StatementCount tc))
      (Primrec.pair (Primrec.const 0) Primrec.id))

theorem simStepDataForLabelIndexStartWithSearchCode_primrec_fixed_of_trAux
    (tc : Turing.ToPartrec.Code)
    (haux : Primrec (fun p : SourceStmt tc × PartrecVar × SourceSymbol =>
      Turing.TM1to0.trAux (TM0Route.partrecStartedTM1Machine tc) p.2.2 p.1 p.2.1)) :
    Primrec (simStepDataForLabelIndexStartWithSearchCode tc) := by
  unfold simStepDataForLabelIndexStartWithSearchCode
  exact (simStepDataForLabelIndexFromWithSearchCode_primrec_fixed_of_trAux tc haux).comp
    (Primrec.pair (Primrec.const (TM0Route.partrecStartedTM0StatementCount tc))
      (Primrec.pair (Primrec.const 0) Primrec.id))

theorem simStepDataForLabelIndexStartWithPositionCode_primrec_fixed_of_trAux
    (tc : Turing.ToPartrec.Code)
    (haux : Primrec (fun p : SourceStmt tc × PartrecVar × SourceSymbol =>
      Turing.TM1to0.trAux (TM0Route.partrecStartedTM1Machine tc) p.2.2 p.1 p.2.1)) :
    Primrec (simStepDataForLabelIndexStartWithPositionCode tc) := by
  unfold simStepDataForLabelIndexStartWithPositionCode
  exact (simStepDataForLabelIndexFromWithPositionCode_primrec_fixed_of_trAux tc haux).comp
    (Primrec.pair (Primrec.const (TM0Route.partrecStartedTM0StatementCount tc))
      (Primrec.pair (Primrec.const 0) Primrec.id))

theorem simStepDataForLabelIndexStart_primrec_fixed_of_machine
    (tc : Turing.ToPartrec.Code)
    (hmachine : Primrec (TM0Route.partrecStartedTM1Machine tc)) :
    Primrec (simStepDataForLabelIndexStart tc) :=
  simStepDataForLabelIndexStart_primrec_fixed_of_trAux tc
    (trAux_primrec_fixed_of_machine tc hmachine)

theorem simStepDataForLabelIndexStartWithCode_primrec_fixed_of_machine
    (tc : Turing.ToPartrec.Code)
    (hmachine : Primrec (TM0Route.partrecStartedTM1Machine tc)) :
    Primrec (simStepDataForLabelIndexStartWithCode tc) :=
  simStepDataForLabelIndexStartWithCode_primrec_fixed_of_trAux tc
    (trAux_primrec_fixed_of_machine tc hmachine)

theorem simStepDataForLabelIndexStartWithSearchCode_primrec_fixed_of_machine
    (tc : Turing.ToPartrec.Code)
    (hmachine : Primrec (TM0Route.partrecStartedTM1Machine tc)) :
    Primrec (simStepDataForLabelIndexStartWithSearchCode tc) :=
  simStepDataForLabelIndexStartWithSearchCode_primrec_fixed_of_trAux tc
    (trAux_primrec_fixed_of_machine tc hmachine)

theorem simStepDataForLabelIndexStartWithPositionCode_primrec_fixed_of_machine
    (tc : Turing.ToPartrec.Code)
    (hmachine : Primrec (TM0Route.partrecStartedTM1Machine tc)) :
    Primrec (simStepDataForLabelIndexStartWithPositionCode tc) :=
  simStepDataForLabelIndexStartWithPositionCode_primrec_fixed_of_trAux tc
    (trAux_primrec_fixed_of_machine tc hmachine)

theorem simStepDataForLabelIndexStart_primrec_fixed
    (tc : Turing.ToPartrec.Code) :
    Primrec (simStepDataForLabelIndexStart tc) :=
  simStepDataForLabelIndexStart_primrec_fixed_of_machine tc
    (TM0Route.partrecStartedTM1Machine_primrec tc)

theorem simStepDataForLabelIndexStartWithCode_primrec_fixed
    (tc : Turing.ToPartrec.Code) :
    Primrec (simStepDataForLabelIndexStartWithCode tc) :=
  simStepDataForLabelIndexStartWithCode_primrec_fixed_of_machine tc
    (TM0Route.partrecStartedTM1Machine_primrec tc)

theorem simStepDataForLabelIndexStartWithSearchCode_primrec_fixed
    (tc : Turing.ToPartrec.Code) :
    Primrec (simStepDataForLabelIndexStartWithSearchCode tc) :=
  simStepDataForLabelIndexStartWithSearchCode_primrec_fixed_of_machine tc
    (TM0Route.partrecStartedTM1Machine_primrec tc)

theorem simStepDataForLabelIndexStartWithPositionCode_primrec_fixed
    (tc : Turing.ToPartrec.Code) :
    Primrec (simStepDataForLabelIndexStartWithPositionCode tc) :=
  simStepDataForLabelIndexStartWithPositionCode_primrec_fixed_of_machine tc
    (TM0Route.partrecStartedTM1Machine_primrec tc)

theorem simStepDataForLabelIndex_primrec_fixed_of_trAux
    (tc : Turing.ToPartrec.Code)
    (haux : Primrec (fun p : SourceStmt tc × PartrecVar × SourceSymbol =>
      Turing.TM1to0.trAux (TM0Route.partrecStartedTM1Machine tc) p.2.2 p.1 p.2.1)) :
    Primrec (simStepDataForLabelIndex tc) :=
  (simStepDataForLabelIndexStart_primrec_fixed_of_trAux tc haux).of_eq fun i =>
    simStepDataForLabelIndexStart_eq tc i

theorem simStepDataForLabelIndex_primrec_fixed_of_machine
    (tc : Turing.ToPartrec.Code)
    (hmachine : Primrec (TM0Route.partrecStartedTM1Machine tc)) :
    Primrec (simStepDataForLabelIndex tc) :=
  simStepDataForLabelIndex_primrec_fixed_of_trAux tc
    (trAux_primrec_fixed_of_machine tc hmachine)

theorem simStepDataForLabelIndex_primrec_fixed
    (tc : Turing.ToPartrec.Code) :
    Primrec (simStepDataForLabelIndex tc) :=
  simStepDataForLabelIndex_primrec_fixed_of_machine tc
    (TM0Route.partrecStartedTM1Machine_primrec tc)

end TM0FoldedCompiler

end LeanWang
