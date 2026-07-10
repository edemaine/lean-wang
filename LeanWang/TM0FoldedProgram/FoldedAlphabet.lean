/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedProgram.Source

/-!
Folded alphabet, folded states, and input-prelude state data.
-/

namespace LeanWang

namespace TM0FoldedCompiler

open TM0Route

def foldedSymbolCode (marked : Bool) (left right : SourceSymbol) : Nat :=
  Nat.pair (if marked then 1 else 0)
    (Nat.pair
      (TM0Route.partrecStartedTM0SymbolCode left)
      (TM0Route.partrecStartedTM0SymbolCode right))

theorem foldedSymbolCode_primrec :
    Primrec (fun p : Bool × SourceSymbol × SourceSymbol =>
      foldedSymbolCode p.1 p.2.1 p.2.2) := by
  classical
  exact Primrec.dom_finite (fun p : Bool × SourceSymbol × SourceSymbol =>
    foldedSymbolCode p.1 p.2.1 p.2.2)

theorem foldedSymbolCode_eq {marked marked' : Bool} {left right left' right' : SourceSymbol}
    (h :
      foldedSymbolCode marked' left' right' =
        foldedSymbolCode marked left right) :
    marked' = marked ∧ left' = left ∧ right' = right := by
  unfold foldedSymbolCode at h
  have htag := (Nat.pair_eq_pair.mp h).1
  have hpayload := (Nat.pair_eq_pair.mp h).2
  have hleftCode := (Nat.pair_eq_pair.mp hpayload).1
  have hrightCode := (Nat.pair_eq_pair.mp hpayload).2
  have hmarked : marked' = marked := by
    cases marked' <;> cases marked <;> simp at htag ⊢
  exact ⟨hmarked,
    TM0Route.partrecStartedTM0SymbolCode_injective hleftCode,
    TM0Route.partrecStartedTM0SymbolCode_injective hrightCode⟩

def foldedSymbolList : List Nat :=
  [false, true].flatMap fun marked =>
    TM0Route.partrecStartedTM0SymbolList.flatMap fun left =>
      TM0Route.partrecStartedTM0SymbolList.map fun right =>
        foldedSymbolCode marked left right

theorem foldedSymbolCode_mem_symbols
    (marked : Bool) (left right : SourceSymbol) :
    foldedSymbolCode marked left right ∈ foldedSymbolList := by
  unfold foldedSymbolList
  rw [List.mem_flatMap]
  refine ⟨marked, by cases marked <;> simp, ?_⟩
  rw [List.mem_flatMap]
  refine ⟨left, TM0Route.mem_partrecStartedTM0SymbolList left, ?_⟩
  exact List.mem_map_of_mem (TM0Route.mem_partrecStartedTM0SymbolList right)

def foldedBlank : Nat :=
  foldedSymbolCode false default default

/-- Blank folded cells belong to the finite folded alphabet. -/
theorem foldedBlank_mem_symbols : foldedBlank ∈ foldedSymbolList := by
  unfold foldedBlank
  exact foldedSymbolCode_mem_symbols false default default

def foldedOriginSymbol (a : SourceSymbol) : Nat :=
  foldedSymbolCode true default a

/-- Marked origin cells belong to the finite folded alphabet. -/
theorem foldedOriginSymbol_mem_symbols (a : SourceSymbol) :
    foldedOriginSymbol a ∈ foldedSymbolList := by
  unfold foldedOriginSymbol
  exact foldedSymbolCode_mem_symbols true default a

theorem foldedOriginSymbol_primrec : Primrec foldedOriginSymbol := by
  classical
  exact Primrec.dom_finite foldedOriginSymbol

def foldedRead (side : FoldSide) (left right : SourceSymbol) : SourceSymbol :=
  match side with
  | FoldSide.left => left
  | FoldSide.right => right

theorem foldedRead_primrec :
    Primrec (fun p : FoldSide × SourceSymbol × SourceSymbol =>
      foldedRead p.1 p.2.1 p.2.2) := by
  classical
  exact Primrec.dom_finite (fun p : FoldSide × SourceSymbol × SourceSymbol =>
    foldedRead p.1 p.2.1 p.2.2)

def foldedWrite (side : FoldSide) (new left right : SourceSymbol) : Nat :=
  match side with
  | FoldSide.left => foldedSymbolCode false new right
  | FoldSide.right => foldedSymbolCode false left new

theorem foldedWrite_mem_symbols (side : FoldSide) (new left right : SourceSymbol) :
    foldedWrite side new left right ∈ foldedSymbolList := by
  cases side <;> simp [foldedWrite, foldedSymbolCode_mem_symbols]

theorem foldedWrite_primrec :
    Primrec (fun p : FoldSide × SourceSymbol × SourceSymbol × SourceSymbol =>
      foldedWrite p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  classical
  exact Primrec.dom_finite (fun p : FoldSide × SourceSymbol × SourceSymbol × SourceSymbol =>
    foldedWrite p.1 p.2.1 p.2.2.1 p.2.2.2)

def foldedWriteMarked (side : FoldSide) (new left right : SourceSymbol) : Nat :=
  match side with
  | FoldSide.left => foldedSymbolCode true new right
  | FoldSide.right => foldedSymbolCode true left new

theorem foldedWriteMarked_mem_symbols (side : FoldSide) (new left right : SourceSymbol) :
    foldedWriteMarked side new left right ∈ foldedSymbolList := by
  cases side <;> simp [foldedWriteMarked, foldedSymbolCode_mem_symbols]

theorem foldedWriteMarked_primrec :
    Primrec (fun p : FoldSide × SourceSymbol × SourceSymbol × SourceSymbol =>
      foldedWriteMarked p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  classical
  exact Primrec.dom_finite (fun p : FoldSide × SourceSymbol × SourceSymbol × SourceSymbol =>
    foldedWriteMarked p.1 p.2.1 p.2.2.1 p.2.2.2)

def stateTagSim : Nat := 0
def stateTagInit : Nat := 1
def stateTagReturn : Nat := 2

def taggedState (tag payload : Nat) : Nat :=
  Nat.pair tag payload

theorem taggedState_primrec :
    Primrec (fun p : Nat × Nat => taggedState p.1 p.2) := by
  exact Primrec₂.natPair.comp Primrec.fst Primrec.snd

/-- State used while simulating a Mathlib TM0 label on one side of the folded tape. -/
def foldedSimStateCode (tc : Turing.ToPartrec.Code)
    (side : FoldSide) (q : SourceLabel tc) : Nat :=
  taggedState stateTagSim
    (Nat.pair side.code (TM0FiniteCompiler.stateCode tc q))

def foldedSimStateOfCode (side : FoldSide) (qCode : Nat) : Nat :=
  taggedState stateTagSim (Nat.pair side.code qCode)

theorem foldedSimStateOfCode_primrec :
    Primrec (fun p : FoldSide × Nat => foldedSimStateOfCode p.1 p.2) := by
  unfold foldedSimStateOfCode taggedState
  exact Primrec₂.natPair.comp (Primrec.const stateTagSim)
    (Primrec₂.natPair.comp (FoldSide.code_primrec.comp Primrec.fst) Primrec.snd)

theorem foldedSimStateCode_eq_ofCode (tc : Turing.ToPartrec.Code)
    (side : FoldSide) (q : SourceLabel tc) :
    foldedSimStateCode tc side q =
      foldedSimStateOfCode side (TM0FiniteCompiler.stateCode tc q) := by
  rfl

theorem foldedSimStateOfCode_eq_foldedSimStateCode_iff
    {tc : Turing.ToPartrec.Code} {side side' : FoldSide} {qCode : Nat}
    {q : SourceLabel tc} :
    foldedSimStateOfCode side qCode = foldedSimStateCode tc side' q ↔
      side = side' ∧ qCode = TM0FiniteCompiler.stateCode tc q := by
  unfold foldedSimStateOfCode foldedSimStateCode taggedState
  constructor
  · intro h
    have hpayload := (Nat.pair_eq_pair.mp h).2
    have hparts := Nat.pair_eq_pair.mp hpayload
    have hside : side = side' := by
      cases side <;> cases side' <;> simp [FoldSide.code] at hparts ⊢
    exact ⟨hside, hparts.2⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem foldedSimStateCode_side_of_same_label_eq {tc : Turing.ToPartrec.Code}
    {side side' : FoldSide} {q : SourceLabel tc}
    (h : foldedSimStateCode tc side' q = foldedSimStateCode tc side q) :
    side' = side := by
  exact (foldedSimStateOfCode_eq_foldedSimStateCode_iff
    (tc := tc) (side := side') (side' := side)
    (qCode := TM0FiniteCompiler.stateCode tc q) (q := q)).1 h |>.1

theorem foldedSimStateCode_primrec_fixed (tc : Turing.ToPartrec.Code)
    [Primcodable (Turing.TM1.Stmt
      (Turing.TM2to1.Γ' PartrecStack PartrecStackSymbol)
      (Turing.TM2to1.Λ' PartrecStack PartrecStackSymbol (StartedLabel tc) PartrecVar)
      PartrecVar)] :
    Primrec (fun p : FoldSide × SourceLabel tc =>
      foldedSimStateCode tc p.1 p.2) := by
  exact (foldedSimStateOfCode_primrec.comp
    (Primrec.pair Primrec.fst
      (TM0FiniteCompiler.stateCode_primrec_fixed tc |>.comp Primrec.snd))).of_eq
    fun _ => rfl

def foldedSimStartStateCode : Nat :=
  foldedSimStateOfCode FoldSide.right TM0Route.partrecStartedTM0Start

def initWriteOriginState : Nat :=
  taggedState stateTagInit 0

/-- Prelude state that moves from an initialized right-side input cell to the next cell. -/
def initMoveRightState (i : Nat) : Nat :=
  taggedState stateTagInit (2 * i + 1)

theorem initMoveRightState_primrec : Primrec initMoveRightState := by
  unfold initMoveRightState taggedState stateTagInit
  have hpayload : Primrec (fun i : Nat => 2 * i + 1) :=
    Primrec.succ.comp ((Primrec.nat_mul).comp (Primrec.const 2) Primrec.id)
  exact Primrec₂.natPair.comp (Primrec.const 1) hpayload

/-- Prelude state that writes right-side input cell `i + 1`. -/
def initWriteRightState (i : Nat) : Nat :=
  taggedState stateTagInit (2 * i + 2)

theorem initWriteRightState_primrec : Primrec initWriteRightState := by
  unfold initWriteRightState taggedState stateTagInit
  have hpayload : Primrec (fun i : Nat => 2 * i + 2) :=
    Primrec.succ.comp (Primrec.succ.comp ((Primrec.nat_mul).comp (Primrec.const 2) Primrec.id))
  exact Primrec₂.natPair.comp (Primrec.const 1) hpayload

/-- Prelude state with `i` left moves remaining before simulation starts. -/
def initReturnState (i : Nat) : Nat :=
  taggedState stateTagReturn i

theorem initReturnState_primrec : Primrec initReturnState := by
  unfold initReturnState taggedState stateTagReturn
  exact Primrec₂.natPair.comp (Primrec.const 2) Primrec.id

def foldedStartState : Nat :=
  initWriteOriginState

def foldedSimStartState (_tc : Turing.ToPartrec.Code) : Nat :=
  foldedSimStartStateCode

theorem foldedSimStartState_eq (tc : Turing.ToPartrec.Code) : foldedSimStartState tc =
    taggedState stateTagSim (Nat.pair FoldSide.right.code TM0Route.partrecStartedTM0Start) := by
  simp [foldedSimStartState, foldedSimStartStateCode, foldedSimStateOfCode,
    taggedState, TM0Route.partrecStartedTM0Start]

theorem foldedSimStartState_primrec :
    Primrec (fun _tc : Turing.ToPartrec.Code => foldedSimStartState _tc) := by
  refine (Primrec.const
    (taggedState stateTagSim (Nat.pair FoldSide.right.code
      TM0Route.partrecStartedTM0Start))).of_eq ?_
  intro tc
  exact (foldedSimStartState_eq (tc := tc)).symm

def foldedInitStateList : List Nat :=
  [initWriteOriginState, initReturnState 0] ++
    (List.range TM0Route.partrecStartedTM0Input.length).flatMap fun i =>
      [initMoveRightState i, initWriteRightState i, initReturnState i]

def foldedSimStateListOfCodes (qCodes : List Nat) : List Nat :=
  qCodes.flatMap fun qCode =>
    foldSideList.map fun side => foldedSimStateOfCode side qCode

theorem foldedSimStateListOfCodes_primrec : Primrec foldedSimStateListOfCodes := by
  unfold foldedSimStateListOfCodes
  refine Primrec.list_flatMap Primrec.id ?_
  apply Primrec₂.mk
  refine Primrec.list_map (Primrec.const foldSideList) ?_
  apply Primrec₂.mk
  exact foldedSimStateOfCode_primrec.comp
    (Primrec.pair Primrec.snd (Primrec.snd.comp Primrec.fst))

def foldedSimStateList (tc : Turing.ToPartrec.Code) : List Nat :=
  foldedSimStateListOfCodes (TM0Route.partrecStartedTM0States tc)

theorem foldedSimStateList_primrec : Primrec foldedSimStateList := by
  unfold foldedSimStateList
  exact foldedSimStateListOfCodes_primrec.comp
    TM0Route.partrecStartedTM0States_primrec

theorem foldedSimStateList_computable : Computable foldedSimStateList :=
  foldedSimStateList_primrec.to_comp

def foldedStateListOfCodes (qCodes : List Nat) : List Nat :=
  foldedInitStateList ++ foldedSimStateListOfCodes qCodes

theorem foldedStateListOfCodes_primrec : Primrec foldedStateListOfCodes := by
  unfold foldedStateListOfCodes
  exact Primrec.list_append.comp (Primrec.const foldedInitStateList)
    foldedSimStateListOfCodes_primrec

def foldedStateListForCount (stateCount : Nat) : List Nat :=
  foldedStateListOfCodes (List.range stateCount)

theorem foldedStateListForCount_primrec : Primrec foldedStateListForCount := by
  unfold foldedStateListForCount
  exact foldedStateListOfCodes_primrec.comp Primrec.list_range

def foldedStateList (tc : Turing.ToPartrec.Code) : List Nat :=
  foldedStateListOfCodes (TM0Route.partrecStartedTM0States tc)

theorem foldedSimStateCode_mem_states (tc : Turing.ToPartrec.Code)
    (side : FoldSide) {q : SourceLabel tc}
    (hq : q ∈ TM0Route.partrecStartedTM0LabelList tc) :
    foldedSimStateCode tc side q ∈ foldedStateList tc := by
  unfold foldedStateList foldedStateListOfCodes foldedSimStateListOfCodes
  rw [List.mem_append]
  apply Or.inr
  rw [List.mem_flatMap]
  refine ⟨TM0FiniteCompiler.stateCode tc q, ?_, ?_⟩
  · exact TM0FiniteCompiler.stateCode_mem_states tc q
      ((TM0Route.mem_partrecStartedTM0LabelList tc q).1 hq)
  · exact List.mem_map_of_mem (mem_foldSideList side)

theorem foldedSimStartState_mem_states (tc : Turing.ToPartrec.Code) :
    foldedSimStartState tc ∈ foldedStateList tc := by
  unfold foldedSimStartState foldedSimStartStateCode foldedSimStateOfCode
    foldedStateList foldedStateListOfCodes foldedSimStateListOfCodes
  rw [List.mem_append]
  apply Or.inr
  rw [List.mem_flatMap]
  refine ⟨TM0Route.partrecStartedTM0Start,
    TM0Route.partrecStartedTM0Start_mem_states tc, ?_⟩
  exact List.mem_map_of_mem (mem_foldSideList FoldSide.right)

theorem foldedStateList_primrec : Primrec foldedStateList := by
  unfold foldedStateList
  exact foldedStateListOfCodes_primrec.comp
    TM0Route.partrecStartedTM0States_primrec

theorem foldedStateList_computable : Computable foldedStateList :=
  foldedStateList_primrec.to_comp

def inputSymbol (i : Nat) : SourceSymbol :=
  TM0Route.partrecStartedTM0Input.getI i

theorem inputSymbol_primrec : Primrec inputSymbol := by
  unfold inputSymbol
  exact Primrec.list_getI.comp
    (Primrec.const TM0Route.partrecStartedTM0Input) Primrec.id

def nextAfterOrigin : Nat :=
  if TM0Route.partrecStartedTM0Input.length ≤ 1 then
    initReturnState 0
  else
    initMoveRightState 0

theorem partrecStartedTM0Input_length :
    TM0Route.partrecStartedTM0Input.length = 1 := by
  simp [TM0Route.partrecStartedTM0Input, TM0Route.partrecStartedTM0InputFor,
    TM0Route.partrecStartedTM2InputFor, Turing.TM2to1.trInit,
    Turing.PartrecToTM2.trList]

theorem nextAfterOrigin_eq_initReturnState_zero :
    nextAfterOrigin = initReturnState 0 := by
  unfold nextAfterOrigin
  rw [partrecStartedTM0Input_length]
  simp

/-- The state reached after writing the origin marker is in the folded state support. -/
theorem nextAfterOrigin_mem_states (tc : Turing.ToPartrec.Code) :
    nextAfterOrigin ∈ foldedStateList tc := by
  unfold nextAfterOrigin
  by_cases h : TM0Route.partrecStartedTM0Input.length ≤ 1
  · simp [h, foldedStateList, foldedStateListOfCodes, foldedInitStateList]
  · have hlen : 0 < TM0Route.partrecStartedTM0Input.length := by omega
    unfold foldedStateList foldedStateListOfCodes foldedInitStateList
    rw [List.mem_append]
    apply Or.inl
    rw [List.mem_append]
    apply Or.inr
    rw [List.mem_flatMap]
    refine ⟨0, List.mem_range.2 hlen, ?_⟩
    simp [h]


end TM0FoldedCompiler

end LeanWang
