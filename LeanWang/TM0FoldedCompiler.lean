/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FiniteCompiler

/-!
Finite one-sided TM0 program data for a folded simulation of Mathlib's TM0.

Mathlib's `Turing.TM0` configurations use a two-sided tape. The local
`FiniteTM0Program` model used by the current Wang-tile layer has a one-sided
`Nat`-indexed tape. This file starts the cleaner bridge between the two models:
one local tape cell stores the pair of Mathlib symbols at positions `-i-1` and
`i`, plus an origin marker. The finite control stores which side of the folded
cell is currently active.
-/

noncomputable section

namespace LeanWang

namespace TM0FoldedCompiler

open TM0Route

abbrev SourceSymbol : Type :=
  Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol

abbrev SourceLabel (tc : Turing.ToPartrec.Code) : Type :=
  Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc)

/-- Which half of a folded one-sided cell is the simulated two-sided head reading? -/
inductive FoldSide where
  | left
  | right
deriving DecidableEq, Repr

namespace FoldSide

def code : FoldSide → Nat
  | left => 0
  | right => 1

theorem code_injective : Function.Injective code := by
  intro s t h
  cases s <;> cases t <;> simp [code] at h ⊢

end FoldSide

def foldSideList : List FoldSide :=
  [FoldSide.left, FoldSide.right]

theorem mem_foldSideList (s : FoldSide) : s ∈ foldSideList := by
  cases s <;> simp [foldSideList]

/--
Code a folded tape cell.

The Boolean marker distinguishes the origin cell, which is the only place where
a simulated left/right move can cross between the two folded sides without
moving the local one-sided head.
-/
def foldedSymbolCode (marked : Bool) (left right : SourceSymbol) : Nat :=
  Nat.pair (if marked then 1 else 0)
    (Nat.pair
      (TM0Route.partrecStartedTM0SymbolCode left)
      (TM0Route.partrecStartedTM0SymbolCode right))

def foldedSymbolList : List Nat :=
  [false, true].flatMap fun marked =>
    TM0Route.partrecStartedTM0SymbolList.flatMap fun left =>
      TM0Route.partrecStartedTM0SymbolList.map fun right =>
        foldedSymbolCode marked left right

theorem foldedSymbolCode_mem_symbols
    (marked : Bool) (left right : SourceSymbol) :
    foldedSymbolCode marked left right ∈ foldedSymbolList := by
  unfold foldedSymbolList
  cases marked <;>
    simp [TM0Route.mem_partrecStartedTM0SymbolList]

/-- Blank folded cell away from the origin. -/
def foldedBlank : Nat :=
  foldedSymbolCode false default default

theorem foldedBlank_mem_symbols : foldedBlank ∈ foldedSymbolList := by
  unfold foldedBlank
  exact foldedSymbolCode_mem_symbols false default default

/-- Initial origin cell when the Mathlib input head reads `a`. -/
def foldedOriginSymbol (a : SourceSymbol) : Nat :=
  foldedSymbolCode true default a

theorem foldedOriginSymbol_mem_symbols (a : SourceSymbol) :
    foldedOriginSymbol a ∈ foldedSymbolList := by
  unfold foldedOriginSymbol
  exact foldedSymbolCode_mem_symbols true default a

def foldedRead (side : FoldSide) (left right : SourceSymbol) : SourceSymbol :=
  match side with
  | FoldSide.left => left
  | FoldSide.right => right

def foldedWrite (side : FoldSide) (new left right : SourceSymbol) : Nat :=
  match side with
  | FoldSide.left => foldedSymbolCode false new right
  | FoldSide.right => foldedSymbolCode false left new

def foldedWriteMarked (side : FoldSide) (new left right : SourceSymbol) : Nat :=
  match side with
  | FoldSide.left => foldedSymbolCode true new right
  | FoldSide.right => foldedSymbolCode true left new

theorem foldedWrite_mem_symbols (side : FoldSide) (new left right : SourceSymbol) :
    foldedWrite side new left right ∈ foldedSymbolList := by
  cases side <;> simp [foldedWrite, foldedSymbolCode_mem_symbols]

theorem foldedWriteMarked_mem_symbols (side : FoldSide) (new left right : SourceSymbol) :
    foldedWriteMarked side new left right ∈ foldedSymbolList := by
  cases side <;> simp [foldedWriteMarked, foldedSymbolCode_mem_symbols]

def stateTagSim : Nat := 0
def stateTagInit : Nat := 1
def stateTagReturn : Nat := 2

def taggedState (tag payload : Nat) : Nat :=
  Nat.pair tag payload

/-- State used while simulating a Mathlib TM0 label on one side of the folded tape. -/
def foldedSimStateCode (tc : Turing.ToPartrec.Code)
    (side : FoldSide) (q : SourceLabel tc) : Nat :=
  taggedState stateTagSim
    (Nat.pair side.code (TM0FiniteCompiler.stateCode tc q))

/-- First prelude state: write the marked origin cell. -/
def initWriteOriginState : Nat :=
  taggedState stateTagInit 0

/-- Prelude state that moves from an initialized right-side input cell to the next cell. -/
def initMoveRightState (i : Nat) : Nat :=
  taggedState stateTagInit (2 * i + 1)

/-- Prelude state that writes right-side input cell `i + 1`. -/
def initWriteRightState (i : Nat) : Nat :=
  taggedState stateTagInit (2 * i + 2)

/-- Prelude state with `i` left moves remaining before simulation starts. -/
def initReturnState (i : Nat) : Nat :=
  taggedState stateTagReturn i

def foldedStartState : Nat :=
  initWriteOriginState

def foldedSimStartState (tc : Turing.ToPartrec.Code) : Nat :=
  foldedSimStateCode tc FoldSide.right default

def foldedInitStateList : List Nat :=
  [initWriteOriginState, initReturnState 0] ++
    (List.range TM0Route.partrecStartedTM0Input.length).flatMap fun i =>
      [initMoveRightState i, initWriteRightState i, initReturnState i]

def foldedSimStateList (tc : Turing.ToPartrec.Code) : List Nat :=
  (TM0Route.partrecStartedTM0LabelList tc).flatMap fun q =>
    foldSideList.map fun side => foldedSimStateCode tc side q

def foldedStateList (tc : Turing.ToPartrec.Code) : List Nat :=
  foldedInitStateList ++ foldedSimStateList tc

theorem foldedStartState_mem_states (tc : Turing.ToPartrec.Code) :
    foldedStartState ∈ foldedStateList tc := by
  simp [foldedStateList, foldedInitStateList, foldedStartState, initWriteOriginState]

theorem initReturnState_zero_mem_states (tc : Turing.ToPartrec.Code) :
    initReturnState 0 ∈ foldedStateList tc := by
  simp [foldedStateList, foldedInitStateList]

theorem initMoveRightState_mem_states {tc : Turing.ToPartrec.Code} {i : Nat}
    (hi : i < TM0Route.partrecStartedTM0Input.length) :
    initMoveRightState i ∈ foldedStateList tc := by
  unfold foldedStateList foldedInitStateList
  apply List.mem_append_left
  apply List.mem_append_right
  rw [List.mem_flatMap]
  refine ⟨i, List.mem_range.2 hi, ?_⟩
  simp

theorem initWriteRightState_mem_states {tc : Turing.ToPartrec.Code} {i : Nat}
    (hi : i < TM0Route.partrecStartedTM0Input.length) :
    initWriteRightState i ∈ foldedStateList tc := by
  unfold foldedStateList foldedInitStateList
  apply List.mem_append_left
  apply List.mem_append_right
  rw [List.mem_flatMap]
  refine ⟨i, List.mem_range.2 hi, ?_⟩
  simp

theorem initReturnState_mem_states {tc : Turing.ToPartrec.Code} {i : Nat}
    (hi : i < TM0Route.partrecStartedTM0Input.length) :
    initReturnState i ∈ foldedStateList tc := by
  unfold foldedStateList foldedInitStateList
  apply List.mem_append_left
  apply List.mem_append_right
  rw [List.mem_flatMap]
  refine ⟨i, List.mem_range.2 hi, ?_⟩
  simp

theorem default_mem_partrecStartedTM0LabelList (tc : Turing.ToPartrec.Code) :
    (default : SourceLabel tc) ∈ TM0Route.partrecStartedTM0LabelList tc := by
  exact (TM0Route.mem_partrecStartedTM0LabelList tc default).2
    (TM0Route.partrecStartedTM0_supports tc).1

theorem foldedSimStateCode_mem_states (tc : Turing.ToPartrec.Code)
    (side : FoldSide) {q : SourceLabel tc}
    (hq : q ∈ TM0Route.partrecStartedTM0LabelList tc) :
    foldedSimStateCode tc side q ∈ foldedStateList tc := by
  unfold foldedStateList foldedSimStateList
  apply List.mem_append_right
  rw [List.mem_flatMap]
  refine ⟨q, hq, ?_⟩
  exact List.mem_map_of_mem (mem_foldSideList side)

theorem foldedSimStartState_mem_states (tc : Turing.ToPartrec.Code) :
    foldedSimStartState tc ∈ foldedStateList tc := by
  unfold foldedSimStartState
  exact foldedSimStateCode_mem_states tc FoldSide.right
    (default_mem_partrecStartedTM0LabelList tc)

def inputSymbol (i : Nat) : SourceSymbol :=
  TM0Route.partrecStartedTM0Input.getI i

def nextAfterOrigin : Nat :=
  if TM0Route.partrecStartedTM0Input.length ≤ 1 then
    initReturnState 0
  else
    initMoveRightState 0

theorem nextAfterOrigin_mem_states (tc : Turing.ToPartrec.Code) :
    nextAfterOrigin ∈ foldedStateList tc := by
  unfold nextAfterOrigin
  by_cases h : TM0Route.partrecStartedTM0Input.length ≤ 1
  · simp [h, initReturnState_zero_mem_states tc]
  · have hlen : 0 < TM0Route.partrecStartedTM0Input.length := by omega
    simp [h, initMoveRightState_mem_states (tc := tc) hlen]

def mkRow (state read next : Nat) (stmt : PostStmt) : PostTransition where
  state := state
  read := read
  next := next
  stmt := stmt

@[simp]
theorem mkRow_matchesInput (state read next : Nat) (stmt : PostStmt) :
    (mkRow state read next stmt).matchesInput state read = true := by
  simp [mkRow, PostTransition.matchesInput]

theorem mkRow_matchesInput_of_state_ne {state state' read read' next : Nat}
    {stmt : PostStmt} (h : state ≠ state') :
    (mkRow state read next stmt).matchesInput state' read' = false := by
  simp [mkRow, PostTransition.matchesInput, h]

theorem mkRow_matchesInput_of_read_ne {state read read' next : Nat}
    {stmt : PostStmt} (h : read ≠ read') :
    (mkRow state read next stmt).matchesInput state read' = false := by
  simp [mkRow, PostTransition.matchesInput, h]

private theorem find?_append_of_eq_some {α : Type} {xs ys : List α} {p : α → Bool} {a : α}
    (h : xs.find? p = some a) :
    (xs ++ ys).find? p = some a := by
  induction xs with
  | nil =>
      simp at h
  | cons x xs ih =>
      by_cases hp : p x = true
      · have hx : x = a := by
          simpa [hp] using h
        subst a
        simp [hp]
      · have htail : xs.find? p = some a := by
          simpa [hp] using h
        simp [hp, htail]

private theorem find?_append_of_eq_none {α : Type} {xs ys : List α} {p : α → Bool}
    (h : xs.find? p = none) :
    (xs ++ ys).find? p = ys.find? p := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      by_cases hp : p x = true
      · simp [hp] at h
      · have htail : xs.find? p = none := by
          simpa [hp] using h
        simpa [hp] using ih htail

theorem initWriteOriginState_ne_initMoveRightState (i : Nat) :
    initWriteOriginState ≠ initMoveRightState i := by
  intro h
  unfold initWriteOriginState initMoveRightState taggedState stateTagInit at h
  have hpayload := (Nat.pair_eq_pair.mp h).2
  omega

theorem initWriteOriginState_ne_initWriteRightState (i : Nat) :
    initWriteOriginState ≠ initWriteRightState i := by
  intro h
  unfold initWriteOriginState initWriteRightState taggedState stateTagInit at h
  have hpayload := (Nat.pair_eq_pair.mp h).2
  omega

theorem initWriteOriginState_ne_initReturnState (i : Nat) :
    initWriteOriginState ≠ initReturnState i := by
  intro h
  unfold initWriteOriginState initReturnState taggedState stateTagInit stateTagReturn at h
  have htag := (Nat.pair_eq_pair.mp h).1
  omega

/-- First initialization row: mark the origin and write the first input symbol. -/
def initWriteOriginRow : PostTransition :=
  mkRow initWriteOriginState foldedBlank nextAfterOrigin
    (PostStmt.write (foldedOriginSymbol (inputSymbol 0)))

def initMoveRightRow (i read : Nat) : PostTransition :=
  mkRow (initMoveRightState i) read (initWriteRightState i) (PostStmt.move Move.right)

theorem initMoveRightState_injective :
    Function.Injective initMoveRightState := by
  intro i j h
  unfold initMoveRightState taggedState stateTagInit at h
  have hpayload := (Nat.pair_eq_pair.mp h).2
  omega

theorem initMoveRightState_ne_initWriteRightState (i j : Nat) :
    initMoveRightState i ≠ initWriteRightState j := by
  intro h
  unfold initMoveRightState initWriteRightState taggedState stateTagInit at h
  have hpayload := (Nat.pair_eq_pair.mp h).2
  omega

theorem initMoveRightState_ne_initReturnState (i j : Nat) :
    initMoveRightState i ≠ initReturnState j := by
  intro h
  unfold initMoveRightState initReturnState taggedState stateTagInit stateTagReturn at h
  have htag := (Nat.pair_eq_pair.mp h).1
  omega

def initMoveRightRows : List PostTransition :=
  (List.range (TM0Route.partrecStartedTM0Input.length - 1)).flatMap fun i =>
    foldedSymbolList.map fun read => initMoveRightRow i read

private theorem find?_map_initMoveRightRow_of_read
    (i read : Nat) (reads : List Nat) (hread : read ∈ reads) :
    (reads.map fun r => initMoveRightRow i r).find?
        (fun e => e.matchesInput (initMoveRightState i) read) =
      some (initMoveRightRow i read) := by
  induction reads with
  | nil =>
      cases hread
  | cons r reads ih =>
      simp only [List.mem_cons] at hread
      by_cases hr : r = read
      · subst r
        simp [initMoveRightRow, mkRow, PostTransition.matchesInput]
      · have htail : read ∈ reads := by
          rcases hread with h | h
          · exact False.elim (hr h.symm)
          · exact h
        have hmiss :
            (initMoveRightRow i r).matchesInput (initMoveRightState i) read = false := by
          exact mkRow_matchesInput_of_read_ne hr
        simp [hmiss, ih htail]

private theorem find?_map_initMoveRightRow_eq_none_of_index_ne
    {i j read : Nat} (hne : j ≠ i) (reads : List Nat) :
    (reads.map fun r => initMoveRightRow j r).find?
        (fun e => e.matchesInput (initMoveRightState i) read) =
      none := by
  have hstate : initMoveRightState j ≠ initMoveRightState i := by
    intro h
    exact hne (initMoveRightState_injective h)
  induction reads with
  | nil =>
      simp
  | cons r reads ih =>
      have hmiss :
          (initMoveRightRow j r).matchesInput (initMoveRightState i) read = false :=
        mkRow_matchesInput_of_state_ne hstate
      simp [hmiss, ih]

private theorem find?_flatMap_initMoveRightRows_aux
    (i read : Nat) (indices : List Nat)
    (hi : i ∈ indices) (hread : read ∈ foldedSymbolList) :
    (indices.flatMap fun j => foldedSymbolList.map fun r => initMoveRightRow j r).find?
        (fun e => e.matchesInput (initMoveRightState i) read) =
      some (initMoveRightRow i read) := by
  induction indices with
  | nil =>
      cases hi
  | cons j indices ih =>
      simp only [List.mem_cons] at hi
      by_cases hji : j = i
      · subst j
        have hhead := find?_map_initMoveRightRow_of_read i read foldedSymbolList hread
        simp only [List.flatMap_cons]
        exact find?_append_of_eq_some hhead
      · have hi_tail : i ∈ indices := by
          rcases hi with h | h
          · exact False.elim (hji h.symm)
          · exact h
        have hhead := find?_map_initMoveRightRow_eq_none_of_index_ne
          (i := i) (j := j) (read := read) hji foldedSymbolList
        have htail := ih hi_tail
        simp only [List.flatMap_cons]
        rw [find?_append_of_eq_none hhead]
        exact htail

theorem initMoveRightRows_find?_of_mem {i read : Nat}
    (hi : i < TM0Route.partrecStartedTM0Input.length - 1)
    (hread : read ∈ foldedSymbolList) :
    initMoveRightRows.find?
        (fun e => e.matchesInput (initMoveRightState i) read) =
      some (initMoveRightRow i read) := by
  unfold initMoveRightRows
  exact find?_flatMap_initMoveRightRows_aux i read
    (List.range (TM0Route.partrecStartedTM0Input.length - 1)) (List.mem_range.2 hi) hread

def nextAfterWriteRight (i : Nat) : Nat :=
  if i + 2 < TM0Route.partrecStartedTM0Input.length then
    initMoveRightState (i + 1)
  else
    initReturnState (i + 1)

def initWriteRightRow (i : Nat) : PostTransition :=
  mkRow (initWriteRightState i) foldedBlank (nextAfterWriteRight i)
    (PostStmt.write (foldedSymbolCode false default (inputSymbol (i + 1))))

theorem initWriteRightState_injective :
    Function.Injective initWriteRightState := by
  intro i j h
  unfold initWriteRightState taggedState stateTagInit at h
  have hpayload := (Nat.pair_eq_pair.mp h).2
  omega

theorem initWriteRightState_ne_initReturnState (i j : Nat) :
    initWriteRightState i ≠ initReturnState j := by
  intro h
  unfold initWriteRightState initReturnState taggedState stateTagInit stateTagReturn at h
  have htag := (Nat.pair_eq_pair.mp h).1
  omega

def initWriteRightRows : List PostTransition :=
  (List.range (TM0Route.partrecStartedTM0Input.length - 1)).map fun i =>
    initWriteRightRow i

def initReturnRow (tc : Turing.ToPartrec.Code) (i read : Nat) : PostTransition :=
  if i = 0 then
    mkRow (initReturnState 0) read (foldedSimStartState tc) (PostStmt.write read)
  else
    mkRow (initReturnState i) read (initReturnState (i - 1)) (PostStmt.move Move.left)

def initReturnIndexList : List Nat :=
  0 :: List.range TM0Route.partrecStartedTM0Input.length

theorem initReturnState_injective :
    Function.Injective initReturnState := by
  intro i j h
  unfold initReturnState taggedState stateTagReturn at h
  exact (Nat.pair_eq_pair.mp h).2

def initReturnRows (tc : Turing.ToPartrec.Code) : List PostTransition :=
  initReturnIndexList.flatMap fun i =>
    foldedSymbolList.map fun read => initReturnRow tc i read

def initRows (tc : Turing.ToPartrec.Code) : List PostTransition :=
  initWriteOriginRow :: initMoveRightRows ++ initWriteRightRows ++ initReturnRows tc

theorem initWriteOriginRow_mem_initRows (tc : Turing.ToPartrec.Code) :
    initWriteOriginRow ∈ initRows tc := by
  simp [initRows]

theorem initMoveRightRow_mem_initMoveRightRows {i read : Nat}
    (hi : i < TM0Route.partrecStartedTM0Input.length - 1)
    (hread : read ∈ foldedSymbolList) :
    initMoveRightRow i read ∈ initMoveRightRows := by
  unfold initMoveRightRows
  rw [List.mem_flatMap]
  refine ⟨i, List.mem_range.2 hi, ?_⟩
  exact List.mem_map_of_mem hread

theorem initMoveRightRow_mem_initRows (tc : Turing.ToPartrec.Code) {i read : Nat}
    (hi : i < TM0Route.partrecStartedTM0Input.length - 1)
    (hread : read ∈ foldedSymbolList) :
    initMoveRightRow i read ∈ initRows tc := by
  unfold initRows
  simp [initMoveRightRow_mem_initMoveRightRows hi hread]

theorem nextAfterWriteRight_mem_states (tc : Turing.ToPartrec.Code) {i : Nat}
    (hi : i < TM0Route.partrecStartedTM0Input.length - 1) :
    nextAfterWriteRight i ∈ foldedStateList tc := by
  unfold nextAfterWriteRight
  by_cases hnext : i + 2 < TM0Route.partrecStartedTM0Input.length
  · rw [if_pos hnext]
    exact initMoveRightState_mem_states (tc := tc) (by omega)
  · rw [if_neg hnext]
    exact initReturnState_mem_states (tc := tc) (by omega)

theorem initWriteRightRow_mem_initWriteRightRows {i : Nat}
    (hi : i < TM0Route.partrecStartedTM0Input.length - 1) :
    initWriteRightRow i ∈ initWriteRightRows := by
  unfold initWriteRightRows
  exact List.mem_map_of_mem (List.mem_range.2 hi)

theorem initWriteRightRow_mem_initRows (tc : Turing.ToPartrec.Code) {i : Nat}
    (hi : i < TM0Route.partrecStartedTM0Input.length - 1) :
    initWriteRightRow i ∈ initRows tc := by
  unfold initRows
  simp [initWriteRightRow_mem_initWriteRightRows hi]

theorem initWriteRightRow_write_mem_symbols (i : Nat) :
    foldedSymbolCode false default (inputSymbol (i + 1)) ∈ foldedSymbolList := by
  exact foldedSymbolCode_mem_symbols false default (inputSymbol (i + 1))

theorem initReturnRow_mem_initReturnRows (tc : Turing.ToPartrec.Code) {i read : Nat}
    (hi : i ∈ initReturnIndexList)
    (hread : read ∈ foldedSymbolList) :
    initReturnRow tc i read ∈ initReturnRows tc := by
  unfold initReturnRows
  rw [List.mem_flatMap]
  refine ⟨i, hi, ?_⟩
  exact List.mem_map_of_mem hread

theorem initReturnRow_zero_mem_initRows (tc : Turing.ToPartrec.Code) {read : Nat}
    (hread : read ∈ foldedSymbolList) :
    initReturnRow tc 0 read ∈ initRows tc := by
  unfold initRows
  apply List.mem_cons_of_mem
  apply List.mem_append_right
  exact initReturnRow_mem_initReturnRows tc (by simp [initReturnIndexList]) hread

theorem initReturnRow_mem_initRows_of_lt (tc : Turing.ToPartrec.Code) {i read : Nat}
    (hi : i < TM0Route.partrecStartedTM0Input.length)
    (hread : read ∈ foldedSymbolList) :
    initReturnRow tc i read ∈ initRows tc := by
  unfold initRows
  apply List.mem_cons_of_mem
  apply List.mem_append_right
  exact initReturnRow_mem_initReturnRows tc
    (by simp [initReturnIndexList, List.mem_range.2 hi]) hread

/--
Folded finite one-sided TM0 program header.

The transition table currently contains the initialization prelude. The next
layer will append folded simulation rows over `foldedSymbolList` and
`foldedStateList`.
-/
def programHeader (tc : Turing.ToPartrec.Code) : FiniteTM0Program where
  symbols := foldedSymbolList
  states := foldedStateList tc
  blank := foldedBlank
  start := foldedStartState
  table := initRows tc

@[simp]
theorem programHeader_symbols (tc : Turing.ToPartrec.Code) :
    (programHeader tc).symbols = foldedSymbolList := rfl

@[simp]
theorem programHeader_states (tc : Turing.ToPartrec.Code) :
    (programHeader tc).states = foldedStateList tc := rfl

@[simp]
theorem programHeader_blank (tc : Turing.ToPartrec.Code) :
    (programHeader tc).blank = foldedBlank := rfl

@[simp]
theorem programHeader_start (tc : Turing.ToPartrec.Code) :
    (programHeader tc).start = foldedStartState := rfl

@[simp]
theorem programHeader_table (tc : Turing.ToPartrec.Code) :
    (programHeader tc).table = initRows tc := rfl

theorem programHeader_blank_mem_symbols (tc : Turing.ToPartrec.Code) :
    (programHeader tc).blank ∈ (programHeader tc).symbols := by
  simp [foldedBlank_mem_symbols]

theorem programHeader_start_mem_states (tc : Turing.ToPartrec.Code) :
    (programHeader tc).start ∈ (programHeader tc).states := by
  simp [foldedStartState_mem_states tc]

theorem programHeader_transition?_start_blank (tc : Turing.ToPartrec.Code) :
    (programHeader tc).transition? foldedStartState foldedBlank =
      some initWriteOriginRow := by
  simp [PostProgram.transition?, initRows, initWriteOriginRow, foldedStartState]

theorem programHeader_step_start_blank (tc : Turing.ToPartrec.Code) :
    (programHeader tc).step foldedStartState foldedBlank =
      some (nextAfterOrigin, PostStmt.write (foldedOriginSymbol (inputSymbol 0))) := by
  have hfind := programHeader_transition?_start_blank tc
  have hnext : nextAfterOrigin ∈ foldedStateList tc :=
    nextAfterOrigin_mem_states tc
  have hwrite : foldedOriginSymbol (inputSymbol 0) ∈ foldedSymbolList :=
    foldedOriginSymbol_mem_symbols (inputSymbol 0)
  simp [PostProgram.step, hfind, initWriteOriginRow, mkRow, hnext, hwrite]

theorem programHeader_transition?_initMoveRight
    (tc : Turing.ToPartrec.Code) {i read : Nat}
    (hi : i < TM0Route.partrecStartedTM0Input.length - 1)
    (hread : read ∈ foldedSymbolList) :
    (programHeader tc).transition? (initMoveRightState i) read =
      some (initMoveRightRow i read) := by
  have horigin :
      initWriteOriginRow.matchesInput (initMoveRightState i) read = false := by
    unfold initWriteOriginRow
    exact mkRow_matchesInput_of_state_ne (initWriteOriginState_ne_initMoveRightState i)
  have hmove := initMoveRightRows_find?_of_mem hi hread
  unfold PostProgram.transition?
  change (initRows tc).find? (fun e => e.matchesInput (initMoveRightState i) read) =
    some (initMoveRightRow i read)
  unfold initRows
  have htail :
      (initMoveRightRows ++ initWriteRightRows ++ initReturnRows tc).find?
          (fun e => e.matchesInput (initMoveRightState i) read) =
        some (initMoveRightRow i read) := by
    exact find?_append_of_eq_some (ys := initWriteRightRows ++ initReturnRows tc) hmove
  simpa [horigin] using htail

theorem programHeader_step_initMoveRight
    (tc : Turing.ToPartrec.Code) {i read : Nat}
    (hi : i < TM0Route.partrecStartedTM0Input.length - 1)
    (hread : read ∈ foldedSymbolList) :
    (programHeader tc).step (initMoveRightState i) read =
      some (initWriteRightState i, PostStmt.move Move.right) := by
  have hfind := programHeader_transition?_initMoveRight tc hi hread
  have hnext : initWriteRightState i ∈ foldedStateList tc :=
    initWriteRightState_mem_states (tc := tc) (by omega)
  simp [PostProgram.step, hfind, initMoveRightRow, mkRow, hnext]

end TM0FoldedCompiler

end LeanWang
