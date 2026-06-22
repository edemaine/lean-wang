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

/-- First initialization row: mark the origin and write the first input symbol. -/
def initWriteOriginRow : PostTransition :=
  mkRow initWriteOriginState foldedBlank nextAfterOrigin
    (PostStmt.write (foldedOriginSymbol (inputSymbol 0)))

def initMoveRightRows : List PostTransition :=
  (List.range (TM0Route.partrecStartedTM0Input.length - 1)).flatMap fun i =>
    foldedSymbolList.map fun read =>
      mkRow (initMoveRightState i) read (initWriteRightState i) (PostStmt.move Move.right)

def nextAfterWriteRight (i : Nat) : Nat :=
  if i + 2 < TM0Route.partrecStartedTM0Input.length then
    initMoveRightState (i + 1)
  else
    initReturnState (i + 1)

def initWriteRightRows : List PostTransition :=
  (List.range (TM0Route.partrecStartedTM0Input.length - 1)).map fun i =>
    mkRow (initWriteRightState i) foldedBlank (nextAfterWriteRight i)
      (PostStmt.write (foldedSymbolCode false default (inputSymbol (i + 1))))

def initReturnRow (tc : Turing.ToPartrec.Code) (i read : Nat) : PostTransition :=
  if i = 0 then
    mkRow (initReturnState 0) read (foldedSimStartState tc) (PostStmt.write read)
  else
    mkRow (initReturnState i) read (initReturnState (i - 1)) (PostStmt.move Move.left)

def initReturnIndexList : List Nat :=
  0 :: List.range TM0Route.partrecStartedTM0Input.length

def initReturnRows (tc : Turing.ToPartrec.Code) : List PostTransition :=
  initReturnIndexList.flatMap fun i =>
    foldedSymbolList.map fun read => initReturnRow tc i read

def initRows (tc : Turing.ToPartrec.Code) : List PostTransition :=
  initWriteOriginRow :: initMoveRightRows ++ initWriteRightRows ++ initReturnRows tc

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

end TM0FoldedCompiler

end LeanWang
