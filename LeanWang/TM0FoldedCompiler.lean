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

theorem foldedSymbolCode_injective :
    Function.Injective (fun p : Bool × SourceSymbol × SourceSymbol =>
      foldedSymbolCode p.1 p.2.1 p.2.2) := by
  intro p r h
  rcases p with ⟨marked, left, right⟩
  rcases r with ⟨marked', left', right'⟩
  unfold foldedSymbolCode at h
  have hpair := Nat.pair_eq_pair.mp h
  have hmarked : marked = marked' := by
    cases marked <;> cases marked' <;> simp at hpair ⊢
  have hsymbols := Nat.pair_eq_pair.mp hpair.2
  have hleft : left = left' :=
    TM0Route.partrecStartedTM0SymbolCode_injective hsymbols.1
  have hright : right = right' :=
    TM0Route.partrecStartedTM0SymbolCode_injective hsymbols.2
  cases hmarked
  cases hleft
  cases hright
  rfl

theorem foldedSymbolCode_eq {marked marked' : Bool} {left right left' right' : SourceSymbol}
    (h : foldedSymbolCode marked left right = foldedSymbolCode marked' left' right') :
    marked = marked' ∧ left = left' ∧ right = right' := by
  have hp :
      (marked, left, right) = (marked', left', right') :=
    foldedSymbolCode_injective h
  cases hp
  exact ⟨rfl, rfl, rfl⟩

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

theorem foldedSimStateCode_injective_on_labels {tc : Turing.ToPartrec.Code}
    {side side' : FoldSide} {q q' : SourceLabel tc}
    (hq : q ∈ TM0Route.partrecStartedTM0LabelList tc)
    (hq' : q' ∈ TM0Route.partrecStartedTM0LabelList tc)
    (h : foldedSimStateCode tc side q = foldedSimStateCode tc side' q') :
    side = side' ∧ q = q' := by
  unfold foldedSimStateCode taggedState stateTagSim at h
  have hpayload := (Nat.pair_eq_pair.mp h).2
  have hparts := Nat.pair_eq_pair.mp hpayload
  have hside : side = side' :=
    FoldSide.code_injective hparts.1
  have hqset : q ∈ TM0Route.partrecStartedTM0Labels tc :=
    (TM0Route.mem_partrecStartedTM0LabelList tc q).1 hq
  have hq'set : q' ∈ TM0Route.partrecStartedTM0Labels tc :=
    (TM0Route.mem_partrecStartedTM0LabelList tc q').1 hq'
  have hqeq : q = q' :=
    TM0FiniteCompiler.stateCode_injective_on_labels hqset hq'set hparts.2
  exact ⟨hside, hqeq⟩

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

private theorem find?_eq_none_of_forall_matchesInput_false
    {xs : List PostTransition} {q a : Nat}
    (h : ∀ e ∈ xs, e.matchesInput q a = false) :
    xs.find? (fun e => e.matchesInput q a) = none := by
  induction xs with
  | nil =>
      simp
  | cons e xs ih =>
      have hhead : e.matchesInput q a = false := h e (by simp)
      have htail : xs.find? (fun e => e.matchesInput q a) = none := by
        apply ih
        intro e he
        exact h e (by simp [he])
      simp [hhead, htail]

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

theorem initWriteOriginState_ne_foldedSimStateCode
    (tc : Turing.ToPartrec.Code) (side : FoldSide) (q : SourceLabel tc) :
    initWriteOriginState ≠ foldedSimStateCode tc side q := by
  intro h
  unfold initWriteOriginState foldedSimStateCode taggedState stateTagInit stateTagSim at h
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

theorem initMoveRightState_ne_foldedSimStateCode
    (tc : Turing.ToPartrec.Code) (i : Nat) (side : FoldSide) (q : SourceLabel tc) :
    initMoveRightState i ≠ foldedSimStateCode tc side q := by
  intro h
  unfold initMoveRightState foldedSimStateCode taggedState stateTagInit stateTagSim at h
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

theorem initWriteRightState_ne_foldedSimStateCode
    (tc : Turing.ToPartrec.Code) (i : Nat) (side : FoldSide) (q : SourceLabel tc) :
    initWriteRightState i ≠ foldedSimStateCode tc side q := by
  intro h
  unfold initWriteRightState foldedSimStateCode taggedState stateTagInit stateTagSim at h
  have htag := (Nat.pair_eq_pair.mp h).1
  omega

def initWriteRightRows : List PostTransition :=
  (List.range (TM0Route.partrecStartedTM0Input.length - 1)).map fun i =>
    initWriteRightRow i

private theorem find?_map_initWriteRightRows_aux
    (i : Nat) (indices : List Nat) (hi : i ∈ indices) :
    (indices.map fun j => initWriteRightRow j).find?
        (fun e => e.matchesInput (initWriteRightState i) foldedBlank) =
      some (initWriteRightRow i) := by
  induction indices with
  | nil =>
      cases hi
  | cons j indices ih =>
      simp only [List.mem_cons] at hi
      by_cases hji : j = i
      · subst j
        simp [initWriteRightRow, mkRow, PostTransition.matchesInput]
      · have hi_tail : i ∈ indices := by
          rcases hi with h | h
          · exact False.elim (hji h.symm)
          · exact h
        have hstate : initWriteRightState j ≠ initWriteRightState i := by
          intro h
          exact hji (initWriteRightState_injective h)
        have hmiss :
            (initWriteRightRow j).matchesInput (initWriteRightState i) foldedBlank = false :=
          mkRow_matchesInput_of_state_ne hstate
        simp [hmiss, ih hi_tail]

theorem initWriteRightRows_find?_of_mem {i : Nat}
    (hi : i < TM0Route.partrecStartedTM0Input.length - 1) :
    initWriteRightRows.find?
        (fun e => e.matchesInput (initWriteRightState i) foldedBlank) =
      some (initWriteRightRow i) := by
  unfold initWriteRightRows
  exact find?_map_initWriteRightRows_aux i
    (List.range (TM0Route.partrecStartedTM0Input.length - 1)) (List.mem_range.2 hi)

theorem initMoveRightRows_find?_eq_none_of_initWriteRightState (i read : Nat) :
    initMoveRightRows.find?
        (fun e => e.matchesInput (initWriteRightState i) read) =
      none := by
  unfold initMoveRightRows
  induction List.range (TM0Route.partrecStartedTM0Input.length - 1) with
  | nil =>
      simp
  | cons j indices ih =>
      have hhead :
          (foldedSymbolList.map fun r => initMoveRightRow j r).find?
              (fun e => e.matchesInput (initWriteRightState i) read) = none := by
        have hstate : initMoveRightState j ≠ initWriteRightState i :=
          initMoveRightState_ne_initWriteRightState j i
        induction foldedSymbolList with
        | nil =>
            simp
        | cons r reads ihReads =>
            have hmiss :
                (initMoveRightRow j r).matchesInput (initWriteRightState i) read = false :=
              mkRow_matchesInput_of_state_ne hstate
            simp [hmiss, ihReads]
      simp only [List.flatMap_cons]
      rw [find?_append_of_eq_none hhead]
      exact ih

theorem initMoveRightRows_find?_eq_none_of_foldedSimStateCode
    (tc : Turing.ToPartrec.Code) (side : FoldSide) (q : SourceLabel tc) (read : Nat) :
    initMoveRightRows.find?
        (fun e => e.matchesInput (foldedSimStateCode tc side q) read) =
      none := by
  unfold initMoveRightRows
  induction List.range (TM0Route.partrecStartedTM0Input.length - 1) with
  | nil =>
      simp
  | cons j indices ih =>
      have hhead :
          (foldedSymbolList.map fun r => initMoveRightRow j r).find?
              (fun e => e.matchesInput (foldedSimStateCode tc side q) read) = none := by
        have hstate : initMoveRightState j ≠ foldedSimStateCode tc side q :=
          initMoveRightState_ne_foldedSimStateCode tc j side q
        induction foldedSymbolList with
        | nil =>
            simp
        | cons r reads ihReads =>
            have hmiss :
                (initMoveRightRow j r).matchesInput
                    (foldedSimStateCode tc side q) read = false :=
              mkRow_matchesInput_of_state_ne hstate
            simp [hmiss, ihReads]
      simp only [List.flatMap_cons]
      rw [find?_append_of_eq_none hhead]
      exact ih

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

theorem initReturnState_ne_foldedSimStateCode
    (tc : Turing.ToPartrec.Code) (i : Nat) (side : FoldSide) (q : SourceLabel tc) :
    initReturnState i ≠ foldedSimStateCode tc side q := by
  intro h
  unfold initReturnState foldedSimStateCode taggedState stateTagReturn stateTagSim at h
  have htag := (Nat.pair_eq_pair.mp h).1
  omega

def initReturnRows (tc : Turing.ToPartrec.Code) : List PostTransition :=
  initReturnIndexList.flatMap fun i =>
    foldedSymbolList.map fun read => initReturnRow tc i read

private theorem find?_map_initReturnRow_of_read
    (tc : Turing.ToPartrec.Code) (i read : Nat) (reads : List Nat)
    (hread : read ∈ reads) :
    (reads.map fun r => initReturnRow tc i r).find?
        (fun e => e.matchesInput (initReturnState i) read) =
      some (initReturnRow tc i read) := by
  induction reads with
  | nil =>
      cases hread
  | cons r reads ih =>
      simp only [List.mem_cons] at hread
      by_cases hr : r = read
      · subst r
        by_cases hi0 : i = 0
        · subst i
          simp [initReturnRow, mkRow, PostTransition.matchesInput]
        · simp [initReturnRow, hi0, mkRow, PostTransition.matchesInput]
      · have htail : read ∈ reads := by
          rcases hread with h | h
          · exact False.elim (hr h.symm)
          · exact h
        have hmiss :
            (initReturnRow tc i r).matchesInput (initReturnState i) read = false := by
          by_cases hi0 : i = 0
          · subst i
            exact mkRow_matchesInput_of_read_ne hr
          · unfold initReturnRow
            rw [if_neg hi0]
            exact mkRow_matchesInput_of_read_ne hr
        simp [hmiss, ih htail]

private theorem find?_map_initReturnRow_eq_none_of_index_ne
    (tc : Turing.ToPartrec.Code) {i j read : Nat} (hne : j ≠ i)
    (reads : List Nat) :
    (reads.map fun r => initReturnRow tc j r).find?
        (fun e => e.matchesInput (initReturnState i) read) =
      none := by
  have hstate : initReturnState j ≠ initReturnState i := by
    intro h
    exact hne (initReturnState_injective h)
  induction reads with
  | nil =>
      simp
  | cons r reads ih =>
      have hmiss :
          (initReturnRow tc j r).matchesInput (initReturnState i) read = false := by
        by_cases hj0 : j = 0
        · subst j
          exact mkRow_matchesInput_of_state_ne hstate
        · unfold initReturnRow
          rw [if_neg hj0]
          exact mkRow_matchesInput_of_state_ne hstate
      simp [hmiss, ih]

private theorem find?_flatMap_initReturnRows_aux
    (tc : Turing.ToPartrec.Code) (i read : Nat) (indices : List Nat)
    (hi : i ∈ indices) (hread : read ∈ foldedSymbolList) :
    (indices.flatMap fun j => foldedSymbolList.map fun r => initReturnRow tc j r).find?
        (fun e => e.matchesInput (initReturnState i) read) =
      some (initReturnRow tc i read) := by
  induction indices with
  | nil =>
      cases hi
  | cons j indices ih =>
      simp only [List.mem_cons] at hi
      by_cases hji : j = i
      · subst j
        have hhead := find?_map_initReturnRow_of_read tc i read foldedSymbolList hread
        simp only [List.flatMap_cons]
        exact find?_append_of_eq_some hhead
      · have hi_tail : i ∈ indices := by
          rcases hi with h | h
          · exact False.elim (hji h.symm)
          · exact h
        have hhead := find?_map_initReturnRow_eq_none_of_index_ne
          tc (i := i) (j := j) (read := read) hji foldedSymbolList
        have htail := ih hi_tail
        simp only [List.flatMap_cons]
        rw [find?_append_of_eq_none hhead]
        exact htail

theorem initReturnRows_find?_of_mem (tc : Turing.ToPartrec.Code) {i read : Nat}
    (hi : i ∈ initReturnIndexList)
    (hread : read ∈ foldedSymbolList) :
    (initReturnRows tc).find?
        (fun e => e.matchesInput (initReturnState i) read) =
      some (initReturnRow tc i read) := by
  unfold initReturnRows
  exact find?_flatMap_initReturnRows_aux tc i read initReturnIndexList hi hread

theorem initReturnRows_find?_eq_none_of_foldedSimStateCode
    (tc : Turing.ToPartrec.Code) (side : FoldSide) (q : SourceLabel tc) (read : Nat) :
    (initReturnRows tc).find?
        (fun e => e.matchesInput (foldedSimStateCode tc side q) read) =
      none := by
  unfold initReturnRows
  induction initReturnIndexList with
  | nil =>
      simp
  | cons i indices ih =>
      have hhead :
          (foldedSymbolList.map fun r => initReturnRow tc i r).find?
              (fun e => e.matchesInput (foldedSimStateCode tc side q) read) = none := by
        have hstate : initReturnState i ≠ foldedSimStateCode tc side q :=
          initReturnState_ne_foldedSimStateCode tc i side q
        induction foldedSymbolList with
        | nil =>
            simp
        | cons r reads ihReads =>
            have hmiss :
                (initReturnRow tc i r).matchesInput
                    (foldedSimStateCode tc side q) read = false := by
              by_cases hi0 : i = 0
              · subst i
                exact mkRow_matchesInput_of_state_ne hstate
              · unfold initReturnRow
                rw [if_neg hi0]
                exact mkRow_matchesInput_of_state_ne hstate
            simp [hmiss, ihReads]
      simp only [List.flatMap_cons]
      rw [find?_append_of_eq_none hhead]
      exact ih

theorem initMoveRightRows_find?_eq_none_of_initReturnState (i read : Nat) :
    initMoveRightRows.find?
        (fun e => e.matchesInput (initReturnState i) read) =
      none := by
  unfold initMoveRightRows
  induction List.range (TM0Route.partrecStartedTM0Input.length - 1) with
  | nil =>
      simp
  | cons j indices ih =>
      have hhead :
          (foldedSymbolList.map fun r => initMoveRightRow j r).find?
              (fun e => e.matchesInput (initReturnState i) read) = none := by
        have hstate : initMoveRightState j ≠ initReturnState i :=
          initMoveRightState_ne_initReturnState j i
        induction foldedSymbolList with
        | nil =>
            simp
        | cons r reads ihReads =>
            have hmiss :
                (initMoveRightRow j r).matchesInput (initReturnState i) read = false :=
              mkRow_matchesInput_of_state_ne hstate
            simp [hmiss, ihReads]
      simp only [List.flatMap_cons]
      rw [find?_append_of_eq_none hhead]
      exact ih

theorem initWriteRightRows_find?_eq_none_of_initReturnState (i read : Nat) :
    initWriteRightRows.find?
        (fun e => e.matchesInput (initReturnState i) read) =
      none := by
  unfold initWriteRightRows
  induction List.range (TM0Route.partrecStartedTM0Input.length - 1) with
  | nil =>
      simp
  | cons j indices ih =>
      have hstate : initWriteRightState j ≠ initReturnState i :=
        initWriteRightState_ne_initReturnState j i
      have hmiss :
          (initWriteRightRow j).matchesInput (initReturnState i) read = false :=
        mkRow_matchesInput_of_state_ne hstate
      simp [hmiss, ih]

theorem initWriteRightRows_find?_eq_none_of_foldedSimStateCode
    (tc : Turing.ToPartrec.Code) (side : FoldSide) (q : SourceLabel tc) (read : Nat) :
    initWriteRightRows.find?
        (fun e => e.matchesInput (foldedSimStateCode tc side q) read) =
      none := by
  unfold initWriteRightRows
  induction List.range (TM0Route.partrecStartedTM0Input.length - 1) with
  | nil =>
      simp
  | cons j indices ih =>
      have hstate : initWriteRightState j ≠ foldedSimStateCode tc side q :=
        initWriteRightState_ne_foldedSimStateCode tc j side q
      have hmiss :
          (initWriteRightRow j).matchesInput (foldedSimStateCode tc side q) read = false :=
        mkRow_matchesInput_of_state_ne hstate
      simp [hmiss, ih]

def initRows (tc : Turing.ToPartrec.Code) : List PostTransition :=
  initWriteOriginRow :: initMoveRightRows ++ initWriteRightRows ++ initReturnRows tc

theorem initRows_find?_eq_none_of_foldedSimStateCode
    (tc : Turing.ToPartrec.Code) (side : FoldSide) (q : SourceLabel tc) (read : Nat) :
    (initRows tc).find?
        (fun e => e.matchesInput (foldedSimStateCode tc side q) read) =
      none := by
  have horigin :
      initWriteOriginRow.matchesInput (foldedSimStateCode tc side q) read = false := by
    unfold initWriteOriginRow
    exact mkRow_matchesInput_of_state_ne
      (initWriteOriginState_ne_foldedSimStateCode tc side q)
  have hmove := initMoveRightRows_find?_eq_none_of_foldedSimStateCode tc side q read
  have hwrite := initWriteRightRows_find?_eq_none_of_foldedSimStateCode tc side q read
  have hreturn := initReturnRows_find?_eq_none_of_foldedSimStateCode tc side q read
  unfold initRows
  have htail :
      (initMoveRightRows ++ initWriteRightRows ++ initReturnRows tc).find?
          (fun e => e.matchesInput (foldedSimStateCode tc side q) read) =
        none := by
    rw [show initMoveRightRows ++ initWriteRightRows ++ initReturnRows tc =
        initMoveRightRows ++ (initWriteRightRows ++ initReturnRows tc) by
      rw [List.append_assoc]]
    rw [find?_append_of_eq_none hmove]
    rw [find?_append_of_eq_none hwrite]
    exact hreturn
  simpa [horigin] using htail

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

/-- Side of the folded tape after a simulated TM0 move. -/
def foldedMoveNextSide (side : FoldSide) (marked : Bool) (dir : Turing.Dir) : FoldSide :=
  match side, marked, dir with
  | FoldSide.right, true, Turing.Dir.left => FoldSide.left
  | FoldSide.left, true, Turing.Dir.right => FoldSide.right
  | _, _, _ => side

theorem foldedMoveNextSide_mem_foldSideList
    (side : FoldSide) (marked : Bool) (dir : Turing.Dir) :
    foldedMoveNextSide side marked dir ∈ foldSideList := by
  exact mem_foldSideList _

/--
Local one-sided command for a simulated TM0 move.

Moving across the origin changes the folded side without moving the local head,
implemented as a no-op write of the current folded cell.
-/
def foldedMoveStmt (side : FoldSide) (marked : Bool) (cell : Nat)
    (dir : Turing.Dir) : PostStmt :=
  match side, marked, dir with
  | FoldSide.right, true, Turing.Dir.left => PostStmt.write cell
  | FoldSide.left, true, Turing.Dir.right => PostStmt.write cell
  | FoldSide.right, _, Turing.Dir.right => PostStmt.move Move.right
  | FoldSide.right, _, Turing.Dir.left => PostStmt.move Move.left
  | FoldSide.left, _, Turing.Dir.left => PostStmt.move Move.right
  | FoldSide.left, _, Turing.Dir.right => PostStmt.move Move.left

def foldedWriteForStmt (side : FoldSide) (marked : Bool)
    (new left right : SourceSymbol) : Nat :=
  if marked then
    foldedWriteMarked side new left right
  else
    foldedWrite side new left right

theorem foldedWriteForStmt_mem_symbols
    (side : FoldSide) (marked : Bool) (new left right : SourceSymbol) :
    foldedWriteForStmt side marked new left right ∈ foldedSymbolList := by
  unfold foldedWriteForStmt
  by_cases h : marked
  · simp [h, foldedWriteMarked_mem_symbols]
  · simp [h, foldedWrite_mem_symbols]

def simRowOfStep (tc : Turing.ToPartrec.Code)
    (side : FoldSide) (marked : Bool)
    (q q' : SourceLabel tc) (left right : SourceSymbol)
    (stmt : Turing.TM0.Stmt SourceSymbol) : PostTransition :=
  let read := foldedSymbolCode marked left right
  match stmt with
  | Turing.TM0.Stmt.write new =>
      mkRow (foldedSimStateCode tc side q) read
        (foldedSimStateCode tc side q')
        (PostStmt.write (foldedWriteForStmt side marked new left right))
  | Turing.TM0.Stmt.move dir =>
      mkRow (foldedSimStateCode tc side q) read
        (foldedSimStateCode tc (foldedMoveNextSide side marked dir) q')
        (foldedMoveStmt side marked read dir)

@[simp]
theorem simRowOfStep_matchesInput (tc : Turing.ToPartrec.Code)
    (side : FoldSide) (marked : Bool)
    (q q' : SourceLabel tc) (left right : SourceSymbol)
    (stmt : Turing.TM0.Stmt SourceSymbol) :
    (simRowOfStep tc side marked q q' left right stmt).matchesInput
        (foldedSimStateCode tc side q) (foldedSymbolCode marked left right) = true := by
  cases stmt <;> simp [simRowOfStep, mkRow, PostTransition.matchesInput]

theorem simRowOfStep_state (tc : Turing.ToPartrec.Code)
    (side : FoldSide) (marked : Bool)
    (q q' : SourceLabel tc) (left right : SourceSymbol)
    (stmt : Turing.TM0.Stmt SourceSymbol) :
    (simRowOfStep tc side marked q q' left right stmt).state =
      foldedSimStateCode tc side q := by
  cases stmt <;> rfl

theorem simRowOfStep_read (tc : Turing.ToPartrec.Code)
    (side : FoldSide) (marked : Bool)
    (q q' : SourceLabel tc) (left right : SourceSymbol)
    (stmt : Turing.TM0.Stmt SourceSymbol) :
    (simRowOfStep tc side marked q q' left right stmt).read =
      foldedSymbolCode marked left right := by
  cases stmt <;> rfl

theorem foldedSimStateCode_side_of_same_label_eq {tc : Turing.ToPartrec.Code}
    {side side' : FoldSide} {q : SourceLabel tc}
    (h : foldedSimStateCode tc side q = foldedSimStateCode tc side' q) :
    side = side' := by
  unfold foldedSimStateCode taggedState stateTagSim at h
  have hpayload := (Nat.pair_eq_pair.mp h).2
  exact FoldSide.code_injective (Nat.pair_eq_pair.mp hpayload).1

theorem simRowOfStep_matchesInput_of_side_ne {tc : Turing.ToPartrec.Code}
    {side side' : FoldSide} {marked marked' : Bool}
    {q q' : SourceLabel tc} {left right left' right' : SourceSymbol}
    {stmt : Turing.TM0.Stmt SourceSymbol}
    (hside : side' ≠ side) :
    (simRowOfStep tc side' marked' q q' left' right' stmt).matchesInput
        (foldedSimStateCode tc side q) (foldedSymbolCode marked left right) = false := by
  have hstate :
      foldedSimStateCode tc side' q ≠ foldedSimStateCode tc side q := by
    intro h
    exact hside (foldedSimStateCode_side_of_same_label_eq h)
  cases stmt <;> exact mkRow_matchesInput_of_state_ne hstate

theorem simRowOfStep_matchesInput_of_label_ne {tc : Turing.ToPartrec.Code}
    {side side' : FoldSide} {marked marked' : Bool}
    {q r r' : SourceLabel tc} {left right left' right' : SourceSymbol}
    {stmt : Turing.TM0.Stmt SourceSymbol}
    (hq : q ∈ TM0Route.partrecStartedTM0LabelList tc)
    (hr : r ∈ TM0Route.partrecStartedTM0LabelList tc)
    (hne : r ≠ q) :
    (simRowOfStep tc side' marked' r r' left' right' stmt).matchesInput
        (foldedSimStateCode tc side q) (foldedSymbolCode marked left right) = false := by
  have hstate : foldedSimStateCode tc side' r ≠ foldedSimStateCode tc side q := by
    intro h
    exact hne (foldedSimStateCode_injective_on_labels hr hq h).2
  cases stmt <;> exact mkRow_matchesInput_of_state_ne hstate

theorem simRowOfStep_matchesInput_of_read_ne {tc : Turing.ToPartrec.Code}
    {side : FoldSide} {marked marked' : Bool}
    {q q' : SourceLabel tc} {left right left' right' : SourceSymbol}
    {stmt : Turing.TM0.Stmt SourceSymbol}
    (hread :
      foldedSymbolCode marked' left' right' ≠ foldedSymbolCode marked left right) :
    (simRowOfStep tc side marked' q q' left' right' stmt).matchesInput
        (foldedSimStateCode tc side q) (foldedSymbolCode marked left right) = false := by
  cases stmt <;> exact mkRow_matchesInput_of_read_ne hread

theorem simRowOfStep_state_mem_states (tc : Turing.ToPartrec.Code)
    (side : FoldSide) (marked : Bool)
    {q q' : SourceLabel tc} (hq : q ∈ TM0Route.partrecStartedTM0LabelList tc)
    (left right : SourceSymbol) (stmt : Turing.TM0.Stmt SourceSymbol) :
    (simRowOfStep tc side marked q q' left right stmt).state ∈ foldedStateList tc := by
  cases stmt <;> simp [simRowOfStep, mkRow, foldedSimStateCode_mem_states tc side hq]

theorem simRowOfStep_read_mem_symbols (tc : Turing.ToPartrec.Code)
    (side : FoldSide) (marked : Bool)
    (q q' : SourceLabel tc) (left right : SourceSymbol)
    (stmt : Turing.TM0.Stmt SourceSymbol) :
    (simRowOfStep tc side marked q q' left right stmt).read ∈ foldedSymbolList := by
  cases stmt <;> simp [simRowOfStep, mkRow, foldedSymbolCode_mem_symbols]

theorem simRowOfStep_next_mem_states (tc : Turing.ToPartrec.Code)
    (side : FoldSide) (marked : Bool)
    (q : SourceLabel tc) {q' : SourceLabel tc}
    (hq' : q' ∈ TM0Route.partrecStartedTM0LabelList tc)
    (left right : SourceSymbol) (stmt : Turing.TM0.Stmt SourceSymbol) :
    (simRowOfStep tc side marked q q' left right stmt).next ∈ foldedStateList tc := by
  cases stmt with
  | move dir =>
      simp [simRowOfStep, mkRow,
        foldedSimStateCode_mem_states tc (foldedMoveNextSide side marked dir) hq']
  | write new =>
      simp [simRowOfStep, mkRow, foldedSimStateCode_mem_states tc side hq']

theorem foldedMoveStmt_write_mem_symbols
    (side : FoldSide) (marked : Bool) (cell : Nat) (dir : Turing.Dir)
    (hcell : cell ∈ foldedSymbolList) :
    match foldedMoveStmt side marked cell dir with
    | PostStmt.move _ => True
    | PostStmt.write b => b ∈ foldedSymbolList := by
  cases side <;> cases marked <;> cases dir <;> simp [foldedMoveStmt, hcell]

theorem simRowOfStep_write_mem_symbols (tc : Turing.ToPartrec.Code)
    (side : FoldSide) (marked : Bool)
    (q q' : SourceLabel tc) (left right : SourceSymbol)
    (stmt : Turing.TM0.Stmt SourceSymbol) :
    match (simRowOfStep tc side marked q q' left right stmt).stmt with
    | PostStmt.move _ => True
    | PostStmt.write b => b ∈ foldedSymbolList := by
  cases stmt with
  | move dir =>
      exact foldedMoveStmt_write_mem_symbols side marked
        (foldedSymbolCode marked left right) dir
        (foldedSymbolCode_mem_symbols marked left right)
  | write new =>
      exact foldedWriteForStmt_mem_symbols side marked new left right

def simTransitionOfStep (tc : Turing.ToPartrec.Code)
    (q : SourceLabel tc) (side : FoldSide)
    (marked : Bool) (left right : SourceSymbol) : Option PostTransition :=
  match TM0Route.partrecStartedTM0Machine tc q (foldedRead side left right) with
  | none => none
  | some (q', stmt) => some (simRowOfStep tc side marked q q' left right stmt)

theorem simTransitionOfStep_eq_some_of_step {tc : Turing.ToPartrec.Code}
    {q q' : SourceLabel tc} {side : FoldSide} {marked : Bool}
    {left right : SourceSymbol} {stmt : Turing.TM0.Stmt SourceSymbol}
    (hstep :
      TM0Route.partrecStartedTM0Machine tc q (foldedRead side left right) =
        some (q', stmt)) :
    simTransitionOfStep tc q side marked left right =
      some (simRowOfStep tc side marked q q' left right stmt) := by
  unfold simTransitionOfStep
  rw [hstep]

theorem simTransitionOfStep_eq_none_of_no_step {tc : Turing.ToPartrec.Code}
    {q : SourceLabel tc} {side : FoldSide} {marked : Bool}
    {left right : SourceSymbol}
    (hstep :
      TM0Route.partrecStartedTM0Machine tc q (foldedRead side left right) = none) :
    simTransitionOfStep tc q side marked left right = none := by
  unfold simTransitionOfStep
  rw [hstep]

theorem simTransitionOfStep_matchesInput_of_side_ne {tc : Turing.ToPartrec.Code}
    {q : SourceLabel tc} {side side' : FoldSide} {marked marked' : Bool}
    {left right left' right' : SourceSymbol} {e : PostTransition}
    (hside : side' ≠ side)
    (he : simTransitionOfStep tc q side' marked' left' right' = some e) :
    e.matchesInput (foldedSimStateCode tc side q) (foldedSymbolCode marked left right) =
      false := by
  unfold simTransitionOfStep at he
  split at he
  · cases he
  · rename_i q' stmt hstep
    cases he
    exact simRowOfStep_matchesInput_of_side_ne hside

theorem simTransitionOfStep_matchesInput_of_label_ne {tc : Turing.ToPartrec.Code}
    {q r : SourceLabel tc} {side side' : FoldSide} {marked marked' : Bool}
    {left right left' right' : SourceSymbol} {e : PostTransition}
    (hq : q ∈ TM0Route.partrecStartedTM0LabelList tc)
    (hr : r ∈ TM0Route.partrecStartedTM0LabelList tc)
    (hne : r ≠ q)
    (he : simTransitionOfStep tc r side' marked' left' right' = some e) :
    e.matchesInput (foldedSimStateCode tc side q) (foldedSymbolCode marked left right) =
      false := by
  unfold simTransitionOfStep at he
  split at he
  · cases he
  · rename_i r' stmt hstep
    cases he
    exact simRowOfStep_matchesInput_of_label_ne hq hr hne

theorem simTransitionOfStep_matchesInput_of_read_ne {tc : Turing.ToPartrec.Code}
    {q : SourceLabel tc} {side : FoldSide} {marked marked' : Bool}
    {left right left' right' : SourceSymbol} {e : PostTransition}
    (hread :
      foldedSymbolCode marked' left' right' ≠ foldedSymbolCode marked left right)
    (he : simTransitionOfStep tc q side marked' left' right' = some e) :
    e.matchesInput (foldedSimStateCode tc side q) (foldedSymbolCode marked left right) =
      false := by
  unfold simTransitionOfStep at he
  split at he
  · cases he
  · rename_i q' stmt hstep
    cases he
    exact simRowOfStep_matchesInput_of_read_ne hread

private theorem find?_filterMap_simTransition_right_of_step_aux
    {tc : Turing.ToPartrec.Code}
    {q q' : SourceLabel tc} {side : FoldSide} {marked : Bool}
    {left right : SourceSymbol} {stmt : Turing.TM0.Stmt SourceSymbol}
    (rights : List SourceSymbol) (hright : right ∈ rights)
    (hstep :
      TM0Route.partrecStartedTM0Machine tc q (foldedRead side left right) =
        some (q', stmt)) :
    (rights.filterMap fun r => simTransitionOfStep tc q side marked left r).find?
        (fun e =>
          e.matchesInput (foldedSimStateCode tc side q)
            (foldedSymbolCode marked left right)) =
      some (simRowOfStep tc side marked q q' left right stmt) := by
  induction rights with
  | nil =>
      cases hright
  | cons r rights ih =>
      simp only [List.mem_cons] at hright
      by_cases hrr : r = right
      · subst r
        have hrow := simTransitionOfStep_eq_some_of_step
          (tc := tc) (q := q) (q' := q') (side := side) (marked := marked)
          (left := left) (right := right) (stmt := stmt) hstep
        simp [hrow, simRowOfStep_matchesInput]
      · have hright_tail : right ∈ rights := by
          rcases hright with h | h
          · exact False.elim (hrr h.symm)
          · exact h
        have ih_tail := ih hright_tail
        cases hrow : simTransitionOfStep tc q side marked left r with
        | none =>
            simp [hrow, ih_tail]
        | some e =>
            have hread :
                foldedSymbolCode marked left r ≠ foldedSymbolCode marked left right := by
              intro hcode
              exact hrr (foldedSymbolCode_eq hcode).2.2
            have hmiss := simTransitionOfStep_matchesInput_of_read_ne
              (tc := tc) (q := q) (side := side) (marked := marked)
              (marked' := marked) (left := left) (right := right)
              (left' := left) (right' := r) hread hrow
            simp [hrow, hmiss, ih_tail]

theorem simRowsForLabel_right_find?_of_step
    {tc : Turing.ToPartrec.Code}
    {q q' : SourceLabel tc} {side : FoldSide} {marked : Bool}
    {left right : SourceSymbol} {stmt : Turing.TM0.Stmt SourceSymbol}
    (hstep :
      TM0Route.partrecStartedTM0Machine tc q (foldedRead side left right) =
        some (q', stmt)) :
    (TM0Route.partrecStartedTM0SymbolList.filterMap
        fun r => simTransitionOfStep tc q side marked left r).find?
        (fun e =>
          e.matchesInput (foldedSimStateCode tc side q)
            (foldedSymbolCode marked left right)) =
      some (simRowOfStep tc side marked q q' left right stmt) := by
  exact find?_filterMap_simTransition_right_of_step_aux
    TM0Route.partrecStartedTM0SymbolList
    (TM0Route.mem_partrecStartedTM0SymbolList right) hstep

private theorem find?_filterMap_simTransition_right_eq_none_of_read_ne_aux
    {tc : Turing.ToPartrec.Code}
    {q : SourceLabel tc} {side : FoldSide} {marked marked' : Bool}
    {left left' right : SourceSymbol}
    (rights : List SourceSymbol)
    (hread : ∀ r : SourceSymbol,
      foldedSymbolCode marked' left' r ≠ foldedSymbolCode marked left right) :
    (rights.filterMap fun r => simTransitionOfStep tc q side marked' left' r).find?
        (fun e =>
          e.matchesInput (foldedSimStateCode tc side q)
            (foldedSymbolCode marked left right)) =
      none := by
  induction rights with
  | nil =>
      simp
  | cons r rights ih =>
      cases hrow : simTransitionOfStep tc q side marked' left' r with
      | none =>
          simp [hrow, ih]
      | some e =>
          have hmiss := simTransitionOfStep_matchesInput_of_read_ne
            (tc := tc) (q := q) (side := side) (marked := marked)
            (marked' := marked') (left := left) (right := right)
            (left' := left') (right' := r) (hread r) hrow
          simp [hrow, hmiss, ih]

private theorem find?_filterMap_simTransition_right_eq_none_of_side_ne_aux
    {tc : Turing.ToPartrec.Code}
    {q : SourceLabel tc} {side side' : FoldSide} {marked marked' : Bool}
    {left right left' : SourceSymbol}
    (rights : List SourceSymbol) (hside : side' ≠ side) :
    (rights.filterMap fun r => simTransitionOfStep tc q side' marked' left' r).find?
        (fun e =>
          e.matchesInput (foldedSimStateCode tc side q)
            (foldedSymbolCode marked left right)) =
      none := by
  induction rights with
  | nil =>
      simp
  | cons r rights ih =>
      cases hrow : simTransitionOfStep tc q side' marked' left' r with
      | none =>
          simp [hrow, ih]
      | some e =>
          have hmiss := simTransitionOfStep_matchesInput_of_side_ne
            (tc := tc) (q := q) (side := side) (side' := side')
            (marked := marked) (marked' := marked') (left := left) (right := right)
            (left' := left') (right' := r) hside hrow
          simp [hrow, hmiss, ih]

private theorem find?_flatMap_simTransition_left_of_step_aux
    {tc : Turing.ToPartrec.Code}
    {q q' : SourceLabel tc} {side : FoldSide} {marked : Bool}
    {left right : SourceSymbol} {stmt : Turing.TM0.Stmt SourceSymbol}
    (lefts : List SourceSymbol) (hleft : left ∈ lefts)
    (hstep :
      TM0Route.partrecStartedTM0Machine tc q (foldedRead side left right) =
        some (q', stmt)) :
    (lefts.flatMap fun l =>
        TM0Route.partrecStartedTM0SymbolList.filterMap
          fun r => simTransitionOfStep tc q side marked l r).find?
        (fun e =>
          e.matchesInput (foldedSimStateCode tc side q)
            (foldedSymbolCode marked left right)) =
      some (simRowOfStep tc side marked q q' left right stmt) := by
  induction lefts with
  | nil =>
      cases hleft
  | cons l lefts ih =>
      simp only [List.mem_cons] at hleft
      by_cases hll : l = left
      · subst l
        have hhead := simRowsForLabel_right_find?_of_step
          (tc := tc) (q := q) (q' := q') (side := side) (marked := marked)
          (left := left) (right := right) (stmt := stmt) hstep
        simp only [List.flatMap_cons]
        exact find?_append_of_eq_some hhead
      · have hleft_tail : left ∈ lefts := by
          rcases hleft with h | h
          · exact False.elim (hll h.symm)
          · exact h
        have hhead :
            (TM0Route.partrecStartedTM0SymbolList.filterMap
                fun r => simTransitionOfStep tc q side marked l r).find?
              (fun e =>
                e.matchesInput (foldedSimStateCode tc side q)
                  (foldedSymbolCode marked left right)) = none := by
          exact find?_filterMap_simTransition_right_eq_none_of_read_ne_aux
            (tc := tc) (q := q) (side := side) (marked := marked)
            (marked' := marked) (left := left) (right := right) (left' := l)
            TM0Route.partrecStartedTM0SymbolList
            (by
              intro r hcode
              exact hll (foldedSymbolCode_eq hcode).2.1)
        have htail := ih hleft_tail
        simp only [List.flatMap_cons]
        rw [find?_append_of_eq_none hhead]
        exact htail

theorem simRowsForLabel_left_find?_of_step
    {tc : Turing.ToPartrec.Code}
    {q q' : SourceLabel tc} {side : FoldSide} {marked : Bool}
    {left right : SourceSymbol} {stmt : Turing.TM0.Stmt SourceSymbol}
    (hstep :
      TM0Route.partrecStartedTM0Machine tc q (foldedRead side left right) =
        some (q', stmt)) :
    (TM0Route.partrecStartedTM0SymbolList.flatMap fun l =>
        TM0Route.partrecStartedTM0SymbolList.filterMap
          fun r => simTransitionOfStep tc q side marked l r).find?
        (fun e =>
          e.matchesInput (foldedSimStateCode tc side q)
            (foldedSymbolCode marked left right)) =
      some (simRowOfStep tc side marked q q' left right stmt) := by
  exact find?_flatMap_simTransition_left_of_step_aux
    TM0Route.partrecStartedTM0SymbolList
    (TM0Route.mem_partrecStartedTM0SymbolList left) hstep

private theorem find?_flatMap_simTransition_left_eq_none_of_read_ne_aux
    {tc : Turing.ToPartrec.Code}
    {q : SourceLabel tc} {side : FoldSide} {marked marked' : Bool}
    {left right : SourceSymbol}
    (lefts : List SourceSymbol)
    (hread : ∀ l r : SourceSymbol,
      foldedSymbolCode marked' l r ≠ foldedSymbolCode marked left right) :
    (lefts.flatMap fun l =>
        TM0Route.partrecStartedTM0SymbolList.filterMap
          fun r => simTransitionOfStep tc q side marked' l r).find?
        (fun e =>
          e.matchesInput (foldedSimStateCode tc side q)
            (foldedSymbolCode marked left right)) =
      none := by
  induction lefts with
  | nil =>
      simp
  | cons l lefts ih =>
      have hhead :
          (TM0Route.partrecStartedTM0SymbolList.filterMap
              fun r => simTransitionOfStep tc q side marked' l r).find?
            (fun e =>
              e.matchesInput (foldedSimStateCode tc side q)
                (foldedSymbolCode marked left right)) = none :=
        find?_filterMap_simTransition_right_eq_none_of_read_ne_aux
          (tc := tc) (q := q) (side := side) (marked := marked)
          (marked' := marked') (left := left) (right := right) (left' := l)
          TM0Route.partrecStartedTM0SymbolList (hread l)
      simp only [List.flatMap_cons]
      rw [find?_append_of_eq_none hhead]
      exact ih

private theorem find?_flatMap_simTransition_left_eq_none_of_side_ne_aux
    {tc : Turing.ToPartrec.Code}
    {q : SourceLabel tc} {side side' : FoldSide} {marked marked' : Bool}
    {left right : SourceSymbol}
    (lefts : List SourceSymbol) (hside : side' ≠ side) :
    (lefts.flatMap fun l =>
        TM0Route.partrecStartedTM0SymbolList.filterMap
          fun r => simTransitionOfStep tc q side' marked' l r).find?
        (fun e =>
          e.matchesInput (foldedSimStateCode tc side q)
            (foldedSymbolCode marked left right)) =
      none := by
  induction lefts with
  | nil =>
      simp
  | cons l lefts ih =>
      have hhead :
          (TM0Route.partrecStartedTM0SymbolList.filterMap
              fun r => simTransitionOfStep tc q side' marked' l r).find?
            (fun e =>
              e.matchesInput (foldedSimStateCode tc side q)
                (foldedSymbolCode marked left right)) = none :=
        find?_filterMap_simTransition_right_eq_none_of_side_ne_aux
          (tc := tc) (q := q) (side := side) (side' := side')
          (marked := marked) (marked' := marked') (left := left) (right := right)
          (left' := l) TM0Route.partrecStartedTM0SymbolList hside
      simp only [List.flatMap_cons]
      rw [find?_append_of_eq_none hhead]
      exact ih

private theorem find?_flatMap_simTransition_marked_of_step_aux
    {tc : Turing.ToPartrec.Code}
    {q q' : SourceLabel tc} {side : FoldSide} {marked : Bool}
    {left right : SourceSymbol} {stmt : Turing.TM0.Stmt SourceSymbol}
    (markers : List Bool) (hmarked : marked ∈ markers)
    (hstep :
      TM0Route.partrecStartedTM0Machine tc q (foldedRead side left right) =
        some (q', stmt)) :
    (markers.flatMap fun m =>
        TM0Route.partrecStartedTM0SymbolList.flatMap fun l =>
          TM0Route.partrecStartedTM0SymbolList.filterMap
            fun r => simTransitionOfStep tc q side m l r).find?
        (fun e =>
          e.matchesInput (foldedSimStateCode tc side q)
            (foldedSymbolCode marked left right)) =
      some (simRowOfStep tc side marked q q' left right stmt) := by
  induction markers with
  | nil =>
      cases hmarked
  | cons m markers ih =>
      simp only [List.mem_cons] at hmarked
      by_cases hmm : m = marked
      · subst m
        have hhead := simRowsForLabel_left_find?_of_step
          (tc := tc) (q := q) (q' := q') (side := side) (marked := marked)
          (left := left) (right := right) (stmt := stmt) hstep
        simp only [List.flatMap_cons]
        exact find?_append_of_eq_some hhead
      · have hmarked_tail : marked ∈ markers := by
          rcases hmarked with h | h
          · exact False.elim (hmm h.symm)
          · exact h
        have hhead :
            (TM0Route.partrecStartedTM0SymbolList.flatMap fun l =>
                TM0Route.partrecStartedTM0SymbolList.filterMap
                  fun r => simTransitionOfStep tc q side m l r).find?
              (fun e =>
                e.matchesInput (foldedSimStateCode tc side q)
                  (foldedSymbolCode marked left right)) = none := by
          exact find?_flatMap_simTransition_left_eq_none_of_read_ne_aux
            (tc := tc) (q := q) (side := side) (marked := marked) (marked' := m)
            (left := left) (right := right) TM0Route.partrecStartedTM0SymbolList
            (by
              intro l r hcode
              exact hmm (foldedSymbolCode_eq hcode).1)
        have htail := ih hmarked_tail
        simp only [List.flatMap_cons]
        rw [find?_append_of_eq_none hhead]
        exact htail

theorem simRowsForLabel_marked_find?_of_step
    {tc : Turing.ToPartrec.Code}
    {q q' : SourceLabel tc} {side : FoldSide} {marked : Bool}
    {left right : SourceSymbol} {stmt : Turing.TM0.Stmt SourceSymbol}
    (hstep :
      TM0Route.partrecStartedTM0Machine tc q (foldedRead side left right) =
        some (q', stmt)) :
    ([false, true].flatMap fun m =>
        TM0Route.partrecStartedTM0SymbolList.flatMap fun l =>
          TM0Route.partrecStartedTM0SymbolList.filterMap
            fun r => simTransitionOfStep tc q side m l r).find?
        (fun e =>
          e.matchesInput (foldedSimStateCode tc side q)
            (foldedSymbolCode marked left right)) =
      some (simRowOfStep tc side marked q q' left right stmt) := by
  exact find?_flatMap_simTransition_marked_of_step_aux
    [false, true] (by cases marked <;> simp) hstep

private theorem find?_flatMap_simTransition_marked_eq_none_of_side_ne_aux
    {tc : Turing.ToPartrec.Code}
    {q : SourceLabel tc} {side side' : FoldSide} {marked : Bool}
    {left right : SourceSymbol} (markers : List Bool) (hside : side' ≠ side) :
    (markers.flatMap fun m =>
        TM0Route.partrecStartedTM0SymbolList.flatMap fun l =>
          TM0Route.partrecStartedTM0SymbolList.filterMap
            fun r => simTransitionOfStep tc q side' m l r).find?
        (fun e =>
          e.matchesInput (foldedSimStateCode tc side q)
            (foldedSymbolCode marked left right)) =
      none := by
  induction markers with
  | nil =>
      simp
  | cons m markers ih =>
      have hhead :
          (TM0Route.partrecStartedTM0SymbolList.flatMap fun l =>
              TM0Route.partrecStartedTM0SymbolList.filterMap
                fun r => simTransitionOfStep tc q side' m l r).find?
            (fun e =>
              e.matchesInput (foldedSimStateCode tc side q)
                (foldedSymbolCode marked left right)) = none :=
        find?_flatMap_simTransition_left_eq_none_of_side_ne_aux
          (tc := tc) (q := q) (side := side) (side' := side')
          (marked := marked) (marked' := m) (left := left) (right := right)
          TM0Route.partrecStartedTM0SymbolList hside
      simp only [List.flatMap_cons]
      rw [find?_append_of_eq_none hhead]
      exact ih

private theorem find?_flatMap_simTransition_side_of_step_aux
    {tc : Turing.ToPartrec.Code}
    {q q' : SourceLabel tc} {side : FoldSide} {marked : Bool}
    {left right : SourceSymbol} {stmt : Turing.TM0.Stmt SourceSymbol}
    (sides : List FoldSide) (hside_mem : side ∈ sides)
    (hstep :
      TM0Route.partrecStartedTM0Machine tc q (foldedRead side left right) =
        some (q', stmt)) :
    (sides.flatMap fun s =>
        [false, true].flatMap fun m =>
          TM0Route.partrecStartedTM0SymbolList.flatMap fun l =>
            TM0Route.partrecStartedTM0SymbolList.filterMap
              fun r => simTransitionOfStep tc q s m l r).find?
        (fun e =>
          e.matchesInput (foldedSimStateCode tc side q)
            (foldedSymbolCode marked left right)) =
      some (simRowOfStep tc side marked q q' left right stmt) := by
  induction sides with
  | nil =>
      cases hside_mem
  | cons s sides ih =>
      simp only [List.mem_cons] at hside_mem
      by_cases hss : s = side
      · subst s
        have hhead := simRowsForLabel_marked_find?_of_step
          (tc := tc) (q := q) (q' := q') (side := side) (marked := marked)
          (left := left) (right := right) (stmt := stmt) hstep
        simp only [List.flatMap_cons]
        exact find?_append_of_eq_some hhead
      · have hside_tail : side ∈ sides := by
          rcases hside_mem with h | h
          · exact False.elim (hss h.symm)
          · exact h
        have hhead :
            ([false, true].flatMap fun m =>
                TM0Route.partrecStartedTM0SymbolList.flatMap fun l =>
                  TM0Route.partrecStartedTM0SymbolList.filterMap
                    fun r => simTransitionOfStep tc q s m l r).find?
              (fun e =>
                e.matchesInput (foldedSimStateCode tc side q)
                  (foldedSymbolCode marked left right)) = none :=
          find?_flatMap_simTransition_marked_eq_none_of_side_ne_aux
            (tc := tc) (q := q) (side := side) (side' := s) (marked := marked)
            (left := left) (right := right) [false, true] hss
        have htail := ih hside_tail
        simp only [List.flatMap_cons]
        change (([false, true].flatMap fun m =>
              TM0Route.partrecStartedTM0SymbolList.flatMap fun l =>
                TM0Route.partrecStartedTM0SymbolList.filterMap
                  fun r => simTransitionOfStep tc q s m l r) ++
            (sides.flatMap fun s =>
              [false, true].flatMap fun m =>
                TM0Route.partrecStartedTM0SymbolList.flatMap fun l =>
                  TM0Route.partrecStartedTM0SymbolList.filterMap
                    fun r => simTransitionOfStep tc q s m l r)).find?
              (fun e =>
                e.matchesInput (foldedSimStateCode tc side q)
                  (foldedSymbolCode marked left right)) =
            some (simRowOfStep tc side marked q q' left right stmt)
        rw [find?_append_of_eq_none hhead]
        exact htail

def simRowsForLabel (tc : Turing.ToPartrec.Code) (q : SourceLabel tc) :
    List PostTransition :=
  foldSideList.flatMap fun side =>
    [false, true].flatMap fun marked =>
      TM0Route.partrecStartedTM0SymbolList.flatMap fun left =>
        TM0Route.partrecStartedTM0SymbolList.filterMap fun right =>
          simTransitionOfStep tc q side marked left right

theorem simRowsForLabel_find?_of_step
    {tc : Turing.ToPartrec.Code}
    {q q' : SourceLabel tc} {side : FoldSide} {marked : Bool}
    {left right : SourceSymbol} {stmt : Turing.TM0.Stmt SourceSymbol}
    (hstep :
      TM0Route.partrecStartedTM0Machine tc q (foldedRead side left right) =
        some (q', stmt)) :
    (simRowsForLabel tc q).find?
        (fun e =>
          e.matchesInput (foldedSimStateCode tc side q)
            (foldedSymbolCode marked left right)) =
      some (simRowOfStep tc side marked q q' left right stmt) := by
  unfold simRowsForLabel
  exact find?_flatMap_simTransition_side_of_step_aux
    foldSideList (mem_foldSideList side) hstep

theorem simRowsForLabel_find?_eq_none_of_label_ne
    {tc : Turing.ToPartrec.Code}
    {q r : SourceLabel tc} {side : FoldSide} {marked : Bool}
    {left right : SourceSymbol}
    (hq : q ∈ TM0Route.partrecStartedTM0LabelList tc)
    (hr : r ∈ TM0Route.partrecStartedTM0LabelList tc)
    (hne : r ≠ q) :
    (simRowsForLabel tc r).find?
        (fun e =>
          e.matchesInput (foldedSimStateCode tc side q)
            (foldedSymbolCode marked left right)) =
      none := by
  apply find?_eq_none_of_forall_matchesInput_false
  intro e he
  unfold simRowsForLabel at he
  rw [List.mem_flatMap] at he
  rcases he with ⟨s, _hs, he⟩
  rw [List.mem_flatMap] at he
  rcases he with ⟨m, _hm, he⟩
  rw [List.mem_flatMap] at he
  rcases he with ⟨l, _hl, he⟩
  rw [List.mem_filterMap] at he
  rcases he with ⟨a, _ha, hrow⟩
  exact simTransitionOfStep_matchesInput_of_label_ne
    (tc := tc) (q := q) (r := r) (side := side) (side' := s)
    (marked := marked) (marked' := m) (left := left) (right := right)
    (left' := l) (right' := a) hq hr hne hrow

def simRows (tc : Turing.ToPartrec.Code) : List PostTransition :=
  (TM0Route.partrecStartedTM0LabelList tc).flatMap fun q => simRowsForLabel tc q

private theorem find?_flatMap_simRowsForLabel_of_step_aux
    {tc : Turing.ToPartrec.Code}
    {q q' : SourceLabel tc} {side : FoldSide} {marked : Bool}
    {left right : SourceSymbol} {stmt : Turing.TM0.Stmt SourceSymbol}
    (labels : List (SourceLabel tc))
    (hall : ∀ r, r ∈ labels → r ∈ TM0Route.partrecStartedTM0LabelList tc)
    (hqmem : q ∈ labels)
    (hstep :
      TM0Route.partrecStartedTM0Machine tc q (foldedRead side left right) =
        some (q', stmt)) :
    (labels.flatMap fun r => simRowsForLabel tc r).find?
        (fun e =>
          e.matchesInput (foldedSimStateCode tc side q)
            (foldedSymbolCode marked left right)) =
      some (simRowOfStep tc side marked q q' left right stmt) := by
  induction labels with
  | nil =>
      cases hqmem
  | cons r labels ih =>
      simp only [List.mem_cons] at hqmem
      have hall_tail : ∀ s, s ∈ labels → s ∈ TM0Route.partrecStartedTM0LabelList tc := by
        intro s hs
        exact hall s (by simp [hs])
      by_cases hrq : r = q
      · subst r
        have hhead := simRowsForLabel_find?_of_step
          (tc := tc) (q := q) (q' := q') (side := side) (marked := marked)
          (left := left) (right := right) (stmt := stmt) hstep
        simp only [List.flatMap_cons]
        exact find?_append_of_eq_some hhead
      · have hqmem_tail : q ∈ labels := by
          rcases hqmem with h | h
          · exact False.elim (hrq h.symm)
          · exact h
        have hr : r ∈ TM0Route.partrecStartedTM0LabelList tc :=
          hall r (by simp)
        have hq : q ∈ TM0Route.partrecStartedTM0LabelList tc :=
          hall q (by simp [hqmem])
        have hhead := simRowsForLabel_find?_eq_none_of_label_ne
          (tc := tc) (q := q) (r := r) (side := side) (marked := marked)
          (left := left) (right := right) hq hr hrq
        have htail := ih hall_tail hqmem_tail
        simp only [List.flatMap_cons]
        rw [find?_append_of_eq_none hhead]
        exact htail

theorem simRows_find?_of_step
    {tc : Turing.ToPartrec.Code}
    {q q' : SourceLabel tc} {side : FoldSide} {marked : Bool}
    {left right : SourceSymbol} {stmt : Turing.TM0.Stmt SourceSymbol}
    (hqlist : q ∈ TM0Route.partrecStartedTM0LabelList tc)
    (hstep :
      TM0Route.partrecStartedTM0Machine tc q (foldedRead side left right) =
        some (q', stmt)) :
    (simRows tc).find?
        (fun e =>
          e.matchesInput (foldedSimStateCode tc side q)
            (foldedSymbolCode marked left right)) =
      some (simRowOfStep tc side marked q q' left right stmt) := by
  unfold simRows
  exact find?_flatMap_simRowsForLabel_of_step_aux
    (TM0Route.partrecStartedTM0LabelList tc)
    (fun r hr => hr) hqlist hstep

theorem mem_simRows_state_mem {tc : Turing.ToPartrec.Code} {e : PostTransition}
    (he : e ∈ simRows tc) :
    e.state ∈ foldedStateList tc := by
  unfold simRows simRowsForLabel at he
  rw [List.mem_flatMap] at he
  rcases he with ⟨q, hq, he⟩
  rw [List.mem_flatMap] at he
  rcases he with ⟨side, _hside, he⟩
  rw [List.mem_flatMap] at he
  rcases he with ⟨marked, _hmarked, he⟩
  rw [List.mem_flatMap] at he
  rcases he with ⟨left, _hleft, he⟩
  rw [List.mem_filterMap] at he
  rcases he with ⟨right, _hright, hrow⟩
  unfold simTransitionOfStep at hrow
  split at hrow
  · cases hrow
  · rename_i q' stmt hstep
    cases hrow
    exact simRowOfStep_state_mem_states tc side marked hq left right stmt

theorem mem_simRows_read_mem {tc : Turing.ToPartrec.Code} {e : PostTransition}
    (he : e ∈ simRows tc) :
    e.read ∈ foldedSymbolList := by
  unfold simRows simRowsForLabel at he
  rw [List.mem_flatMap] at he
  rcases he with ⟨q, _hq, he⟩
  rw [List.mem_flatMap] at he
  rcases he with ⟨side, _hside, he⟩
  rw [List.mem_flatMap] at he
  rcases he with ⟨marked, _hmarked, he⟩
  rw [List.mem_flatMap] at he
  rcases he with ⟨left, _hleft, he⟩
  rw [List.mem_filterMap] at he
  rcases he with ⟨right, _hright, hrow⟩
  unfold simTransitionOfStep at hrow
  split at hrow
  · cases hrow
  · rename_i q' stmt hstep
    cases hrow
    exact simRowOfStep_read_mem_symbols tc side marked q q' left right stmt

theorem mem_simRows_next_mem {tc : Turing.ToPartrec.Code} {e : PostTransition}
    (he : e ∈ simRows tc) :
    e.next ∈ foldedStateList tc := by
  unfold simRows simRowsForLabel at he
  rw [List.mem_flatMap] at he
  rcases he with ⟨q, hq, he⟩
  rw [List.mem_flatMap] at he
  rcases he with ⟨side, _hside, he⟩
  rw [List.mem_flatMap] at he
  rcases he with ⟨marked, _hmarked, he⟩
  rw [List.mem_flatMap] at he
  rcases he with ⟨left, _hleft, he⟩
  rw [List.mem_filterMap] at he
  rcases he with ⟨right, _hright, hrow⟩
  unfold simTransitionOfStep at hrow
  split at hrow
  · cases hrow
  · rename_i q' stmt hstep
    cases hrow
    have hqset : q ∈ TM0Route.partrecStartedTM0Labels tc :=
      (TM0Route.mem_partrecStartedTM0LabelList tc q).1 hq
    have hq'set : q' ∈ TM0Route.partrecStartedTM0Labels tc :=
      TM0FiniteCompiler.next_label_mem_of_step hqset hstep
    have hq' : q' ∈ TM0Route.partrecStartedTM0LabelList tc :=
      (TM0Route.mem_partrecStartedTM0LabelList tc q').2 hq'set
    exact simRowOfStep_next_mem_states tc side marked q hq' left right stmt

theorem mem_simRows_write_mem {tc : Turing.ToPartrec.Code} {e : PostTransition}
    (he : e ∈ simRows tc) :
    match e.stmt with
    | PostStmt.move _ => True
    | PostStmt.write b => b ∈ foldedSymbolList := by
  unfold simRows simRowsForLabel at he
  rw [List.mem_flatMap] at he
  rcases he with ⟨q, _hq, he⟩
  rw [List.mem_flatMap] at he
  rcases he with ⟨side, _hside, he⟩
  rw [List.mem_flatMap] at he
  rcases he with ⟨marked, _hmarked, he⟩
  rw [List.mem_flatMap] at he
  rcases he with ⟨left, _hleft, he⟩
  rw [List.mem_filterMap] at he
  rcases he with ⟨right, _hright, hrow⟩
  unfold simTransitionOfStep at hrow
  split at hrow
  · cases hrow
  · rename_i q' stmt hstep
    cases hrow
    exact simRowOfStep_write_mem_symbols tc side marked q q' left right stmt

def program (tc : Turing.ToPartrec.Code) : FiniteTM0Program where
  symbols := foldedSymbolList
  states := foldedStateList tc
  blank := foldedBlank
  start := foldedStartState
  table := initRows tc ++ simRows tc

@[simp]
theorem program_symbols (tc : Turing.ToPartrec.Code) :
    (program tc).symbols = foldedSymbolList := rfl

@[simp]
theorem program_states (tc : Turing.ToPartrec.Code) :
    (program tc).states = foldedStateList tc := rfl

@[simp]
theorem program_blank (tc : Turing.ToPartrec.Code) :
    (program tc).blank = foldedBlank := rfl

@[simp]
theorem program_start (tc : Turing.ToPartrec.Code) :
    (program tc).start = foldedStartState := rfl

@[simp]
theorem program_table (tc : Turing.ToPartrec.Code) :
    (program tc).table = initRows tc ++ simRows tc := rfl

theorem program_blank_mem_symbols (tc : Turing.ToPartrec.Code) :
    (program tc).blank ∈ (program tc).symbols := by
  simp [foldedBlank_mem_symbols]

theorem program_start_mem_states (tc : Turing.ToPartrec.Code) :
    (program tc).start ∈ (program tc).states := by
  simp [foldedStartState_mem_states tc]

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

theorem programHeader_transition?_initWriteRight
    (tc : Turing.ToPartrec.Code) {i : Nat}
    (hi : i < TM0Route.partrecStartedTM0Input.length - 1) :
    (programHeader tc).transition? (initWriteRightState i) foldedBlank =
      some (initWriteRightRow i) := by
  have horigin :
      initWriteOriginRow.matchesInput (initWriteRightState i) foldedBlank = false := by
    unfold initWriteOriginRow
    exact mkRow_matchesInput_of_state_ne (initWriteOriginState_ne_initWriteRightState i)
  have hmove := initMoveRightRows_find?_eq_none_of_initWriteRightState i foldedBlank
  have hwrite := initWriteRightRows_find?_of_mem hi
  unfold PostProgram.transition?
  change (initRows tc).find?
      (fun e => e.matchesInput (initWriteRightState i) foldedBlank) =
    some (initWriteRightRow i)
  unfold initRows
  have htail :
      (initMoveRightRows ++ initWriteRightRows ++ initReturnRows tc).find?
          (fun e => e.matchesInput (initWriteRightState i) foldedBlank) =
        some (initWriteRightRow i) := by
    rw [show initMoveRightRows ++ initWriteRightRows ++ initReturnRows tc =
        initMoveRightRows ++ (initWriteRightRows ++ initReturnRows tc) by
      rw [List.append_assoc]]
    rw [find?_append_of_eq_none hmove]
    exact find?_append_of_eq_some (ys := initReturnRows tc) hwrite
  simpa [horigin] using htail

theorem programHeader_step_initWriteRight
    (tc : Turing.ToPartrec.Code) {i : Nat}
    (hi : i < TM0Route.partrecStartedTM0Input.length - 1) :
    (programHeader tc).step (initWriteRightState i) foldedBlank =
      some (nextAfterWriteRight i,
        PostStmt.write (foldedSymbolCode false default (inputSymbol (i + 1)))) := by
  have hfind := programHeader_transition?_initWriteRight tc hi
  have hnext : nextAfterWriteRight i ∈ foldedStateList tc :=
    nextAfterWriteRight_mem_states tc hi
  have hwrite : foldedSymbolCode false default (inputSymbol (i + 1)) ∈ foldedSymbolList :=
    initWriteRightRow_write_mem_symbols i
  simp [PostProgram.step, hfind, initWriteRightRow, mkRow, hnext, hwrite]

theorem programHeader_transition?_initReturn
    (tc : Turing.ToPartrec.Code) {i read : Nat}
    (hi : i ∈ initReturnIndexList)
    (hread : read ∈ foldedSymbolList) :
    (programHeader tc).transition? (initReturnState i) read =
      some (initReturnRow tc i read) := by
  have horigin :
      initWriteOriginRow.matchesInput (initReturnState i) read = false := by
    unfold initWriteOriginRow
    exact mkRow_matchesInput_of_state_ne (initWriteOriginState_ne_initReturnState i)
  have hmove := initMoveRightRows_find?_eq_none_of_initReturnState i read
  have hwrite := initWriteRightRows_find?_eq_none_of_initReturnState i read
  have hreturn := initReturnRows_find?_of_mem tc hi hread
  unfold PostProgram.transition?
  change (initRows tc).find?
      (fun e => e.matchesInput (initReturnState i) read) =
    some (initReturnRow tc i read)
  unfold initRows
  have htail :
      (initMoveRightRows ++ initWriteRightRows ++ initReturnRows tc).find?
          (fun e => e.matchesInput (initReturnState i) read) =
        some (initReturnRow tc i read) := by
    rw [show initMoveRightRows ++ initWriteRightRows ++ initReturnRows tc =
        initMoveRightRows ++ (initWriteRightRows ++ initReturnRows tc) by
      rw [List.append_assoc]]
    rw [find?_append_of_eq_none hmove]
    rw [find?_append_of_eq_none hwrite]
    exact hreturn
  simpa [horigin] using htail

theorem programHeader_step_initReturn_zero
    (tc : Turing.ToPartrec.Code) {read : Nat}
    (hread : read ∈ foldedSymbolList) :
    (programHeader tc).step (initReturnState 0) read =
      some (foldedSimStartState tc, PostStmt.write read) := by
  have hfind := programHeader_transition?_initReturn tc
    (i := 0) (read := read) (by simp [initReturnIndexList]) hread
  have hnext : foldedSimStartState tc ∈ foldedStateList tc :=
    foldedSimStartState_mem_states tc
  simp [PostProgram.step, hfind, initReturnRow, mkRow, hnext, hread]

theorem programHeader_step_initReturn_succ
    (tc : Turing.ToPartrec.Code) {i read : Nat}
    (hi : i + 1 < TM0Route.partrecStartedTM0Input.length)
    (hread : read ∈ foldedSymbolList) :
    (programHeader tc).step (initReturnState (i + 1)) read =
      some (initReturnState i, PostStmt.move Move.left) := by
  have hidx : i + 1 ∈ initReturnIndexList := by
    simp [initReturnIndexList, List.mem_range.2 hi]
  have hfind := programHeader_transition?_initReturn tc hidx hread
  have hnext : initReturnState i ∈ foldedStateList tc :=
    initReturnState_mem_states (tc := tc) (by omega)
  simp [PostProgram.step, hfind, initReturnRow, mkRow, hnext]

theorem program_transition?_start_blank (tc : Turing.ToPartrec.Code) :
    (program tc).transition? foldedStartState foldedBlank =
      some initWriteOriginRow := by
  have hheader := programHeader_transition?_start_blank tc
  unfold PostProgram.transition? at hheader ⊢
  change (initRows tc).find? (fun e => e.matchesInput foldedStartState foldedBlank) =
    some initWriteOriginRow at hheader
  change (initRows tc ++ simRows tc).find?
      (fun e => e.matchesInput foldedStartState foldedBlank) =
    some initWriteOriginRow
  exact find?_append_of_eq_some hheader

theorem program_step_start_blank (tc : Turing.ToPartrec.Code) :
    (program tc).step foldedStartState foldedBlank =
      some (nextAfterOrigin, PostStmt.write (foldedOriginSymbol (inputSymbol 0))) := by
  have hfind := program_transition?_start_blank tc
  have hnext : nextAfterOrigin ∈ foldedStateList tc :=
    nextAfterOrigin_mem_states tc
  have hwrite : foldedOriginSymbol (inputSymbol 0) ∈ foldedSymbolList :=
    foldedOriginSymbol_mem_symbols (inputSymbol 0)
  simp [PostProgram.step, hfind, initWriteOriginRow, mkRow, hnext, hwrite]

theorem program_transition?_initMoveRight
    (tc : Turing.ToPartrec.Code) {i read : Nat}
    (hi : i < TM0Route.partrecStartedTM0Input.length - 1)
    (hread : read ∈ foldedSymbolList) :
    (program tc).transition? (initMoveRightState i) read =
      some (initMoveRightRow i read) := by
  have hheader := programHeader_transition?_initMoveRight tc hi hread
  unfold PostProgram.transition? at hheader ⊢
  change (initRows tc).find?
      (fun e => e.matchesInput (initMoveRightState i) read) =
    some (initMoveRightRow i read) at hheader
  change (initRows tc ++ simRows tc).find?
      (fun e => e.matchesInput (initMoveRightState i) read) =
    some (initMoveRightRow i read)
  exact find?_append_of_eq_some hheader

theorem program_step_initMoveRight
    (tc : Turing.ToPartrec.Code) {i read : Nat}
    (hi : i < TM0Route.partrecStartedTM0Input.length - 1)
    (hread : read ∈ foldedSymbolList) :
    (program tc).step (initMoveRightState i) read =
      some (initWriteRightState i, PostStmt.move Move.right) := by
  have hfind := program_transition?_initMoveRight tc hi hread
  have hnext : initWriteRightState i ∈ foldedStateList tc :=
    initWriteRightState_mem_states (tc := tc) (by omega)
  simp [PostProgram.step, hfind, initMoveRightRow, mkRow, hnext]

theorem program_transition?_initWriteRight
    (tc : Turing.ToPartrec.Code) {i : Nat}
    (hi : i < TM0Route.partrecStartedTM0Input.length - 1) :
    (program tc).transition? (initWriteRightState i) foldedBlank =
      some (initWriteRightRow i) := by
  have hheader := programHeader_transition?_initWriteRight tc hi
  unfold PostProgram.transition? at hheader ⊢
  change (initRows tc).find?
      (fun e => e.matchesInput (initWriteRightState i) foldedBlank) =
    some (initWriteRightRow i) at hheader
  change (initRows tc ++ simRows tc).find?
      (fun e => e.matchesInput (initWriteRightState i) foldedBlank) =
    some (initWriteRightRow i)
  exact find?_append_of_eq_some hheader

theorem program_step_initWriteRight
    (tc : Turing.ToPartrec.Code) {i : Nat}
    (hi : i < TM0Route.partrecStartedTM0Input.length - 1) :
    (program tc).step (initWriteRightState i) foldedBlank =
      some (nextAfterWriteRight i,
        PostStmt.write (foldedSymbolCode false default (inputSymbol (i + 1)))) := by
  have hfind := program_transition?_initWriteRight tc hi
  have hnext : nextAfterWriteRight i ∈ foldedStateList tc :=
    nextAfterWriteRight_mem_states tc hi
  have hwrite : foldedSymbolCode false default (inputSymbol (i + 1)) ∈ foldedSymbolList :=
    initWriteRightRow_write_mem_symbols i
  simp [PostProgram.step, hfind, initWriteRightRow, mkRow, hnext, hwrite]

theorem program_transition?_initReturn
    (tc : Turing.ToPartrec.Code) {i read : Nat}
    (hi : i ∈ initReturnIndexList)
    (hread : read ∈ foldedSymbolList) :
    (program tc).transition? (initReturnState i) read =
      some (initReturnRow tc i read) := by
  have hheader := programHeader_transition?_initReturn tc hi hread
  unfold PostProgram.transition? at hheader ⊢
  change (initRows tc).find?
      (fun e => e.matchesInput (initReturnState i) read) =
    some (initReturnRow tc i read) at hheader
  change (initRows tc ++ simRows tc).find?
      (fun e => e.matchesInput (initReturnState i) read) =
    some (initReturnRow tc i read)
  exact find?_append_of_eq_some hheader

theorem program_step_initReturn_zero
    (tc : Turing.ToPartrec.Code) {read : Nat}
    (hread : read ∈ foldedSymbolList) :
    (program tc).step (initReturnState 0) read =
      some (foldedSimStartState tc, PostStmt.write read) := by
  have hfind := program_transition?_initReturn tc
    (i := 0) (read := read) (by simp [initReturnIndexList]) hread
  have hnext : foldedSimStartState tc ∈ foldedStateList tc :=
    foldedSimStartState_mem_states tc
  simp [PostProgram.step, hfind, initReturnRow, mkRow, hnext, hread]

theorem program_step_initReturn_succ
    (tc : Turing.ToPartrec.Code) {i read : Nat}
    (hi : i + 1 < TM0Route.partrecStartedTM0Input.length)
    (hread : read ∈ foldedSymbolList) :
    (program tc).step (initReturnState (i + 1)) read =
      some (initReturnState i, PostStmt.move Move.left) := by
  have hidx : i + 1 ∈ initReturnIndexList := by
    simp [initReturnIndexList, List.mem_range.2 hi]
  have hfind := program_transition?_initReturn tc hidx hread
  have hnext : initReturnState i ∈ foldedStateList tc :=
    initReturnState_mem_states (tc := tc) (by omega)
  simp [PostProgram.step, hfind, initReturnRow, mkRow, hnext]

theorem program_transition?_sim_of_step
    {tc : Turing.ToPartrec.Code}
    {q q' : SourceLabel tc} {side : FoldSide} {marked : Bool}
    {left right : SourceSymbol} {stmt : Turing.TM0.Stmt SourceSymbol}
    (hqlist : q ∈ TM0Route.partrecStartedTM0LabelList tc)
    (hstep :
      TM0Route.partrecStartedTM0Machine tc q (foldedRead side left right) =
        some (q', stmt)) :
    (program tc).transition? (foldedSimStateCode tc side q)
        (foldedSymbolCode marked left right) =
      some (simRowOfStep tc side marked q q' left right stmt) := by
  have hinit := initRows_find?_eq_none_of_foldedSimStateCode tc side q
    (foldedSymbolCode marked left right)
  have hsim := simRows_find?_of_step
    (tc := tc) (q := q) (q' := q') (side := side) (marked := marked)
    (left := left) (right := right) (stmt := stmt) hqlist hstep
  unfold PostProgram.transition?
  change (initRows tc ++ simRows tc).find?
      (fun e =>
        e.matchesInput (foldedSimStateCode tc side q)
          (foldedSymbolCode marked left right)) =
    some (simRowOfStep tc side marked q q' left right stmt)
  rw [find?_append_of_eq_none hinit]
  exact hsim

theorem program_step_sim_of_step
    {tc : Turing.ToPartrec.Code}
    {q q' : SourceLabel tc} {side : FoldSide} {marked : Bool}
    {left right : SourceSymbol} {stmt : Turing.TM0.Stmt SourceSymbol}
    (hqlist : q ∈ TM0Route.partrecStartedTM0LabelList tc)
    (hstep :
      TM0Route.partrecStartedTM0Machine tc q (foldedRead side left right) =
        some (q', stmt)) :
    (program tc).step (foldedSimStateCode tc side q)
        (foldedSymbolCode marked left right) =
      some ((simRowOfStep tc side marked q q' left right stmt).next,
        (simRowOfStep tc side marked q q' left right stmt).stmt) := by
  have hfind := program_transition?_sim_of_step
    (tc := tc) (q := q) (q' := q') (side := side) (marked := marked)
    (left := left) (right := right) (stmt := stmt) hqlist hstep
  have hqset : q ∈ TM0Route.partrecStartedTM0Labels tc :=
    (TM0Route.mem_partrecStartedTM0LabelList tc q).1 hqlist
  have hq'set : q' ∈ TM0Route.partrecStartedTM0Labels tc :=
    TM0FiniteCompiler.next_label_mem_of_step hqset hstep
  have hq'list : q' ∈ TM0Route.partrecStartedTM0LabelList tc :=
    (TM0Route.mem_partrecStartedTM0LabelList tc q').2 hq'set
  have hnext :
      (simRowOfStep tc side marked q q' left right stmt).next ∈ foldedStateList tc :=
    simRowOfStep_next_mem_states tc side marked q hq'list left right stmt
  have hwrite := simRowOfStep_write_mem_symbols tc side marked q q' left right stmt
  unfold PostProgram.step
  rw [hfind]
  simp only [program_states, program_symbols, dite_eq_ite, Option.ite_none_right_eq_some]
  constructor
  · exact hnext
  cases hstmt : (simRowOfStep tc side marked q q' left right stmt).stmt with
  | move m =>
      simp
  | write b =>
      have hb : b ∈ foldedSymbolList := by
        simpa [hstmt] using hwrite
      simp [hb]

/-!
## Folded semantic relation

Mathlib's `TM0.Cfg.Tape` is centered at the simulated head, while the local
one-sided program keeps a fixed folded origin. The local head and folded side
therefore determine the simulated head's absolute position in the fixed folded
coordinate system.
-/

def rightAbs (i : Nat) : Int :=
  i

def leftAbs (i : Nat) : Int :=
  -((i : Int) + 1)

def activeAbs : FoldSide → Nat → Int
  | FoldSide.right, h => rightAbs h
  | FoldSide.left, h => leftAbs h

def sourceOffset (side : FoldSide) (head : Nat) (abs : Int) : Int :=
  abs - activeAbs side head

def foldedCellOfTapeAt (T : Turing.Tape SourceSymbol)
    (side : FoldSide) (head i : Nat) : Nat :=
  foldedSymbolCode (decide (i = 0))
    (T.nth (sourceOffset side head (leftAbs i)))
    (T.nth (sourceOffset side head (rightAbs i)))

def FoldedTapeRel (T : Turing.Tape SourceSymbol)
    (side : FoldSide) (head : Nat) (tape : Nat → Nat) : Prop :=
  ∀ i : Nat, tape i = foldedCellOfTapeAt T side head i

def FoldedConfigRel (tc : Turing.ToPartrec.Code)
    (cfg : Turing.TM0.Cfg SourceSymbol (SourceLabel tc)) (id : PostID) : Prop :=
  ∃ side : FoldSide,
    cfg.q ∈ TM0Route.partrecStartedTM0LabelList tc ∧
      id.state = some (foldedSimStateCode tc side cfg.q) ∧
      FoldedTapeRel cfg.Tape side id.head id.tape

@[simp]
theorem sourceOffset_right_head (h : Nat) :
    sourceOffset FoldSide.right h (rightAbs h) = 0 := by
  simp [sourceOffset, activeAbs, rightAbs]

@[simp]
theorem sourceOffset_left_head (h : Nat) :
    sourceOffset FoldSide.left h (leftAbs h) = 0 := by
  simp [sourceOffset, activeAbs, leftAbs]

theorem foldedRead_active_cell (T : Turing.Tape SourceSymbol)
    (side : FoldSide) (head : Nat) :
    foldedRead side
        (T.nth (sourceOffset side head (leftAbs head)))
        (T.nth (sourceOffset side head (rightAbs head))) =
      T.head := by
  cases side <;> simp [foldedRead, Turing.Tape.nth_zero]

theorem sourceOffset_right_left_head_ne_zero (head : Nat) :
    sourceOffset FoldSide.right head (leftAbs head) ≠ 0 := by
  simp [sourceOffset, activeAbs, rightAbs, leftAbs]
  omega

theorem sourceOffset_left_right_head_ne_zero (head : Nat) :
    sourceOffset FoldSide.left head (rightAbs head) ≠ 0 := by
  simp [sourceOffset, activeAbs, rightAbs, leftAbs]
  omega

set_option linter.flexible false in
set_option linter.unusedSimpArgs false in
theorem foldedCellOfTapeAt_write_active (T : Turing.Tape SourceSymbol)
    (side : FoldSide) (head : Nat) (new : SourceSymbol) :
    foldedCellOfTapeAt (T.write new) side head head =
      foldedWriteForStmt side (decide (head = 0)) new
        (T.nth (sourceOffset side head (leftAbs head)))
        (T.nth (sourceOffset side head (rightAbs head))) := by
  cases side
  · by_cases h : head = 0
    · simp [foldedCellOfTapeAt, foldedWriteForStmt, foldedWrite, foldedWriteMarked,
        sourceOffset_left_head, sourceOffset_left_right_head_ne_zero, h]
      change foldedSymbolCode true new
          (T.nth (sourceOffset FoldSide.left 0 (rightAbs 0))) =
        foldedSymbolCode true new
          (T.nth (sourceOffset FoldSide.left 0 (rightAbs 0)))
      rfl
    · simp [foldedCellOfTapeAt, foldedWriteForStmt, foldedWrite, foldedWriteMarked,
        sourceOffset_left_head, sourceOffset_left_right_head_ne_zero, h]
      change foldedSymbolCode false new
          (T.nth (sourceOffset FoldSide.left head (rightAbs head))) =
        foldedSymbolCode false new
          (T.nth (sourceOffset FoldSide.left head (rightAbs head)))
      rfl
  · by_cases h : head = 0
    · simp [foldedCellOfTapeAt, foldedWriteForStmt, foldedWrite, foldedWriteMarked,
        sourceOffset_right_head, sourceOffset_right_left_head_ne_zero, h]
      change foldedSymbolCode true
          (T.nth (sourceOffset FoldSide.right 0 (leftAbs 0))) new =
        foldedSymbolCode true
          (T.nth (sourceOffset FoldSide.right 0 (leftAbs 0))) new
      rfl
    · simp [foldedCellOfTapeAt, foldedWriteForStmt, foldedWrite, foldedWriteMarked,
        sourceOffset_right_head, sourceOffset_right_left_head_ne_zero, h]
      change foldedSymbolCode false
          (T.nth (sourceOffset FoldSide.right head (leftAbs head))) new =
        foldedSymbolCode false
          (T.nth (sourceOffset FoldSide.right head (leftAbs head))) new
      rfl

theorem activeAbs_move_right_regular {head : Nat} (h : head ≠ 0) :
    activeAbs FoldSide.left (head - 1) =
      activeAbs FoldSide.left head + 1 := by
  cases head with
  | zero => exact False.elim (h rfl)
  | succ n =>
      simp [activeAbs, leftAbs]

theorem activeAbs_move_left_regular (head : Nat) :
    activeAbs FoldSide.left (head + 1) =
      activeAbs FoldSide.left head - 1 := by
  simp [activeAbs, leftAbs]
  omega

theorem activeAbs_move_right_from_origin :
    activeAbs FoldSide.right 0 =
      activeAbs FoldSide.left 0 + 1 := by
  simp [activeAbs, leftAbs, rightAbs]

theorem activeAbs_move_left_from_origin :
    activeAbs FoldSide.left 0 =
      activeAbs FoldSide.right 0 - 1 := by
  simp [activeAbs, leftAbs, rightAbs]

theorem activeAbs_move_right_right (head : Nat) :
    activeAbs FoldSide.right (head + 1) =
      activeAbs FoldSide.right head + 1 := by
  simp [activeAbs, rightAbs]

theorem activeAbs_move_left_right {head : Nat} (h : head ≠ 0) :
    activeAbs FoldSide.right (head - 1) =
      activeAbs FoldSide.right head - 1 := by
  cases head with
  | zero => exact False.elim (h rfl)
  | succ n =>
      simp [activeAbs, rightAbs]

theorem FoldedConfigRel_state_some {tc : Turing.ToPartrec.Code}
    {cfg : Turing.TM0.Cfg SourceSymbol (SourceLabel tc)} {id : PostID}
    (hrel : FoldedConfigRel tc cfg id) :
    ∃ side : FoldSide,
      id.state = some (foldedSimStateCode tc side cfg.q) := by
  rcases hrel with ⟨side, _hq, hstate, _htape⟩
  exact ⟨side, hstate⟩

theorem FoldedConfigRel_label_mem {tc : Turing.ToPartrec.Code}
    {cfg : Turing.TM0.Cfg SourceSymbol (SourceLabel tc)} {id : PostID}
    (hrel : FoldedConfigRel tc cfg id) :
    cfg.q ∈ TM0Route.partrecStartedTM0LabelList tc := by
  rcases hrel with ⟨_side, hq, _hstate, _htape⟩
  exact hq

theorem FoldedConfigRel_read_head {tc : Turing.ToPartrec.Code}
    {cfg : Turing.TM0.Cfg SourceSymbol (SourceLabel tc)} {id : PostID}
    (hrel : FoldedConfigRel tc cfg id) :
    ∃ side : FoldSide,
      id.state = some (foldedSimStateCode tc side cfg.q) ∧
        id.tape id.head =
          foldedCellOfTapeAt cfg.Tape side id.head id.head ∧
        foldedRead side
          (cfg.Tape.nth (sourceOffset side id.head (leftAbs id.head)))
          (cfg.Tape.nth (sourceOffset side id.head (rightAbs id.head))) =
            cfg.Tape.head := by
  rcases hrel with ⟨side, _hq, hstate, htape⟩
  exact ⟨side, hstate, htape id.head, foldedRead_active_cell cfg.Tape side id.head⟩

end TM0FoldedCompiler

end LeanWang
