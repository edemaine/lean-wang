/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Kari.Hooper.RegisterLayout
import Mathlib.Data.Fintype.Option

/-!
# A finite marker alphabet for the four-register layout

`RegisterLayout` proves the arithmetic of Hooper's sparse four-register
representation using an integer-valued bookkeeping tape.  This file replaces
that bookkeeping tape by the actual finite tape alphabet used by a marker
machine: one blank symbol and five distinctly labelled boundary symbols.

The canonical tape contains boundary `j` exactly at `boundaryPos j`; every
other cell is blank.  In particular, each of the four register gaps supports
rightward and leftward `SearchGap`s on the symbol tape itself.  The labelled
versions identify the precise boundary reached by the search, while the
unlabelled versions expose the common marker predicate used by generic search
machinery.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace MarkerTape

open Turing
open CounterMachine

/-- The core alphabet of the four-register marker representation.  Boundary
labels run from the initial boundary through the four right boundaries. -/
inductive Symbol where
  | blank
  | boundary (index : Fin 5)
  deriving DecidableEq

namespace Symbol

/-- A primitive-recursive sum code for the finite marker alphabet. -/
def equivCode : Symbol ≃ Option (Fin 5) where
  toFun
    | .blank => none
    | .boundary i => some i
  invFun
    | none => .blank
    | some i => .boundary i
  left_inv := by
    intro symbol
    cases symbol <;> rfl
  right_inv := by
    intro code
    cases code <;> rfl

instance : Fintype Symbol :=
  Fintype.ofEquiv (Option (Fin 5)) equivCode.symm

instance : Primcodable Symbol :=
  Primcodable.ofEquiv (Option (Fin 5)) equivCode

end Symbol

/-- Predicate selecting the unique blank symbol. -/
def IsBlank : Symbol → Prop
  | .blank => True
  | .boundary _ => False

/-- Predicate selecting any of the five boundary symbols. -/
def IsBoundary : Symbol → Prop
  | .blank => False
  | .boundary _ => True

/-- Predicate selecting one specified boundary label. -/
def IsBoundaryLabel (j : Fin 5) : Symbol → Prop
  | .blank => False
  | .boundary k => k = j

@[simp] theorem isBlank_blank : IsBlank .blank :=
  trivial

theorem isBlank_iff_eq_blank (symbol : Symbol) :
    IsBlank symbol ↔ symbol = .blank := by
  cases symbol <;> simp [IsBlank]

@[simp] theorem not_isBlank_boundary (j : Fin 5) : ¬ IsBlank (.boundary j) := by
  simp [IsBlank]

@[simp] theorem not_isBoundary_blank : ¬ IsBoundary .blank := by
  simp [IsBoundary]

@[simp] theorem isBoundary_boundary (j : Fin 5) : IsBoundary (.boundary j) :=
  trivial

@[simp] theorem isBoundaryLabel_boundary (i j : Fin 5) :
    IsBoundaryLabel i (.boundary j) ↔ j = i := by
  rfl

@[simp] theorem not_isBoundaryLabel_blank (i : Fin 5) :
    ¬ IsBoundaryLabel i .blank := by
  simp [IsBoundaryLabel]

/-- A specified boundary label is, in particular, a boundary symbol. -/
theorem isBoundary_of_isBoundaryLabel {i : Fin 5} {symbol : Symbol}
    (h : IsBoundaryLabel i symbol) : IsBoundary symbol := by
  cases symbol <;> simp_all [IsBoundaryLabel, IsBoundary]

/-- Absolute integer coordinate of labelled boundary `j`. -/
def boundaryPosition (v : Registers) (j : Fin 5) : Int :=
  CounterLayout.boundaryPos (RegisterLayout.values v) j

/-- Distinct labels have distinct boundary coordinates. -/
theorem boundaryPosition_injective (v : Registers) :
    Function.Injective (boundaryPosition v) := by
  intro i j h
  apply Fin.ext
  apply (CounterLayout.boundaryPos_strictMono (RegisterLayout.values v)).injective
  change (CounterLayout.boundaryPos (RegisterLayout.values v) i : Int) =
    CounterLayout.boundaryPos (RegisterLayout.values v) j at h
  exact_mod_cast h

@[simp] theorem boundaryPosition_start (v : Registers) :
    boundaryPosition v 0 = RegisterLayout.startBoundary v :=
  rfl

@[simp] theorem boundaryPosition_left (v : Registers) :
    boundaryPosition v 1 = RegisterLayout.leftBoundary v :=
  rfl

@[simp] theorem boundaryPosition_right (v : Registers) :
    boundaryPosition v 2 = RegisterLayout.rightBoundary v :=
  rfl

@[simp] theorem boundaryPosition_temp (v : Registers) :
    boundaryPosition v 3 = RegisterLayout.tempBoundary v :=
  rfl

@[simp] theorem boundaryPosition_clock (v : Registers) :
    boundaryPosition v 4 = RegisterLayout.clockBoundary v :=
  rfl

noncomputable section

/-- The canonical full symbol tape for a four-register value.  It has exactly
five marked cells, with label `j` at `boundaryPosition v j`, and is blank at
every other integer coordinate. -/
def canonicalTape (v : Registers) : FullTM0.Tape Symbol :=
  fun position =>
    if h : ∃ j : Fin 5, boundaryPosition v j = position then
      .boundary h.choose
    else
      .blank

/-- Reading a canonical tape at a boundary coordinate returns its label. -/
@[simp]
theorem canonicalTape_boundary (v : Registers) (j : Fin 5) :
    canonicalTape v (boundaryPosition v j) = .boundary j := by
  simp only [canonicalTape]
  split
  next h =>
    have hj : h.choose = j :=
      boundaryPosition_injective v (by simpa using h.choose_spec)
    simp [hj]
  next h =>
    exact (h ⟨j, rfl⟩).elim

/-- A specified boundary label occurs at exactly one coordinate. -/
@[simp]
theorem canonicalTape_eq_boundary_iff (v : Registers) (position : Int)
    (j : Fin 5) :
    canonicalTape v position = .boundary j ↔
      position = boundaryPosition v j := by
  constructor
  · intro hread
    simp only [canonicalTape] at hread
    split at hread
    next h =>
      have hj : h.choose = j := by
        simpa only [Symbol.boundary.injEq] using hread
      simpa [hj] using h.choose_spec.symm
    next _ =>
      contradiction
  · rintro rfl
    exact canonicalTape_boundary v j

/-- A canonical tape cell is blank exactly when it is not one of the five
labelled boundary coordinates. -/
@[simp]
theorem canonicalTape_eq_blank_iff (v : Registers) (position : Int) :
    canonicalTape v position = .blank ↔
      ∀ j : Fin 5, position ≠ boundaryPosition v j := by
  constructor
  · intro hread j hj
    subst position
    simp at hread
  · intro hnone
    simp only [canonicalTape]
    split
    next h =>
      exact (hnone h.choose h.choose_spec.symm).elim
    next _ =>
      rfl

/-- Coordinate-level blankness from `CounterLayout` implies actual symbol
blankness.  This is the basic bridge from the arithmetic layout proofs to the
finite marker tape. -/
theorem canonicalTape_blank_of_coordinateBlank (v : Registers) (position : Int)
    (hblank : CounterLayout.IsBlank (RegisterLayout.values v) position) :
    canonicalTape v position = .blank := by
  rw [canonicalTape_eq_blank_iff]
  intro j hj
  apply hblank
  refine ⟨j, ?_⟩
  simpa [boundaryPosition] using hj

/-- Every cell strictly inside one of the four register gaps is blank. -/
theorem canonicalTape_gapInterior (v : Registers) (i : Fin 4) (k : Nat)
    (hk : k < RegisterLayout.values v i) :
    canonicalTape v
        ((CounterLayout.boundaryPos (RegisterLayout.values v) i : Int) + 1 + k) =
      .blank := by
  have hgap := CounterLayout.searchGap_firstGapCellTape
    (RegisterLayout.values v) i
  have hblank := hgap.blank hk
  simpa [CounterLayout.firstGapCellTape] using
    canonicalTape_blank_of_coordinateBlank v _ hblank

/-- Actual symbol tape with the head at the first cell of gap `i`. -/
def firstGapCellTape (v : Registers) (i : Nat) : FullTM0.Tape Symbol :=
  fun offset => canonicalTape v
    (CounterLayout.firstGapCellTape (RegisterLayout.values v) i offset)

/-- Actual symbol tape with the head at the last cell of gap `i`. -/
def lastGapCellTape (v : Registers) (i : Nat) : FullTM0.Tape Symbol :=
  fun offset => canonicalTape v
    (CounterLayout.lastGapCellTape (RegisterLayout.values v) i offset)

/-- Searching gap `i` to the right reaches precisely its labelled right
boundary after crossing `values v i` blank cells. -/
theorem searchGap_right_label (v : Registers) (i : Fin 4) :
    SearchGap IsBlank (IsBoundaryLabel i.succ) (firstGapCellTape v i)
      .right (RegisterLayout.values v i) := by
  have hgap := CounterLayout.searchGap_firstGapCellTape
    (RegisterLayout.values v) i
  constructor
  · intro k hk
    rw [isBlank_iff_eq_blank]
    unfold firstGapCellTape
    have hblank := canonicalTape_blank_of_coordinateBlank v _ (hgap.blank hk)
    exact hblank
  · change IsBoundaryLabel i.succ (canonicalTape v
      (CounterLayout.firstGapCellTape (RegisterLayout.values v) i
        (FullTM0.Tape.offset .right (RegisterLayout.values v i))))
    have hposition :
        CounterLayout.firstGapCellTape (RegisterLayout.values v) i
            (FullTM0.Tape.offset .right (RegisterLayout.values v i)) =
          boundaryPosition v i.succ := by
      simp only [CounterLayout.firstGapCellTape, FullTM0.Tape.offset_right,
        boundaryPosition]
      exact_mod_cast CounterLayout.firstGapCell_add_value
        (RegisterLayout.values v) i
    rw [hposition, canonicalTape_boundary]
    rfl

/-- Searching gap `i` to the left reaches precisely its labelled left
boundary after crossing `values v i` blank cells. -/
theorem searchGap_left_label (v : Registers) (i : Fin 4) :
    SearchGap IsBlank (IsBoundaryLabel i.castSucc) (lastGapCellTape v i)
      .left (RegisterLayout.values v i) := by
  have hgap := CounterLayout.searchGap_lastGapCellTape
    (RegisterLayout.values v) i
  constructor
  · intro k hk
    rw [isBlank_iff_eq_blank]
    unfold lastGapCellTape
    have hblank := canonicalTape_blank_of_coordinateBlank v _ (hgap.blank hk)
    exact hblank
  · change IsBoundaryLabel i.castSucc (canonicalTape v
      (CounterLayout.lastGapCellTape (RegisterLayout.values v) i
        (FullTM0.Tape.offset .left (RegisterLayout.values v i))))
    have hposition :
        CounterLayout.lastGapCellTape (RegisterLayout.values v) i
            (FullTM0.Tape.offset .left (RegisterLayout.values v i)) =
          boundaryPosition v i.castSucc := by
      have hsucc :
          (CounterLayout.boundaryPos (RegisterLayout.values v) (i + 1) : Int) =
            CounterLayout.boundaryPos (RegisterLayout.values v) i +
              RegisterLayout.values v i + 1 := by
        exact_mod_cast CounterLayout.boundaryPos_succ
          (RegisterLayout.values v) i
      unfold CounterLayout.lastGapCellTape boundaryPosition
      simp only [FullTM0.Tape.offset_left]
      rw [hsucc]
      simp only [Fin.val_castSucc]
      omega
    rw [hposition, canonicalTape_boundary]
    rfl

/-- Unlabelled-marker form of the generic rightward search theorem. -/
theorem searchGap_right (v : Registers) (i : Fin 4) :
    SearchGap IsBlank IsBoundary (firstGapCellTape v i)
      .right (RegisterLayout.values v i) := by
  have h := searchGap_right_label v i
  exact ⟨h.1, isBoundary_of_isBoundaryLabel h.2⟩

/-- Unlabelled-marker form of the generic leftward search theorem. -/
theorem searchGap_left (v : Registers) (i : Fin 4) :
    SearchGap IsBlank IsBoundary (lastGapCellTape v i)
      .left (RegisterLayout.values v i) := by
  have h := searchGap_left_label v i
  exact ⟨h.1, isBoundary_of_isBoundaryLabel h.2⟩

/-- Rightward search across the `left` register gap. -/
theorem searchGap_left_right (v : Registers) :
    SearchGap IsBlank (IsBoundaryLabel 1) (firstGapCellTape v 0)
      .right v.left := by
  simpa using searchGap_right_label v (0 : Fin 4)

/-- Leftward search across the `left` register gap. -/
theorem searchGap_left_left (v : Registers) :
    SearchGap IsBlank (IsBoundaryLabel 0) (lastGapCellTape v 0)
      .left v.left := by
  simpa using searchGap_left_label v (0 : Fin 4)

/-- Rightward search across the `right` register gap. -/
theorem searchGap_right_right (v : Registers) :
    SearchGap IsBlank (IsBoundaryLabel 2) (firstGapCellTape v 1)
      .right v.right := by
  simpa using searchGap_right_label v (1 : Fin 4)

/-- Leftward search across the `right` register gap. -/
theorem searchGap_right_left (v : Registers) :
    SearchGap IsBlank (IsBoundaryLabel 1) (lastGapCellTape v 1)
      .left v.right := by
  simpa using searchGap_left_label v (1 : Fin 4)

/-- Rightward search across the `temp` register gap. -/
theorem searchGap_temp_right (v : Registers) :
    SearchGap IsBlank (IsBoundaryLabel 3) (firstGapCellTape v 2)
      .right v.temp := by
  simpa using searchGap_right_label v (2 : Fin 4)

/-- Leftward search across the `temp` register gap. -/
theorem searchGap_temp_left (v : Registers) :
    SearchGap IsBlank (IsBoundaryLabel 2) (lastGapCellTape v 2)
      .left v.temp := by
  simpa using searchGap_left_label v (2 : Fin 4)

/-- Rightward search across the `clock` register gap. -/
theorem searchGap_clock_right (v : Registers) :
    SearchGap IsBlank (IsBoundaryLabel 4) (firstGapCellTape v 3)
      .right v.clock := by
  simpa using searchGap_right_label v (3 : Fin 4)

/-- Leftward search across the `clock` register gap. -/
theorem searchGap_clock_left (v : Registers) :
    SearchGap IsBlank (IsBoundaryLabel 3) (lastGapCellTape v 3)
      .left v.clock := by
  simpa using searchGap_left_label v (3 : Fin 4)

end

end MarkerTape
end Hooper
end Kari
end LeanWang
