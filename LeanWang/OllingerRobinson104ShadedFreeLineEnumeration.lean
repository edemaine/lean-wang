/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104ShadedFreeGrid

/-!
Finite enumeration of all free rows and columns inside a shaded board.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace ShadedFreeLineEnumeration

open RedCycles RedShadeCycles ShadedFreeGrid ShadedPlaneSignalGrid
  Signals.FreeCellLocal

set_option maxRecDepth 20000

def freeRowBool (indexGrid : Nat → Nat → Index)
    (shadeGrid : Nat → Nat → RedShades.State)
    (west east row : Nat) : Bool :=
  betweenAll (quarterWest west) (quarterEast east) fun quarterX =>
    decide (ShadedSignals.selectedVerticalFor
      (componentAt indexGrid quarterX row) (quadrantAt quarterX row)
      (shadeGrid quarterX row) = none)

def freeColumnBool (indexGrid : Nat → Nat → Index)
    (shadeGrid : Nat → Nat → RedShades.State)
    (south north column : Nat) : Bool :=
  betweenAll (quarterSouth south) (quarterNorth north) fun quarterY =>
    decide (ShadedSignals.selectedHorizontalFor
      (componentAt indexGrid column quarterY) (quadrantAt column quarterY)
      (shadeGrid column quarterY) = none)

theorem freeRowBool_eq_true_iff
    (indexGrid : Nat → Nat → Index)
    (shadeGrid : Nat → Nat → RedShades.State)
    (west east row : Nat) :
    freeRowBool indexGrid shadeGrid west east row = true ↔
      IsFreeRow indexGrid shadeGrid west east row := by
  rw [freeRowBool, RedCycles.betweenAll_eq_true_iff]
  simp only [decide_eq_true_eq]
  rfl

theorem freeColumnBool_eq_true_iff
    (indexGrid : Nat → Nat → Index)
    (shadeGrid : Nat → Nat → RedShades.State)
    (south north column : Nat) :
    freeColumnBool indexGrid shadeGrid south north column = true ↔
      IsFreeColumn indexGrid shadeGrid south north column := by
  rw [freeColumnBool, RedCycles.betweenAll_eq_true_iff]
  simp only [decide_eq_true_eq]
  rfl

def freeRows (indexGrid : Nat → Nat → Index)
    (shadeGrid : Nat → Nat → RedShades.State)
    (west east south north : Nat) : Finset Nat :=
  (Finset.Ioo (quarterSouth south) (quarterNorth north)).filter fun row =>
    freeRowBool indexGrid shadeGrid west east row = true

def freeColumns (indexGrid : Nat → Nat → Index)
    (shadeGrid : Nat → Nat → RedShades.State)
    (west east south north : Nat) : Finset Nat :=
  (Finset.Ioo (quarterWest west) (quarterEast east)).filter fun column =>
    freeColumnBool indexGrid shadeGrid south north column = true

@[simp] theorem mem_freeRows_iff
    {indexGrid : Nat → Nat → Index}
    {shadeGrid : Nat → Nat → RedShades.State}
    {west east south north row : Nat} :
    row ∈ freeRows indexGrid shadeGrid west east south north ↔
      quarterSouth south < row ∧ row < quarterNorth north ∧
        IsFreeRow indexGrid shadeGrid west east row := by
  simp [freeRows, freeRowBool_eq_true_iff]

@[simp] theorem mem_freeColumns_iff
    {indexGrid : Nat → Nat → Index}
    {shadeGrid : Nat → Nat → RedShades.State}
    {west east south north column : Nat} :
    column ∈ freeColumns indexGrid shadeGrid west east south north ↔
      quarterWest west < column ∧ column < quarterEast east ∧
        IsFreeColumn indexGrid shadeGrid south north column := by
  simp [freeColumns, freeColumnBool_eq_true_iff]

theorem FreeGrid.size_le_freeRows_card
    {indexGrid : Nat → Nat → Index}
    {shadeGrid : Nat → Nat → RedShades.State}
    {west east south north size : Nat}
    (freeGrid : FreeGrid indexGrid shadeGrid west east south north size) :
    size ≤ (freeRows indexGrid shadeGrid west east south north).card := by
  let embed : Fin size →
      {row // row ∈ freeRows indexGrid shadeGrid west east south north} :=
    fun i => ⟨freeGrid.rowAt i, (mem_freeRows_iff).2
      ⟨freeGrid.row_south i, freeGrid.row_north i, freeGrid.freeRow i⟩⟩
  have hinjective : Function.Injective embed := by
    intro i j heq
    apply Fin.ext
    by_contra hne
    have hcases : i < j ∨ j < i := lt_or_gt_of_ne hne
    rcases hcases with hij | hji
    · have := freeGrid.row_strictMono hij
      exact (Nat.ne_of_lt this) (congrArg Subtype.val heq)
    · have := freeGrid.row_strictMono hji
      exact (Nat.ne_of_lt this) (congrArg Subtype.val heq).symm
  simpa only [Fintype.card_fin, Fintype.card_coe] using
    Fintype.card_le_of_injective embed hinjective

theorem FreeGrid.size_le_freeColumns_card
    {indexGrid : Nat → Nat → Index}
    {shadeGrid : Nat → Nat → RedShades.State}
    {west east south north size : Nat}
    (freeGrid : FreeGrid indexGrid shadeGrid west east south north size) :
    size ≤ (freeColumns indexGrid shadeGrid west east south north).card := by
  let embed : Fin size →
      {column // column ∈ freeColumns indexGrid shadeGrid west east south north} :=
    fun i => ⟨freeGrid.columnAt i, (mem_freeColumns_iff).2
      ⟨freeGrid.column_west i, freeGrid.column_east i, freeGrid.freeColumn i⟩⟩
  have hinjective : Function.Injective embed := by
    intro i j heq
    apply Fin.ext
    by_contra hne
    have hcases : i < j ∨ j < i := lt_or_gt_of_ne hne
    rcases hcases with hij | hji
    · have := freeGrid.column_strictMono hij
      exact (Nat.ne_of_lt this) (congrArg Subtype.val heq)
    · have := freeGrid.column_strictMono hji
      exact (Nat.ne_of_lt this) (congrArg Subtype.val heq).symm
  simpa only [Fintype.card_fin, Fintype.card_coe] using
    Fintype.card_le_of_injective embed hinjective

end ShadedFreeLineEnumeration
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
