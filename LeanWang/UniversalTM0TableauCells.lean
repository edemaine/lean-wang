/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.MachineTiles
import LeanWang.UniversalTM0Semantic

/-!
# Finite cells for a direct folded TM0 tableau

Cell `i` stores source positions `-(i+1)` and `i`.  The optional head marker
records which half is active and carries the TM0 label.  A source step is thus
a radius-one synchronous update, so these cells can use the existing local
history-block Wang encoding without compiling the TM0 into another machine.
-/

noncomputable section

namespace LeanWang
namespace UniversalTM0Tableau

open UniversalTM0Semantic

abbrev Symbol := Turing.TM2to1.Γ' Stack StackSymbol
abbrev Label := Turing.TM1to0.Λ' tm1

private instance : DecidableEq Symbol := Classical.decEq Symbol
private instance : DecidableEq Label := Classical.decEq Label

def symbols : List Symbol := Finset.univ.toList

theorem mem_symbols (a : Symbol) : a ∈ symbols := by
  simp [symbols]

def labels : List Label := tm0Support.toList

theorem labels_nodup : labels.Nodup := Finset.nodup_toList _

theorem mem_labels_iff (q : Label) : q ∈ labels ↔ q ∈ tm0Support := by
  simp [labels]

theorem default_mem_labels : (default : Label) ∈ labels := by
  rw [mem_labels_iff]
  exact tm0_supports.1

theorem next_mem_labels {q q' : Label} {a : Symbol}
    {stmt : Turing.TM0.Stmt Symbol} (hq : q ∈ labels)
    (hstep : tm0 q a = some (q', stmt)) : q' ∈ labels := by
  rw [mem_labels_iff] at hq ⊢
  have hm : (q', stmt) ∈ tm0 q a := by rw [hstep]; simp
  exact tm0_supports.2 hm hq

inductive Side where
  | left
  | right
deriving DecidableEq, Repr

def sides : List Side := [.left, .right]

theorem mem_sides (side : Side) : side ∈ sides := by
  cases side <;> simp [sides]

def sideCode : Side → Nat
  | .left => 0
  | .right => 1

theorem sideCode_injective : Function.Injective sideCode := by
  intro side other h
  cases side <;> cases other <;> simp_all [sideCode]

def symbolCode (a : Symbol) : Nat := Encodable.encode a

theorem symbolCode_injective : Function.Injective symbolCode :=
  Encodable.encode_injective

def labelCode (q : Label) : Nat := labels.idxOf q

theorem labelCode_injective_on_labels {q r : Label}
    (hq : q ∈ labels) (_hr : r ∈ labels)
    (h : labelCode q = labelCode r) : q = r := by
  exact (List.idxOf_inj hq).1 h

abbrev Head := Option (Side × Label)

def Head.Mem : Head → Prop
  | none => True
  | some (_, q) => q ∈ labels

instance (head : Head) : Decidable head.Mem := by
  cases head with
  | none => exact isTrue trivial
  | some pair => exact inferInstanceAs (Decidable (pair.2 ∈ labels))

def headCode : Head → Nat
  | none => 0
  | some (side, q) => Nat.succ (Nat.pair (sideCode side) (labelCode q))

theorem headCode_injective_on_mem {head other : Head}
    (hhead : head.Mem) (hother : other.Mem)
    (h : headCode head = headCode other) : head = other := by
  cases head with
  | none => cases other <;> simp_all [headCode]
  | some pair =>
      rcases pair with ⟨side, q⟩
      cases other with
      | none => simp [headCode] at h
      | some pair =>
          rcases pair with ⟨otherSide, r⟩
          simp only [headCode, Nat.succ.injEq, Nat.pair_eq_pair] at h
          have hside := sideCode_injective h.1
          have hlabel := labelCode_injective_on_labels hhead hother h.2
          cases hside
          cases hlabel
          rfl

/-- One folded source-tape cell and its optional TM0 head marker. -/
structure Cell where
  left : Symbol
  right : Symbol
  head : Head

namespace Cell

def Mem (cell : Cell) : Prop := cell.head.Mem

instance (cell : Cell) : Decidable cell.Mem :=
  inferInstanceAs (Decidable cell.head.Mem)

def activeSymbol (cell : Cell) (side : Side) : Symbol :=
  match side with
  | .left => cell.left
  | .right => cell.right

def code (cell : Cell) : Nat :=
  Nat.pair (headCode cell.head)
    (Nat.pair (symbolCode cell.left) (symbolCode cell.right))

theorem code_injective_on_mem {cell other : Cell}
    (hcell : cell.Mem) (hother : other.Mem)
    (h : cell.code = other.code) : cell = other := by
  have hp := Nat.pair_eq_pair.mp h
  have hs := Nat.pair_eq_pair.mp hp.2
  rcases cell with ⟨left, right, head⟩
  rcases other with ⟨otherLeft, otherRight, otherHead⟩
  simp only at hcell hother hp hs ⊢
  have hhead := headCode_injective_on_mem hcell hother hp.1
  have hleft := symbolCode_injective hs.1
  have hright := symbolCode_injective hs.2
  cases hhead
  cases hleft
  cases hright
  rfl

def toMachineCell (cell : Cell) : MachineCell := .plain cell.code

theorem toMachineCell_injective_on_mem {cell other : Cell}
    (hcell : cell.Mem) (hother : other.Mem)
    (h : cell.toMachineCell = other.toMachineCell) : cell = other := by
  exact code_injective_on_mem hcell hother (MachineCell.plain.inj h)

end Cell

def heads : List Head :=
  none :: sides.flatMap fun side => labels.map fun q => some (side, q)

theorem mem_heads_iff (head : Head) : head ∈ heads ↔ head.Mem := by
  cases head with
  | none => simp [heads, Head.Mem]
  | some pair =>
      rcases pair with ⟨side, q⟩
      simp [heads, Head.Mem, mem_sides]

def cells : List Cell := do
  let head ← heads
  let left ← symbols
  let right ← symbols
  pure ⟨left, right, head⟩

theorem mem_cells_iff (cell : Cell) : cell ∈ cells ↔ cell.Mem := by
  rcases cell with ⟨left, right, head⟩
  simp [cells, Cell.Mem, mem_heads_iff, mem_symbols]

def machineCells : List MachineCell := cells.map Cell.toMachineCell

theorem toMachineCell_mem {cell : Cell} (hcell : cell.Mem) :
    cell.toMachineCell ∈ machineCells := by
  exact List.mem_map.2 ⟨cell, (mem_cells_iff cell).2 hcell, rfl⟩

theorem exists_cell_of_mem_machineCells {machineCell : MachineCell}
    (hcell : machineCell ∈ machineCells) :
    ∃ cell : Cell, cell.Mem ∧ cell.toMachineCell = machineCell := by
  rcases List.mem_map.1 hcell with ⟨cell, hmem, rfl⟩
  exact ⟨cell, (mem_cells_iff cell).1 hmem, rfl⟩

def blankCell : Cell := ⟨default, default, none⟩

theorem blankCell_mem : blankCell.Mem := trivial

end UniversalTM0Tableau
end LeanWang
