/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlSearchSystem

/-!
# Tape geometry of a partially completed cleanup suffix

Each collision-cleanup command searches inward for a boundary, erases it,
and departs one further cell inward.  Looking backward from the new head,
the erased boundary and the entire gap just traversed are blank.  Repeating
the operation concatenates these blank intervals.

The final shared-return dispatcher erases the saved tag and turns around.
Consequently every accumulated blank cell becomes a blank prefix of the
resumed outward search.  This coordinate lemma is independent of the
counter-control table and is the strict-distance core of the direct cleanup
branch in Hooper's unnesting argument.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlCleanupSuffixGeometry

open Turing
open BoundedMarkerProgram

noncomputable section

private instance {numTags : Nat} : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-- Exact tape after finding and erasing a target and departing once farther
in the same direction. -/
def eraseDepart {numTags : Nat}
    (T : FullTM0.Tape (Symbol numTags)) (inward : Turing.Dir)
    (distance : Nat) : FullTM0.Tape (Symbol numTags) :=
  ((T.moveN inward distance).write blankSymbol).move inward

/-- A blank interval immediately behind the current head.  Position `1` is
the first cell in the direction opposite `inward`; position `length` is the
last asserted blank cell. -/
def BlankBehind {numTags : Nat}
    (T : FullTM0.Tape (Symbol numTags)) (inward : Turing.Dir)
    (length : Nat) : Prop :=
  ∀ i : Nat, 0 < i → i ≤ length →
    T (FullTM0.Tape.offset (NestingMachine.opposite inward) i) =
      blankSymbol

@[simp] theorem blankBehind_zero {numTags : Nat}
    (T : FullTM0.Tape (Symbol numTags)) (inward : Turing.Dir) :
    BlankBehind T inward 0 := by
  intro i hi hle
  omega

/-- One erase-and-depart step prepends its traversed gap and erased target to
the blank interval already behind the old head. -/
theorem blankBehind_eraseDepart
    {numTags : Nat} {mark : Symbol numTags → Prop}
    {T : FullTM0.Tape (Symbol numTags)} {inward : Turing.Dir}
    {distance previous : Nat}
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      mark T inward distance)
    (hbehind : BlankBehind T inward previous) :
    BlankBehind (eraseDepart T inward distance) inward
      (distance + 1 + previous) := by
  intro i hi hle
  by_cases hfront : i ≤ distance + 1
  · by_cases hone : i = 1
    · subst i
      cases inward <;>
        simp [eraseDepart, FullTM0.Tape.offset,
          NestingMachine.opposite, FullTM0.Tape.move, FullTM0.Tape.write]
    · have hitwo : 2 ≤ i := by omega
      let k := distance + 1 - i
      have hk : k < distance := by
        dsimp [k]
        omega
      have hblank := hgap.blank hk
      cases hinward : inward with
      | left =>
          rw [hinward] at hblank
          have hcoord :
              (i : Int) - 1 + -(distance : Int) = -(k : Int) := by
            dsimp [k]
            omega
          simp only [eraseDepart, NestingMachine.opposite,
            FullTM0.Tape.offset_right, FullTM0.Tape.move_left_apply,
            FullTM0.Tape.write_apply, FullTM0.Tape.moveN_apply,
            FullTM0.Tape.offset_left]
          rw [if_neg (by omega), hcoord]
          simpa [FullTM0.Tape.offset_left] using hblank
      | right =>
          rw [hinward] at hblank
          have hcoord :
              -(i : Int) + 1 + distance = (k : Int) := by
            dsimp [k]
            omega
          simp only [eraseDepart, NestingMachine.opposite,
            FullTM0.Tape.offset_left, FullTM0.Tape.move_right_apply,
            FullTM0.Tape.write_apply, FullTM0.Tape.moveN_apply,
            FullTM0.Tape.offset_right]
          rw [if_neg (by omega), hcoord]
          simpa [FullTM0.Tape.offset_right] using hblank
  · let j := i - (distance + 1)
    have hjpos : 0 < j := by
      dsimp [j]
      omega
    have hjle : j ≤ previous := by
      dsimp [j]
      omega
    have hblank := hbehind j hjpos hjle
    cases hinward : inward with
    | left =>
        rw [hinward] at hblank
        have hcoord :
            (i : Int) - 1 + -(distance : Int) = (j : Int) := by
          dsimp [j]
          omega
        simp only [eraseDepart, NestingMachine.opposite,
          FullTM0.Tape.offset_right, FullTM0.Tape.move_left_apply,
          FullTM0.Tape.write_apply, FullTM0.Tape.moveN_apply,
          FullTM0.Tape.offset_left]
        rw [if_neg (by omega), hcoord]
        simpa [NestingMachine.opposite, FullTM0.Tape.offset_right] using hblank
    | right =>
        rw [hinward] at hblank
        have hcoord :
            -(i : Int) + 1 + distance = -(j : Int) := by
          dsimp [j]
          omega
        simp only [eraseDepart, NestingMachine.opposite,
          FullTM0.Tape.offset_left, FullTM0.Tape.move_right_apply,
          FullTM0.Tape.write_apply, FullTM0.Tape.moveN_apply,
          FullTM0.Tape.offset_right]
        rw [if_neg (by omega), hcoord]
        simpa [NestingMachine.opposite, FullTM0.Tape.offset_left] using hblank

/-- After the return tag is erased and the head turns around, a blank interval
behind the return head becomes an ordinary blank prefix. -/
theorem blankPrefix_after_return
    {numTags : Nat} {T : FullTM0.Tape (Symbol numTags)}
    {inward : Turing.Dir} {length : Nat}
    (hbehind : BlankBehind T inward length) :
    ∀ i < length,
      ((T.write blankSymbol).move (NestingMachine.opposite inward))
          (FullTM0.Tape.offset (NestingMachine.opposite inward) i) =
        blankSymbol := by
  intro i hi
  have hblank := hbehind (i + 1) (by omega) (by omega)
  cases hinward : inward with
  | left =>
      rw [hinward] at hblank
      simp only [NestingMachine.opposite,
        FullTM0.Tape.offset_right, FullTM0.Tape.move_right_apply]
      rw [FullTM0.Tape.write_apply_of_ne _ _ (by omega)]
      simpa only [NestingMachine.opposite, FullTM0.Tape.offset_right,
        Nat.cast_add, Nat.cast_one] using hblank
  | right =>
      rw [hinward] at hblank
      simp only [NestingMachine.opposite,
        FullTM0.Tape.offset_left, FullTM0.Tape.move_left_apply]
      rw [FullTM0.Tape.write_apply_of_ne _ _ (by omega)]
      simpa only [NestingMachine.opposite, FullTM0.Tape.offset_left,
        Nat.cast_add, Nat.cast_one, neg_add, sub_eq_add_neg] using hblank

/-- Any nonblank-marked search on the returned tape must lie beyond the
entire accumulated blank prefix. -/
theorem distance_ge_of_blankBehind_return
    {numTags : Nat} {mark : Symbol numTags → Prop}
    (hmarkNonblank : ∀ symbol, mark symbol → symbol ≠ blankSymbol)
    {T : FullTM0.Tape (Symbol numTags)} {inward : Turing.Dir}
    {length distance : Nat}
    (hbehind : BlankBehind T inward length)
    (hgap : SearchGap (fun symbol => symbol = blankSymbol) mark
      ((T.write blankSymbol).move (NestingMachine.opposite inward))
      (NestingMachine.opposite inward) distance) :
    length ≤ distance := by
  by_contra hnot
  have hblank := blankPrefix_after_return hbehind distance (by omega)
  have hmarked := hgap.marked
  exact hmarkNonblank _ hmarked hblank

end

end CounterControlCleanupSuffixGeometry
end Hooper
end Kari
end LeanWang
