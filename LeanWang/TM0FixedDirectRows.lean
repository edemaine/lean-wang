/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedProgram.FoldedAlphabet

/-!
# Generic rows used by the direct fixed-TM0 simulation

These constructors are independent of the obsolete generated initializer.
-/

namespace LeanWang
namespace TM0FoldedCompiler

def mkRow (state read next : Nat) (stmt : PostStmt) : PostTransition where
  state := state
  read := read
  next := next
  stmt := stmt

theorem mkRow_matchesInput_of_state_ne_data {state state' read read' next : Nat}
    {stmt : PostStmt} (hstate : state ≠ state') :
    (mkRow state read next stmt).matchesInput state' read' = false := by
  simp [mkRow, PostTransition.matchesInput, hstate]

theorem mkRow_matchesInput_of_read_ne {state read read' next : Nat}
    {stmt : PostStmt} (hread : read ≠ read') :
    (mkRow state read next stmt).matchesInput state read' = false := by
  simp [mkRow, PostTransition.matchesInput, hread]

theorem mkRow_primrec :
    Primrec (fun p : Nat × Nat × Nat × PostStmt =>
      mkRow p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  exact PostTransition.mk_primrec

theorem postStmtMove_primrec : Primrec PostStmt.move := by
  exact PostStmt.ofSum_primrec.comp Primrec.sumInl

theorem postStmtWrite_primrec : Primrec PostStmt.write := by
  exact PostStmt.ofSum_primrec.comp Primrec.sumInr

theorem program_find?_append_of_eq_none {α : Type} {xs ys : List α}
    {p : α → Bool} (h : xs.find? p = none) :
    (xs ++ ys).find? p = ys.find? p := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      by_cases hx : p x = true
      · simp [hx] at h
      · simp [hx]
        simpa [hx] using ih (by simpa [hx] using h)

theorem program_find?_append_of_eq_some {α : Type} {xs ys : List α}
    {p : α → Bool} {a : α} (h : xs.find? p = some a) :
    (xs ++ ys).find? p = some a := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
      by_cases hx : p x = true
      · have hxa : x = a := by simpa [hx] using h
        subst a
        simp [hx]
      · simp [hx, ih (by simpa [hx] using h)]

theorem program_find?_eq_none_of_forall_matchesInput_false
    {xs : List PostTransition} {q a : Nat}
    (h : ∀ e ∈ xs, e.matchesInput q a = false) :
    xs.find? (fun e => e.matchesInput q a) = none := by
  induction xs with
  | nil => simp
  | cons e xs ih =>
      have hhead : e.matchesInput q a = false := h e (by simp)
      have htail : xs.find? (fun e => e.matchesInput q a) = none := by
        exact ih fun e he => h e (by simp [he])
      simp [hhead, htail]

end TM0FoldedCompiler
end LeanWang
