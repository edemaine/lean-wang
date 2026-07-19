/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlResumedRouteEmbedding

/-!
# Consecutive outward counter routes

This dependency-light module records the combinatorial shape of a consecutive
outward boundary route and its endpoint semantics.  Increment and decrement
arguments can share this algebra without importing one another.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlOutwardRoute

open Turing CounterMachine
open BoundedMarkerProgram FramedMarkerTape
open CounterControlPlan CounterControlBridge
open CounterControlRouteSuffixMortality
open CounterControlResumedRouteEmbedding

noncomputable section

/-- Consecutive rightward legs from `source` through an arbitrary upper
boundary `target`. -/
inductive ToUpper : Fin 5 → Fin 5 → List MarkerValidation.Leg → Prop where
  | here (target : Fin 5) : ToUpper target target []
  | step (i : Fin 4) {target : Fin 5}
      {rest : List MarkerValidation.Leg}
      (tail : ToUpper i.succ target rest) :
      ToUpper i.castSucc target (⟨i.succ, .right⟩ :: rest)

theorem ToUpper.source_le
    {source target : Fin 5} {route : List MarkerValidation.Leg}
    (hroute : ToUpper source target route) :
    (source : Nat) ≤ (target : Nat) := by
  induction hroute with
  | here => simp
  | step i _ ih =>
      exact (show (i.castSucc : Nat) ≤ (i.succ : Nat) by simp).trans ih

/-- A traced consecutive outward route ends centered on its advertised
upper boundary. -/
theorem ToUpper.finish_read
    {growth : Turing.Dir} {source target : Fin 5}
    {route : List MarkerValidation.Leg}
    (hroute : ToUpper source target route)
    {start finish : FullTM0.Tape (Symbol numTags)}
    (hread : start.read = boundarySymbol source)
    (htrace : RouteTailGaps growth route start finish) :
    finish.read = boundarySymbol target := by
  induction hroute generalizing start finish with
  | here =>
      cases htrace
      exact hread
  | step i tail ih =>
      rcases htrace.uncons with ⟨distance, gap, restTrace⟩
      let found :=
        ((start.move (orient growth .right)).moveN
          (orient growth .right) distance)
      have hfoundRead : found.read = boundarySymbol i.succ := by
        change (Target.boundary i.succ).Matches found.read
        simpa [found, FullTM0.Tape.read_moveN] using gap.marked
      exact ih hfoundRead restTrace

/-- Split a route to boundary `4` at any boundary not below its source. -/
theorem ToFour.splitAt
    {source : Fin 5} {route : List MarkerValidation.Leg}
    (hroute : ToFour source route) (target : Fin 5)
    (hle : (source : Nat) ≤ (target : Nat)) :
    ∃ early late,
      route = early ++ late ∧
      ToUpper source target early ∧ ToFour target late := by
  induction hroute generalizing target with
  | four =>
      have htarget : target = 4 := by
        apply Fin.ext
        have hbound := target.isLt
        simp at hle ⊢
        omega
      subst target
      exact ⟨[], [], rfl, .here 4, .four⟩
  | step i tail ih =>
      by_cases htarget : target = i.castSucc
      · subst target
        exact ⟨[], ⟨i.succ, .right⟩ :: _, rfl, .here _, .step i tail⟩
      · have hupper : (i.succ : Nat) ≤ (target : Nat) := by
          have htargetVal : (i.castSucc : Nat) < (target : Nat) := by
            have hne : (i.castSucc : Nat) ≠ (target : Nat) := by
              intro heq
              apply htarget
              exact Fin.ext heq.symm
            omega
          have hstep : (i.succ : Nat) = (i.castSucc : Nat) + 1 := by
            simp
          omega
        rcases ih target hupper with
          ⟨early, late, htail, hearly, hlate⟩
        exact ⟨⟨i.succ, .right⟩ :: early, late, by simp [htail],
          .step i hearly, hlate⟩

theorem ToUpper.eq_nil_of_same
    {source : Fin 5} {route : List MarkerValidation.Leg}
    (hroute : ToUpper source source route) : route = [] := by
  cases hroute with
  | here => rfl
  | step i tail =>
      have hle := tail.source_le
      have hstep : (i.succ : Nat) = (i.castSucc : Nat) + 1 := by simp
      omega

end

end CounterControlOutwardRoute
end Hooper
end Kari
end LeanWang
