/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlGuardedRouteEmbedding
import LeanWang.Kari.Hooper.CounterControlGuardedGapEmbedding
import LeanWang.Kari.Hooper.CounterControlTargetUniqueness

/-!
# Guarded inward preserving-route margins

The decrement-entry route consists of consecutive leftward searches from
boundary `4` to the boundary immediately after the tested register.  This
file reverses an arbitrary retained suffix of that route from a canonical
endpoint.  The erased predecessor of a guarded caller then turns ordinary
containment into a strict one-cell-extended margin.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlGuardedInwardRouteMargin

open Turing CounterMachine
open BoundedMarkerProgram FramedMarkerTape
open CounterControlPlan CounterControlBridge
open CounterControlCoreFrame CounterControlGlobalUnnesting
open CounterControlGuardedSearch CounterControlGuardedRouteEmbedding
open CounterControlResumedRouteEmbedding
open CounterControlRouteSuffixMortality

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-- Consecutive leftward boundary searches from `source` down to `target`.
The tape at the start and finish of such a route is centered on those two
boundaries respectively. -/
inductive ToBoundary : Fin 5 → Fin 5 →
    List MarkerValidation.Leg → Prop where
  | here (target : Fin 5) : ToBoundary target target []
  | step (i : Fin 4) {target : Fin 5}
      {rest : List MarkerValidation.Leg}
      (tail : ToBoundary i.castSucc target rest) :
      ToBoundary i.succ target (⟨i.castSucc, .left⟩ :: rest)

/-- Any selected position of a nonempty inward route is a leftward leg and
retains an inward route from its found boundary to the original target. -/
theorem ToBoundary.position
    {source target : Fin 5} {route before : List MarkerValidation.Leg}
    {current : MarkerValidation.Leg}
    {remaining : List MarkerValidation.Leg}
    (hroute : ToBoundary source target route)
    (hposition : route = before ++ current :: remaining) :
    ∃ i : Fin 4,
      current = ⟨i.castSucc, .left⟩ ∧
        ToBoundary i.castSucc target remaining := by
  induction hroute generalizing before current remaining with
  | here => simp at hposition
  | step i tail ih =>
      cases before with
      | nil =>
          simp only [List.nil_append, List.cons.injEq] at hposition
          exact ⟨i, hposition.1.symm, hposition.2 ▸ tail⟩
      | cons first before =>
          simp only [List.cons_append, List.cons.injEq] at hposition
          exact ih hposition.2

/-- Every decrement-entry route is one consecutive inward route. -/
theorem routeToDecrementStart_toBoundary (register : Register) :
    ToBoundary 4 (MarkerSchedule.decrementStartBoundary register)
      (AnchoredCounterGeometry.routeToDecrementStart register) := by
  cases register with
  | left => exact .step 3 (.step 2 (.step 1 (.here 1)))
  | right => exact .step 3 (.step 2 (.here 2))
  | temp => exact .step 3 (.here 3)
  | clock => exact .here 4

/-- A successful inward route ending on a canonical boundary started on its
corresponding canonical source boundary. -/
theorem ToBoundary.start_eq
    {registers : Registers} {growth : Turing.Dir}
    {coreTape T finish : FullTM0.Tape (Symbol numTags)}
    {source target : Fin 5} {route : List MarkerValidation.Leg}
    (hcore : CoreRepresents registers growth coreTape)
    (hroute : ToBoundary source target route)
    (hread : T.read = boundarySymbol source)
    (htrace : RouteTailGaps growth route T finish)
    (hfinish : finish =
      atLogical growth coreTape (boundaryOffset registers target)) :
    T = atLogical growth coreTape (boundaryOffset registers source) := by
  induction hroute generalizing T finish with
  | here =>
      cases htrace with
      | nil => exact hfinish
  | step i tail ih =>
      cases htrace with
      | cons _ _ T finish trace =>
          rcases routeGaps_uncons growth ⟨i.castSucc, .left⟩ _ _ _
              trace with ⟨distance, gap, restTrace⟩
          let found :=
            ((T.move (orient growth .left)).moveN
              (orient growth .left) distance)
          have hfoundRead : found.read = boundarySymbol i.castSucc := by
            change (Target.boundary i.castSucc).Matches found.read
            simpa [found, FullTM0.Tape.read_moveN] using gap.marked
          have hfoundCanonical :
              found = atLogical growth coreTape
                (boundaryOffset registers i.castSucc) := by
            exact ih hfoundRead restTrace hfinish
          exact start_eq_of_leftLeg_found hcore i distance hread gap
            hfoundCanonical

/-- Pure coordinate form of strict containment for a guarded caller inside
a consecutive inward decrement-entry route. -/
theorem parentDistance_lt_layoutEnd_of_toBoundary_endpoint
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GuardedSearch base c)
    {growth : Turing.Dir} {source searchSlot directSlot : Nat}
    {after : ControlRef} {route : List MarkerValidation.Leg}
    (progress : GuardedRouteEnd current growth source searchSlot directSlot
      after route)
    {registers : Registers}
    {coreTape : FullTM0.Tape (Symbol numTags)} {target : Fin 5}
    (hcore : CoreRepresents registers growth coreTape)
    (hcenter : progress.suffix.finish =
      atLogical growth coreTape (boundaryOffset registers target))
    (hroute : ToBoundary 4 target route) :
    current.current.distance + 1 < layoutEnd registers := by
  rcases hroute.position progress.suffix.route_eq with
    ⟨i, hcurrent, htail⟩
  have hread : current.foundTape.read = boundarySymbol i.castSucc := by
    have hread' := progress.current_read
    rw [hcurrent] at hread'
    exact hread'
  have hfound : current.foundTape =
      atLogical growth coreTape
        (boundaryOffset registers i.castSucc) := by
    exact htail.start_eq hcore hread progress.suffix.tailGaps hcenter
  have hdirection : current.direction = orient growth .left := by
    have hdirection := current.current.selectedRaw_direction_eq
    rw [CounterControlCommandAt.compileRawCommand_searchDirection]
      at hdirection
    rw [progress.suffix.raw_eq, hcurrent] at hdirection
    exact hdirection.symm
  have htarget : (CounterControlSearchSystem.command base c
      current.current.search).target = Target.boundary i.castSucc := by
    have hcompiled := CounterControlTargetUniqueness.target_eq_of_matches
      current.selectedRaw_target_matches_foundTape
      (show (Target.boundary i.castSucc).Matches current.foundTape.read by
        simpa [Target.Matches] using hread)
    rw [current.compileRawCommand_selectedRaw] at hcompiled
    exact hcompiled
  exact
    CounterControlGuardedGapEmbedding.leftGap_parentDistance_lt_layoutEnd
      current hcore i hdirection htarget hfound

end

end CounterControlGuardedInwardRouteMargin
end Hooper
end Kari
end LeanWang
