/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlDirectSemantics
import LeanWang.Kari.Hooper.CounterControlNavigationSemantics
import LeanWang.Kari.Hooper.OrientedMarkerTape

/-!
# Semantics of compiled boundary-navigation routes

`CounterControlPlan.routeCommandsAux` compiles every leg of a marker route
to a bounded boundary search.  The entry and continuation rules supply the
one-cell departures between those searches.  This file proves the semantic
compiler theorem: an exact `MarkerValidation.Executes` derivation either
reaches the route's advertised continuation, or the first search whose gap
is too large launches its exact tag-selected canonical frame.

The theorem is parameterized only by inclusion of the generated commands and
direct rules in the global controller enumerations.  Consequently the same
result applies to validation sweeps and to the increment/decrement recovery
routes without duplicating the operational induction.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlRouteSemantics

open Turing
open BoundedMarkerProgram FramedMarkerTape
open CounterControlPlan CounterControlCommandAt

noncomputable section

/-! ## Encoding an oriented marker route -/

/-- A six-symbol marker tape embedded in the tagged controller alphabet and
reflected when the chosen counter copy grows left. -/
def routeTape (growth : Turing.Dir)
    (T : FullTM0.Tape MarkerMachine.Symbol) :
    FullTM0.Tape (Symbol numTags) :=
  encodeTape (OrientedMarkerTape.orientTape growth T)

@[simp]
theorem routeTape_read (growth : Turing.Dir)
    (T : FullTM0.Tape MarkerMachine.Symbol) :
    (routeTape growth T).read = baseSymbol T.read := by
  change baseSymbol (OrientedMarkerTape.orientTape growth T).read =
    baseSymbol T.read
  rw [OrientedMarkerTape.orientTape_read]

@[simp]
theorem routeTape_move (growth logical : Turing.Dir)
    (T : FullTM0.Tape MarkerMachine.Symbol) :
    routeTape growth (T.move logical) =
      (routeTape growth T).move (orient growth logical) := by
  simp [routeTape, CounterControlBridge.orient_eq_orientDirection]

@[simp]
theorem routeTape_moveN (growth logical : Turing.Dir)
    (T : FullTM0.Tape MarkerMachine.Symbol) (distance : Nat) :
    routeTape growth (T.moveN logical distance) =
      (routeTape growth T).moveN (orient growth logical) distance := by
  simp [routeTape, CounterControlBridge.orient_eq_orientDirection]

/-- Boundary search geometry is preserved by embedding the marker alphabet
in the tagged alphabet. -/
theorem searchGap_encode_boundary (growth logical : Turing.Dir)
    (target : Fin 5) (T : FullTM0.Tape MarkerMachine.Symbol)
    (distance : Nat)
    (hgap : SearchGap (fun symbol => symbol = MarkerMachine.blankSymbol)
      (fun symbol => symbol = MarkerMachine.boundarySymbol target)
      T logical distance) :
    SearchGap (fun symbol : Symbol numTags => symbol = blankSymbol)
      (Target.boundary target).Matches
      (routeTape growth T) (orient growth logical) distance := by
  have horiented :=
    (OrientedMarkerTape.searchGap_orient_iff growth logical T distance).2 hgap
  constructor
  · intro i hi
    have hblank := horiented.blank hi
    simpa [routeTape, blankSymbol_eq_baseSymbol] using
      congrArg (@baseSymbol numTags) hblank
  · have hmarked := horiented.marked
    simpa [routeTape, Target.Matches, boundarySymbol_eq_baseSymbol] using
      congrArg (@baseSymbol numTags) hmarked

/-! ## The dependent nested alternative -/

/-- A route outcome in which one of its generated searches is the first far
leg.  The predicate retains the exact raw command, its physical search tape,
the strict distance witness, and the corresponding finite-frame invariant. -/
def NestsDuring (base : Nat) (c : Nat.Partrec.Code)
    (start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State)
    (route : List RawCommand) : Prop :=
  ∃ (raw : RawCommand) (hroute : raw ∈ route)
      (hraw : raw ∈ rawCommands)
      (outer : FullTM0.Tape (Symbol numTags)) (distance : Nat)
      (hfar : NestingMachine.bound (CanonicalInitializer.radius c) < distance),
    FullTM0.Reaches (CounterControlNestingBridge.machine base c) start
        (CounterControlNestingBridge.nestedCfg base c
          (rawTag raw hraw) outer) ∧
      FramedMarkerTape.Represents
        (FramedMarkerTape.frameSpec c
          (compileRawCommand base c raw hraw) distance hfar)
        (FramedMarkerTape.initializeTape c
          (compileRawCommand base c raw hraw) outer)

/-! ## Running a route after its first departure -/

/-- Once the first departure has reached its bounded-search entry, the
compiled search commands and continuation rules execute an arbitrary exact
marker route. -/
private theorem searches_reach_or_nests
    (base : Nat) (c : Nat.Partrec.Code) (growth : Turing.Dir)
    (counterState searchSlot directSlot : Nat) (after : ControlRef)
    (first : MarkerValidation.Leg) (rest : List MarkerValidation.Leg)
    (T U : FullTM0.Tape MarkerMachine.Symbol)
    (hexec : MarkerValidation.Executes (first :: rest) T U)
    (hcommands : ∀ raw,
      raw ∈ routeCommandsAux growth counterState searchSlot directSlot
          after (first :: rest) →
        raw ∈ rawCommands)
    (hcontinuations : ∀ rule,
      rule ∈ routeContinuationRules growth counterState searchSlot
          directSlot (first :: rest) →
        rule ∈ rawDirectRules) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨growth, counterState, searchSlot⟩,
          routeTape growth (T.move first.direction)⟩
        ⟨resolve base c after, routeTape growth U⟩ ∨
      NestsDuring base c
        ⟨searchState base c ⟨growth, counterState, searchSlot⟩,
          routeTape growth (T.move first.direction)⟩
        (routeCommandsAux growth counterState searchSlot directSlot after
          (first :: rest)) := by
  induction rest generalizing first T U searchSlot directSlot with
  | nil =>
      cases hexec with
      | cons _ _ _ V _ hfirst hrest =>
          cases hrest
          rcases hfirst with ⟨distance, hgap, hfinish⟩
          let raw : RawCommand :=
            .boundaryNavigation ⟨growth, counterState, searchSlot⟩
              first.target first.direction after .preserve
          have hroute : raw ∈ routeCommandsAux growth counterState
              searchSlot directSlot after [first] := by
            simp [raw, routeCommandsAux]
          have hraw : raw ∈ rawCommands := hcommands raw hroute
          have hencoded := searchGap_encode_boundary growth first.direction
            first.target (T.move first.direction) distance hgap
          have hrun :=
            CounterControlNavigationSemantics.machine_reaches_boundary_preserve_or_nests
              base c ⟨growth, counterState, searchSlot⟩ first.target
              first.direction after hraw
              (routeTape growth (T.move first.direction)) distance hencoded
          rcases hrun with hnear | hfar
          · left
            simpa [raw, hfinish, routeTape_moveN] using hnear
          · right
            rcases hfar with ⟨hfar, hreach, hframe⟩
            exact ⟨raw, hroute, hraw,
              routeTape growth (T.move first.direction), distance, hfar,
              hreach, hframe⟩
  | cons next tail ih =>
      cases hexec with
      | cons _ _ _ V _ hfirst hrest =>
          rcases hfirst with ⟨distance, hgap, hfinish⟩
          let handoff : ControlRef :=
            directRef growth counterState directSlot
          let raw : RawCommand :=
            .boundaryNavigation ⟨growth, counterState, searchSlot⟩
              first.target first.direction handoff .preserve
          let continuation : RawDirectRule :=
            ⟨growth, handoff, .boundary first.target,
              searchRef growth counterState (searchSlot + 1), next.direction⟩
          have hroute : raw ∈ routeCommandsAux growth counterState
              searchSlot directSlot after (first :: next :: tail) := by
            simp [raw, handoff, routeCommandsAux]
          have hraw : raw ∈ rawCommands := hcommands raw hroute
          have hcontinuationRoute : continuation ∈
              routeContinuationRules growth counterState searchSlot
                directSlot (first :: next :: tail) := by
            simp [continuation, handoff, routeContinuationRules,
              routeContinuationRulesFrom]
          have hcontinuation : continuation ∈ rawDirectRules :=
            hcontinuations continuation hcontinuationRoute
          have hencoded := searchGap_encode_boundary growth first.direction
            first.target (T.move first.direction) distance hgap
          have hrun :=
            CounterControlNavigationSemantics.machine_reaches_boundary_preserve_or_nests
              base c ⟨growth, counterState, searchSlot⟩ first.target
              first.direction handoff hraw
              (routeTape growth (T.move first.direction)) distance hencoded
          rcases hrun with hnear | hfar
          · have hVread : V.read = MarkerMachine.boundarySymbol first.target := by
              rw [hfinish]
              simpa [FullTM0.Tape.read] using hgap.marked
            have hmatch : continuation.read.Matches
                (routeTape growth V).read := by
              change (routeTape growth V).read = boundarySymbol first.target
              rw [routeTape_read, hVread, boundarySymbol_eq_baseSymbol]
            have hdirectLocal :=
              CounterControlDirectSemantics.reaches_directRule base c
                continuation hcontinuation (routeTape growth V) hmatch
            have hdirect : FullTM0.Reaches
                (CounterControlNestingBridge.machine base c)
                ⟨resolve base c handoff, routeTape growth V⟩
                ⟨searchState base c
                    ⟨growth, counterState, searchSlot + 1⟩,
                  routeTape growth (V.move next.direction)⟩ := by
              simpa [CounterControlNestingBridge.machine,
                BoundedMarkerProgram.machine, CounterControlPlan.table,
                continuation, handoff, searchRef,
                CounterControlPlan.resolve, routeTape_move] using hdirectLocal
            have hcommandsTail : ∀ command,
                command ∈ routeCommandsAux growth counterState
                    (searchSlot + 1) (directSlot + 1) after
                    (next :: tail) →
                  command ∈ rawCommands := by
              intro command hcommand
              apply hcommands command
              exact List.mem_cons_of_mem _ hcommand
            have hcontinuationsTail : ∀ rule,
                rule ∈ routeContinuationRules growth counterState
                    (searchSlot + 1) (directSlot + 1) (next :: tail) →
                  rule ∈ rawDirectRules := by
              intro rule hrule
              apply hcontinuations rule
              simp only [routeContinuationRules,
                routeContinuationRulesFrom, List.mem_cons]
              exact Or.inr hrule
            have htail := ih (first := next) (T := V) (U := U)
              (searchSlot := searchSlot + 1)
              (directSlot := directSlot + 1) hrest
              hcommandsTail hcontinuationsTail
            have hprefix : FullTM0.Reaches
                (CounterControlNestingBridge.machine base c)
                ⟨searchState base c
                    ⟨growth, counterState, searchSlot⟩,
                  routeTape growth (T.move first.direction)⟩
                ⟨searchState base c
                    ⟨growth, counterState, searchSlot + 1⟩,
                  routeTape growth (V.move next.direction)⟩ := by
              have hnear' : FullTM0.Reaches
                  (CounterControlNestingBridge.machine base c)
                  ⟨searchState base c
                      ⟨growth, counterState, searchSlot⟩,
                    routeTape growth (T.move first.direction)⟩
                  ⟨resolve base c handoff, routeTape growth V⟩ := by
                simpa [raw, handoff, hfinish, routeTape_moveN] using hnear
              exact hnear'.trans hdirect
            rcases htail with hsuccess | hnested
            · left
              exact hprefix.trans hsuccess
            · right
              rcases hnested with
                ⟨nestedRaw, hnestedRoute, hnestedRaw,
                  outer, nestedDistance, nestedFar, hnestedReach, hnestedFrame⟩
              refine ⟨nestedRaw, ?_, hnestedRaw, outer, nestedDistance,
                nestedFar, hprefix.trans hnestedReach, hnestedFrame⟩
              exact List.mem_cons_of_mem _ hnestedRoute
          · right
            rcases hfar with ⟨hfar, hreach, hframe⟩
            exact ⟨raw, hroute, hraw,
              routeTape growth (T.move first.direction), distance, hfar,
              hreach, hframe⟩

/-! ## Complete routes, including their entry departure -/

/-- Compile an exact nonempty marker route from an arbitrary direct or
logical source state.  If all bounded gaps are nearby, execution reaches the
advertised `after` state on the exact encoded, oriented finish tape.  If a
gap is far, execution instead reaches the first selected nested frame. -/
theorem route_reaches_or_nests
    (base : Nat) (c : Nat.Partrec.Code) (growth : Turing.Dir)
    (counterState searchSlot directSlot : Nat)
    (source after : ControlRef) (sourceBoundary : Fin 5)
    (first : MarkerValidation.Leg) (rest : List MarkerValidation.Leg)
    (T U : FullTM0.Tape MarkerMachine.Symbol)
    (hsource : T.read = MarkerMachine.boundarySymbol sourceBoundary)
    (hexec : MarkerValidation.Executes (first :: rest) T U)
    (hcommands : ∀ raw,
      raw ∈ routeCommandsAux growth counterState searchSlot directSlot
          after (first :: rest) →
        raw ∈ rawCommands)
    (hrules : ∀ rule,
      rule ∈
          routeEntryRules growth counterState source sourceBoundary searchSlot
              (first :: rest) ++
            routeContinuationRules growth counterState searchSlot directSlot
              (first :: rest) →
        rule ∈ rawDirectRules) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨resolve base c source, routeTape growth T⟩
        ⟨resolve base c after, routeTape growth U⟩ ∨
      NestsDuring base c
        ⟨resolve base c source, routeTape growth T⟩
        (routeCommandsAux growth counterState searchSlot directSlot after
          (first :: rest)) := by
  let entry : RawDirectRule :=
    ⟨growth, source, .boundary sourceBoundary,
      searchRef growth counterState searchSlot, first.direction⟩
  have hentryRoute : entry ∈
      routeEntryRules growth counterState source sourceBoundary searchSlot
        (first :: rest) := by
    simp [entry, routeEntryRules]
  have hentry : entry ∈ rawDirectRules := by
    apply hrules entry
    exact List.mem_append_left _ hentryRoute
  have hmatch : entry.read.Matches (routeTape growth T).read := by
    change (routeTape growth T).read = boundarySymbol sourceBoundary
    rw [routeTape_read, hsource, boundarySymbol_eq_baseSymbol]
  have hentryLocal := CounterControlDirectSemantics.reaches_directRule
    base c entry hentry (routeTape growth T) hmatch
  have hentryReach : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      ⟨resolve base c source, routeTape growth T⟩
      ⟨searchState base c ⟨growth, counterState, searchSlot⟩,
        routeTape growth (T.move first.direction)⟩ := by
    simpa [CounterControlNestingBridge.machine, BoundedMarkerProgram.machine,
      CounterControlPlan.table, entry, searchRef,
      CounterControlPlan.resolve, routeTape_move] using hentryLocal
  have hcontinuations : ∀ rule,
      rule ∈ routeContinuationRules growth counterState searchSlot
          directSlot (first :: rest) →
        rule ∈ rawDirectRules := by
    intro rule hrule
    apply hrules rule
    exact List.mem_append_right _ hrule
  have hsearches := searches_reach_or_nests base c growth counterState
    searchSlot directSlot after first rest T U hexec hcommands hcontinuations
  rcases hsearches with hsuccess | hnested
  · left
    exact hentryReach.trans hsuccess
  · right
    rcases hnested with
      ⟨raw, hroute, hraw, outer, distance, hfar, hreach, hframe⟩
    exact ⟨raw, hroute, hraw, outer, distance, hfar,
      hentryReach.trans hreach, hframe⟩

end

end CounterControlRouteSemantics
end Hooper
end Kari
end LeanWang
