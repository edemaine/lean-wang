/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlInstructionSemantics

/-!
# Resolving compiled counter-controller searches

The forward instruction semantics assumes that every strictly shorter search
reaches its found state.  For the converse direction, Hooper's simultaneous
induction instead supplies `SearchSystem.Resolves`: every shorter search
either reaches that same found state or makes the complete controller halt.

This file lifts that dichotomy through a compiled raw search, its preserving
continuation, and an arbitrary nonempty marker route.  Whenever a later route
leg halts, `FullTM0.HaltsFrom.of_reaches` prepends the already executed route
prefix.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlSearchResolution

open Turing CounterMachine
open BoundedMarkerProgram FramedMarkerTape FramedCounterGeometry
open CounterControlPlan CounterControlCommandAt CounterControlBridge
open CounterControlInstructionSemantics

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-- Every genuine compiled search shorter than `limit` either finds its
target or makes the complete controller halt. -/
def ShortResolves (base : Nat) (c : Nat.Partrec.Code) (limit : Nat) : Prop :=
  ∀ j < limit,
    (CounterControlSearchSystem.searchSystem base c).Resolves j

/-! ## Resolving one compiled search -/

/-- A generated raw search at a strictly shorter distance either reaches its
native `foundState`, or the complete controller halts from that exact search
configuration. -/
theorem rawSearch_reaches_found_or_halts
    (base : Nat) (c : Nat.Partrec.Code) (limit : Nat)
    (hshort : ShortResolves base c limit)
    (raw : RawCommand) (hraw : raw ∈ rawCommands)
    (outer : FullTM0.Tape (Symbol numTags)) (distance : Nat)
    (hdistance : distance < limit)
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (compileRawCommand base c raw hraw).target.Matches outer
      (compileRawCommand base c raw hraw).searchDirection distance) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨searchState base c raw.address, outer⟩
        ⟨foundState (CanonicalInitializer.radius c)
            (searchState base c raw.address),
          outer.moveN
            (compileRawCommand base c raw hraw).searchDirection distance⟩ ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨searchState base c raw.address, outer⟩ := by
  have hresolve := hshort distance hdistance
    (rawTag raw hraw) outer
  have hgap' : SearchGap
      (CounterControlSearchSystem.searchSystem base c).isBlank
      ((CounterControlSearchSystem.searchSystem base c).isMark
        (rawTag raw hraw)) outer
      ((CounterControlSearchSystem.searchSystem base c).direction
        (rawTag raw hraw)) distance := by
    simpa [CounterControlSearchSystem.searchSystem,
      CounterControlSearchSystem.command, compileRawCommand] using hgap
  have hrun := hresolve hgap'
  change
    (FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨CounterControlSearchSystem.commandOffset base c (rawTag raw hraw),
          outer⟩
        ⟨foundState (CanonicalInitializer.radius c)
            (CounterControlSearchSystem.commandOffset base c
              (rawTag raw hraw)),
          outer.moveN
            (CounterControlSearchSystem.command base c
              (rawTag raw hraw)).searchDirection distance⟩ ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨CounterControlSearchSystem.commandOffset base c (rawTag raw hraw),
          outer⟩) at hrun
  have hoffset : CounterControlSearchSystem.commandOffset base c
      (rawTag raw hraw) = searchState base c raw.address := by
    unfold CounterControlSearchSystem.commandOffset
    rw [rawCommands_get_rawTag]
  have hcommand : CounterControlSearchSystem.command base c
      (rawTag raw hraw) = compileRawCommand base c raw hraw := rfl
  rw [hoffset, hcommand] at hrun
  exact hrun

/-- Resolving-search form of a preserving boundary command.  The continuation
is executed only in the successful branch; an already halting search is
returned unchanged. -/
theorem machine_reaches_boundary_preserve_or_halts
    (base : Nat) (c : Nat.Partrec.Code) (limit : Nat)
    (hshort : ShortResolves base c limit)
    (address : SearchAddress) (expected : Fin 5)
    (direction : Turing.Dir) (success : ControlRef)
    (hraw : RawCommand.boundaryNavigation address expected direction success
      .preserve ∈ rawCommands)
    (outer : FullTM0.Tape (Symbol numTags)) (distance : Nat)
    (hdistance : distance < limit)
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary expected).Matches outer
      (orient address.growth direction) distance) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨searchState base c address, outer⟩
        ⟨resolve base c success,
          outer.moveN (orient address.growth direction) distance⟩ ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨searchState base c address, outer⟩ := by
  let raw : RawCommand :=
    .boundaryNavigation address expected direction success .preserve
  have hspec := compileRawCommand_spec base c raw hraw
  have hcompiledGap : SearchGap (fun symbol => symbol = blankSymbol)
      (compileRawCommand base c raw hraw).target.Matches outer
      (compileRawCommand base c raw hraw).searchDirection distance := by
    rw [hspec]
    simpa [raw, compileRawAtTag, Command.target,
      Command.searchDirection, compileNavigationAction] using hgap
  have hsearch := rawSearch_reaches_found_or_halts base c limit hshort
    raw hraw outer distance hdistance hcompiledGap
  rcases hsearch with hfound | hhalts
  · left
    have hfound' : FullTM0.Reaches
        (CounterControlNestingBridge.machine base c)
        ⟨searchState base c address, outer⟩
        ⟨foundState (CanonicalInitializer.radius c)
            (searchState base c address),
          outer.moveN (orient address.growth direction) distance⟩ := by
      rw [hspec] at hfound
      simpa [raw, compileRawAtTag, RawCommand.address,
        Command.searchDirection, compileNavigationAction] using hfound
    have hatRaw := CommandAt.compileRawCommand base c raw hraw
    have hat : CommandAt (CanonicalInitializer.radius c) base
        (searchState base c address)
        (.boundaryNavigation expected (orient address.growth direction)
          (resolve base c success) (rawTag raw hraw) .preserve)
        (commands base c) := by
      rw [hspec] at hatRaw
      simpa [raw, compileRawAtTag, RawCommand.address,
        compileNavigationAction] using hatRaw
    have hmatch : (Target.boundary expected).Matches
        (outer.moveN (orient address.growth direction) distance).read := by
      simpa [FullTM0.Tape.moveN, FullTM0.Tape.read] using hgap.marked
    have hcontinue :=
      BoundedMarkerContinuation.machine_reaches_navigation_native
        (coreTable base c) (Target.boundary expected)
        (orient address.growth direction) (resolve base c success)
        (rawTag raw hraw) hat
        (outer.moveN (orient address.growth direction) distance) hmatch
    exact hfound'.trans hcontinue
  · right
    simpa [raw, RawCommand.address] using hhalts

/-! ## Resolving marker routes -/

/-- Extract the concrete search gap of one route leg and bound its length by
the active outer-search distance. -/
private theorem legExecutesAt_depart_below
    {growth : Turing.Dir} {T : FullTM0.Tape (Symbol numTags)}
    {leg : MarkerValidation.Leg} {source finish limit : Nat}
    (h : LegExecutesAt growth T leg source finish)
    (hsource : source < limit) (hfinish : finish < limit) :
    ∃ distance,
      distance < limit ∧
      SearchGap (fun symbol => symbol = blankSymbol)
        (Target.boundary leg.target).Matches
        ((atLogical growth T source).move (orient growth leg.direction))
        (orient growth leg.direction) distance ∧
      ((atLogical growth T source).move
          (orient growth leg.direction)).moveN
          (orient growth leg.direction) distance =
        atLogical growth T finish := by
  cases hdirection : leg.direction with
  | right =>
      rw [LegExecutesAt, hdirection] at h
      rcases h with ⟨distance, hgap, hfinishEq⟩
      refine ⟨distance, by omega, ?_, ?_⟩
      · simpa only [orient_eq_orientDirection,
          atLogical_move_right] using hgap
      · rw [orient_eq_orientDirection, atLogical_move_right,
          atLogical_moveN_right, hfinishEq]
        apply congrArg (atLogical growth T)
        omega
  | left =>
      rw [LegExecutesAt, hdirection] at h
      rcases h with ⟨distance, hsourceEq, hgap⟩
      refine ⟨distance, by omega, ?_, ?_⟩
      · rw [hsourceEq, orient_eq_orientDirection,
          atLogical_move_left]
        exact hgap
      · rw [hsourceEq, orient_eq_orientDirection,
          atLogical_move_left, atLogical_moveN_left]

/-- Once the route's entry rule has entered its first search, every leg
resolves in sequence.  A halting later leg is pulled back across all earlier
successful legs. -/
private theorem searches_reach_or_halt_at
    (base : Nat) (c : Nat.Partrec.Code) (limit : Nat)
    (hshort : ShortResolves base c limit) (growth : Turing.Dir)
    (counterState searchSlot directSlot : Nat) (after : ControlRef)
    (first : MarkerValidation.Leg) (rest : List MarkerValidation.Leg)
    (T : FullTM0.Tape (Symbol numTags)) (source finish : Nat)
    (hexec : RouteExecutesWithin growth T limit (first :: rest)
      source finish)
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
          (atLogical growth T source).move
            (orient growth first.direction)⟩
        ⟨resolve base c after, atLogical growth T finish⟩ ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨growth, counterState, searchSlot⟩,
          (atLogical growth T source).move
            (orient growth first.direction)⟩ := by
  induction rest generalizing first source finish searchSlot directSlot with
  | nil =>
      cases hexec with
      | cons _ _ _ middle _ hsource hfirst hrest =>
        cases hrest with
        | nil _ hmiddle =>
          rcases legExecutesAt_depart_below hfirst hsource hmiddle with
            ⟨distance, hdistance, hgap, hfound⟩
          let raw : RawCommand :=
            .boundaryNavigation ⟨growth, counterState, searchSlot⟩
              first.target first.direction after .preserve
          have hroute : raw ∈ routeCommandsAux growth counterState
              searchSlot directSlot after [first] := by
            simp [raw, routeCommandsAux]
          have hraw : raw ∈ rawCommands := hcommands raw hroute
          have hrun := machine_reaches_boundary_preserve_or_halts
            base c limit hshort ⟨growth, counterState, searchSlot⟩
            first.target first.direction after hraw
            ((atLogical growth T source).move
              (orient growth first.direction)) distance hdistance hgap
          rw [hfound] at hrun
          exact hrun
  | cons next tail ih =>
      cases hexec with
      | cons _ _ _ middle _ hsource hfirst hrest =>
        have hmiddle := RouteExecutesWithin.start_lt hrest
        rcases legExecutesAt_depart_below hfirst hsource hmiddle with
          ⟨distance, hdistance, hgap, hfound⟩
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
        have hsearch := machine_reaches_boundary_preserve_or_halts
          base c limit hshort ⟨growth, counterState, searchSlot⟩
          first.target first.direction handoff hraw
          ((atLogical growth T source).move
            (orient growth first.direction)) distance hdistance hgap
        rcases hsearch with hsearch | hhalts
        · have hsearch' : FullTM0.Reaches
              (CounterControlNestingBridge.machine base c)
              ⟨searchState base c ⟨growth, counterState, searchSlot⟩,
                (atLogical growth T source).move
                  (orient growth first.direction)⟩
              ⟨resolve base c handoff, atLogical growth T middle⟩ := by
            rw [hfound] at hsearch
            exact hsearch
          have hmatch : continuation.read.Matches
              (atLogical growth T middle).read := by
            change (atLogical growth T middle).read =
              boundarySymbol first.target
            change (Target.boundary first.target).Matches
              (atLogical growth T middle).read
            rw [← hfound]
            simpa [FullTM0.Tape.moveN, FullTM0.Tape.read] using hgap.marked
          have hdirectLocal :=
            CounterControlDirectSemantics.reaches_directRule base c
              continuation hcontinuation (atLogical growth T middle) hmatch
          have hdirect : FullTM0.Reaches
              (CounterControlNestingBridge.machine base c)
              ⟨resolve base c handoff, atLogical growth T middle⟩
              ⟨searchState base c
                  ⟨growth, counterState, searchSlot + 1⟩,
                (atLogical growth T middle).move
                  (orient growth next.direction)⟩ := by
            simpa [CounterControlNestingBridge.machine,
              BoundedMarkerProgram.machine, CounterControlPlan.table,
              continuation, handoff, searchRef,
              CounterControlPlan.resolve] using hdirectLocal
          have hcommandsTail : ∀ command,
              command ∈ routeCommandsAux growth counterState
                  (searchSlot + 1) (directSlot + 1) after (next :: tail) →
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
            simp only [routeContinuationRules, routeContinuationRulesFrom,
              List.mem_cons]
            exact Or.inr hrule
          have htail := ih
            (first := next) (source := middle) (finish := finish)
            (searchSlot := searchSlot + 1)
            (directSlot := directSlot + 1) hrest hcommandsTail
            hcontinuationsTail
          have hprefix := hsearch'.trans hdirect
          rcases htail with hsuccess | htailHalts
          · exact Or.inl (hprefix.trans hsuccess)
          · exact Or.inr
              (FullTM0.HaltsFrom.of_reaches hprefix htailHalts)
        · exact Or.inr hhalts

/-- Compile a nonempty marker route under the shorter-search resolution
hypothesis.  The route reaches its advertised continuation, or the complete
controller halts from the route's original logical configuration. -/
theorem route_reaches_or_halts_at
    (base : Nat) (c : Nat.Partrec.Code) (limit : Nat)
    (hshort : ShortResolves base c limit) (growth : Turing.Dir)
    (counterState searchSlot directSlot : Nat)
    (source after : ControlRef) (sourceBoundary : Fin 5)
    (first : MarkerValidation.Leg) (rest : List MarkerValidation.Leg)
    (T : FullTM0.Tape (Symbol numTags)) (sourcePosition finishPosition : Nat)
    (hsource : (atLogical growth T sourcePosition).read =
      boundarySymbol sourceBoundary)
    (hexec : RouteExecutesWithin growth T limit (first :: rest)
      sourcePosition finishPosition)
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
        ⟨resolve base c source, atLogical growth T sourcePosition⟩
        ⟨resolve base c after, atLogical growth T finishPosition⟩ ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨resolve base c source, atLogical growth T sourcePosition⟩ := by
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
  have hmatch : entry.read.Matches
      (atLogical growth T sourcePosition).read := by
    change (atLogical growth T sourcePosition).read =
      boundarySymbol sourceBoundary
    exact hsource
  have hentryLocal := CounterControlDirectSemantics.reaches_directRule
    base c entry hentry (atLogical growth T sourcePosition) hmatch
  have hentryReach : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      ⟨resolve base c source, atLogical growth T sourcePosition⟩
      ⟨searchState base c ⟨growth, counterState, searchSlot⟩,
        (atLogical growth T sourcePosition).move
          (orient growth first.direction)⟩ := by
    simpa [CounterControlNestingBridge.machine, BoundedMarkerProgram.machine,
      CounterControlPlan.table, entry, searchRef,
      CounterControlPlan.resolve] using hentryLocal
  have hcontinuations : ∀ rule,
      rule ∈ routeContinuationRules growth counterState searchSlot
          directSlot (first :: rest) →
        rule ∈ rawDirectRules := by
    intro rule hrule
    apply hrules rule
    exact List.mem_append_right _ hrule
  have hsearches := searches_reach_or_halt_at base c limit hshort growth
    counterState searchSlot directSlot after first rest T sourcePosition
    finishPosition hexec hcommands hcontinuations
  rcases hsearches with hsuccess | hhalts
  · exact Or.inl (hentryReach.trans hsuccess)
  · exact Or.inr (FullTM0.HaltsFrom.of_reaches hentryReach hhalts)

end

end CounterControlSearchResolution
end Hooper
end Kari
end LeanWang
