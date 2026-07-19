/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlRawCallerClassification
import LeanWang.Kari.Hooper.CounterControlValidationMortality
import LeanWang.Kari.Hooper.CounterControlExactCommandContinuation

/-!
# Preserving route suffixes from an arbitrary generated caller

The route compiler emits a list of preserving boundary searches separated by
one-cell direct moves.  Existing route mortality starts at the first search.
A resumed parent caller, however, can be any search in that list.

This file supplies the suffix form.  It inverts membership in
`routeCommandsAux`, records the exact prefix/current/suffix decomposition,
and follows only the commands after the selected caller.  The resulting
`RouteTailGaps` retains every absolute tape movement, while the endpoint is
the route's original advertised `after` reference.  Thus validation and the
three ordinary recovery families can share one coordinate-preserving API.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlRouteSuffixMortality

open Turing CounterMachine
open BoundedMarkerProgram CounterControlPlan
open CounterControlCommandContinuationMortality
open CounterControlValidationMortality
open CounterControlExactCommandContinuation

noncomputable section

/-- Every command emitted by a marker route is preserving boundary
navigation. -/
theorem boundaryPreserve_of_mem_routeCommandsAux
    (growth : Turing.Dir) (source searchSlot directSlot : Nat)
    (after : ControlRef) (route : List MarkerValidation.Leg)
    {raw : RawCommand}
    (hraw : raw ∈ routeCommandsAux growth source searchSlot directSlot
      after route) :
    ∃ address expected direction success,
      raw = .boundaryNavigation address expected direction success
        .preserve := by
  induction route generalizing searchSlot directSlot with
  | nil => simp [routeCommandsAux] at hraw
  | cons leg route ih =>
      simp only [routeCommandsAux, List.mem_cons] at hraw
      rcases hraw with hhead | htail
      · subst raw
        exact ⟨_, _, _, _, rfl⟩
      · exact ih (searchSlot := searchSlot + 1)
          (directSlot := directSlot + 1) htail

/-- Preserving route commands leave the tape unchanged after their exact
successful continuation. -/
theorem exactSuccessTape_eq_of_mem_routeCommandsAux
    (growth : Turing.Dir) (source searchSlot directSlot : Nat)
    (after : ControlRef) (route : List MarkerValidation.Leg)
    {raw : RawCommand}
    (hraw : raw ∈ routeCommandsAux growth source searchSlot directSlot
      after route)
    (T : FullTM0.Tape (Symbol numTags)) :
    exactSuccessTape raw T = T := by
  rcases boundaryPreserve_of_mem_routeCommandsAux growth source searchSlot
      directSlot after route hraw with
    ⟨address, expected, direction, success, rfl⟩
  rfl

/-- Preserving route commands never have a shift-collision outcome. -/
theorem destinationFree_of_mem_routeCommandsAux
    (growth : Turing.Dir) (source searchSlot directSlot : Nat)
    (after : ControlRef) (route : List MarkerValidation.Leg)
    {raw : RawCommand}
    (hraw : raw ∈ routeCommandsAux growth source searchSlot directSlot
      after route)
    (T : FullTM0.Tape (Symbol numTags)) :
    ¬ ShiftDestinationOccupied raw T := by
  rcases boundaryPreserve_of_mem_routeCommandsAux growth source searchSlot
      directSlot after route hraw with
    ⟨address, expected, direction, success, rfl⟩
  simp [ShiftDestinationOccupied]

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-- Constructor-level statement that a raw command is centered on the
target it just found.  Unlike a compiled-target statement, this does not
depend on a proof of global command membership. -/
def RawTargetMatches (raw : RawCommand)
    (T : FullTM0.Tape (Symbol numTags)) : Prop :=
  match raw with
  | .boundaryNavigation _ expected _ _ _ =>
      T.read = boundarySymbol expected
  | .tagNavigation .. =>
      (Target.anyTag : Target numTags).Matches T.read
  | .markerShift _ expected _ _ _ _ _ =>
      T.read = boundarySymbol expected

/-- The compiled target match implies the corresponding raw-command target
match. -/
theorem rawTargetMatches_of_compiled
    (base : Nat) (c : Nat.Partrec.Code)
    (raw : RawCommand) (hraw : raw ∈ rawCommands)
    (T : FullTM0.Tape (Symbol numTags))
    (hmatch : (CounterControlCommandAt.compileRawCommand base c raw hraw).target.Matches
      T.read) :
    RawTargetMatches raw T := by
  rw [CounterControlCommandAt.compileRawCommand_spec] at hmatch
  cases raw <;>
    simpa [CounterControlCommandAt.compileRawAtTag,
      compileNavigationAction, Command.target,
      RawTargetMatches, Target.Matches] using hmatch

/-- Gap trace after a selected preserving route command has already found
its target and entered its success reference.  A nonempty tail begins with
the direct one-cell departure toward the next route search. -/
inductive RouteTailGaps (growth : Turing.Dir) :
    List MarkerValidation.Leg →
      FullTM0.Tape (Symbol numTags) →
      FullTM0.Tape (Symbol numTags) → Prop where
  | nil (T : FullTM0.Tape (Symbol numTags)) :
      RouteTailGaps growth [] T T
  | cons (next : MarkerValidation.Leg)
      (rest : List MarkerValidation.Leg)
      (T finish : FullTM0.Tape (Symbol numTags))
      (trace : RouteGaps growth (next :: rest)
        (T.move (orient growth next.direction)) finish) :
      RouteTailGaps growth (next :: rest) T finish

/-- An empty route tail does not move the tape. -/
theorem RouteTailGaps.nil_finish
    {growth : Turing.Dir}
    {start finish : FullTM0.Tape (Symbol numTags)}
    (trace : RouteTailGaps growth [] start finish) : finish = start := by
  cases trace
  rfl

/-- Expose the first found tape of a nonempty preserving-route trace. -/
theorem routeGaps_uncons
    (growth : Turing.Dir) (leg : MarkerValidation.Leg)
    (rest : List MarkerValidation.Leg)
    (outer finish : FullTM0.Tape (Symbol numTags))
    (trace : RouteGaps growth (leg :: rest) outer finish) :
    ∃ distance,
      SearchGap (fun symbol => symbol = blankSymbol)
        (Target.boundary leg.target).Matches outer
        (orient growth leg.direction) distance ∧
      RouteTailGaps growth rest
        (outer.moveN (orient growth leg.direction) distance) finish := by
  cases rest with
  | nil =>
      cases trace with
      | last _ _ distance gap => exact ⟨distance, gap, .nil _⟩
  | cons next rest =>
      cases trace with
      | cons _ _ _ _ distance gap finish tail =>
          exact ⟨distance, gap, .cons next rest _ finish tail⟩

/-- Expose the first exact gap of a nonempty preserving-route tail while
retaining the remaining trace in found-state form.  This nondependent
destructor lets finite route proofs avoid eliminating `RouteGaps` directly.
-/
theorem RouteTailGaps.uncons
    {growth : Turing.Dir} {next : MarkerValidation.Leg}
    {rest : List MarkerValidation.Leg}
    {start finish : FullTM0.Tape (Symbol numTags)}
    (trace : RouteTailGaps growth (next :: rest) start finish) :
    ∃ distance,
      SearchGap (fun symbol => symbol = blankSymbol)
        (Target.boundary next.target).Matches
        (start.move (orient growth next.direction))
        (orient growth next.direction) distance ∧
      RouteTailGaps growth rest
        ((start.move (orient growth next.direction)).moveN
          (orient growth next.direction) distance) finish := by
  cases trace with
  | cons _ _ start finish routeTrace =>
      cases rest with
      | nil =>
          cases routeTrace with
          | last _ _ distance gap =>
              exact ⟨distance, gap, .nil _⟩
      | cons following tail =>
          cases routeTrace with
          | cons _ _ _ _ distance gap finish remaining =>
              exact ⟨distance, gap,
                .cons following tail _ finish remaining⟩

/-- Split a nonempty route trace after a nonempty list prefix. -/
theorem routeGaps_split
    (growth : Turing.Dir) (leg : MarkerValidation.Leg)
    (rest late : List MarkerValidation.Leg)
    (outer finish : FullTM0.Tape (Symbol numTags))
    (trace : RouteGaps growth ((leg :: rest) ++ late) outer finish) :
    ∃ middle,
      RouteGaps growth (leg :: rest) outer middle ∧
      RouteTailGaps growth late middle finish := by
  induction rest generalizing leg outer with
  | nil =>
      cases late with
      | nil =>
          exact ⟨finish, by simpa using trace, .nil finish⟩
      | cons next late =>
          cases trace with
          | cons _ _ _ outer distance gap finish tail =>
              let middle := outer.moveN (orient growth leg.direction) distance
              exact ⟨middle, .last leg outer distance gap,
                .cons next late middle finish tail⟩
  | cons next rest ih =>
      cases trace with
      | cons _ _ _ outer distance gap finish tail =>
          rcases ih next
              ((outer.moveN (orient growth leg.direction) distance).move
                (orient growth next.direction)) tail with
            ⟨middle, earlyTrace, lateTrace⟩
          exact ⟨middle,
            .cons leg next rest outer distance gap middle earlyTrace,
            lateTrace⟩

/-- Split a route-tail trace according to a list decomposition. -/
theorem RouteTailGaps.split
    {growth : Turing.Dir}
    {early late : List MarkerValidation.Leg}
    {start finish : FullTM0.Tape (Symbol numTags)}
    (trace : RouteTailGaps growth (early ++ late) start finish) :
    ∃ middle,
      RouteTailGaps growth early start middle ∧
      RouteTailGaps growth late middle finish := by
  cases early with
  | nil => exact ⟨start, .nil start, by simpa using trace⟩
  | cons leg rest =>
      cases trace with
      | cons _ _ start finish routeTrace =>
          rcases routeGaps_split growth leg rest late
              (start.move (orient growth leg.direction)) finish routeTrace with
            ⟨middle, earlyTrace, lateTrace⟩
          exact ⟨middle, .cons leg rest start middle earlyTrace, lateTrace⟩

/-- Success reference selected by one route position. -/
def routeSuffixSuccess (growth : Turing.Dir) (source directSlot : Nat)
    (after : ControlRef) : List MarkerValidation.Leg → ControlRef
  | [] => after
  | _ :: _ => directRef growth source directSlot

/-- Exact position and operational suffix of one selected command in a
preserving route. -/
structure RouteSuffixReached
    (base : Nat) (c : Nat.Partrec.Code)
    (growth : Turing.Dir) (source searchSlot directSlot : Nat)
    (after : ControlRef) (route : List MarkerValidation.Leg)
    (raw : RawCommand) (T : FullTM0.Tape (Symbol numTags)) : Type where
  before : List MarkerValidation.Leg
  current : MarkerValidation.Leg
  remaining : List MarkerValidation.Leg
  route_eq : route = before ++ current :: remaining
  raw_eq : raw = .boundaryNavigation
    ⟨growth, source, searchSlot + before.length⟩
    current.target current.direction
    (routeSuffixSuccess growth source (directSlot + before.length)
      after remaining)
    .preserve
  finish : FullTM0.Tape (Symbol numTags)
  tailGaps : RouteTailGaps growth remaining T finish
  reaches : FullTM0.Reaches
    (CounterControlNestingBridge.machine base c)
    ⟨resolve base c (rawSuccessRef raw), T⟩
    ⟨resolve base c after, finish⟩

/-- An immortal success handoff from any command in a generated preserving
route traverses exactly the remainder of that route.  The hypotheses that
embed route commands and direct continuations in the global plan are kept
abstract so the theorem applies uniformly to validation and all recovery
routes. -/
theorem reaches_routeSuffix_of_immortal
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (growth : Turing.Dir) (source searchSlot directSlot : Nat)
    (after : ControlRef) (route : List MarkerValidation.Leg)
    (raw : RawCommand)
    (hraw : raw ∈ routeCommandsAux growth source searchSlot directSlot
      after route)
    (hcommands : ∀ command,
      command ∈ routeCommandsAux growth source searchSlot directSlot
          after route →
        command ∈ rawCommands)
    (hcontinuations : ∀ rule,
      rule ∈ routeContinuationRules growth source searchSlot directSlot
          route →
        rule ∈ rawDirectRules)
    (T : FullTM0.Tape (Symbol numTags))
    (htarget : RawTargetMatches raw T)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      ⟨resolve base c (rawSuccessRef raw), T⟩) :
    Nonempty (RouteSuffixReached base c growth source searchSlot directSlot
      after route raw T) := by
  induction route generalizing searchSlot directSlot raw with
  | nil => simp [routeCommandsAux] at hraw
  | cons leg route ih =>
      cases route with
      | nil =>
          simp only [routeCommandsAux, List.mem_cons, List.not_mem_nil,
            or_false] at hraw
          subst raw
          refine ⟨⟨[], leg, [], rfl, ?_, T, .nil T, ?_⟩⟩
          · simp [routeSuffixSuccess]
          · change FullTM0.Reaches
              (CounterControlNestingBridge.machine base c)
              ⟨resolve base c after, T⟩ ⟨resolve base c after, T⟩
            exact Relation.ReflTransGen.refl
      | cons next rest =>
          simp only [routeCommandsAux, List.mem_cons] at hraw
          rcases hraw with hhead | htail
          · subst raw
            let handoff := directRef growth source directSlot
            let continuation : RawDirectRule :=
              ⟨growth, handoff, .boundary leg.target,
                searchRef growth source (searchSlot + 1), next.direction⟩
            have hcontinuation : continuation ∈ rawDirectRules := by
              apply hcontinuations continuation
              simp [continuation, handoff, routeContinuationRules,
                routeContinuationRulesFrom]
            have hread :
                (RawRead.boundary leg.target).Matches T.read := by
              simpa [RawTargetMatches, RawRead.Matches] using htarget
            have hdirect : FullTM0.Reaches
                (CounterControlNestingBridge.machine base c)
                ⟨resolve base c handoff, T⟩
                ⟨searchState base c ⟨growth, source, searchSlot + 1⟩,
                  T.move (orient growth next.direction)⟩ := by
              have hrun := CounterControlDirectSemantics.reaches_directRule
                base c continuation hcontinuation T hread
              simpa [BoundedMarkerProgram.machine, CounterControlPlan.table,
                continuation, handoff, searchRef, CounterControlPlan.resolve]
                using hrun
            have himmortalHandoff : FullTM0.ImmortalFrom
                (CounterControlNestingBridge.machine base c)
                ⟨resolve base c handoff, T⟩ := by
              simpa [rawSuccessRef, handoff] using himmortal
            have hcommandsTail : ∀ command,
                command ∈ routeCommandsAux growth source (searchSlot + 1)
                    (directSlot + 1) after (next :: rest) →
                  command ∈ rawCommands := by
              intro command hcommand
              apply hcommands command
              simpa only [routeCommandsAux, List.mem_cons] using
                (Or.inr hcommand)
            have hcontinuationsTail : ∀ rule,
                rule ∈ routeContinuationRules growth source
                    (searchSlot + 1) (directSlot + 1) (next :: rest) →
                  rule ∈ rawDirectRules := by
              intro rule hrule
              apply hcontinuations rule
              simp only [routeContinuationRules, routeContinuationRulesFrom,
                List.mem_cons]
              exact Or.inr hrule
            rcases reaches_routeGaps_of_immortal base c hmortal
                himmortalHandoff growth source (searchSlot + 1)
                (directSlot + 1) after next rest
                (T.move (orient growth next.direction)) hdirect
                hcommandsTail hcontinuationsTail with
              ⟨finish, htrace, hfinish⟩
            refine ⟨⟨[], leg, next :: rest, rfl, ?_, finish,
              .cons next rest T finish htrace, ?_⟩⟩
            · simp [routeSuffixSuccess]
            · simpa [rawSuccessRef, handoff] using hfinish
          · have hcommandsTail : ∀ command,
                command ∈ routeCommandsAux growth source (searchSlot + 1)
                    (directSlot + 1) after (next :: rest) →
                  command ∈ rawCommands := by
              intro command hcommand
              apply hcommands command
              simpa only [routeCommandsAux, List.mem_cons] using
                (Or.inr hcommand)
            have hcontinuationsTail : ∀ rule,
                rule ∈ routeContinuationRules growth source
                    (searchSlot + 1) (directSlot + 1) (next :: rest) →
                  rule ∈ rawDirectRules := by
              intro rule hrule
              apply hcontinuations rule
              simp only [routeContinuationRules, routeContinuationRulesFrom,
                List.mem_cons]
              exact Or.inr hrule
            have htail' : raw ∈ routeCommandsAux growth source
                (searchSlot + 1) (directSlot + 1) after
                (next :: rest) := by
              simpa only [routeCommandsAux, List.mem_cons] using htail
            rcases ih (searchSlot + 1) (directSlot + 1) raw htail'
                hcommandsTail hcontinuationsTail htarget himmortal with
              ⟨suffix⟩
            refine ⟨⟨leg :: suffix.before, suffix.current,
              suffix.remaining, ?_, ?_, suffix.finish, suffix.tailGaps,
              suffix.reaches⟩⟩
            · simp only [List.cons_append]
              rw [← suffix.route_eq]
            · simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm,
                Nat.add_left_comm] using suffix.raw_eq

end

end CounterControlRouteSuffixMortality
end Hooper
end Kari
end LeanWang
