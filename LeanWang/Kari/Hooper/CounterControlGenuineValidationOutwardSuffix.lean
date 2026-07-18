/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlGenuineValidation

/-!
# Geometry retained by an outward validation suffix

Every outward validation obligation starts on one of boundaries `1` through
`4` and retains the consecutive rightward route from that boundary to
boundary `4`.  This module exposes that common dependent package so the
instruction-specific continuations do not need four nearly identical finite
position arguments.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlGenuineValidationOutwardSuffix

open Turing CounterMachine
open BoundedMarkerProgram CounterControlPlan
open CounterControlGlobalUnnesting
open CounterControlGenuineRouteEmbedding
open CounterControlGenuineValidation
open CounterControlRouteSuffixMortality
open CounterControlResumedRouteEmbedding
open CounterControlParentContinuation

noncomputable section

/-- The common geometry carried by any of the four outward validation
positions.  `index.succ` is the boundary found by the original caller, and
the retained tail visits every subsequent boundary through boundary `4`. -/
structure Suffix
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GenuineSearch base c)
    (growth : Turing.Dir) (source : Nat)
    (instruction : CounterMachine.Instruction) : Type where
  progress : ValidationEnd current growth source instruction
  index : Fin 4
  current_eq : progress.suffix.current = ⟨index.succ, .right⟩
  remaining_toFour : ToFour index.succ progress.suffix.remaining

/-- The original caller found the source boundary of the retained outward
suffix. -/
theorem Suffix.current_read
    {base : Nat} {c : Nat.Partrec.Code}
    {current : GenuineSearch base c}
    {growth : Turing.Dir} {source : Nat}
    {instruction : CounterMachine.Instruction}
    (suffix : Suffix current growth source instruction) :
    current.foundTape.read = boundarySymbol suffix.index.succ := by
  have hread := suffix.progress.current_read
  rw [suffix.current_eq] at hread
  exact hread

/-- The original validation search is physically outward. -/
theorem Suffix.current_direction
    {base : Nat} {c : Nat.Partrec.Code}
    {current : GenuineSearch base c}
    {growth : Turing.Dir} {source : Nat}
    {instruction : CounterMachine.Instruction}
    (suffix : Suffix current growth source instruction) :
    current.direction = orient growth .right := by
  have hdirection := current.selectedRaw_direction_eq
  rw [CounterControlCommandAt.compileRawCommand_searchDirection]
    at hdirection
  rw [suffix.progress.suffix.raw_eq, suffix.current_eq] at hdirection
  exact hdirection.symm

/-- Exact blank gap of the original outward validation search. -/
theorem Suffix.current_gap
    {base : Nat} {c : Nat.Partrec.Code}
    {current : GenuineSearch base c}
    {growth : Turing.Dir} {source : Nat}
    {instruction : CounterMachine.Instruction}
    (suffix : Suffix current growth source instruction) :
    SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary suffix.index.succ).Matches current.outer
      (orient growth .right) current.distance := by
  have hgap := suffix.progress.current_gap
  rw [suffix.current_eq] at hgap
  exact hgap

/-- The original found tape is the outward endpoint of its exact gap. -/
theorem Suffix.current_foundTape
    {base : Nat} {c : Nat.Partrec.Code}
    {current : GenuineSearch base c}
    {growth : Turing.Dir} {source : Nat}
    {instruction : CounterMachine.Instruction}
    (suffix : Suffix current growth source instruction) :
    current.outer.moveN (orient growth .right) current.distance =
      current.foundTape := by
  have hfound := suffix.progress.current_foundTape
  rw [suffix.current_eq] at hfound
  exact hfound

/-- Exact tape trace from the original found boundary through every later
outward validation boundary. -/
theorem Suffix.tailGaps
    {base : Nat} {c : Nat.Partrec.Code}
    {current : GenuineSearch base c}
    {growth : Turing.Dir} {source : Nat}
    {instruction : CounterMachine.Instruction}
    (suffix : Suffix current growth source instruction) :
    RouteTailGaps growth suffix.progress.suffix.remaining current.foundTape
      suffix.progress.suffix.finish :=
  suffix.progress.suffix.tailGaps

/-- Expose the first found tape of a nonempty route trace. -/
private theorem routeGaps_uncons
    (growth : Turing.Dir) (leg : MarkerValidation.Leg)
    (rest : List MarkerValidation.Leg)
    (outer finish : FullTM0.Tape (Symbol numTags))
    (htrace : CounterControlValidationMortality.RouteGaps growth
      (leg :: rest) outer finish) :
    ∃ distance,
      SearchGap (fun symbol => symbol = blankSymbol)
        (Target.boundary leg.target).Matches outer
        (orient growth leg.direction) distance ∧
      RouteTailGaps growth rest
        (outer.moveN (orient growth leg.direction) distance) finish := by
  cases rest with
  | nil =>
      cases htrace with
      | last _ _ distance gap =>
          exact ⟨distance, gap, .nil _⟩
  | cons next rest =>
      cases htrace with
      | cons _ _ _ _ distance gap finish tail =>
          exact ⟨distance, gap, .cons next rest _ finish tail⟩

/-- A consecutive outward suffix ending at boundary `4` is centered on that
boundary at its final tape. -/
private theorem toFour_finish_read
    {growth : Turing.Dir} {start finish : FullTM0.Tape (Symbol numTags)}
    {source : Fin 5} {route : List MarkerValidation.Leg}
    (hroute : ToFour source route)
    (hread : start.read = boundarySymbol source)
    (htrace : RouteTailGaps growth route start finish) :
    finish.read = boundarySymbol 4 := by
  induction hroute generalizing start finish with
  | four =>
      cases htrace
      exact hread
  | step i tail ih =>
      cases htrace with
      | cons _ _ start finish trace =>
          rcases routeGaps_uncons growth ⟨i.succ, .right⟩ _ _ _ trace with
            ⟨distance, gap, restTrace⟩
          let found :=
            ((start.move (orient growth .right)).moveN
              (orient growth .right) distance)
          have hfoundRead : found.read = boundarySymbol i.succ := by
            change (Target.boundary i.succ).Matches found.read
            simpa [found, FullTM0.Tape.read_moveN] using gap.marked
          exact ih hfoundRead restTrace

/-- The completed validation suffix is centered on boundary `4`. -/
theorem Suffix.finish_read
    {base : Nat} {c : Nat.Partrec.Code}
    {current : GenuineSearch base c}
    {growth : Turing.Dir} {source : Nat}
    {instruction : CounterMachine.Instruction}
    (suffix : Suffix current growth source instruction) :
    suffix.progress.suffix.finish.read = boundarySymbol 4 := by
  exact toFour_finish_read suffix.remaining_toFour suffix.current_read
    suffix.tailGaps

/-- Operationally, the retained validation suffix reaches the selected
instruction body on its boundary-`4`-centered final tape. -/
theorem Suffix.reaches_bodyEntry
    {base : Nat} {c : Nat.Partrec.Code}
    {current : GenuineSearch base c}
    {growth : Turing.Dir} {source : Nat}
    {instruction : CounterMachine.Instruction}
    (suffix : Suffix current growth source instruction) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      (foundCfg current)
      ⟨resolve base c (bodyEntry growth source instruction),
        suffix.progress.suffix.finish⟩ :=
  suffix.progress.reaches

private theorem remaining_of_boundaryRaw
    {base : Nat} {c : Nat.Partrec.Code}
    {current : GenuineSearch base c}
    {growth : Turing.Dir} {source : Nat}
    {instruction : CounterMachine.Instruction}
    (progress : ValidationEnd current growth source instruction)
    (slot : Nat) (expected : Fin 5) (success : ControlRef)
    (hraw : current.selectedRaw = .boundaryNavigation
      ⟨growth, source, slot⟩ expected .right success .preserve) :
    progress.suffix.remaining = MarkerValidation.sweep.drop (slot + 1) := by
  have hroute := progress.suffix.route_eq
  have hcompiled := hraw.symm.trans progress.suffix.raw_eq
  simp [validationSearchBase, validationDirectBase,
    routeSuffixSuccess] at hcompiled
  calc
    progress.suffix.remaining =
        List.drop (progress.suffix.before.length + 1)
          (progress.suffix.before ++
            progress.suffix.current :: progress.suffix.remaining) := by
      simp
    _ = List.drop (slot + 1) MarkerValidation.sweep := by
      rw [← hroute]
      congr 1
      omega

private theorem current_eq_of_boundaryRaw
    {base : Nat} {c : Nat.Partrec.Code}
    {current : GenuineSearch base c}
    {growth : Turing.Dir} {source : Nat}
    {instruction : CounterMachine.Instruction}
    (progress : ValidationEnd current growth source instruction)
    (slot : Nat) (expected : Fin 5) (success : ControlRef)
    (hraw : current.selectedRaw = .boundaryNavigation
      ⟨growth, source, slot⟩ expected .right success .preserve) :
    progress.suffix.current = ⟨expected, .right⟩ := by
  have hcompiled := hraw.symm.trans progress.suffix.raw_eq
  have hpair : (expected, .right) =
      (progress.suffix.current.target,
        progress.suffix.current.direction) := by
    apply Option.some.inj
    exact congrArg
      (fun raw => match raw with
        | .boundaryNavigation _ target direction _ _ =>
            some (target, direction)
        | _ => none)
      hcompiled
  have htarget : progress.suffix.current.target = expected :=
    by simpa using (congrArg Prod.fst hpair).symm
  have hdirection : progress.suffix.current.direction = .right :=
    by simpa using (congrArg Prod.snd hpair).symm
  have leg_eq (leg : MarkerValidation.Leg)
      (htarget : leg.target = expected)
      (hdirection : leg.direction = .right) :
      leg = ⟨expected, .right⟩ := by
    cases leg with
    | mk target direction =>
        cases htarget
        cases hdirection
        rfl
  exact leg_eq progress.suffix.current htarget hdirection

/-- Extract the uniform consecutive suffix from any exact outward
validation obligation. -/
theorem suffix
    {base : Nat} {c : Nat.Partrec.Code}
    {current : GenuineSearch base c}
    {growth : Turing.Dir} {source : Nat}
    {instruction : CounterMachine.Instruction}
    (obligation : OutwardObligation current growth source instruction) :
    Nonempty (Suffix current growth source instruction) := by
  cases obligation with
  | one progress hraw =>
      have hremaining := remaining_of_boundaryRaw progress 4 1
        (directRef growth source 4) hraw
      refine ⟨⟨progress, 0, current_eq_of_boundaryRaw progress 4 1
        (directRef growth source 4) hraw, ?_⟩⟩
      rw [hremaining]
      exact .step 1 (.step 2 (.step 3 .four))
  | two progress hraw =>
      have hremaining := remaining_of_boundaryRaw progress 5 2
        (directRef growth source 5) hraw
      refine ⟨⟨progress, 1, current_eq_of_boundaryRaw progress 5 2
        (directRef growth source 5) hraw, ?_⟩⟩
      rw [hremaining]
      exact .step 2 (.step 3 .four)
  | three progress hraw =>
      have hremaining := remaining_of_boundaryRaw progress 6 3
        (directRef growth source 6) hraw
      refine ⟨⟨progress, 2, current_eq_of_boundaryRaw progress 6 3
        (directRef growth source 6) hraw, ?_⟩⟩
      rw [hremaining]
      exact .step 3 .four
  | four progress hraw =>
      have hremaining := remaining_of_boundaryRaw progress 7 4
        (bodyEntry growth source instruction) hraw
      refine ⟨⟨progress, 3, current_eq_of_boundaryRaw progress 7 4
        (bodyEntry growth source instruction) hraw, ?_⟩⟩
      rw [hremaining]
      exact .four

end

end CounterControlGenuineValidationOutwardSuffix
end Hooper
end Kari
end LeanWang
