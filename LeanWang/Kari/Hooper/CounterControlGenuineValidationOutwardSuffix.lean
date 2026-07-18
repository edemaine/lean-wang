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
