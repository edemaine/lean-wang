/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlCommandContinuationMortality

/-!
# Exact continuation of a found generated command

The generic controller normalizer deliberately forgets tape coordinates.  For
the parent-embedding argument we instead retain the exact tape produced after
a generated bounded search has reached its advertised target.

Every raw command has one of three constructor-level outcomes.  Navigation
and a collision-free shift take their success reference; an occupied shift
with a collision reference takes that reference; and an occupied shift with
no collision reference is explicitly recorded as blocked.  The last case is
kept as data rather than silently assuming that the orbit is immortal, so the
classification is reusable independently of mortality.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlExactCommandContinuation

open Turing
open BoundedMarkerProgram CounterControlPlan CounterControlCommandAt
open CounterControlCommandContinuationMortality

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-! ## Exact constructor-level tapes -/

/-- Tape at the success reference of a raw command, assuming a marker shift
finds a blank destination. -/
def exactSuccessTape (raw : RawCommand)
    (T : FullTM0.Tape (Symbol numTags)) :
    FullTM0.Tape (Symbol numTags) :=
  match raw with
  | .boundaryNavigation _ _ _ _ .preserve => T
  | .boundaryNavigation address _ _ _ (.erase departure) =>
      match departure.map (orient address.growth) with
      | none => T.write blankSymbol
      | some direction => (T.write blankSymbol).move direction
  | .tagNavigation .. => T
  | .markerShift address expected _ shift _ departure _ =>
      let destination :=
        (T.write blankSymbol).move (orient address.growth shift)
      let written := destination.write (boundarySymbol expected)
      match departure.map (orient address.growth) with
      | none => written
      | some direction => written.move direction

/-- Tape at the collision reference of a marker shift.  The other
constructors have no collision reference; returning `T` there makes this a
total function while the outcome type prevents those values from being used.
-/
def exactCollisionTape (raw : RawCommand)
    (T : FullTM0.Tape (Symbol numTags)) :
    FullTM0.Tape (Symbol numTags) :=
  match raw with
  | .markerShift address _ _ shift _ _ _ =>
      (T.write blankSymbol).move (orient address.growth shift)
  | _ => T

/-- A marker shift sees a nonblank destination after clearing its source.
The predicate is false for navigation commands. -/
def ShiftDestinationOccupied (raw : RawCommand)
    (T : FullTM0.Tape (Symbol numTags)) : Prop :=
  match raw with
  | .markerShift address _ _ shift _ _ _ =>
      ((T.write blankSymbol).move
        (orient address.growth shift)).read ≠ blankSymbol
  | _ => False

/-- The only unhandled found-state continuation: a marker shift has an
occupied destination but was compiled without a collision reference. -/
def ShiftBlocked (raw : RawCommand)
    (T : FullTM0.Tape (Symbol numTags)) : Prop :=
  rawCollisionRef raw = none ∧ ShiftDestinationOccupied raw T

/-! ## Exact found-state classification -/

/-- Exact continuation outcome from the found state of a generated raw
command.  Both exit alternatives retain the entire resulting tape rather
than normalizing immediately to a controller frontier. -/
inductive FoundContinuationOutcome (base : Nat) (c : Nat.Partrec.Code)
    (raw : RawCommand) (hraw : raw ∈ rawCommands)
    (T : FullTM0.Tape (Symbol numTags)) : Type where
  | success
      (reaches : FullTM0.Reaches
        (CounterControlNestingBridge.machine base c)
        ⟨foundState (CanonicalInitializer.radius c)
            (searchState base c raw.address), T⟩
        ⟨resolve base c (rawSuccessRef raw), exactSuccessTape raw T⟩)
  | collision (reference : ControlRef)
      (isCollision : rawCollisionRef raw = some reference)
      (isOccupied : ShiftDestinationOccupied raw T)
      (reaches : FullTM0.Reaches
        (CounterControlNestingBridge.machine base c)
        ⟨foundState (CanonicalInitializer.radius c)
            (searchState base c raw.address), T⟩
        ⟨resolve base c reference, exactCollisionTape raw T⟩)
  | blocked (isBlocked : ShiftBlocked raw T)

namespace FoundContinuationOutcome

/-- If the marker-shift destination is known not to be occupied, the exact
classification collapses to its success reachability witness.  Navigation
commands satisfy the premise definitionally. -/
def reachesSuccess_of_destinationFree
    {base : Nat} {c : Nat.Partrec.Code}
    {raw : RawCommand} {hraw : raw ∈ rawCommands}
    {T : FullTM0.Tape (Symbol numTags)}
    (outcome : FoundContinuationOutcome base c raw hraw T)
    (hfree : ¬ ShiftDestinationOccupied raw T) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      ⟨foundState (CanonicalInitializer.radius c)
          (searchState base c raw.address), T⟩
      ⟨resolve base c (rawSuccessRef raw), exactSuccessTape raw T⟩ := by
  cases outcome with
  | success reaches => exact reaches
  | collision _ _ occupied _ => exact False.elim (hfree occupied)
  | blocked blocked => exact False.elim (hfree blocked.2)

end FoundContinuationOutcome

/-- A generated command at its exact found target either executes to its
exact success tape, executes to its exact collision tape, or is an occupied
marker shift with no collision reference. -/
def exact_found_continuation
    (base : Nat) (c : Nat.Partrec.Code)
    (raw : RawCommand) (hraw : raw ∈ rawCommands)
    (T : FullTM0.Tape (Symbol numTags))
    (hmatch : (compileRawCommand base c raw hraw).target.Matches T.read) :
    FoundContinuationOutcome base c raw hraw T := by
  -- Follow the raw-command constructors.  Navigation commands always
  -- succeed at a matching target; only marker shifts inspect another cell.
  cases raw with
  | boundaryNavigation address expected direction success action =>
      -- Preserving and erasing navigation use the corresponding native
      -- continuation theorem after exposing the compiled `CommandAt` fact.
      cases action with
      | preserve =>
          have hatRaw := CommandAt.compileRawCommand base c
            (.boundaryNavigation address expected direction success .preserve)
            hraw
          rw [compileRawCommand_spec] at hatRaw
          have hat : CommandAt (CanonicalInitializer.radius c) base
              (searchState base c address)
              (.boundaryNavigation expected (orient address.growth direction)
                (resolve base c success)
                (rawTag
                  (.boundaryNavigation address expected direction success
                    .preserve) hraw)
                .preserve)
              (commands base c) := by
            simpa [compileRawAtTag, RawCommand.address,
              compileNavigationAction] using hatRaw
          rw [compileRawCommand_spec] at hmatch
          have htarget : (Target.boundary expected).Matches T.read := by
            simpa [compileRawAtTag, Command.target,
              compileNavigationAction] using hmatch
          apply FoundContinuationOutcome.success
          have hrun :=
            BoundedMarkerContinuation.machine_reaches_navigation_native
              (coreTable base c) (Target.boundary expected)
              (orient address.growth direction) (resolve base c success)
              (rawTag
                (.boundaryNavigation address expected direction success
                  .preserve) hraw)
              hat T htarget
          simpa [rawSuccessRef, exactSuccessTape, RawCommand.address] using hrun
      | erase departure =>
          have hatRaw := CommandAt.compileRawCommand base c
            (.boundaryNavigation address expected direction success
              (.erase departure)) hraw
          rw [compileRawCommand_spec] at hatRaw
          have hat : CommandAt (CanonicalInitializer.radius c) base
              (searchState base c address)
              (.boundaryNavigation expected (orient address.growth direction)
                (resolve base c success)
                (rawTag
                  (.boundaryNavigation address expected direction success
                    (.erase departure)) hraw)
                (.erase (departure.map (orient address.growth))))
              (commands base c) := by
            simpa [compileRawAtTag, RawCommand.address,
              compileNavigationAction] using hatRaw
          rw [compileRawCommand_spec] at hmatch
          have hread : T.read = boundarySymbol expected := by
            simpa [compileRawAtTag, Command.target, Target.Matches,
              compileNavigationAction] using hmatch
          apply FoundContinuationOutcome.success
          have hrun :=
            BoundedMarkerContinuation.machine_reaches_erase_native
              (coreTable base c) expected (orient address.growth direction)
              (resolve base c success)
              (rawTag
                (.boundaryNavigation address expected direction success
                  (.erase departure)) hraw)
              (departure.map (orient address.growth)) hat T hread
          cases departure <;>
            simpa [rawSuccessRef, exactSuccessTape, RawCommand.address] using
              hrun
  | tagNavigation address direction success =>
      -- A tag target is ordinary preserving navigation with `anyTag`.
      have hatRaw := CommandAt.compileRawCommand base c
        (.tagNavigation address direction success) hraw
      rw [compileRawCommand_spec] at hatRaw
      have hat : CommandAt (CanonicalInitializer.radius c) base
          (searchState base c address)
          (.tagNavigation (orient address.growth direction)
            (resolve base c success)
            (rawTag (.tagNavigation address direction success) hraw))
          (commands base c) := by
        simpa [compileRawAtTag, RawCommand.address] using hatRaw
      rw [compileRawCommand_spec] at hmatch
      have htarget : (Target.anyTag : Target numTags).Matches T.read := by
        simpa [compileRawAtTag, Command.target] using hmatch
      apply FoundContinuationOutcome.success
      have hrun :=
        BoundedMarkerContinuation.machine_reaches_navigation_native
          (coreTable base c) (Target.anyTag : Target numTags)
          (orient address.growth direction) (resolve base c success)
          (rawTag (.tagNavigation address direction success) hraw)
          hat T htarget
      simpa [rawSuccessRef, exactSuccessTape, RawCommand.address] using hrun
  | markerShift address expected search shift success departure collision =>
      -- A blank destination takes the success continuation.  An occupied
      -- destination either reports its collision reference or is blocked
      -- when the command deliberately has no such reference.
      let move : MarkerProgram.Move :=
        ⟨expected, orient address.growth search,
          orient address.growth shift⟩
      have hatRaw := CommandAt.compileRawCommand base c
        (.markerShift address expected search shift success departure collision)
        hraw
      rw [compileRawCommand_spec] at hatRaw
      have hat : CommandAt (CanonicalInitializer.radius c) base
          (searchState base c address)
          (.markerShift move (resolve base c success)
            (rawTag
              (.markerShift address expected search shift success departure
                collision) hraw)
            (departure.map (orient address.growth))
            (collision.map (resolve base c)))
          (commands base c) := by
        simpa [move, compileRawAtTag, RawCommand.address] using hatRaw
      rw [compileRawCommand_spec] at hmatch
      have hread : T.read = boundarySymbol expected := by
        simpa [move, compileRawAtTag, Command.target, Target.Matches] using
          hmatch
      by_cases hblank :
          ((T.write blankSymbol).move
            (orient address.growth shift)).read = blankSymbol
      · apply FoundContinuationOutcome.success
        have hrun :=
          BoundedMarkerContinuation.machine_reaches_shift_success_native
            (coreTable base c) move (resolve base c success)
            (rawTag
              (.markerShift address expected search shift success departure
                collision) hraw)
            (departure.map (orient address.growth))
            (collision.map (resolve base c)) hat T hread (by
              simpa [move] using hblank)
        cases departure <;>
          simpa [move, rawSuccessRef, exactSuccessTape,
            RawCommand.address] using hrun
      · cases collision with
        | none =>
            apply FoundContinuationOutcome.blocked
            exact ⟨rfl, hblank⟩
        | some reference =>
            apply FoundContinuationOutcome.collision reference rfl (by
              simpa [ShiftDestinationOccupied] using hblank)
            have hrun :=
              BoundedMarkerContinuation.machine_reaches_shift_collision_native
                (coreTable base c) move (resolve base c success)
                (resolve base c reference)
                (rawTag
                  (.markerShift address expected search shift success departure
                    (some reference)) hraw)
                (departure.map (orient address.growth)) hat T hread (by
                  simpa [move] using hblank)
            simpa [move, exactCollisionTape, RawCommand.address] using hrun

end

end CounterControlExactCommandContinuation
end Hooper
end Kari
end LeanWang
