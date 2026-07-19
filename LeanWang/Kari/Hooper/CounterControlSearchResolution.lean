/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlInstructionSearchSemantics
import LeanWang.Kari.Hooper.CounterControlSearchExecution

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
open CounterControlInstructionSemantics CounterControlCoreRoutes

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
  exact CounterControlSearchExecution.reaches_found_or_halts_of_resolves
    base c raw hraw outer distance (hshort distance hdistance) hgap

/-- The simultaneous resolving-search hypothesis as a compiled-search
runner whose failure predicate is halting. -/
def resolvingSearchRunner
    (base : Nat) (c : Nat.Partrec.Code) (limit : Nat)
    (hshort : ShortResolves base c limit) :
    CompiledSearchRunner base c limit
      (FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)) where
  pullback := FullTM0.HaltsFrom.of_reaches
  search := by
    intro raw hraw outer distance hdistance hgap
    exact rawSearch_reaches_found_or_halts base c limit hshort raw hraw outer
      distance hdistance hgap

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
  exact machine_reaches_boundary_preserve_with base c limit
    (FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c))
    (resolvingSearchRunner base c limit hshort) address expected direction
    success hraw outer distance hdistance hgap

/-! ## Resolving marker routes -/

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
  exact route_reaches_with_failure_at base c limit
    (FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c))
    FullTM0.HaltsFrom.of_reaches
    (by
      intro address expected direction success hraw outer distance hdistance
        hgap
      exact machine_reaches_boundary_preserve_or_halts base c limit hshort
        address expected direction success hraw outer distance hdistance hgap)
    growth counterState searchSlot directSlot source after sourceBoundary
    first rest T sourcePosition finishPosition hsource hexec hcommands hrules

end

end CounterControlSearchResolution
end Hooper
end Kari
end LeanWang
