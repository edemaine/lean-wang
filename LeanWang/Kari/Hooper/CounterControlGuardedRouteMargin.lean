/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlGuardedRouteEmbedding
import LeanWang.Kari.Hooper.CounterControlGuardedGapEmbedding
import LeanWang.Kari.Hooper.CounterControlTargetUniqueness

/-!
# Guarded preserving-route margins

A suffix of consecutive rightward boundary searches can be read backward
from a canonical boundary-`4` endpoint.  Combining that coordinate recovery
with the erased predecessor of a guarded caller proves that the caller's
extended parent gap is strictly inside the reconstructed core.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlGuardedRouteMargin

open Turing CounterMachine
open BoundedMarkerProgram FramedMarkerTape
open CounterControlPlan CounterControlBridge
open CounterControlCoreFrame CounterControlGlobalUnnesting
open CounterControlGuardedSearch CounterControlGuardedRouteEmbedding
open CounterControlResumedRouteEmbedding

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-- Pure coordinate form of guarded route containment.  No logical-state or
source-program hypotheses are needed once the suffix endpoint has been
identified with canonical boundary `4`. -/
theorem parentDistance_lt_layoutEnd_of_toFour_endpoint
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GuardedSearch base c)
    {growth : Turing.Dir} {source searchSlot directSlot : Nat}
    {after : ControlRef} {route : List MarkerValidation.Leg}
    (progress : GuardedRouteEnd current growth source searchSlot directSlot
      after route)
    {registers : Registers}
    {coreTape : FullTM0.Tape (Symbol numTags)}
    (hcore : CoreRepresents registers growth coreTape)
    (hcenter : progress.suffix.finish =
      atLogical growth coreTape (layoutEnd registers))
    (hroute : ∃ routeSource : Fin 5, ToFour routeSource route) :
    current.current.distance + 1 < layoutEnd registers := by
  rcases hroute with ⟨routeSource, hroute⟩
  rcases hroute.position progress.suffix.route_eq with
    ⟨i, hcurrent, htail⟩
  have hread : current.foundTape.read = boundarySymbol i.succ := by
    have hread' := progress.current_read
    rw [hcurrent] at hread'
    exact hread'
  have hfound : current.foundTape =
      atLogical growth coreTape (boundaryOffset registers i.succ) := by
    exact htail.start_eq hcore hread progress.suffix.tailGaps hcenter
  have hdirection : current.direction = orient growth .right := by
    have hdirection := current.selectedRaw_direction_eq
    rw [CounterControlCommandAt.compileRawCommand_searchDirection]
      at hdirection
    rw [progress.suffix.raw_eq, hcurrent] at hdirection
    exact hdirection.symm
  have htarget : (CounterControlSearchSystem.command base c
      current.current.search).target = Target.boundary i.succ := by
    have htarget' := CounterControlTargetUniqueness.target_eq_of_matches
      current.selectedRaw_target_matches_foundTape
      (show (Target.boundary i.succ : Target numTags).Matches
          current.foundTape.read by
        simpa [Target.Matches] using hread)
    simpa using htarget'
  exact
    CounterControlGuardedGapEmbedding.rightGap_parentDistance_lt_layoutEnd
      current hcore i hdirection htarget hfound

end

end CounterControlGuardedRouteMargin
end Hooper
end Kari
end LeanWang
