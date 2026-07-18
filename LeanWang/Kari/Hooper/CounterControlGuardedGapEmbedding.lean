/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlGuardedCoordinates
import LeanWang.Kari.Hooper.CounterControlResumedRouteEmbedding

/-!
# Strict core margins from guarded search gaps

The erased cell behind a guarded search extends its ordinary gap by one.
When the found target is an internal boundary of a reconstructed counter
core, the existing canonical-gap bounds therefore apply to `distance + 1`.
This is the two-cell margin needed to survive an immediately following
positive decrement.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlGuardedGapEmbedding

open Turing
open BoundedMarkerProgram FramedMarkerTape
open CounterControlPlan CounterControlSearchSystem
open CounterControlCoreFrame CounterControlGlobalUnnesting
open CounterControlGuardedSearch

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-- A guarded rightward search ending on canonical boundary `i+1` has its
entire one-cell-extended parent gap strictly inside the reconstructed core. -/
theorem rightGap_parentDistance_lt_layoutEnd
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GuardedSearch base c)
    {registers : CounterMachine.Registers} {growth : Turing.Dir}
    {coreTape : FullTM0.Tape (Symbol numTags)}
    (hcore : CoreRepresents registers growth coreTape) (i : Fin 4)
    (hdirection : current.direction = orient growth .right)
    (htarget : (command base c current.current.search).target =
      Target.boundary i.succ)
    (hfound : current.foundTape =
      atLogical growth coreTape (boundaryOffset registers i.succ)) :
    current.current.distance + 1 < layoutEnd registers := by
  apply CounterControlResumedRouteEmbedding.rightGap_distance_lt_layoutEnd
    hcore i (current.current.distance + 1)
  · have hgap := current.parentGap
    rw [hdirection, htarget] at hgap
    exact hgap
  · rw [← hdirection]
    exact current.foundTape_eq_parentMoveN.symm.trans hfound

/-- Leftward counterpart: a guarded search ending on canonical boundary
`i` has its extended parent gap strictly inside the reconstructed core. -/
theorem leftGap_parentDistance_lt_layoutEnd
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GuardedSearch base c)
    {registers : CounterMachine.Registers} {growth : Turing.Dir}
    {coreTape : FullTM0.Tape (Symbol numTags)}
    (hcore : CoreRepresents registers growth coreTape) (i : Fin 4)
    (hdirection : current.direction = orient growth .left)
    (htarget : (command base c current.current.search).target =
      Target.boundary i.castSucc)
    (hfound : current.foundTape =
      atLogical growth coreTape (boundaryOffset registers i.castSucc)) :
    current.current.distance + 1 < layoutEnd registers := by
  apply CounterControlResumedRouteEmbedding.leftGap_distance_lt_layoutEnd
    hcore i (current.current.distance + 1)
  · have hgap := current.parentGap
    rw [hdirection, htarget] at hgap
    exact hgap
  · rw [← hdirection]
    exact current.foundTape_eq_parentMoveN.symm.trans hfound

end

end CounterControlGuardedGapEmbedding
end Hooper
end Kari
end LeanWang
