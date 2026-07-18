/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlResumedRouteEmbedding

/-!
# Transporting an outward gap through inward-ray agreement

An instruction may alter markers strictly outward of an old validation
boundary while leaving the whole inward ray at that boundary unchanged.
This file packages the resulting comparison with a reconstructed logical
core.  It is deliberately independent of any particular increment,
decrement, or cleanup schedule.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlOutwardGapTransport

open Turing CounterMachine
open BoundedMarkerProgram FramedMarkerTape OrientedMarkerTape
open CounterControlPlan CounterControlBridge CounterControlCoreFrame
open CounterControlResumedRouteEmbedding

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-- Moving inward by `distance` and then outward by a shorter amount leaves
the head `distance - forward` cells inward of its starting position. -/
theorem moveN_opposite_then_partial
    (T : FullTM0.Tape (Symbol numTags)) (direction : Turing.Dir)
    (distance forward : Nat) (hforward : forward ≤ distance) :
    (T.moveN (NestingMachine.opposite direction) distance).moveN
        direction forward =
      T.moveN (NestingMachine.opposite direction) (distance - forward) := by
  funext position
  cases direction <;>
    simp [NestingMachine.opposite, FullTM0.Tape.moveN,
      FullTM0.Tape.offset] <;>
    congr 1 <;> omega

/-- Looking back `distance - forward` cells from the endpoint of a
`distance`-cell move returns to its `forward`-cell intermediate tape. -/
theorem moveN_then_opposite_sub
    (T : FullTM0.Tape (Symbol numTags)) (direction : Turing.Dir)
    (distance forward : Nat) (hforward : forward ≤ distance) :
    (T.moveN direction distance).moveN
        (NestingMachine.opposite direction) (distance - forward) =
      T.moveN direction forward := by
  funext position
  cases direction <;>
    simp [NestingMachine.opposite, FullTM0.Tape.moveN,
      FullTM0.Tape.offset] <;>
    congr 1 <;> omega

/-- If a new boundary-centered tape agrees inward with the endpoint of an
old outward blank gap, recentering the new tape at the old gap's origin
reconstructs an exact gap of the same length. -/
theorem rightGap_of_inwardAgreement
    {growth : Turing.Dir} {index : Fin 4}
    {oldOuter oldFound newFound : FullTM0.Tape (Symbol numTags)}
    {distance : Nat}
    (oldGap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary index.succ).Matches oldOuter
      (orient growth .right) distance)
    (oldFound_eq : oldOuter.moveN (orient growth .right) distance =
      oldFound)
    (agreement : ∀ back ≤ distance,
      (newFound.moveN (orient growth .left) back).read =
        (oldFound.moveN (orient growth .left) back).read) :
    SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary index.succ).Matches
      (newFound.moveN (orient growth .left) distance)
      (orient growth .right) distance := by
  have hopposite : NestingMachine.opposite (orient growth .right) =
      orient growth .left := by
    cases growth <;> rfl
  constructor
  · intro forward hforward
    rw [← FullTM0.Tape.read_moveN
      (newFound.moveN (orient growth .left) distance)
      (orient growth .right) forward]
    have hle : forward ≤ distance := Nat.le_of_lt hforward
    let back := distance - forward
    have hagreement := agreement back (by
      dsimp [back]
      omega)
    have hnew :
        ((newFound.moveN (orient growth .left) distance).moveN
          (orient growth .right) forward).read =
        (newFound.moveN (orient growth .left) back).read := by
      rw [← hopposite]
      exact congrArg FullTM0.Tape.read
        (moveN_opposite_then_partial newFound
          (orient growth .right) distance forward hle)
    have hold :
        (oldFound.moveN (orient growth .left) back).read =
        (oldOuter.moveN (orient growth .right) forward).read := by
      rw [← oldFound_eq, ← hopposite]
      exact congrArg FullTM0.Tape.read
        (moveN_then_opposite_sub oldOuter
          (orient growth .right) distance forward hle)
    rw [hnew, hagreement, hold]
    simpa only [FullTM0.Tape.read_moveN] using oldGap.blank hforward
  · have hreturn :
        (newFound.moveN (orient growth .left) distance).moveN
            (orient growth .right) distance = newFound := by
      have hcancel := CanonicalInitializerProgram.moveN_opposite newFound
        (orient growth .left) distance
      cases growth <;>
        simpa [orient, NestingMachine.opposite] using hcancel
    have hagreement := agreement 0 (Nat.zero_le distance)
    have holdRead : oldFound.read = boundarySymbol index.succ := by
      rw [← oldFound_eq]
      simpa [Target.Matches, FullTM0.Tape.read_moveN] using oldGap.marked
    have hagreementZero : newFound.read = oldFound.read := by
      simpa using hagreement
    rw [← FullTM0.Tape.read_moveN
      (newFound.moveN (orient growth .left) distance)
      (orient growth .right) distance]
    rw [hreturn]
    change newFound.read = boundarySymbol index.succ
    exact hagreementZero.trans holdRead

/-- Looking inward from the found endpoint of an outward gap reads blank at
every positive distance no larger than the gap. -/
theorem found_inward_read_blank
    {direction : Turing.Dir} {target : Fin 5}
    {outer found : FullTM0.Tape (Symbol numTags)} {distance back : Nat}
    (gap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary target).Matches outer direction distance)
    (found_eq : outer.moveN direction distance = found)
    (back_pos : 0 < back) (back_le : back ≤ distance) :
    (found.moveN (NestingMachine.opposite direction) back).read =
      blankSymbol := by
  let forward := distance - back
  have forward_lt : forward < distance := by
    dsimp [forward]
    omega
  have forward_le : forward ≤ distance := Nat.sub_le distance back
  have hmove := moveN_then_opposite_sub outer direction distance forward
    forward_le
  have hsub : distance - forward = back := by
    dsimp [forward]
    omega
  rw [hsub, found_eq] at hmove
  rw [hmove]
  simpa only [FullTM0.Tape.read_moveN] using gap.blank forward_lt

/-- A positive canonical anchor followed inward to the old found endpoint
retains the old gap margin as soon as boundary `0` is absent along the
intervening prefix. -/
theorem distance_lt_anchor_of_centerOffset
    {registers : Registers} {growth : Turing.Dir} {target : Fin 5}
    {coreTape center oldOuter oldFound :
      FullTM0.Tape (Symbol numTags)}
    {distance anchor toFound : Nat}
    (core : CoreRepresents registers growth coreTape)
    (oldGap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary target).Matches oldOuter
      (orient growth .right) distance)
    (oldFound_eq : oldOuter.moveN (orient growth .right) distance =
      oldFound)
    (anchor_pos : 1 < anchor)
    (centered : center = atLogical growth coreTape anchor)
    (foundAt : center.moveN (orient growth .left) toFound = oldFound)
    (avoidsZero : ∀ back ≤ toFound,
      (center.moveN (orient growth .left) back).read ≠ boundarySymbol 0) :
    distance < anchor := by
  have hboundaryZero :
      (center.moveN (orient growth .left)
        (anchor - 1)).read = boundarySymbol 0 := by
    rw [centered]
    have hend : anchor = 1 + (anchor - 1) := by omega
    conv_lhs =>
      enter [1, 1]
      rw [hend]
    simp only [orient_eq_orientDirection]
    rw [atLogical_moveN_left, atLogical_read]
    simpa using core.boundary (0 : Fin 5)
  by_contra hnot
  have hdistance : anchor ≤ distance :=
    Nat.le_of_not_gt hnot
  by_cases hprefix : anchor - 1 ≤ toFound
  · exact (avoidsZero (anchor - 1) hprefix) hboundaryZero
  · have htoFound : toFound < anchor - 1 :=
      Nat.lt_of_not_ge hprefix
    let remaining := anchor - 1 - toFound
    have hremainingPos : 0 < remaining := by
      dsimp [remaining]
      omega
    have hremainingLe : remaining ≤ distance := by
      dsimp [remaining]
      omega
    have hsum : toFound + remaining = anchor - 1 := by
      dsimp [remaining]
      omega
    have hblank := found_inward_read_blank oldGap oldFound_eq
      hremainingPos hremainingLe
    have hopposite : NestingMachine.opposite (orient growth .right) =
        orient growth .left := by
      cases growth <;> rfl
    rw [hopposite] at hblank
    have hcoordinate :
        (center.moveN (orient growth .left)
          (toFound + remaining)).read =
        (oldFound.moveN (orient growth .left) remaining).read := by
      rw [← FullTM0.Tape.moveN_add, foundAt]
    have hzeroBlank :
        (center.moveN (orient growth .left)
          (anchor - 1)).read = blankSymbol := by
      rw [← hsum, hcoordinate]
      exact hblank
    rw [hboundaryZero] at hzeroBlank
    exact blankSymbol_ne_boundarySymbol 0 hzeroBlank.symm

/-- A canonical logical-end center followed inward to the old found endpoint
retains the old gap margin.  This is the common specialization used by
completed instruction schedules. -/
theorem distance_lt_layoutEnd_of_centerOffset
    {registers : Registers} {growth : Turing.Dir} {target : Fin 5}
    {coreTape center oldOuter oldFound :
      FullTM0.Tape (Symbol numTags)}
    {distance toFound : Nat}
    (core : CoreRepresents registers growth coreTape)
    (oldGap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary target).Matches oldOuter
      (orient growth .right) distance)
    (oldFound_eq : oldOuter.moveN (orient growth .right) distance =
      oldFound)
    (centered : center = atLogical growth coreTape (layoutEnd registers))
    (foundAt : center.moveN (orient growth .left) toFound = oldFound)
    (avoidsZero : ∀ back ≤ toFound,
      (center.moveN (orient growth .left) back).read ≠ boundarySymbol 0) :
    distance < layoutEnd registers := by
  apply distance_lt_anchor_of_centerOffset core oldGap oldFound_eq
  · simp [layoutEnd, RegisterLayout.clockBoundary_eq]
  · exact centered
  · exact foundAt
  · exact avoidsZero

/-- Inward-ray agreement at the corresponding canonical boundary is enough
to retain the original outward caller's strict layout margin. -/
theorem distance_lt_layoutEnd_of_inwardAgreement
    {registers : Registers} {growth : Turing.Dir} {index : Fin 4}
    {coreTape oldOuter oldFound newFound :
      FullTM0.Tape (Symbol numTags)}
    {distance : Nat}
    (core : CoreRepresents registers growth coreTape)
    (oldGap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary index.succ).Matches oldOuter
      (orient growth .right) distance)
    (oldFound_eq : oldOuter.moveN (orient growth .right) distance =
      oldFound)
    (agreement : ∀ back ≤ distance,
      (newFound.moveN (orient growth .left) back).read =
        (oldFound.moveN (orient growth .left) back).read)
    (canonical : newFound =
      atLogical growth coreTape (boundaryOffset registers index.succ)) :
    distance < layoutEnd registers := by
  let newOuter := newFound.moveN (orient growth .left) distance
  have newGap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary index.succ).Matches newOuter
      (orient growth .right) distance := by
    simpa only [newOuter] using
      rightGap_of_inwardAgreement oldGap oldFound_eq agreement
  have hopposite : NestingMachine.opposite (orient growth .left) =
      orient growth .right := by
    cases growth <;> rfl
  have newFound_eq : newOuter.moveN (orient growth .right) distance =
      atLogical growth coreTape (boundaryOffset registers index.succ) := by
    rw [← hopposite]
    exact (CanonicalInitializerProgram.moveN_opposite newFound
      (orient growth .left) distance).trans canonical
  exact rightGap_distance_lt_layoutEnd core index distance newGap newFound_eq

end

end CounterControlOutwardGapTransport
end Hooper
end Kari
end LeanWang
