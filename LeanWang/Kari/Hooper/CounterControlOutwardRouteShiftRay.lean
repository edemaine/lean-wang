/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlGuardedShiftEmbedding
import LeanWang.Kari.Hooper.CounterControlOutwardRoute

/-!
# Inward rays behind an outward route followed by marker shifts

A positive decrement can begin strictly outside the boundary found by an
earlier outward validation search.  The preserving route from the old found
boundary to the decrement boundary changes no cells.  Moving the latter
boundary one cell inward therefore leaves a finite inward bridge to the old
found tape.  This file records that bridge without choosing canonical
coordinates, then composes it with the backward geometry of the remaining
shift suffix.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlOutwardRouteShiftRay

open Turing CounterMachine
open BoundedMarkerProgram FramedMarkerTape
open CounterControlPlan CounterControlBridge
open CounterControlRouteSuffixMortality
open CounterControlGuardedShiftEmbedding
open CounterControlOutwardRoute
open CounterControlResumedShiftCoordinates

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-- An inward ray from `center` reaches `found` after `travel` cells, and
boundary `0` is absent from the finite intervening prefix. -/
structure InwardRayBridge (growth : Turing.Dir)
    (center found : FullTM0.Tape (Symbol numTags)) : Type where
  travel : Nat
  ray : ∀ back,
    (center.moveN (orient growth .left) (travel + back)).read =
      (found.moveN (orient growth .left) back).read
  avoidsZero : ∀ back ≤ travel,
    (center.moveN (orient growth .left) back).read ≠ boundarySymbol 0

/-- Absolute forward geometry of a preserving consecutive outward route.
Besides its total physical travel, it records that boundary `0` is absent
from the traversed interval. -/
private structure OutwardRouteGeometry (growth : Turing.Dir)
    (start finish : FullTM0.Tape (Symbol numTags)) : Type where
  travel : Nat
  finish_eq : finish = start.moveN (orient growth .right) travel
  avoidsZero : ∀ forward ≤ travel,
    (start.moveN (orient growth .right) forward).read ≠ boundarySymbol 0

/-- A consecutive preserving route between nonzero boundaries has absolute
outward geometry avoiding boundary `0`. -/
private theorem ToUpper.outwardRouteGeometry
    {growth : Turing.Dir} {source target : Fin 5}
    {route : List MarkerValidation.Leg}
    (hroute : ToUpper source target route)
    {start finish : FullTM0.Tape (Symbol numTags)}
    (hread : start.read = boundarySymbol source)
    (hsource : source ≠ 0)
    (htrace : RouteTailGaps growth route start finish) :
    Nonempty (OutwardRouteGeometry growth start finish) := by
  induction hroute generalizing start finish with
  | here =>
      cases htrace
      refine ⟨⟨0, by simp, ?_⟩⟩
      intro forward hforward
      have hzero : forward = 0 := by omega
      subst forward
      rw [FullTM0.Tape.moveN_zero, hread]
      intro heq
      exact hsource ((boundarySymbol_injective _ _).mp heq)
  | @step i target rest tail ih =>
      rcases htrace.uncons with ⟨distance, gap, remaining⟩
      let upper :=
        (start.move (orient growth .right)).moveN
          (orient growth .right) distance
      have hupperRead : upper.read = boundarySymbol i.succ := by
        change (Target.boundary i.succ).Matches upper.read
        simpa [upper, FullTM0.Tape.read_moveN] using gap.marked
      rcases ih hupperRead (Fin.succ_ne_zero i) remaining with
        ⟨⟨tailTravel, hfinish, havoids⟩⟩
      refine ⟨⟨distance + 1 + tailTravel, ?_, ?_⟩⟩
      · calc
          finish = upper.moveN (orient growth .right) tailTravel := hfinish
          _ = (start.moveN (orient growth .right) (distance + 1)).moveN
              (orient growth .right) tailTravel := by
            rw [show upper =
                start.moveN (orient growth .right) (distance + 1) by
              dsimp only [upper]
              exact FullTM0.Tape.move_moveN start
                (orient growth .right) distance]
          _ = start.moveN (orient growth .right)
              (distance + 1 + tailTravel) := by
            rw [FullTM0.Tape.moveN_add]
      · intro forward hforward
        by_cases hzero : forward = 0
        · subst forward
          simpa only [FullTM0.Tape.moveN_zero] using fun heq =>
            hsource
              ((boundarySymbol_injective i.castSucc 0).mp
                (hread.symm.trans heq))
        by_cases hfirst : forward < distance + 1
        · have hindex : forward - 1 < distance := by omega
          have hblank := gap.blank hindex
          have hmove :
              (start.moveN (orient growth .right) forward).read =
                ((start.move (orient growth .right)).moveN
                  (orient growth .right) (forward - 1)).read := by
            rw [FullTM0.Tape.move_moveN]
            congr 2
            omega
          rw [hmove]
          simpa only [FullTM0.Tape.read_moveN] using fun heq =>
            blankSymbol_ne_boundarySymbol 0 (hblank.symm.trans heq)
        · let later := forward - (distance + 1)
          have hlater : later ≤ tailTravel := by
            dsimp only [later]
            omega
          have hstartUpper :
              start.moveN (orient growth .right) (distance + 1) = upper := by
            dsimp only [upper]
            exact (FullTM0.Tape.move_moveN start
              (orient growth .right) distance).symm
          have hsum : distance + 1 + later = forward := by
            dsimp only [later]
            omega
          rw [← hsum, ← FullTM0.Tape.moveN_add, hstartUpper]
          exact havoids later hlater

/-- Moving the terminal boundary of a strict outward preserving route one
cell inward creates an inward ray bridge to the route's original source.

The blank immediately before `finish` is the positive-decrement branch
condition.  It implies that the physical route travel is at least two, so
the shifted terminal boundary does not overwrite the source boundary. -/
theorem ToUpper.inwardRayBridge_of_firstDecrementShift
    {growth : Turing.Dir} {source target : Fin 5}
    {route : List MarkerValidation.Leg}
    (hroute : ToUpper source target route)
    (hstrict : (source : Nat) < (target : Nat))
    {start finish : FullTM0.Tape (Symbol numTags)}
    (hread : start.read = boundarySymbol source)
    (hsource : source ≠ 0)
    (htrace : RouteTailGaps growth route start finish)
    (hblank : (finish.move (orient growth .left)).read = blankSymbol) :
    Nonempty (InwardRayBridge growth
      ((shiftStepTape (orient growth .right)
        (finish.move (orient growth .left)) 1 target).move
          (orient growth .left)) start) := by
  rcases outwardRouteGeometry hroute hread hsource htrace with ⟨geometry⟩
  have hopposite :
      NestingMachine.opposite (orient growth .right) =
        orient growth .left := by
    cases growth <;> rfl
  have htravelPositive : 0 < geometry.travel := by
    by_contra hnot
    have hzero : geometry.travel = 0 := by omega
    have hfinish : finish = start := by simpa [hzero] using geometry.finish_eq
    have htargetRead : finish.read = boundarySymbol target :=
      hroute.finish_read hread htrace
    rw [hfinish, hread] at htargetRead
    have heq := (boundarySymbol_injective source target).mp htargetRead
    exact (Nat.ne_of_lt hstrict) (congrArg Fin.val heq)
  have htravelNeOne : geometry.travel ≠ 1 := by
    intro hone
    have hreturn : finish.move (orient growth .left) = start := by
      rw [geometry.finish_eq, hone]
      funext position
      cases growth <;>
        simp [orient, FullTM0.Tape.move, FullTM0.Tape.moveN,
          FullTM0.Tape.offset]
    rw [hreturn, hread] at hblank
    exact blankSymbol_ne_boundarySymbol source hblank.symm
  have htravelTwo : 2 ≤ geometry.travel := by omega
  let bridgeTravel := geometry.travel - 1
  let shifted := shiftStepTape (orient growth .right)
    (finish.move (orient growth .left)) 1 target
  refine ⟨⟨bridgeTravel, ?_, ?_⟩⟩
  · intro back
    let remaining := geometry.travel - 2 + back
    have hremaining : 1 + remaining = bridgeTravel + back := by
      dsimp only [remaining, bridgeTravel]
      omega
    have hbehind := shiftStepTape_behind (orient growth .right)
      (finish.move (orient growth .left)) 1 remaining target (by omega)
    rw [hopposite] at hbehind
    change ((shifted.move (orient growth .left)).moveN
        (orient growth .left) (1 + remaining)).read = _ at hbehind
    rw [hremaining] at hbehind
    rw [hbehind]
    have hfinishBack :
        ((finish.move (orient growth .left)).move
            (orient growth .left)).moveN (orient growth .left) remaining =
          start.moveN (orient growth .left) back := by
      rw [geometry.finish_eq]
      funext position
      cases growth <;>
        simp [orient, FullTM0.Tape.move, FullTM0.Tape.moveN,
          FullTM0.Tape.offset, remaining] <;>
        congr 1 <;> omega
    rw [hfinishBack]
  · intro back hback
    by_cases hzero : back = 0
    · subst back
      have hdestination := shiftStepTape_destination (orient growth .right)
        (finish.move (orient growth .left)) 1 target
      rw [hopposite] at hdestination
      change (shifted.move (orient growth .left)).read = boundarySymbol target
        at hdestination
      rw [FullTM0.Tape.moveN_zero, hdestination]
      intro heq
      have htarget : target = 0 :=
        (boundarySymbol_injective target 0).mp heq
      subst target
      simp at hstrict
    · have hpositive : 0 < back := Nat.pos_of_ne_zero hzero
      let forward := geometry.travel - (back + 1)
      have hforward : forward ≤ geometry.travel := Nat.sub_le _ _
      have hshiftRead :
          ((shifted.move (orient growth .left)).moveN
              (orient growth .left) back).read =
            (start.moveN (orient growth .right) forward).read := by
        let remaining := back - 1
        have hone : 1 + remaining = back := by
          dsimp only [remaining]
          omega
        have hbehind := shiftStepTape_behind (orient growth .right)
          (finish.move (orient growth .left)) 1 remaining target (by omega)
        rw [hopposite] at hbehind
        change ((shifted.move (orient growth .left)).moveN
            (orient growth .left) (1 + remaining)).read = _ at hbehind
        rw [hone] at hbehind
        rw [hbehind]
        rw [geometry.finish_eq]
        dsimp only [remaining, forward]
        cases growth <;>
          simp [orient, FullTM0.Tape.move, FullTM0.Tape.moveN,
            FullTM0.Tape.offset] <;>
          congr 1 <;> omega
      rw [hshiftRead]
      exact geometry.avoidsZero forward hforward

/-- Prepend the backward geometry of later positive-decrement shifts to an
existing bridge at the first shifted boundary. -/
def InwardRayBridge.prependShiftTail
    {growth : Turing.Dir} {labels : List (Fin 5)}
    {start finish found : FullTM0.Tape (Symbol numTags)}
    (bridge : InwardRayBridge growth
      (start.move (orient growth .left)) found)
    (geometry : ShiftTailBackwardGeometry (orient growth .right)
      labels start finish)
    (labelsNe : ∀ label ∈ labels, label ≠ (0 : Fin 5)) :
    InwardRayBridge growth (finish.move (orient growth .left)) found := by
  refine ⟨geometry.travel + bridge.travel, ?_, ?_⟩
  · intro back
    have hopposite :
        NestingMachine.opposite (orient growth .right) =
          orient growth .left := by
      cases growth <;> rfl
    have hbehind := geometry.behind (bridge.travel + back)
    rw [hopposite] at hbehind
    calc
      ((finish.move (orient growth .left)).moveN
          (orient growth .left)
          (geometry.travel + bridge.travel + back)).read =
        ((finish.move (orient growth .left)).moveN
          (orient growth .left)
          (geometry.travel + (bridge.travel + back))).read := by
            rw [show geometry.travel + bridge.travel + back =
              geometry.travel + (bridge.travel + back) by omega]
      _ = ((start.move (orient growth .left)).moveN
          (orient growth .left) (bridge.travel + back)).read := by
        exact hbehind
      _ = (found.moveN (orient growth .left) back).read := bridge.ray back
  · intro back hback
    have hopposite :
        NestingMachine.opposite (orient growth .right) =
          orient growth .left := by
      cases growth <;> rfl
    by_cases hprefix : back ≤ geometry.travel
    · have hstartAvoid :
          (start.move (orient growth .left)).read ≠ boundarySymbol 0 := by
          simpa only [FullTM0.Tape.moveN_zero] using
            bridge.avoidsZero 0 (Nat.zero_le bridge.travel)
      have havoid := geometry.avoids (0 : Fin 5) (by
        rw [hopposite]
        exact hstartAvoid) labelsNe back hprefix
      rw [hopposite] at havoid
      exact havoid
    · let tailBack := back - geometry.travel
      have hlocal : tailBack ≤ bridge.travel := by
        dsimp only [tailBack]
        omega
      have hsum : back = geometry.travel + tailBack := by
        dsimp only [tailBack]
        omega
      rw [hsum]
      have hbehind := geometry.behind tailBack
      rw [hopposite] at hbehind
      rw [hbehind]
      exact bridge.avoidsZero tailBack hlocal

end

end CounterControlOutwardRouteShiftRay
end Hooper
end Kari
end LeanWang
