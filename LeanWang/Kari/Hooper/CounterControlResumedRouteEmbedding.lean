/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlResumedRouteProgress
import LeanWang.Kari.Hooper.CounterControlValidationRoundtrip

/-!
# Embedding resumed preserving-route callers

The exact route suffix retained by `CounterControlResumedRouteProgress`
locates a resumed caller inside the counter core reconstructed at the next
logical entry.  This file packages the tape geometry needed for that
comparison.  Its basic step runs one successful route leg backwards: if the
leg ends at a known canonical boundary and started on the adjacent labelled
boundary, then its starting tape was the corresponding canonical boundary
view.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlResumedRouteEmbedding

open Turing CounterMachine
open BoundedMarkerProgram FramedMarkerTape
open CounterControlPlan CounterControlBridge
open CounterControlCoreFrame CounterControlPrefixInstructionResolution
open CounterControlParentEmbedding CounterControlParentContinuation
open CounterControlSearchSystem
open CounterControlPrefixResume CounterControlRouteSuffixMortality
open CounterControlResumedRouteProgress

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-! ## Reversing one adjacent route leg -/

/-- Reverse a preserving route search, using the labelled boundary under
the head immediately before its one-cell departure. -/
private theorem reverseGap_of_source_boundary
    {T : FullTM0.Tape (Symbol numTags)} {direction : Turing.Dir}
    {distance : Nat} {found source : Fin 5}
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary found).Matches (T.move direction) direction distance)
    (hsource : T.read = boundarySymbol source) :
    SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary source).Matches
      (((T.move direction).moveN direction distance).move
        (NestingMachine.opposite direction))
      (NestingMachine.opposite direction) distance := by
  have hbehind :
      ((T.move direction).move
        (NestingMachine.opposite direction)).read = boundarySymbol source := by
    cases direction <;>
      simpa [NestingMachine.opposite, FullTM0.Tape.read,
        FullTM0.Tape.move] using hsource
  constructor
  · intro i hi
    let j := distance - i - 1
    have hj : j < distance := by
      dsimp [j]
      omega
    have hsum : j + i + 1 = distance := by
      dsimp [j]
      omega
    have hsumInt : (j : Int) + (i : Int) + 1 = (distance : Int) := by
      exact_mod_cast hsum
    have hblank := hgap.blank hj
    cases direction with
    | left =>
        simp only [NestingMachine.opposite, FullTM0.Tape.move_apply_delta,
          FullTM0.Tape.moveN_apply, FullTM0.Tape.offset_left,
          FullTM0.Tape.offset_right, FullTM0.Tape.delta_right,
          FullTM0.Tape.delta_left] at hblank ⊢
        rw [show -(j : Int) = (i : Int) + 1 + -(distance : Int) by omega]
          at hblank
        exact hblank
    | right =>
        simp only [NestingMachine.opposite, FullTM0.Tape.move_apply_delta,
          FullTM0.Tape.moveN_apply, FullTM0.Tape.offset_left,
          FullTM0.Tape.offset_right, FullTM0.Tape.delta_left,
          FullTM0.Tape.delta_right] at hblank ⊢
        rw [show (j : Int) = -(i : Int) + -1 + (distance : Int) by omega]
          at hblank
        exact hblank
  · cases direction <;>
      simpa [Target.Matches, FullTM0.Tape.read,
        NestingMachine.opposite, FullTM0.Tape.move_apply_delta,
        FullTM0.Tape.moveN_apply, FullTM0.Tape.offset_left,
        FullTM0.Tape.offset_right, FullTM0.Tape.delta_left,
        FullTM0.Tape.delta_right] using hbehind

/-- The tape before a rightward leg is forced to be the canonical preceding
boundary once the found tape is anchored at the canonical next boundary. -/
theorem start_eq_of_rightLeg_found
    {registers : Registers} {growth : Turing.Dir}
    {coreTape T : FullTM0.Tape (Symbol numTags)}
    (hcore : CoreRepresents registers growth coreTape) (i : Fin 4)
    (distance : Nat)
    (hsource : T.read = boundarySymbol i.castSucc)
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary i.succ).Matches
      (T.move (orient growth .right)) (orient growth .right) distance)
    (hfound :
      (T.move (orient growth .right)).moveN
          (orient growth .right) distance =
        atLogical growth coreTape (boundaryOffset registers i.succ)) :
    T = atLogical growth coreTape (boundaryOffset registers i.castSucc) := by
  have hreverse := reverseGap_of_source_boundary hgap hsource
  have hcanonical := hcore.searchGap_adjacent_left i
  have hstart :
      (((T.move (orient growth .right)).moveN
          (orient growth .right) distance).move
            (orient growth .left)) =
        atLogical growth coreTape (lastGapOffset registers i) := by
    rw [hfound]
    simp only [orient_eq_orientDirection]
    rw [show boundaryOffset registers i.succ =
        lastGapOffset registers i + 1 by
      simp [lastGapOffset, boundaryOffset,
        CounterLayout.boundaryPos_succ]]
    rw [atLogical_move_left]
  have hdistance : distance = RegisterLayout.values registers i := by
    apply BoundedMarkerProgram.boundaryGap_distance_unique hreverse
    rw [show NestingMachine.opposite (orient growth .right) =
        orient growth .left by cases growth <;> rfl]
    rw [hstart]
    exact hcanonical
  apply Function.LeftInverse.injective
    (g := fun U : FullTM0.Tape (Symbol numTags) =>
      U.moveN (NestingMachine.opposite (orient growth .right))
        (distance + 1))
    (f := fun U : FullTM0.Tape (Symbol numTags) =>
      U.moveN (orient growth .right) (distance + 1))
  · intro U
    exact CanonicalInitializerProgram.moveN_opposite U
      (orient growth .right) (distance + 1)
  · change T.moveN (orient growth .right) (distance + 1) = _
    rw [← FullTM0.Tape.move_moveN T (orient growth .right) distance,
      hfound, hdistance]
    simp only [orient_eq_orientDirection]
    rw [atLogical_moveN_right]
    congr 1
    simp [boundaryOffset, CounterLayout.boundaryPos_succ]
    omega

/-- Leftward counterpart of `start_eq_of_rightLeg_found`. -/
theorem start_eq_of_leftLeg_found
    {registers : Registers} {growth : Turing.Dir}
    {coreTape T : FullTM0.Tape (Symbol numTags)}
    (hcore : CoreRepresents registers growth coreTape) (i : Fin 4)
    (distance : Nat)
    (hsource : T.read = boundarySymbol i.succ)
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary i.castSucc).Matches
      (T.move (orient growth .left)) (orient growth .left) distance)
    (hfound :
      (T.move (orient growth .left)).moveN
          (orient growth .left) distance =
        atLogical growth coreTape
          (boundaryOffset registers i.castSucc)) :
    T = atLogical growth coreTape (boundaryOffset registers i.succ) := by
  have hreverse := reverseGap_of_source_boundary hgap hsource
  have hcanonical := hcore.searchGap_adjacent_right i
  have hstart :
      (((T.move (orient growth .left)).moveN
          (orient growth .left) distance).move
            (orient growth .right)) =
        atLogical growth coreTape (firstGapOffset registers i) := by
    rw [hfound]
    simp only [orient_eq_orientDirection]
    rw [atLogical_move_right]
    simp [firstGapOffset, boundaryOffset]
  have hdistance : distance = RegisterLayout.values registers i := by
    apply BoundedMarkerProgram.boundaryGap_distance_unique hreverse
    rw [show NestingMachine.opposite (orient growth .left) =
        orient growth .right by cases growth <;> rfl]
    rw [hstart]
    exact hcanonical
  apply Function.LeftInverse.injective
    (g := fun U : FullTM0.Tape (Symbol numTags) =>
      U.moveN (NestingMachine.opposite (orient growth .left))
        (distance + 1))
    (f := fun U : FullTM0.Tape (Symbol numTags) =>
      U.moveN (orient growth .left) (distance + 1))
  · intro U
    exact CanonicalInitializerProgram.moveN_opposite U
      (orient growth .left) (distance + 1)
  · change T.moveN (orient growth .left) (distance + 1) = _
    rw [← FullTM0.Tape.move_moveN T (orient growth .left) distance,
      hfound, hdistance]
    simp only [orient_eq_orientDirection]
    rw [show boundaryOffset registers i.succ =
        boundaryOffset registers i.castSucc +
          (RegisterLayout.values registers i + 1) by
      simp [boundaryOffset, CounterLayout.boundaryPos_succ]
      omega]
    rw [atLogical_moveN_left]

/-! ## Consecutive rightward suffixes ending at boundary four -/

/-- A route consisting of all consecutive rightward legs from one boundary
to boundary `4`.  The boundary index is part of the type, so no coordinate
information is lost when taking a suffix of an instruction route. -/
inductive ToFour : Fin 5 → List MarkerValidation.Leg → Prop where
  | four : ToFour 4 []
  | step (i : Fin 4) {rest : List MarkerValidation.Leg}
      (tail : ToFour i.succ rest) :
      ToFour i.castSucc (⟨i.succ, .right⟩ :: rest)

/-- Any selected position of a nonempty `ToFour` route is a rightward leg
and leaves another `ToFour` route after its found boundary. -/
theorem ToFour.position
    {source : Fin 5} {route before : List MarkerValidation.Leg}
    {current : MarkerValidation.Leg}
    {remaining : List MarkerValidation.Leg}
    (hroute : ToFour source route)
    (hposition : route = before ++ current :: remaining) :
    ∃ i : Fin 4,
      current = ⟨i.succ, .right⟩ ∧ ToFour i.succ remaining := by
  induction hroute generalizing before current remaining with
  | four => simp at hposition
  | step i tail ih =>
      cases before with
      | nil =>
          simp only [List.nil_append, List.cons.injEq] at hposition
          exact ⟨i, hposition.1.symm, hposition.2 ▸ tail⟩
      | cons first before =>
          simp only [List.cons_append, List.cons.injEq] at hposition
          exact ih hposition.2

/-- Increment recovery always follows a consecutive rightward suffix of the
five-boundary layout. -/
theorem routeFromIncrement_toFour (register : Register) :
    ∃ source : Fin 5,
      ToFour source (AnchoredCounterGeometry.routeFromIncrement register) := by
  cases register with
  | left => exact ⟨1, .step 1 (.step 2 (.step 3 .four))⟩
  | right => exact ⟨2, .step 2 (.step 3 .four)⟩
  | temp => exact ⟨3, .step 3 .four⟩
  | clock => exact ⟨4, .four⟩

/-- Zero recovery starts one boundary farther inward and is likewise a
consecutive rightward suffix ending at boundary `4`. -/
theorem routeFromZero_toFour (register : Register) :
    ∃ source : Fin 5,
      ToFour source (AnchoredCounterGeometry.routeFromZero register) := by
  cases register with
  | left => exact ⟨0, .step 0 (.step 1 (.step 2 (.step 3 .four)))⟩
  | right => exact ⟨1, .step 1 (.step 2 (.step 3 .four))⟩
  | temp => exact ⟨2, .step 2 (.step 3 .four)⟩
  | clock => exact ⟨3, .step 3 .four⟩

/-- Expose the first found tape of a nonempty route trace, retaining the
remaining trace in the found-state form used by `RouteTailGaps`. -/
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

/-- A successful consecutive tail ending on canonical boundary `4` started
on the corresponding canonical boundary. -/
theorem ToFour.start_eq
    {registers : Registers} {growth : Turing.Dir}
    {coreTape T finish : FullTM0.Tape (Symbol numTags)}
    {source : Fin 5} {route : List MarkerValidation.Leg}
    (hcore : CoreRepresents registers growth coreTape)
    (hroute : ToFour source route)
    (hread : T.read = boundarySymbol source)
    (htrace : RouteTailGaps growth route T finish)
    (hfinish : finish = atLogical growth coreTape (layoutEnd registers)) :
    T = atLogical growth coreTape (boundaryOffset registers source) := by
  induction hroute generalizing T finish with
  | four =>
      cases htrace with
      | nil =>
          rw [hfinish]
          simp [boundaryOffset_four]
  | step i tail ih =>
      cases htrace with
      | cons _ _ T finish trace =>
          rcases routeGaps_uncons growth ⟨i.succ, .right⟩ _ _ _ trace with
            ⟨distance, gap, restTrace⟩
          let found :=
            ((T.move (orient growth .right)).moveN
              (orient growth .right) distance)
          have hfoundRead : found.read = boundarySymbol i.succ := by
            change (Target.boundary i.succ).Matches found.read
            simpa [found, FullTM0.Tape.read_moveN] using gap.marked
          have hfoundCanonical :
              found = atLogical growth coreTape
                (boundaryOffset registers i.succ) := by
            exact ih hfoundRead restTrace hfinish
          exact start_eq_of_rightLeg_found hcore i distance hread gap
            hfoundCanonical

/-! ## A search ending on an internal canonical boundary is short -/

/-- Moving back a shorter run after a longer run in the opposite direction
subtracts their lengths. -/
private theorem moveN_moveN_opposite_sub
    (T : FullTM0.Tape (Symbol numTags)) (direction : Turing.Dir)
    (distance back : Nat) (hback : back ≤ distance) :
    (T.moveN direction distance).moveN
        (NestingMachine.opposite direction) back =
      T.moveN direction (distance - back) := by
  funext position
  cases direction <;>
    simp [NestingMachine.opposite, FullTM0.Tape.moveN,
      FullTM0.Tape.offset] <;>
    congr 1 <;> omega

/-- A rightward blank search ending at canonical boundary `i+1` cannot be
as long as the complete five-boundary core: otherwise it would cross the
preceding nonblank boundary `i`. -/
theorem rightGap_distance_lt_layoutEnd
    {registers : Registers} {growth : Turing.Dir}
    {coreTape outer : FullTM0.Tape (Symbol numTags)}
    (hcore : CoreRepresents registers growth coreTape) (i : Fin 4)
    (distance : Nat)
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary i.succ).Matches outer (orient growth .right) distance)
    (hfound : outer.moveN (orient growth .right) distance =
      atLogical growth coreTape (boundaryOffset registers i.succ)) :
    distance < layoutEnd registers := by
  by_contra hnot
  have hend : layoutEnd registers ≤ distance := Nat.le_of_not_gt hnot
  let back := RegisterLayout.values registers i + 1
  have hbackPos : 0 < back := by simp [back]
  have hback : back ≤ distance := by
    apply le_trans _ hend
    fin_cases i <;>
      simp [back, layoutEnd_eq, RegisterLayout.values] <;> omega
  let k := distance - back
  have hk : k < distance := by
    dsimp [k]
    omega
  have hblank := hgap.blank hk
  have hreturn :
      outer.moveN (orient growth .right) k =
        atLogical growth coreTape
          (boundaryOffset registers i.castSucc) := by
    calc
      outer.moveN (orient growth .right) k =
          (outer.moveN (orient growth .right) distance).moveN
            (NestingMachine.opposite (orient growth .right)) back := by
        symm
        simpa [k] using moveN_moveN_opposite_sub outer
          (orient growth .right) distance back hback
      _ = (atLogical growth coreTape
            (boundaryOffset registers i.succ)).moveN
              (NestingMachine.opposite (orient growth .right)) back := by
        rw [hfound]
      _ = atLogical growth coreTape
            (boundaryOffset registers i.castSucc) := by
        rw [show NestingMachine.opposite (orient growth .right) =
            OrientedMarkerTape.orientDirection growth .left by
          cases growth <;> rfl]
        rw [show boundaryOffset registers i.succ =
            boundaryOffset registers i.castSucc + back by
          simp [back, boundaryOffset, CounterLayout.boundaryPos_succ]
          omega]
        exact atLogical_moveN_left growth coreTape _ back
  have hblankRead : (outer.moveN (orient growth .right) k).read =
      blankSymbol := by
    simpa [FullTM0.Tape.read_moveN] using hblank
  rw [hreturn, atLogical_read, hcore.boundary] at hblankRead
  exact blankSymbol_ne_boundarySymbol i.castSucc hblankRead.symm

/-- Leftward counterpart of `rightGap_distance_lt_layoutEnd`. -/
theorem leftGap_distance_lt_layoutEnd
    {registers : Registers} {growth : Turing.Dir}
    {coreTape outer : FullTM0.Tape (Symbol numTags)}
    (hcore : CoreRepresents registers growth coreTape) (i : Fin 4)
    (distance : Nat)
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary i.castSucc).Matches outer (orient growth .left) distance)
    (hfound : outer.moveN (orient growth .left) distance =
      atLogical growth coreTape
        (boundaryOffset registers i.castSucc)) :
    distance < layoutEnd registers := by
  by_contra hnot
  have hend : layoutEnd registers ≤ distance := Nat.le_of_not_gt hnot
  let back := RegisterLayout.values registers i + 1
  have hbackPos : 0 < back := by simp [back]
  have hback : back ≤ distance := by
    apply le_trans _ hend
    fin_cases i <;>
      simp [back, layoutEnd_eq, RegisterLayout.values] <;> omega
  let k := distance - back
  have hk : k < distance := by
    dsimp [k]
    omega
  have hblank := hgap.blank hk
  have hreturn :
      outer.moveN (orient growth .left) k =
        atLogical growth coreTape (boundaryOffset registers i.succ) := by
    calc
      outer.moveN (orient growth .left) k =
          (outer.moveN (orient growth .left) distance).moveN
            (NestingMachine.opposite (orient growth .left)) back := by
        symm
        simpa [k] using moveN_moveN_opposite_sub outer
          (orient growth .left) distance back hback
      _ = (atLogical growth coreTape
            (boundaryOffset registers i.castSucc)).moveN
              (NestingMachine.opposite (orient growth .left)) back := by
        rw [hfound]
      _ = atLogical growth coreTape (boundaryOffset registers i.succ) := by
        rw [show NestingMachine.opposite (orient growth .left) =
            OrientedMarkerTape.orientDirection growth .right by
          cases growth <;> rfl]
        rw [atLogical_moveN_right]
        congr 1
        simp [back, boundaryOffset, CounterLayout.boundaryPos_succ]
        omega
  have hblankRead : (outer.moveN (orient growth .left) k).read =
      blankSymbol := by
    simpa [FullTM0.Tape.read_moveN] using hblank
  rw [hreturn, atLogical_read, hcore.boundary] at hblankRead
  exact blankSymbol_ne_boundarySymbol i.succ hblankRead.symm

/-! ## Exact resumed route coordinates -/

/-- The selected route command reads the boundary named by its retained
route position at the exact parent found tape. -/
theorem ResumedRouteEnd.current_read
    {base : Nat} {c : Nat.Partrec.Code}
    {frame : PrefixEnvelope}
    {start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (resumed : PrefixResumedSearch base c frame start)
    {growth : Turing.Dir} {source searchSlot directSlot : Nat}
    {after : ControlRef} {route : List MarkerValidation.Leg}
    (progress : ResumedRouteEnd resumed growth source searchSlot directSlot
      after route) :
    resumed.parentFoundTape.read =
      boundarySymbol progress.suffix.current.target := by
  have htarget := resumed.selectedRaw_target_matches_parentFoundTape
  rw [CounterControlCommandAt.compileRawCommand_spec] at htarget
  simpa [progress.suffix.raw_eq,
    CounterControlCommandAt.compileRawAtTag, Command.target,
    Target.Matches, compileNavigationAction] using htarget

/-- The genuine resumed search is exactly the selected route leg, including
its logical direction and boundary target. -/
theorem ResumedRouteEnd.current_gap
    {base : Nat} {c : Nat.Partrec.Code}
    {frame : PrefixEnvelope}
    {start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (resumed : PrefixResumedSearch base c frame start)
    {growth : Turing.Dir} {source searchSlot directSlot : Nat}
    {after : ControlRef} {route : List MarkerValidation.Leg}
    (progress : ResumedRouteEnd resumed growth source searchSlot directSlot
      after route) :
    SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary progress.suffix.current.target).Matches
      resumed.next.outer
      (orient growth progress.suffix.current.direction)
      resumed.next.distance := by
  have hgap := resumed.next.gap
  rw [← resumed.compileRawCommand_selectedRaw,
    CounterControlCommandAt.compileRawCommand_spec] at hgap
  simpa [progress.suffix.raw_eq,
    CounterControlCommandAt.compileRawAtTag, Command.target,
    Command.searchDirection, compileNavigationAction] using hgap

/-- Resolving the genuine resumed gap reaches the exact parent found tape,
expressed in the selected route leg's physical direction. -/
theorem ResumedRouteEnd.current_foundTape
    {base : Nat} {c : Nat.Partrec.Code}
    {frame : PrefixEnvelope}
    {start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (resumed : PrefixResumedSearch base c frame start)
    {growth : Turing.Dir} {source searchSlot directSlot : Nat}
    {after : ControlRef} {route : List MarkerValidation.Leg}
    (progress : ResumedRouteEnd resumed growth source searchSlot directSlot
      after route) :
    resumed.next.outer.moveN
        (orient growth progress.suffix.current.direction)
        resumed.next.distance =
      resumed.parentFoundTape := by
  have htape := congrArg FullTM0.Cfg.tape resumed.foundCfg_eq_parentFound
  change resumed.next.outer.moveN
      (command base c resumed.next.search).searchDirection
      resumed.next.distance = resumed.parentFoundTape at htape
  rw [← resumed.compileRawCommand_selectedRaw,
    CounterControlCommandAt.compileRawCommand_spec] at htape
  simpa [progress.suffix.raw_eq,
    CounterControlCommandAt.compileRawAtTag,
    Command.searchDirection] using htape

/-! ## Recovery routes reach a containing logical core -/

/-- Generic logical-endpoint theorem for a consecutive rightward recovery
route.  The explicit target-state bound is genuine provenance: the compact
`ResumedRouteEnd` remembers the endpoint reference but not the source-program
rule from which that reference was generated. -/
theorem logical_of_toFour_endpoint
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    {frame : PrefixEnvelope}
    {start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (resumed : PrefixResumedSearch base c frame start)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      (foundCfg resumed.next))
    (growth : Turing.Dir) (source searchSlot directSlot targetState : Nat)
    (route : List MarkerValidation.Leg)
    (progress : ResumedRouteEnd resumed growth source searchSlot directSlot
      (.logical growth targetState) route)
    (htargetState : targetState < logicalSpan)
    (hroute : ∃ routeSource : Fin 5, ToFour routeSource route) :
    Nonempty (FoundParentEmbeddingOutcome resumed.next) := by
  rcases hroute with ⟨routeSource, hroute⟩
  rcases hroute.position progress.suffix.route_eq with
    ⟨i, hcurrent, htail⟩
  have himmortalLogical := FullTM0.ImmortalFrom.of_reaches himmortal
    progress.reaches
  change FullTM0.ImmortalFrom
    (CounterControlNestingBridge.machine base c)
    ⟨logicalState base c growth targetState, progress.suffix.finish⟩
      at himmortalLogical
  rcases CounterControlValidationRoundtrip.logical_reconstructs_coreTarget_fields_of_immortal
      base c hmortal growth targetState htargetState progress.suffix.finish
      himmortalLogical with
    ⟨instruction, registers, coreTape, limit, target, _hrule, hcore,
      hcoreBefore, hrunway, htarget, hcenter, _hbody⟩
  let represented : CoreTargetRepresents registers growth limit target
      coreTape := {
    toCorePrefixRepresents := {
      toCoreRepresents := hcore
      core_before_limit := hcoreBefore
      runway := hrunway }
    target_matches := htarget }
  let core : LogicalCore base c := {
    growth := growth
    source := targetState
    source_lt := htargetState
    registers := registers
    tape := coreTape
    limit := limit
    target := target
    represented := represented }
  have hread : resumed.parentFoundTape.read = boundarySymbol i.succ := by
    have hread' := ResumedRouteEnd.current_read resumed progress
    rw [hcurrent] at hread'
    exact hread'
  have hfoundBoundary : resumed.parentFoundTape =
      atLogical growth coreTape (boundaryOffset registers i.succ) := by
    exact htail.start_eq hcore hread progress.suffix.tailGaps hcenter
  have hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary i.succ).Matches resumed.next.outer
      (orient growth .right) resumed.next.distance := by
    have hgap' := ResumedRouteEnd.current_gap resumed progress
    rw [hcurrent] at hgap'
    exact hgap'
  have hfound : resumed.next.outer.moveN (orient growth .right)
        resumed.next.distance =
      atLogical growth coreTape (boundaryOffset registers i.succ) := by
    have hfound' := ResumedRouteEnd.current_foundTape resumed progress
    rw [hcurrent] at hfound'
    exact hfound'.trans hfoundBoundary
  have hinside : resumed.next.distance < layoutEnd registers :=
    rightGap_distance_lt_layoutEnd hcore i resumed.next.distance hgap hfound
  have hreaches : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      (foundCfg resumed.next) core.cfg := by
    have hrun := progress.reaches
    change FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      (foundCfg resumed.next)
      ⟨logicalState base c growth targetState,
        progress.suffix.finish⟩ at hrun
    rw [hcenter] at hrun
    simpa [core, LogicalCore.cfg, LogicalCore.frame,
      LogicalCore.abstract, prefixLogicalCfg] using hrun
  exact ⟨.logical core hreaches hinside⟩

/-- Increment recovery reaches a containing logical core once its generated
logical target is known to lie in the allocated state interval. -/
theorem incrementRecovery_logical
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    {frame : PrefixEnvelope}
    {start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (resumed : PrefixResumedSearch base c frame start)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      (foundCfg resumed.next))
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (next : Nat)
    (progress : ResumedRouteEnd resumed growth source secondarySearchBase
      (bodyDirectBase + 2) (.logical growth next)
      (AnchoredCounterGeometry.routeFromIncrement register))
    (hnext : next < logicalSpan) :
    Nonempty (FoundParentEmbeddingOutcome resumed.next) := by
  apply logical_of_toFour_endpoint base c hmortal resumed himmortal growth
    source secondarySearchBase (bodyDirectBase + 2) next
    (AnchoredCounterGeometry.routeFromIncrement register) progress hnext
  exact routeFromIncrement_toFour register

/-- Source-program provenance supplies the bounded target required by
`incrementRecovery_logical`. -/
theorem incrementRecovery_logical_of_rule
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    {frame : PrefixEnvelope}
    {start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (resumed : PrefixResumedSearch base c frame start)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      (foundCfg resumed.next))
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (next : Nat)
    (hrule : (source, .increment register next) ∈
      GlobalSourceProgram.program)
    (progress : ResumedRouteEnd resumed growth source secondarySearchBase
      (bodyDirectBase + 2) (.logical growth next)
      (AnchoredCounterGeometry.routeFromIncrement register)) :
    Nonempty (FoundParentEmbeddingOutcome resumed.next) := by
  apply incrementRecovery_logical base c hmortal resumed himmortal growth
    source register next progress
  exact state_lt_logicalSpan
    (CounterControlAbstractTrace.target_mem_programStates hrule
      (by simp [instructionTargets]))

/-- Zero recovery reaches a containing logical core once its generated zero
target is known to lie in the allocated state interval. -/
theorem zeroRecovery_logical
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    {frame : PrefixEnvelope}
    {start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (resumed : PrefixResumedSearch base c frame start)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      (foundCfg resumed.next))
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (ifZero : Nat)
    (progress : ResumedRouteEnd resumed growth source zeroSearchBase
      zeroDirectBase (.logical growth ifZero)
      (AnchoredCounterGeometry.routeFromZero register))
    (hifZero : ifZero < logicalSpan) :
    Nonempty (FoundParentEmbeddingOutcome resumed.next) := by
  apply logical_of_toFour_endpoint base c hmortal resumed himmortal growth
    source zeroSearchBase zeroDirectBase ifZero
    (AnchoredCounterGeometry.routeFromZero register) progress hifZero
  exact routeFromZero_toFour register

/-- Source-program provenance supplies the bounded target required by
`zeroRecovery_logical`. -/
theorem zeroRecovery_logical_of_rule
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    {frame : PrefixEnvelope}
    {start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (resumed : PrefixResumedSearch base c frame start)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      (foundCfg resumed.next))
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (ifZero ifPositive : Nat)
    (hrule : (source, .decrement register ifZero ifPositive) ∈
      GlobalSourceProgram.program)
    (progress : ResumedRouteEnd resumed growth source zeroSearchBase
      zeroDirectBase (.logical growth ifZero)
      (AnchoredCounterGeometry.routeFromZero register)) :
    Nonempty (FoundParentEmbeddingOutcome resumed.next) := by
  apply zeroRecovery_logical base c hmortal resumed himmortal growth source
    register ifZero progress
  exact state_lt_logicalSpan
    (CounterControlAbstractTrace.target_mem_programStates hrule
      (by simp [instructionTargets]))

end

end CounterControlResumedRouteEmbedding
end Hooper
end Kari
end LeanWang
