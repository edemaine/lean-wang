/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlDirectSemantics
import LeanWang.Kari.Hooper.CounterControlNavigationSemantics
import LeanWang.Kari.Hooper.FramedCounterGeometry

/-!
# Collision-cleanup semantics for the compiled counter controller

The first outward increment shift is the only shift which can meet the
suspended outer target.  Its collision exit clears boundary `4` and enters a
fixed cleanup chain.  The chain erases boundaries `3`, `2`, `1`, and `0`,
finds the saved return tag, and lets the shared dispatcher erase that tag.

This file proves the geometry and execution of that chain.  As for every
bounded search, an unexpectedly long register gap may launch another exact
nested frame; the alternative records the command which did so.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlCleanupSemantics

open Turing CounterMachine
open BoundedMarkerProgram FramedMarkerTape FramedCounterGeometry
open CounterControlPlan CounterControlCommandAt CounterControlBridge

noncomputable section

/-! ## The five successive cleanup tapes -/

def clearBoundary {numTags : Nat} (spec : Spec numTags)
    (T : FullTM0.Tape (Symbol numTags)) (label : Fin 5) :
    FullTM0.Tape (Symbol numTags) :=
  writeLogical spec.growth T (boundaryOffset spec.registers label)
    blankSymbol

def afterFour {numTags : Nat} (spec : Spec numTags)
    (T : FullTM0.Tape (Symbol numTags)) :
    FullTM0.Tape (Symbol numTags) :=
  clearBoundary spec T 4

def afterThree {numTags : Nat} (spec : Spec numTags)
    (T : FullTM0.Tape (Symbol numTags)) :
    FullTM0.Tape (Symbol numTags) :=
  clearBoundary spec (afterFour spec T) 3

def afterTwo {numTags : Nat} (spec : Spec numTags)
    (T : FullTM0.Tape (Symbol numTags)) :
    FullTM0.Tape (Symbol numTags) :=
  clearBoundary spec (afterThree spec T) 2

def afterOne {numTags : Nat} (spec : Spec numTags)
    (T : FullTM0.Tape (Symbol numTags)) :
    FullTM0.Tape (Symbol numTags) :=
  clearBoundary spec (afterTwo spec T) 1

def afterZero {numTags : Nat} (spec : Spec numTags)
    (T : FullTM0.Tape (Symbol numTags)) :
    FullTM0.Tape (Symbol numTags) :=
  clearBoundary spec (afterOne spec T) 0

def afterTag {numTags : Nat} (spec : Spec numTags)
    (T : FullTM0.Tape (Symbol numTags)) :
    FullTM0.Tape (Symbol numTags) :=
  writeLogical spec.growth (afterZero spec T) 0 blankSymbol

/-! ## Geometry of one erased-boundary search -/

private theorem atLogical_write_above_apply_left {numTags : Nat}
    (growth : Turing.Dir) (T : FullTM0.Tape (Symbol numTags))
    (written origin k : Nat) (symbol : Symbol numTags)
    (habove : origin < written) :
    atLogical growth (writeLogical growth T written symbol) origin
        (FullTM0.Tape.offset
          (OrientedMarkerTape.orientDirection growth .left) k) =
      atLogical growth T origin
        (FullTM0.Tape.offset
          (OrientedMarkerTape.orientDirection growth .left) k) := by
  rw [atLogical_apply_offset, atLogical_apply_offset]
  cases growth <;>
    simp [logicalTape, OrientedMarkerTape.orientTape, writeLogical,
      physicalCoord, Function.update, FullTM0.Tape.offset] <;> omega

private theorem searchGap_write_above_left {numTags : Nat}
    {IsMark : Symbol numTags → Prop} (growth : Turing.Dir)
    (T : FullTM0.Tape (Symbol numTags)) (written origin distance : Nat)
    (symbol : Symbol numTags) (habove : origin < written)
    (hgap : SearchGap (fun a => a = blankSymbol) IsMark
      (atLogical growth T origin)
      (OrientedMarkerTape.orientDirection growth .left) distance) :
    SearchGap (fun a => a = blankSymbol) IsMark
      (atLogical growth (writeLogical growth T written symbol) origin)
      (OrientedMarkerTape.orientDirection growth .left) distance := by
  constructor
  · intro k hk
    rw [atLogical_write_above_apply_left growth T written origin k symbol
      habove]
    exact hgap.blank hk
  · rw [atLogical_write_above_apply_left growth T written origin distance
      symbol habove]
    exact hgap.marked

private theorem searchGap_prepend_left {numTags : Nat}
    {IsMark : Symbol numTags → Prop} (growth : Turing.Dir)
    (T : FullTM0.Tape (Symbol numTags)) (origin distance : Nat)
    (hblank : (atLogical growth T (origin + 1)).read = blankSymbol)
    (hgap : SearchGap (fun a => a = blankSymbol) IsMark
      (atLogical growth T origin)
      (OrientedMarkerTape.orientDirection growth .left) distance) :
    SearchGap (fun a => a = blankSymbol) IsMark
      (atLogical growth T (origin + 1))
      (OrientedMarkerTape.orientDirection growth .left) (distance + 1) := by
  let start := atLogical growth T (origin + 1)
  let direction := OrientedMarkerTape.orientDirection growth .left
  have htail : SearchGap (fun a => a = blankSymbol) IsMark
      (start.move direction) direction distance := by
    change SearchGap (fun a => a = blankSymbol) IsMark
      ((atLogical growth T (origin + 1)).move
        (OrientedMarkerTape.orientDirection growth .left))
      (OrientedMarkerTape.orientDirection growth .left) distance
    rw [atLogical_move_left]
    exact hgap
  constructor
  · intro k hk
    cases k with
    | zero => simpa [start, FullTM0.Tape.read] using hblank
    | succ k =>
        have hk' : k < distance := by omega
        simpa [start, direction] using htail.blank hk'
  · simpa [start, direction] using htail.marked

private theorem boundaryOffset_succ_eq_lastGap_add_one
    (registers : Registers) (i : Fin 4) :
    boundaryOffset registers i.succ = lastGapOffset registers i + 1 := by
  simp [boundaryOffset, lastGapOffset]

/-- Once the right boundary of gap `i` has been erased, searching left from
that erased cell sees one additional blank followed by the original gap and
then boundary `i`. -/
theorem searchGap_erased_right_boundary {numTags : Nat}
    {spec : Spec numTags} {U : FullTM0.Tape (Symbol numTags)} (i : Fin 4)
    (hgap : SearchGap (fun a => a = blankSymbol)
      (Target.boundary i.castSucc).Matches
      (atLogical spec.growth U (lastGapOffset spec.registers i))
      (OrientedMarkerTape.orientDirection spec.growth .left)
      (RegisterLayout.values spec.registers i))
    (herased : logicalTape spec.growth U
      (boundaryOffset spec.registers i.succ) = blankSymbol) :
    SearchGap (fun a => a = blankSymbol)
      (Target.boundary i.castSucc).Matches
      (atLogical spec.growth U (boundaryOffset spec.registers i.succ))
      (OrientedMarkerTape.orientDirection spec.growth .left)
      (RegisterLayout.values spec.registers i + 1) := by
  rw [boundaryOffset_succ_eq_lastGap_add_one]
  apply searchGap_prepend_left spec.growth U
  · rw [atLogical_read]
    simpa [boundaryOffset_succ_eq_lastGap_add_one] using herased
  · exact hgap

private theorem written_boundary_above_lastGap
    (registers : Registers) (i : Fin 4) (label : Fin 5)
    (hlabel : (i : Nat) < label) :
    lastGapOffset registers i < boundaryOffset registers label := by
  simp only [lastGapOffset, boundaryOffset]
  have hle : (i : Nat) + 1 ≤ label := by omega
  have hmono := CounterLayout.boundaryPos_mono
    (RegisterLayout.values registers) hle
  omega

/-- The first cleanup command searches from erased boundary `4` to boundary
`3`. -/
theorem cleanupGap_three {numTags : Nat} {spec : Spec numTags}
    {T : FullTM0.Tape (Symbol numTags)} (h : Represents spec T) :
    SearchGap (fun a => a = blankSymbol)
      (Target.boundary 3).Matches
      (atLogical spec.growth (afterFour spec T)
        (boundaryOffset spec.registers 4))
      (OrientedMarkerTape.orientDirection spec.growth .left)
      (RegisterLayout.values spec.registers 3 + 1) := by
  have hbase : SearchGap (fun a => a = blankSymbol)
      (Target.boundary 3).Matches
      (atLogical spec.growth T (lastGapOffset spec.registers 3))
      (OrientedMarkerTape.orientDirection spec.growth .left)
      (RegisterLayout.values spec.registers 3) := by
    change SearchGap (fun a => a = blankSymbol)
      (fun symbol => symbol = boundarySymbol 3) _ _ _
    exact h.searchGap_adjacent_left (3 : Fin 4)
  have htail := searchGap_write_above_left spec.growth T
    (boundaryOffset spec.registers 4) (lastGapOffset spec.registers 3)
    (RegisterLayout.values spec.registers 3) blankSymbol
    (written_boundary_above_lastGap spec.registers 3 4 (by decide)) hbase
  apply searchGap_erased_right_boundary (spec := spec) (i := (3 : Fin 4))
  · simpa [afterFour, clearBoundary] using htail
  · change logicalTape spec.growth
      (writeLogical spec.growth T (boundaryOffset spec.registers 4)
        blankSymbol) (boundaryOffset spec.registers 4) = blankSymbol
    exact writeLogical_at spec.growth T
      (boundaryOffset spec.registers 4) blankSymbol

/-- The second cleanup command searches from erased boundary `3` to boundary
`2`; clearing boundaries to its right does not affect this gap. -/
theorem cleanupGap_two {numTags : Nat} {spec : Spec numTags}
    {T : FullTM0.Tape (Symbol numTags)} (h : Represents spec T) :
    SearchGap (fun a => a = blankSymbol)
      (Target.boundary 2).Matches
      (atLogical spec.growth (afterThree spec T)
        (lastGapOffset spec.registers 2))
      (OrientedMarkerTape.orientDirection spec.growth .left)
      (RegisterLayout.values spec.registers 2) := by
  have hbase : SearchGap (fun a => a = blankSymbol)
      (Target.boundary 2).Matches
      (atLogical spec.growth T (lastGapOffset spec.registers 2))
      (OrientedMarkerTape.orientDirection spec.growth .left)
      (RegisterLayout.values spec.registers 2) := by
    change SearchGap (fun a => a = blankSymbol)
      (fun symbol => symbol = boundarySymbol 2) _ _ _
    exact h.searchGap_adjacent_left (2 : Fin 4)
  have hfour := searchGap_write_above_left spec.growth T
    (boundaryOffset spec.registers 4) (lastGapOffset spec.registers 2)
    (RegisterLayout.values spec.registers 2) blankSymbol
    (written_boundary_above_lastGap spec.registers 2 4 (by decide)) hbase
  have hthree := searchGap_write_above_left spec.growth (afterFour spec T)
    (boundaryOffset spec.registers 3) (lastGapOffset spec.registers 2)
    (RegisterLayout.values spec.registers 2) blankSymbol
    (written_boundary_above_lastGap spec.registers 2 3 (by decide))
    (by simpa [afterFour, clearBoundary] using hfour)
  simpa [afterThree, clearBoundary] using hthree

/-- The third cleanup command searches from erased boundary `2` to boundary
`1`. -/
theorem cleanupGap_one {numTags : Nat} {spec : Spec numTags}
    {T : FullTM0.Tape (Symbol numTags)} (h : Represents spec T) :
    SearchGap (fun a => a = blankSymbol)
      (Target.boundary 1).Matches
      (atLogical spec.growth (afterTwo spec T)
        (lastGapOffset spec.registers 1))
      (OrientedMarkerTape.orientDirection spec.growth .left)
      (RegisterLayout.values spec.registers 1) := by
  have hbase : SearchGap (fun a => a = blankSymbol)
      (Target.boundary 1).Matches
      (atLogical spec.growth T (lastGapOffset spec.registers 1))
      (OrientedMarkerTape.orientDirection spec.growth .left)
      (RegisterLayout.values spec.registers 1) := by
    change SearchGap (fun a => a = blankSymbol)
      (fun symbol => symbol = boundarySymbol 1) _ _ _
    exact h.searchGap_adjacent_left (1 : Fin 4)
  have hfour := searchGap_write_above_left spec.growth T
    (boundaryOffset spec.registers 4) (lastGapOffset spec.registers 1)
    (RegisterLayout.values spec.registers 1) blankSymbol
    (written_boundary_above_lastGap spec.registers 1 4 (by decide)) hbase
  have hthree := searchGap_write_above_left spec.growth (afterFour spec T)
    (boundaryOffset spec.registers 3) (lastGapOffset spec.registers 1)
    (RegisterLayout.values spec.registers 1) blankSymbol
    (written_boundary_above_lastGap spec.registers 1 3 (by decide))
    (by simpa [afterFour, clearBoundary] using hfour)
  have htwo := searchGap_write_above_left spec.growth (afterThree spec T)
    (boundaryOffset spec.registers 2) (lastGapOffset spec.registers 1)
    (RegisterLayout.values spec.registers 1) blankSymbol
    (written_boundary_above_lastGap spec.registers 1 2 (by decide))
    (by simpa [afterThree, clearBoundary] using hthree)
  simpa [afterTwo, clearBoundary] using htwo

/-- The fourth cleanup command searches from erased boundary `1` to boundary
`0`. -/
theorem cleanupGap_zero {numTags : Nat} {spec : Spec numTags}
    {T : FullTM0.Tape (Symbol numTags)} (h : Represents spec T) :
    SearchGap (fun a => a = blankSymbol)
      (Target.boundary 0).Matches
      (atLogical spec.growth (afterOne spec T)
        (lastGapOffset spec.registers 0))
      (OrientedMarkerTape.orientDirection spec.growth .left)
      (RegisterLayout.values spec.registers 0) := by
  have hbase : SearchGap (fun a => a = blankSymbol)
      (Target.boundary 0).Matches
      (atLogical spec.growth T (lastGapOffset spec.registers 0))
      (OrientedMarkerTape.orientDirection spec.growth .left)
      (RegisterLayout.values spec.registers 0) := by
    change SearchGap (fun a => a = blankSymbol)
      (fun symbol => symbol = boundarySymbol 0) _ _ _
    exact h.searchGap_adjacent_left (0 : Fin 4)
  have hfour := searchGap_write_above_left spec.growth T
    (boundaryOffset spec.registers 4) (lastGapOffset spec.registers 0)
    (RegisterLayout.values spec.registers 0) blankSymbol
    (written_boundary_above_lastGap spec.registers 0 4 (by decide)) hbase
  have hthree := searchGap_write_above_left spec.growth (afterFour spec T)
    (boundaryOffset spec.registers 3) (lastGapOffset spec.registers 0)
    (RegisterLayout.values spec.registers 0) blankSymbol
    (written_boundary_above_lastGap spec.registers 0 3 (by decide))
    (by simpa [afterFour, clearBoundary] using hfour)
  have htwo := searchGap_write_above_left spec.growth (afterThree spec T)
    (boundaryOffset spec.registers 2) (lastGapOffset spec.registers 0)
    (RegisterLayout.values spec.registers 0) blankSymbol
    (written_boundary_above_lastGap spec.registers 0 2 (by decide))
    (by simpa [afterThree, clearBoundary] using hthree)
  have hone := searchGap_write_above_left spec.growth (afterTwo spec T)
    (boundaryOffset spec.registers 1) (lastGapOffset spec.registers 0)
    (RegisterLayout.values spec.registers 0) blankSymbol
    (written_boundary_above_lastGap spec.registers 0 1 (by decide))
    (by simpa [afterTwo, clearBoundary] using htwo)
  simpa [afterOne, clearBoundary] using hone

/-- After boundary `0` is erased and the command departs left, the saved tag
is already under the head.  The four boundary writes leave it unchanged. -/
theorem cleanupGap_tag {numTags : Nat} {spec : Spec numTags}
    {T : FullTM0.Tape (Symbol numTags)} (h : Represents spec T) :
    SearchGap (fun a => a = blankSymbol)
      (Target.anyTag : Target numTags).Matches
      (atLogical spec.growth (afterZero spec T) 0)
      (OrientedMarkerTape.orientDirection spec.growth .left) 0 := by
  have hbase : SearchGap (fun a => a = blankSymbol)
      (Target.anyTag : Target numTags).Matches
      (atLogical spec.growth T 0)
      (OrientedMarkerTape.orientDirection spec.growth .left) 0 := by
    simpa [atLogical] using h.searchGap_tag
      (OrientedMarkerTape.orientDirection spec.growth .left)
  have hfour := searchGap_write_above_left spec.growth T
    (boundaryOffset spec.registers 4) 0 0 blankSymbol
    (by simp [boundaryOffset]) hbase
  have hthree := searchGap_write_above_left spec.growth (afterFour spec T)
    (boundaryOffset spec.registers 3) 0 0 blankSymbol
    (by simp [boundaryOffset])
    (by simpa [afterFour, clearBoundary] using hfour)
  have htwo := searchGap_write_above_left spec.growth (afterThree spec T)
    (boundaryOffset spec.registers 2) 0 0 blankSymbol
    (by simp [boundaryOffset])
    (by simpa [afterThree, clearBoundary] using hthree)
  have hone := searchGap_write_above_left spec.growth (afterTwo spec T)
    (boundaryOffset spec.registers 1) 0 0 blankSymbol
    (by simp [boundaryOffset])
    (by simpa [afterTwo, clearBoundary] using htwo)
  have hzero := searchGap_write_above_left spec.growth (afterOne spec T)
    (boundaryOffset spec.registers 0) 0 0 blankSymbol
    (by simp [boundaryOffset])
    (by simpa [afterOne, clearBoundary] using hone)
  simpa [afterZero, clearBoundary] using hzero

/-- Boundary cleanup never changes the saved tag at logical coordinate `0`. -/
theorem afterZero_read_tag {numTags : Nat} {spec : Spec numTags}
    {T : FullTM0.Tape (Symbol numTags)} (h : Represents spec T) :
    (atLogical spec.growth (afterZero spec T) 0).read =
      tagSymbol spec.returnTag := by
  rw [atLogical_read]
  simp only [afterZero, afterOne, afterTwo, afterThree, afterFour,
    clearBoundary]
  rw [writeLogical_of_ne spec.growth _
    (boundaryOffset spec.registers 0) 0 blankSymbol (by
      simp only [boundaryOffset]
      omega)]
  rw [writeLogical_of_ne spec.growth _
    (boundaryOffset spec.registers 1) 0 blankSymbol (by
      simp only [boundaryOffset]
      omega)]
  rw [writeLogical_of_ne spec.growth _
    (boundaryOffset spec.registers 2) 0 blankSymbol (by
      simp only [boundaryOffset]
      omega)]
  rw [writeLogical_of_ne spec.growth _
    (boundaryOffset spec.registers 3) 0 blankSymbol (by
      simp only [boundaryOffset]
      omega)]
  rw [writeLogical_of_ne spec.growth _
    (boundaryOffset spec.registers 4) 0 blankSymbol (by
      simp only [boundaryOffset]
      omega)]
  exact h.tag

private theorem lastGap_eq_boundary_add_value
    (registers : Registers) (i : Fin 4) :
    lastGapOffset registers i =
      boundaryOffset registers i.castSucc +
        RegisterLayout.values registers i := by
  simp only [lastGapOffset, boundaryOffset, Fin.val_castSucc]
  rw [CounterLayout.boundaryPos_succ]
  omega

private theorem boundary_three_eq_lastGap_two_add_one
    (registers : Registers) :
    boundaryOffset registers 3 = lastGapOffset registers 2 + 1 := by
  simp [boundaryOffset, lastGapOffset]

private theorem boundary_two_eq_lastGap_one_add_one
    (registers : Registers) :
    boundaryOffset registers 2 = lastGapOffset registers 1 + 1 := by
  simp [boundaryOffset, lastGapOffset]

private theorem boundary_one_eq_lastGap_zero_add_one
    (registers : Registers) :
    boundaryOffset registers 1 = lastGapOffset registers 0 + 1 := by
  simp [boundaryOffset, lastGapOffset]

/-! ## Executing the four erasing commands -/

/-- Exact dependent alternative when one of the four boundary-cleanup
searches is itself too long for the current controller. -/
def NestsDuringCleanup (base : Nat) (c : Nat.Partrec.Code)
    (growth : Turing.Dir) (source : Nat)
  (start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State) : Prop :=
  ∃ (raw : RawCommand) (_hcleanup : raw ∈ cleanupCommands growth source)
      (hraw : raw ∈ rawCommands)
      (outer : FullTM0.Tape (Symbol numTags)) (distance : Nat)
      (hfar : NestingMachine.bound (CanonicalInitializer.radius c) < distance),
    FullTM0.Reaches (CounterControlNestingBridge.machine base c) start
        (CounterControlNestingBridge.nestedCfg base c
          (rawTag raw hraw) outer) ∧
      Represents
        (frameSpec c (compileRawCommand base c raw hraw) distance hfar)
        (initializeTape c (compileRawCommand base c raw hraw) outer)

/-- A failure-parametric implementation of the four cleanup searches. -/
structure CleanupRunner
    (base : Nat) (c : Nat.Partrec.Code) (limit : Nat)
    (growth : Turing.Dir) (source : Nat)
    (Failure : FullTM0.Cfg (Symbol numTags) FiniteTM0.State → Prop) where
  pullback : ∀ {start current},
    FullTM0.Reaches (CounterControlNestingBridge.machine base c) start current →
      Failure current → Failure start
  erase : ∀ (address : SearchAddress) (expected : Fin 5)
      (success : ControlRef)
      (_hcleanup : RawCommand.boundaryNavigation address expected .left success
        (.erase (some .left)) ∈ cleanupCommands growth source)
      (_hraw : RawCommand.boundaryNavigation address expected .left success
        (.erase (some .left)) ∈ rawCommands)
      (outer : FullTM0.Tape (Symbol numTags)) (distance : Nat),
    distance < limit →
    SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary expected).Matches outer
      (orient address.growth .left) distance →
    (FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      ⟨searchState base c address, outer⟩
      ⟨resolve base c success,
        ((outer.moveN (orient address.growth .left) distance).write
          blankSymbol).move (orient address.growth .left)⟩ ∨
      Failure ⟨searchState base c address, outer⟩)

private theorem cleanupResult_trans
    [Inhabited Λ]
    (M : Turing.TM0.Machine Γ Λ) (Failure : FullTM0.Cfg Γ Λ → Prop)
    (pullback : ∀ {start current}, FullTM0.Reaches M start current →
      Failure current → Failure start)
    {start middle finish : FullTM0.Cfg Γ Λ}
    (h₁ : FullTM0.Reaches M start middle ∨ Failure start)
    (h₂ : FullTM0.Reaches M middle finish ∨ Failure middle) :
    FullTM0.Reaches M start finish ∨ Failure start := by
  rcases h₁ with hreach | hfailure
  · rcases h₂ with hfinish | hfailure
    · exact Or.inl (hreach.trans hfinish)
    · exact Or.inr (pullback hreach hfailure)
  · exact Or.inr hfailure

/-- Execute and normalize the complete four-command cleanup chain.  All
representation-specific work is isolated in the four supplied gaps and
distance bounds. -/
theorem machine_reaches_cleanup_return_with
    (base : Nat) (c : Nat.Partrec.Code) (limit source : Nat)
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (Failure : FullTM0.Cfg (Symbol numTags) FiniteTM0.State → Prop)
    (runner : CleanupRunner base c limit spec.growth source Failure)
    (hthreeDistance : RegisterLayout.values spec.registers 3 + 1 < limit)
    (htwoDistance : RegisterLayout.values spec.registers 2 < limit)
    (honeDistance : RegisterLayout.values spec.registers 1 < limit)
    (hzeroDistance : RegisterLayout.values spec.registers 0 < limit)
    (hthreeGap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary 3).Matches
      (atLogical spec.growth (afterFour spec T)
        (boundaryOffset spec.registers 4))
      (orient spec.growth .left)
      (RegisterLayout.values spec.registers 3 + 1))
    (htwoGap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary 2).Matches
      (atLogical spec.growth (afterThree spec T)
        (lastGapOffset spec.registers 2))
      (orient spec.growth .left) (RegisterLayout.values spec.registers 2))
    (honeGap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary 1).Matches
      (atLogical spec.growth (afterTwo spec T)
        (lastGapOffset spec.registers 1))
      (orient spec.growth .left) (RegisterLayout.values spec.registers 1))
    (hzeroGap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary 0).Matches
      (atLogical spec.growth (afterOne spec T)
        (lastGapOffset spec.registers 0))
      (orient spec.growth .left) (RegisterLayout.values spec.registers 0))
    (hcommands : ∀ raw, raw ∈ cleanupCommands spec.growth source →
      raw ∈ rawCommands) :
    (FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      ⟨searchState base c ⟨spec.growth, source, cleanupSearchBase⟩,
        atLogical spec.growth (afterFour spec T)
          (layoutEnd spec.registers)⟩
      ⟨controllerReturn base c spec.growth,
        atLogical spec.growth (afterZero spec T) 0⟩ ∨
      Failure
        ⟨searchState base c ⟨spec.growth, source, cleanupSearchBase⟩,
          atLogical spec.growth (afterFour spec T)
            (layoutEnd spec.registers)⟩) := by
  let rawThree : RawCommand :=
    .boundaryNavigation ⟨spec.growth, source, cleanupSearchBase⟩ 3 .left
      (searchRef spec.growth source (cleanupSearchBase + 1))
      (.erase (some .left))
  let rawTwo : RawCommand :=
    .boundaryNavigation ⟨spec.growth, source, cleanupSearchBase + 1⟩ 2 .left
      (searchRef spec.growth source (cleanupSearchBase + 2))
      (.erase (some .left))
  let rawOne : RawCommand :=
    .boundaryNavigation ⟨spec.growth, source, cleanupSearchBase + 2⟩ 1 .left
      (searchRef spec.growth source (cleanupSearchBase + 3))
      (.erase (some .left))
  let rawZero : RawCommand :=
    .boundaryNavigation ⟨spec.growth, source, cleanupSearchBase + 3⟩ 0 .left
      (.sharedReturn spec.growth) (.erase (some .left))
  have hcleanupThree : rawThree ∈ cleanupCommands spec.growth source := by
    simp [rawThree, cleanupCommands]
  have hcleanupTwo : rawTwo ∈ cleanupCommands spec.growth source := by
    simp [rawTwo, cleanupCommands]
  have hcleanupOne : rawOne ∈ cleanupCommands spec.growth source := by
    simp [rawOne, cleanupCommands]
  have hcleanupZero : rawZero ∈ cleanupCommands spec.growth source := by
    simp [rawZero, cleanupCommands]
  have hrawThree := hcommands rawThree hcleanupThree
  have hrawTwo := hcommands rawTwo hcleanupTwo
  have hrawOne := hcommands rawOne hcleanupOne
  have hrawZero := hcommands rawZero hcleanupZero
  have hthreeRun := runner.erase
    ⟨spec.growth, source, cleanupSearchBase⟩ 3
    (searchRef spec.growth source (cleanupSearchBase + 1))
    (by simpa [rawThree] using hcleanupThree)
    (by simpa [rawThree] using hrawThree)
    (atLogical spec.growth (afterFour spec T)
      (boundaryOffset spec.registers 4))
    (RegisterLayout.values spec.registers 3 + 1) hthreeDistance hthreeGap
  have hthree : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      ⟨searchState base c ⟨spec.growth, source, cleanupSearchBase⟩,
        atLogical spec.growth (afterFour spec T)
          (layoutEnd spec.registers)⟩
      ⟨searchState base c
          ⟨spec.growth, source, cleanupSearchBase + 1⟩,
        atLogical spec.growth (afterThree spec T)
          (lastGapOffset spec.registers 2)⟩ ∨
      Failure
        ⟨searchState base c ⟨spec.growth, source, cleanupSearchBase⟩,
          atLogical spec.growth (afterFour spec T)
            (layoutEnd spec.registers)⟩ := by
    refine hthreeRun.imp ?_ id
    intro hrun
    have hstart : boundaryOffset spec.registers 4 =
        boundaryOffset spec.registers 3 +
          (RegisterLayout.values spec.registers 3 + 1) := by
      simp [boundaryOffset, CounterLayout.boundaryPos]
      omega
    have hfound :
        (atLogical spec.growth (afterFour spec T)
            (boundaryOffset spec.registers 4)).moveN
            (orient spec.growth .left)
            (RegisterLayout.values spec.registers 3 + 1) =
          atLogical spec.growth (afterFour spec T)
            (boundaryOffset spec.registers 3) := by
      rw [hstart, orient_eq_orientDirection, atLogical_moveN_left]
    rw [hfound, orient_eq_orientDirection,
      boundary_three_eq_lastGap_two_add_one,
      erase_departLeft_atLogical] at hrun
    rw [← boundary_three_eq_lastGap_two_add_one] at hrun
    simpa [searchRef, CounterControlPlan.resolve, afterThree,
      clearBoundary] using hrun
  have htwoRun := runner.erase
    ⟨spec.growth, source, cleanupSearchBase + 1⟩ 2
    (searchRef spec.growth source (cleanupSearchBase + 2))
    (by simpa [rawTwo] using hcleanupTwo)
    (by simpa [rawTwo] using hrawTwo)
    (atLogical spec.growth (afterThree spec T)
      (lastGapOffset spec.registers 2))
    (RegisterLayout.values spec.registers 2) htwoDistance htwoGap
  have htwo : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      ⟨searchState base c
          ⟨spec.growth, source, cleanupSearchBase + 1⟩,
        atLogical spec.growth (afterThree spec T)
          (lastGapOffset spec.registers 2)⟩
      ⟨searchState base c
          ⟨spec.growth, source, cleanupSearchBase + 2⟩,
        atLogical spec.growth (afterTwo spec T)
          (lastGapOffset spec.registers 1)⟩ ∨
      Failure
        ⟨searchState base c
            ⟨spec.growth, source, cleanupSearchBase + 1⟩,
          atLogical spec.growth (afterThree spec T)
            (lastGapOffset spec.registers 2)⟩ := by
    refine htwoRun.imp ?_ id
    intro hrun
    have hstart : lastGapOffset spec.registers 2 =
        boundaryOffset spec.registers 2 +
          RegisterLayout.values spec.registers 2 :=
      lastGap_eq_boundary_add_value spec.registers 2
    have hfound :
        (atLogical spec.growth (afterThree spec T)
            (lastGapOffset spec.registers 2)).moveN
            (orient spec.growth .left)
            (RegisterLayout.values spec.registers 2) =
          atLogical spec.growth (afterThree spec T)
            (boundaryOffset spec.registers 2) := by
      rw [hstart, orient_eq_orientDirection, atLogical_moveN_left]
    rw [hfound, orient_eq_orientDirection,
      boundary_two_eq_lastGap_one_add_one,
      erase_departLeft_atLogical] at hrun
    rw [← boundary_two_eq_lastGap_one_add_one] at hrun
    simpa [searchRef, CounterControlPlan.resolve, afterTwo,
      clearBoundary] using hrun
  have honeRun := runner.erase
    ⟨spec.growth, source, cleanupSearchBase + 2⟩ 1
    (searchRef spec.growth source (cleanupSearchBase + 3))
    (by simpa [rawOne] using hcleanupOne)
    (by simpa [rawOne] using hrawOne)
    (atLogical spec.growth (afterTwo spec T)
      (lastGapOffset spec.registers 1))
    (RegisterLayout.values spec.registers 1) honeDistance honeGap
  have hone : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      ⟨searchState base c
          ⟨spec.growth, source, cleanupSearchBase + 2⟩,
        atLogical spec.growth (afterTwo spec T)
          (lastGapOffset spec.registers 1)⟩
      ⟨searchState base c
          ⟨spec.growth, source, cleanupSearchBase + 3⟩,
        atLogical spec.growth (afterOne spec T)
          (lastGapOffset spec.registers 0)⟩ ∨
      Failure
        ⟨searchState base c
            ⟨spec.growth, source, cleanupSearchBase + 2⟩,
          atLogical spec.growth (afterTwo spec T)
            (lastGapOffset spec.registers 1)⟩ := by
    refine honeRun.imp ?_ id
    intro hrun
    have hstart : lastGapOffset spec.registers 1 =
        boundaryOffset spec.registers 1 +
          RegisterLayout.values spec.registers 1 :=
      lastGap_eq_boundary_add_value spec.registers 1
    have hfound :
        (atLogical spec.growth (afterTwo spec T)
            (lastGapOffset spec.registers 1)).moveN
            (orient spec.growth .left)
            (RegisterLayout.values spec.registers 1) =
          atLogical spec.growth (afterTwo spec T)
            (boundaryOffset spec.registers 1) := by
      rw [hstart, orient_eq_orientDirection, atLogical_moveN_left]
    rw [hfound, orient_eq_orientDirection,
      boundary_one_eq_lastGap_zero_add_one,
      erase_departLeft_atLogical] at hrun
    rw [← boundary_one_eq_lastGap_zero_add_one] at hrun
    simpa [searchRef, CounterControlPlan.resolve, afterOne,
      clearBoundary] using hrun
  have hzeroRun := runner.erase
    ⟨spec.growth, source, cleanupSearchBase + 3⟩ 0
    (.sharedReturn spec.growth)
    (by simpa [rawZero] using hcleanupZero)
    (by simpa [rawZero] using hrawZero)
    (atLogical spec.growth (afterOne spec T)
      (lastGapOffset spec.registers 0))
    (RegisterLayout.values spec.registers 0) hzeroDistance hzeroGap
  have hzero : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      ⟨searchState base c
          ⟨spec.growth, source, cleanupSearchBase + 3⟩,
        atLogical spec.growth (afterOne spec T)
          (lastGapOffset spec.registers 0)⟩
      ⟨controllerReturn base c spec.growth,
        atLogical spec.growth (afterZero spec T) 0⟩ ∨
      Failure
        ⟨searchState base c
            ⟨spec.growth, source, cleanupSearchBase + 3⟩,
          atLogical spec.growth (afterOne spec T)
            (lastGapOffset spec.registers 0)⟩ := by
    refine hzeroRun.imp ?_ id
    intro hrun
    have hstart : lastGapOffset spec.registers 0 =
        1 + RegisterLayout.values spec.registers 0 := by
      simpa using lastGap_eq_boundary_add_value spec.registers (0 : Fin 4)
    have hfound :
        (atLogical spec.growth (afterOne spec T)
            (lastGapOffset spec.registers 0)).moveN
            (orient spec.growth .left)
            (RegisterLayout.values spec.registers 0) =
          atLogical spec.growth (afterOne spec T) 1 := by
      rw [hstart, orient_eq_orientDirection, atLogical_moveN_left]
    rw [hfound, orient_eq_orientDirection,
      erase_departLeft_atLogical] at hrun
    simpa [searchRef, CounterControlPlan.resolve, afterZero,
      clearBoundary] using hrun
  exact cleanupResult_trans _ _ runner.pullback hthree
    (cleanupResult_trans _ _ runner.pullback htwo
      (cleanupResult_trans _ _ runner.pullback hone hzero))

/-- Cleanup runner exposing an exact nested frame as its failure. -/
def nestingCleanupRunner
    (base : Nat) (c : Nat.Partrec.Code) (limit source : Nat)
    (growth : Turing.Dir) :
    CleanupRunner base c limit growth source
      (NestsDuringCleanup base c growth source) where
  pullback := by
    intro start current hreach hnests
    rcases hnests with
      ⟨raw, hcleanup, hraw, outer, distance, hfar, hnested, hframe⟩
    exact ⟨raw, hcleanup, hraw, outer, distance, hfar,
      hreach.trans hnested, hframe⟩
  erase := by
    intro address expected success hcleanup hraw outer distance _ hgap
    have hrun :=
      CounterControlNavigationSemantics.machine_reaches_boundary_erase_or_nests
        base c address expected .left success (some .left) hraw outer distance
        hgap
    rcases hrun with hsuccess | hnested
    · exact Or.inl hsuccess
    · rcases hnested with ⟨hfar, hreach, hframe⟩
      exact Or.inr ⟨.boundaryNavigation address expected .left success
        (.erase (some .left)), hcleanup, hraw, outer, distance, hfar,
        hreach, hframe⟩

/-- Starting just after the collision handoff has moved back onto erased
boundary `4`, the four generated erase commands reach the directional return
state while scanning the adjacent saved tag, unless one of their register-gap
searches launches an exact deeper frame. -/
theorem machine_reaches_cleanup_return_or_nests
    (base : Nat) (c : Nat.Partrec.Code) (source : Nat)
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T)
    (hcommands : ∀ raw, raw ∈ cleanupCommands spec.growth source →
      raw ∈ rawCommands) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨spec.growth, source, cleanupSearchBase⟩,
          atLogical spec.growth (afterFour spec T)
            (layoutEnd spec.registers)⟩
        ⟨controllerReturn base c spec.growth, atLogical spec.growth
          (afterZero spec T) 0⟩ ∨
      NestsDuringCleanup base c spec.growth source
        ⟨searchState base c ⟨spec.growth, source, cleanupSearchBase⟩,
          atLogical spec.growth (afterFour spec T)
            (layoutEnd spec.registers)⟩ := by
  have hvalue : ∀ i : Fin 4,
      RegisterLayout.values spec.registers i < spec.outerDistance := by
    intro i
    have hend := spec.core_before_target
    fin_cases i <;>
      simp [RegisterLayout.values, layoutEnd_eq] at hend ⊢ <;> omega
  have hthree :
      RegisterLayout.values spec.registers 3 + 1 < spec.outerDistance := by
    have hend := spec.core_before_target
    simp [RegisterLayout.values, layoutEnd_eq] at hend ⊢
    omega
  exact machine_reaches_cleanup_return_with base c spec.outerDistance source
    (NestsDuringCleanup base c spec.growth source)
    (nestingCleanupRunner base c spec.outerDistance source spec.growth)
    hthree (hvalue 2) (hvalue 1) (hvalue 0)
    (by simpa [orient_eq_orientDirection] using cleanupGap_three h)
    (by simpa [orient_eq_orientDirection] using cleanupGap_two h)
    (by simpa [orient_eq_orientDirection] using cleanupGap_one h)
    (by simpa [orient_eq_orientDirection] using cleanupGap_zero h)
    hcommands

/-! ## The shared return dispatcher -/

/-- The complete linked table contains the return rule selected by every
physical tag at the return state matching that command's search direction.
It clears the tag and enters the corresponding command-local resume state. -/
theorem machine_sharedReturn_reaches_resume
    (base : Nat) (c : Nat.Partrec.Code) (tag : Fin numTags)
    (U : FullTM0.Tape (Symbol numTags))
    (hread : U.read = tagSymbol tag) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      ⟨controllerReturn base c
          (compileCommand base c tag).searchDirection, U⟩
      ⟨resumeState (CanonicalInitializer.radius c)
          (searchState base c (rawCommands.get tag).address),
        U.write blankSymbol⟩ := by
  let command := compileCommand base c tag
  let offset := searchState base c (rawCommands.get tag).address
  have hat : CommandAt (CanonicalInitializer.radius c) base offset command
      (commands base c) := by
    exact CounterControlWellFormed.CommandAt.compileCommand base c tag
  have hlookupLocal :
      FiniteTM0.lookupAction
          (returnTable (CanonicalInitializer.radius c)
            (controllerReturn base c) base (commands base c))
          (controllerReturn base c command.searchDirection)
          (tagSymbol tag) =
        some (resumeState (CanonicalInitializer.radius c) offset,
          .write blankSymbol) := by
    simpa [command, compileCommand_returnTag] using
      (lookupAction_returnTable_of_at
        (sharedReturn := controllerReturn base c) hat
        (commands_returnTags_nodup base c))
  have hreturnDet := returnTable_deterministic
    (CanonicalInitializer.radius c) (controllerReturn base c) base
    (commands base c) (commands_returnTags_nodup base c)
  have hreturnMem :
      FiniteTM0.Rule.mk (controllerReturn base c command.searchDirection)
          (tagSymbol tag)
          (resumeState (CanonicalInitializer.radius c) offset)
          (.write blankSymbol) ∈
        returnTable (CanonicalInitializer.radius c)
          (controllerReturn base c) base (commands base c) :=
    (FiniteTM0.lookupAction_eq_some_iff_of_deterministic hreturnDet).1
      hlookupLocal
  have hreturnStateEq :
      BoundedMarkerProgram.returnState base
          (CanonicalInitializer.radius c) (commands base c) =
        controllerReturn base c := by
    funext growth
    exact controllerReturn_eq base c growth
  have htableMem :
      FiniteTM0.Rule.mk (controllerReturn base c command.searchDirection)
          (tagSymbol tag)
          (resumeState (CanonicalInitializer.radius c) offset)
          (.write blankSymbol) ∈ CounterControlPlan.table base c := by
    unfold CounterControlPlan.table BoundedMarkerProgram.table
      BoundedMarkerProgram.controllerTable
    simp only [List.mem_append]
    exact Or.inl (Or.inr (by
      simpa only [hreturnStateEq] using hreturnMem))
  have hlookup :
      FiniteTM0.lookupAction (CounterControlPlan.table base c)
          (controllerReturn base c command.searchDirection) (tagSymbol tag) =
        some (resumeState (CanonicalInitializer.radius c) offset,
          .write blankSymbol) :=
      (FiniteTM0.lookupAction_eq_some_iff_of_deterministic
      (CounterControlDeterministic.table_deterministic base c)).2 htableMem
  apply Relation.ReflTransGen.single
  change FullTM0.step
      (FiniteTM0.machine (CounterControlPlan.table base c))
      ⟨controllerReturn base c command.searchDirection, U⟩ =
    some ⟨resumeState (CanonicalInitializer.radius c) offset,
      U.write blankSymbol⟩
  simp only [FullTM0.step]
  rw [hread]
  simp only [FiniteTM0.machine_apply, hlookup, Option.map_some,
    FiniteTM0.Action.toStmt_write]

/-- Successful cleanup includes the shared dispatcher's final tag erase. -/
theorem machine_reaches_cleanup_resume_or_nests
    (base : Nat) (c : Nat.Partrec.Code) (source : Nat)
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T)
    (hreturnDirection :
      (compileCommand base c spec.returnTag).searchDirection = spec.growth)
    (hcommands : ∀ raw, raw ∈ cleanupCommands spec.growth source →
      raw ∈ rawCommands) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨spec.growth, source, cleanupSearchBase⟩,
          atLogical spec.growth (afterFour spec T)
            (layoutEnd spec.registers)⟩
        ⟨resumeState (CanonicalInitializer.radius c)
            (searchState base c
              (rawCommands.get spec.returnTag).address),
          atLogical spec.growth (afterTag spec T) 0⟩ ∨
      NestsDuringCleanup base c spec.growth source
        ⟨searchState base c ⟨spec.growth, source, cleanupSearchBase⟩,
          atLogical spec.growth (afterFour spec T)
            (layoutEnd spec.registers)⟩ := by
  rcases machine_reaches_cleanup_return_or_nests base c source h hcommands with
    hreturn | hnests
  · left
    have hread : (atLogical spec.growth (afterZero spec T) 0).read =
        tagSymbol spec.returnTag := afterZero_read_tag h
    have hdispatch := machine_sharedReturn_reaches_resume base c
      spec.returnTag (atLogical spec.growth (afterZero spec T) 0) hread
    have hdispatch' : FullTM0.Reaches
        (CounterControlNestingBridge.machine base c)
        ⟨controllerReturn base c spec.growth,
          atLogical spec.growth (afterZero spec T) 0⟩
        ⟨resumeState (CanonicalInitializer.radius c)
            (searchState base c (rawCommands.get spec.returnTag).address),
          atLogical spec.growth (afterTag spec T) 0⟩ := by
      simpa [hreturnDirection, afterTag, atLogical_write] using hdispatch
    exact hreturn.trans hdispatch'
  · exact Or.inr hnests

/-! ## Identifying the extensional cleanup tape -/

private theorem boundaryOffset_injective (registers : Registers) :
    Function.Injective (boundaryOffset registers) := by
  intro first second heq
  apply Fin.ext
  have hpositions : CounterLayout.boundaryPos
      (RegisterLayout.values registers) first =
      CounterLayout.boundaryPos (RegisterLayout.values registers) second := by
    simpa [boundaryOffset] using heq
  exact (CounterLayout.boundaryPos_strictMono
    (RegisterLayout.values registers)).injective hpositions

private theorem boundaryOffset_ne (registers : Registers)
    {first second : Fin 5} (hne : first ≠ second) :
    boundaryOffset registers first ≠ boundaryOffset registers second :=
  fun heq => hne (boundaryOffset_injective registers heq)

private theorem afterTag_boundary_blank {numTags : Nat}
    (spec : Spec numTags) (T : FullTM0.Tape (Symbol numTags))
    (label : Fin 5) :
    logicalTape spec.growth (afterTag spec T)
        (boundaryOffset spec.registers label) = blankSymbol := by
  have h0 : logicalTape spec.growth (afterTag spec T)
      (boundaryOffset spec.registers 0) = blankSymbol := by
    simp only [afterTag, afterZero, clearBoundary]
    rw [writeLogical_of_ne spec.growth _ 0
      (boundaryOffset spec.registers 0) blankSymbol (by simp [boundaryOffset])]
    exact writeLogical_at spec.growth (afterOne spec T)
      (boundaryOffset spec.registers 0) blankSymbol
  have h1 : logicalTape spec.growth (afterTag spec T)
      (boundaryOffset spec.registers 1) = blankSymbol := by
    simp only [afterTag, afterZero, afterOne, clearBoundary]
    rw [writeLogical_of_ne spec.growth _ 0
      (boundaryOffset spec.registers 1) blankSymbol (by simp [boundaryOffset])]
    rw [writeLogical_of_ne spec.growth _ (boundaryOffset spec.registers 0)
      (boundaryOffset spec.registers 1) blankSymbol
      (boundaryOffset_ne spec.registers (by decide))]
    exact writeLogical_at spec.growth (afterTwo spec T)
      (boundaryOffset spec.registers 1) blankSymbol
  have h2 : logicalTape spec.growth (afterTag spec T)
      (boundaryOffset spec.registers 2) = blankSymbol := by
    simp only [afterTag, afterZero, afterOne, afterTwo, clearBoundary]
    rw [writeLogical_of_ne spec.growth _ 0
      (boundaryOffset spec.registers 2) blankSymbol (by simp [boundaryOffset])]
    rw [writeLogical_of_ne spec.growth _ (boundaryOffset spec.registers 0)
      (boundaryOffset spec.registers 2) blankSymbol
      (boundaryOffset_ne spec.registers (by decide))]
    rw [writeLogical_of_ne spec.growth _ (boundaryOffset spec.registers 1)
      (boundaryOffset spec.registers 2) blankSymbol
      (boundaryOffset_ne spec.registers (by decide))]
    exact writeLogical_at spec.growth (afterThree spec T)
      (boundaryOffset spec.registers 2) blankSymbol
  have h3 : logicalTape spec.growth (afterTag spec T)
      (boundaryOffset spec.registers 3) = blankSymbol := by
    simp only [afterTag, afterZero, afterOne, afterTwo, afterThree,
      clearBoundary]
    rw [writeLogical_of_ne spec.growth _ 0
      (boundaryOffset spec.registers 3) blankSymbol (by simp [boundaryOffset])]
    rw [writeLogical_of_ne spec.growth _ (boundaryOffset spec.registers 0)
      (boundaryOffset spec.registers 3) blankSymbol
      (boundaryOffset_ne spec.registers (by decide))]
    rw [writeLogical_of_ne spec.growth _ (boundaryOffset spec.registers 1)
      (boundaryOffset spec.registers 3) blankSymbol
      (boundaryOffset_ne spec.registers (by decide))]
    rw [writeLogical_of_ne spec.growth _ (boundaryOffset spec.registers 2)
      (boundaryOffset spec.registers 3) blankSymbol
      (boundaryOffset_ne spec.registers (by decide))]
    exact writeLogical_at spec.growth (afterFour spec T)
      (boundaryOffset spec.registers 3) blankSymbol
  have h4 : logicalTape spec.growth (afterTag spec T)
      (boundaryOffset spec.registers 4) = blankSymbol := by
    simp only [afterTag, afterZero, afterOne, afterTwo, afterThree,
      afterFour, clearBoundary]
    rw [writeLogical_of_ne spec.growth _ 0
      (boundaryOffset spec.registers 4) blankSymbol (by simp [boundaryOffset])]
    rw [writeLogical_of_ne spec.growth _ (boundaryOffset spec.registers 0)
      (boundaryOffset spec.registers 4) blankSymbol
      (boundaryOffset_ne spec.registers (by decide))]
    rw [writeLogical_of_ne spec.growth _ (boundaryOffset spec.registers 1)
      (boundaryOffset spec.registers 4) blankSymbol
      (boundaryOffset_ne spec.registers (by decide))]
    rw [writeLogical_of_ne spec.growth _ (boundaryOffset spec.registers 2)
      (boundaryOffset spec.registers 4) blankSymbol
      (boundaryOffset_ne spec.registers (by decide))]
    rw [writeLogical_of_ne spec.growth _ (boundaryOffset spec.registers 3)
      (boundaryOffset spec.registers 4) blankSymbol
      (boundaryOffset_ne spec.registers (by decide))]
    exact writeLogical_at spec.growth T
      (boundaryOffset spec.registers 4) blankSymbol
  rcases label with ⟨value, hvalue⟩
  have hcases : value = 0 ∨ value = 1 ∨ value = 2 ∨ value = 3 ∨
      value = 4 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl
  · simpa using h0
  · simpa using h1
  · simpa using h2
  · simpa using h3
  · simpa using h4

private theorem coreSymbol_blank_of_not_boundary {numTags : Nat}
    (registers : Registers) (position : Nat)
    (hnone : ∀ label : Fin 5,
      position + 1 ≠ boundaryOffset registers label) :
    coreSymbol (numTags := numTags) registers position = blankSymbol := by
  change baseSymbol (MarkerMachine.encodeSymbol
      (MarkerTape.canonicalTape registers position)) =
    baseSymbol MarkerMachine.blankSymbol
  apply congrArg baseSymbol
  rw [MarkerMachine.encodeSymbol_eq_blank_iff]
  rw [MarkerTape.canonicalTape_eq_blank_iff]
  intro label heq
  apply hnone label
  simp only [boundaryOffset]
  congr 1
  exact_mod_cast (show (position : Int) =
    CounterLayout.boundaryPos (RegisterLayout.values registers) label by
      simpa [MarkerTape.boundaryPosition] using heq)

/-- Clearing exactly the tag and the five canonical boundaries clears the
entire finite core, because every other core cell is already blank. -/
theorem afterTag_blank {numTags : Nat} {spec : Spec numTags}
    {T : FullTM0.Tape (Symbol numTags)} (h : Represents spec T)
    (position : Nat) (hposition : position ≤ layoutEnd spec.registers) :
    logicalTape spec.growth (afterTag spec T) position = blankSymbol := by
  by_cases hzero : position = 0
  · subst position
    exact writeLogical_at spec.growth (afterZero spec T) 0 blankSymbol
  by_cases hboundary : ∃ label : Fin 5,
      position = boundaryOffset spec.registers label
  · rcases hboundary with ⟨label, rfl⟩
    exact afterTag_boundary_blank spec T label
  · obtain ⟨corePosition, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hzero
    have hcorePosition : corePosition ≤
        RegisterLayout.clockBoundary spec.registers := by
      simpa [layoutEnd] using hposition
    have hnone : ∀ label : Fin 5,
        corePosition + 1 ≠ boundaryOffset spec.registers label := by
      intro label heq
      exact hboundary ⟨label, heq⟩
    simp only [afterTag, afterZero, afterOne, afterTwo, afterThree, afterFour,
      clearBoundary]
    rw [writeLogical_of_ne spec.growth _ 0 (corePosition + 1)
      blankSymbol (by omega)]
    rw [writeLogical_of_ne spec.growth _ (boundaryOffset spec.registers 0)
      (corePosition + 1) blankSymbol (hnone 0)]
    rw [writeLogical_of_ne spec.growth _ (boundaryOffset spec.registers 1)
      (corePosition + 1) blankSymbol (hnone 1)]
    rw [writeLogical_of_ne spec.growth _ (boundaryOffset spec.registers 2)
      (corePosition + 1) blankSymbol (hnone 2)]
    rw [writeLogical_of_ne spec.growth _ (boundaryOffset spec.registers 3)
      (corePosition + 1) blankSymbol (hnone 3)]
    rw [writeLogical_of_ne spec.growth _ (boundaryOffset spec.registers 4)
      (corePosition + 1) blankSymbol (hnone 4)]
    have hcore := h.core corePosition hcorePosition
    have hblank := coreSymbol_blank_of_not_boundary
      (numTags := numTags) spec.registers corePosition hnone
    have hcore' : logicalTape spec.growth T (corePosition + 1) =
        coreSymbol spec.registers corePosition := by
      simpa only [Nat.cast_add, Nat.cast_one] using hcore
    exact hcore'.trans hblank

private theorem logicalTape_writeLogical_of_neg {numTags : Nat}
    (growth : Turing.Dir) (T : FullTM0.Tape (Symbol numTags))
    (written : Nat) (symbol : Symbol numTags) (position : Int)
    (hnegative : position < 0) :
    logicalTape growth (writeLogical growth T written symbol) position =
      logicalTape growth T position := by
  cases growth <;>
    simp [logicalTape, OrientedMarkerTape.orientTape, writeLogical,
      physicalCoord, Function.update] <;> omega

private theorem boundaryOffset_le_layoutEnd (registers : Registers)
    (label : Fin 5) :
    boundaryOffset registers label ≤ layoutEnd registers := by
  simp only [boundaryOffset, layoutEnd]
  have hlabel : (label : Nat) ≤ 4 := by omega
  have hmono := CounterLayout.boundaryPos_mono
    (RegisterLayout.values registers) hlabel
  exact Nat.add_le_add_right hmono 1

/-- The operational five-write result is exactly the extensional cleanup
specification. -/
theorem afterTag_eq_cleanupTape {numTags : Nat} {spec : Spec numTags}
    {T : FullTM0.Tape (Symbol numTags)} (h : Represents spec T) :
    afterTag spec T = cleanupTape spec T := by
  have hlogical : logicalTape spec.growth (afterTag spec T) =
      logicalTape spec.growth (cleanupTape spec T) := by
    funext position
    by_cases hnegative : position < 0
    · simp only [afterTag, afterZero, afterOne, afterTwo, afterThree,
        afterFour, clearBoundary]
      rw [logicalTape_writeLogical_of_neg spec.growth _ 0 blankSymbol
        position hnegative]
      rw [logicalTape_writeLogical_of_neg spec.growth _
        (boundaryOffset spec.registers 0) blankSymbol position hnegative]
      rw [logicalTape_writeLogical_of_neg spec.growth _
        (boundaryOffset spec.registers 1) blankSymbol position hnegative]
      rw [logicalTape_writeLogical_of_neg spec.growth _
        (boundaryOffset spec.registers 2) blankSymbol position hnegative]
      rw [logicalTape_writeLogical_of_neg spec.growth _
        (boundaryOffset spec.registers 3) blankSymbol position hnegative]
      rw [logicalTape_writeLogical_of_neg spec.growth _
        (boundaryOffset spec.registers 4) blankSymbol position hnegative]
      rw [logicalTape_cleanupTape]
      simp [clearLogicalPrefix, hnegative]
    · have hnonnegative : 0 ≤ position := le_of_not_gt hnegative
      obtain ⟨coordinate, rfl⟩ := Int.eq_ofNat_of_zero_le hnonnegative
      by_cases hcore : coordinate ≤ layoutEnd spec.registers
      · have hleft := afterTag_blank h coordinate hcore
        have hright := cleanupTape_blank spec T coordinate hcore
        simpa using hleft.trans hright.symm
      · have hpast : layoutEnd spec.registers < coordinate :=
          Nat.lt_of_not_ge hcore
        have hzero : coordinate ≠ 0 := by
          have hendPositive : 0 < layoutEnd spec.registers := by
            simp [layoutEnd]
          omega
        have hboundary : ∀ label : Fin 5,
            coordinate ≠ boundaryOffset spec.registers label := by
          intro label heq
          subst coordinate
          exact (Nat.not_lt_of_ge (boundaryOffset_le_layoutEnd
            spec.registers label)) hpast
        simp only [afterTag, afterZero, afterOne, afterTwo, afterThree,
          afterFour, clearBoundary]
        rw [writeLogical_of_ne spec.growth _ 0 coordinate blankSymbol hzero]
        rw [writeLogical_of_ne spec.growth _
          (boundaryOffset spec.registers 0) coordinate blankSymbol
          (hboundary 0)]
        rw [writeLogical_of_ne spec.growth _
          (boundaryOffset spec.registers 1) coordinate blankSymbol
          (hboundary 1)]
        rw [writeLogical_of_ne spec.growth _
          (boundaryOffset spec.registers 2) coordinate blankSymbol
          (hboundary 2)]
        rw [writeLogical_of_ne spec.growth _
          (boundaryOffset spec.registers 3) coordinate blankSymbol
          (hboundary 3)]
        rw [writeLogical_of_ne spec.growth _
          (boundaryOffset spec.registers 4) coordinate blankSymbol
          (hboundary 4)]
        rw [cleanupTape_of_layoutEnd_lt spec T hpast]
  calc
    afterTag spec T =
        logicalTape spec.growth (logicalTape spec.growth (afterTag spec T)) := by
      rw [logicalTape_involutive]
    _ = logicalTape spec.growth
        (logicalTape spec.growth (cleanupTape spec T)) :=
      congrArg (logicalTape spec.growth) hlogical
    _ = cleanupTape spec T := logicalTape_involutive _ _

/-- The exact operational endpoint therefore exposes the suspended outer
search gap proved by the extensional cleanup layer. -/
theorem afterTag_searchGap {numTags : Nat} {spec : Spec numTags}
    {T : FullTM0.Tape (Symbol numTags)} (h : Represents spec T) :
    SearchGap (fun symbol => symbol = blankSymbol) spec.outerTarget.Matches
      (afterTag spec T) spec.growth spec.outerDistance := by
  rw [afterTag_eq_cleanupTape h]
  exact cleanupTape_searchGap h

/-- Public cleanup-chain form whose success endpoint is stated directly with
the extensional `cleanupTape`. -/
theorem machine_reaches_cleanupTape_resume_or_nests
    (base : Nat) (c : Nat.Partrec.Code) (source : Nat)
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T)
    (hreturnDirection :
      (compileCommand base c spec.returnTag).searchDirection = spec.growth)
    (hcommands : ∀ raw, raw ∈ cleanupCommands spec.growth source →
      raw ∈ rawCommands) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨spec.growth, source, cleanupSearchBase⟩,
          atLogical spec.growth (afterFour spec T)
            (layoutEnd spec.registers)⟩
        ⟨resumeState (CanonicalInitializer.radius c)
            (searchState base c
              (rawCommands.get spec.returnTag).address),
          atLogical spec.growth (cleanupTape spec T) 0⟩ ∨
      NestsDuringCleanup base c spec.growth source
        ⟨searchState base c ⟨spec.growth, source, cleanupSearchBase⟩,
          atLogical spec.growth (afterFour spec T)
            (layoutEnd spec.registers)⟩ := by
  simpa only [afterTag_eq_cleanupTape h] using
    machine_reaches_cleanup_resume_or_nests base c source h
      hreturnDirection hcommands

/-! ## Entering cleanup from the collision handoff -/

/-- Direct nonblank branch taken after the outward boundary-`4` shift meets
the suspended outer target. -/
def cleanupEntryRule (growth : Turing.Dir) (source : Nat) : RawDirectRule :=
  ⟨growth, directRef growth source testDirectSlot, .nonblank,
    searchRef growth source cleanupSearchBase, .left⟩

/-- The common nonblank collision handoff from the outward test cell back to
the first cleanup search. -/
theorem machine_reaches_cleanupEntry
    (base : Nat) (c : Nat.Partrec.Code) (source : Nat)
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T)
    (hcollision : layoutEnd spec.registers + 1 = spec.outerDistance)
    (hentry : cleanupEntryRule spec.growth source ∈ rawDirectRules) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      ⟨resolve base c (directRef spec.growth source testDirectSlot),
        atLogical spec.growth (afterFour spec T) spec.outerDistance⟩
      ⟨searchState base c ⟨spec.growth, source, cleanupSearchBase⟩,
        atLogical spec.growth (afterFour spec T)
          (layoutEnd spec.registers)⟩ := by
  have htargetRead : (atLogical spec.growth (afterFour spec T)
      spec.outerDistance).read =
      logicalTape spec.growth T spec.outerDistance := by
    rw [atLogical_read]
    simp only [afterFour, clearBoundary]
    apply writeLogical_of_ne
    rw [boundaryOffset_four]
    omega
  have htargetNonblank : (atLogical spec.growth (afterFour spec T)
      spec.outerDistance).read ≠ blankSymbol := by
    rw [htargetRead]
    intro hblank
    exact target_not_blank spec.outerTarget (hblank ▸ h.target)
  have hentryRun := CounterControlDirectSemantics.reaches_directRule
    base c (cleanupEntryRule spec.growth source) hentry
    (atLogical spec.growth (afterFour spec T) spec.outerDistance)
    htargetNonblank
  have hmove :
      (atLogical spec.growth (afterFour spec T) spec.outerDistance).move
          (orient spec.growth .left) =
        atLogical spec.growth (afterFour spec T)
          (layoutEnd spec.registers) := by
    rw [← hcollision, orient_eq_orientDirection, atLogical_move_left]
  simp only [cleanupEntryRule] at hentryRun
  rw [hmove] at hentryRun
  change FullTM0.Reaches
    (FiniteTM0.machine (CounterControlPlan.table base c)) _ _
  simpa [cleanupEntryRule, searchRef, CounterControlPlan.resolve] using
    hentryRun

/-- From the exact increment-collision endpoint, the generated nonblank glue
rule moves back onto erased boundary `4`; cleanup then resumes the suspended
outer command, or one of its four bounded searches launches a deeper exact
frame. -/
theorem machine_reaches_collision_cleanup_or_nests
    (base : Nat) (c : Nat.Partrec.Code) (source : Nat)
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T)
    (hreturnDirection :
      (compileCommand base c spec.returnTag).searchDirection = spec.growth)
    (hcollision : layoutEnd spec.registers + 1 = spec.outerDistance)
    (hentry : cleanupEntryRule spec.growth source ∈ rawDirectRules)
    (hcommands : ∀ raw, raw ∈ cleanupCommands spec.growth source →
      raw ∈ rawCommands) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨resolve base c (directRef spec.growth source testDirectSlot),
          atLogical spec.growth (afterFour spec T) spec.outerDistance⟩
        ⟨resumeState (CanonicalInitializer.radius c)
            (searchState base c
              (rawCommands.get spec.returnTag).address),
          atLogical spec.growth (cleanupTape spec T) 0⟩ ∨
      NestsDuringCleanup base c spec.growth source
        ⟨resolve base c (directRef spec.growth source testDirectSlot),
          atLogical spec.growth (afterFour spec T) spec.outerDistance⟩ := by
  have hentryRun := machine_reaches_cleanupEntry base c source h
    hcollision hentry
  rcases machine_reaches_cleanupTape_resume_or_nests base c source h
      hreturnDirection hcommands with hresume | hnests
  · exact Or.inl (hentryRun.trans hresume)
  · right
    rcases hnests with ⟨raw, hcleanup, hraw, outer, distance, hfar,
      hreach, hframe⟩
    exact ⟨raw, hcleanup, hraw, outer, distance, hfar,
      hentryRun.trans hreach, hframe⟩

end

end CounterControlCleanupSemantics
end Hooper
end Kari
end LeanWang
