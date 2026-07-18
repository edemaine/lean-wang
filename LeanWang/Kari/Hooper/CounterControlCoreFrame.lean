/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.FramedCounterGeometry

/-!
# Target-free counter-core invariants

`FramedMarkerTape.Represents` describes a genuine suspended search and hence
includes its far target.  Instruction validation and most counter geometry
need much less: the exact five-boundary core, sometimes the adjacent return
tag, and sometimes a blank prefix beyond boundary `4`.

This file factors those three layers.  A finite framed representation maps to
`PrefixRepresents`; the open-frame module supplies the corresponding map from
its infinite runway.  The common boundary and adjacent-gap API below is
therefore independent of whether an outer target exists.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlCoreFrame

open Turing CounterMachine
open BoundedMarkerProgram FramedMarkerTape

noncomputable section

/-- Exact five-boundary unary encoding, with no assumption about a return tag
or any cell outside the core. -/
structure CoreRepresents {numTags : Nat} (registers : Registers)
    (growth : Turing.Dir) (T : FullTM0.Tape (Symbol numTags)) : Prop where
  core : ∀ position ≤ RegisterLayout.clockBoundary registers,
    logicalTape growth T (position + 1) = coreSymbol registers position

/-- A core whose logical coordinate `0` is the specified adjacent return
tag. -/
structure TaggedCoreRepresents {numTags : Nat} (registers : Registers)
    (growth : Turing.Dir) (returnTag : Fin numTags)
    (T : FullTM0.Tape (Symbol numTags)) : Prop extends
    CoreRepresents registers growth T where
  tag : logicalTape growth T 0 = tagSymbol returnTag

/-- A tagged core followed by blanks up to, but not including, `limit`.
Unlike a finite Hooper frame, this predicate does not assert that any target
is present at `limit`. -/
structure PrefixRepresents {numTags : Nat} (registers : Registers)
    (growth : Turing.Dir) (returnTag : Fin numTags) (limit : Nat)
    (T : FullTM0.Tape (Symbol numTags)) : Prop extends
    TaggedCoreRepresents registers growth returnTag T where
  core_before_limit : layoutEnd registers < limit
  runway : ∀ position, layoutEnd registers < position →
    position < limit → logicalTape growth T position = blankSymbol

namespace CoreRepresents

variable {numTags : Nat} {registers : Registers}
variable {growth : Turing.Dir} {T : FullTM0.Tape (Symbol numTags)}

/-- Every labelled canonical boundary follows from the core alone. -/
theorem boundary (h : CoreRepresents registers growth T) (label : Fin 5) :
    logicalTape growth T (boundaryOffset registers label) =
      boundarySymbol label := by
  have hlabel : (label : Nat) ≤ 4 := by omega
  have hposition : CounterLayout.boundaryPos
      (RegisterLayout.values registers) label ≤
      RegisterLayout.clockBoundary registers :=
    CounterLayout.boundaryPos_mono _ hlabel
  simpa [boundaryOffset] using h.core
    (CounterLayout.boundaryPos (RegisterLayout.values registers) label)
    hposition

theorem boundaryAt (h : CoreRepresents registers growth T)
    (label : Fin 5) :
    T (physicalCoord growth (boundaryOffset registers label)) =
      boundarySymbol label := by
  simpa using h.boundary label

theorem boundary_four (h : CoreRepresents registers growth T) :
    logicalTape growth T (layoutEnd registers) = boundarySymbol 4 := by
  simpa using h.boundary (4 : Fin 5)

theorem read_boundary_four (h : CoreRepresents registers growth T) :
    (atLogical growth T (layoutEnd registers)).read = boundarySymbol 4 := by
  rw [atLogical_read]
  exact h.boundary_four

/-- Every genuine cell of a represented register gap is blank. -/
theorem gap_blank (h : CoreRepresents registers growth T)
    (i : Fin 4) (k : Nat) (hk : k < RegisterLayout.values registers i) :
    logicalTape growth T (firstGapOffset registers i + k) = blankSymbol := by
  let position :=
    CounterLayout.boundaryPos (RegisterLayout.values registers) i + 1 + k
  have hi : (i : Nat) + 1 ≤ 4 := by omega
  have hnext : CounterLayout.boundaryPos
      (RegisterLayout.values registers) (i + 1) ≤
      RegisterLayout.clockBoundary registers :=
    CounterLayout.boundaryPos_mono _ hi
  have hlt := CounterLayout.firstGapCell_add_lt_boundary
    (RegisterLayout.values registers) i k hk
  have hposition : position ≤ RegisterLayout.clockBoundary registers :=
    (Nat.le_of_lt hlt).trans hnext
  have hcore := h.core position hposition
  rw [coreSymbol_gapInterior registers i k hk] at hcore
  have hcoordinate : firstGapOffset registers i + k = position + 1 := by
    simp only [firstGapOffset, position]
    omega
  have hcoordinate' :
      (firstGapOffset registers i : Int) + k = (position : Int) + 1 := by
    exact_mod_cast hcoordinate
  rw [hcoordinate']
  exact hcore

/-- The cell immediately preceding the tested boundary is blank when the
selected represented register is positive. -/
theorem positive_predecessor_blank
    (h : CoreRepresents registers growth T) (register : Register)
    (hpositive : 0 < registers.get register) :
    (atLogical growth T
      (boundaryOffset registers
        (MarkerSchedule.decrementStartBoundary register) - 1)).read =
      blankSymbol := by
  rw [atLogical_read]
  have hblank := h.gap_blank
    (AnchoredCounterGeometry.registerGap register)
    (registers.get register - 1) (by
      rw [AnchoredCounterGeometry.values_registerGap]
      omega)
  have hcoordinate :
      (firstGapOffset registers
          (AnchoredCounterGeometry.registerGap register) : Int) +
          (registers.get register - 1 : Nat) =
        (boundaryOffset registers
          (MarkerSchedule.decrementStartBoundary register) - 1 : Nat) := by
    exact_mod_cast AnchoredCounterGeometry.positiveTest_predecessor
      registers register hpositive
  rw [hcoordinate] at hblank
  exact hblank

theorem searchGap_boundary_zero
    (h : CoreRepresents registers growth T) :
    SearchGap (fun symbol => symbol = blankSymbol)
      (fun symbol => symbol = boundarySymbol 0)
      (atLogical growth T 1) growth 0 := by
  rw [SearchGap.zero]
  change (atLogical growth T 1).read = boundarySymbol 0
  rw [atLogical_read]
  simpa using h.boundary (0 : Fin 5)

theorem searchGap_adjacent_right
    (h : CoreRepresents registers growth T) (i : Fin 4) :
    SearchGap (fun symbol => symbol = blankSymbol)
      (fun symbol => symbol = boundarySymbol i.succ)
      (atLogical growth T (firstGapOffset registers i))
      (OrientedMarkerTape.orientDirection growth .right)
      (RegisterLayout.values registers i) := by
  constructor
  · intro k hk
    rw [atLogical_apply_offset]
    have hblank := h.gap_blank i k hk
    simpa [firstGapOffset, FullTM0.Tape.offset_right,
      Nat.cast_add] using hblank
  · rw [atLogical_apply_offset]
    have hboundary := h.boundary i.succ
    have hposition : firstGapOffset registers i +
          RegisterLayout.values registers i =
        boundaryOffset registers i.succ := by
      change CounterLayout.boundaryPos
          (RegisterLayout.values registers) i + 2 +
          RegisterLayout.values registers i =
        CounterLayout.boundaryPos
          (RegisterLayout.values registers) ((i : Nat) + 1) + 1
      rw [CounterLayout.boundaryPos_succ]
      omega
    have hposition' : (firstGapOffset registers i : Int) +
          FullTM0.Tape.offset .right (RegisterLayout.values registers i) =
        boundaryOffset registers i.succ := by
      rw [FullTM0.Tape.offset_right]
      exact_mod_cast hposition
    rw [hposition']
    exact hboundary

theorem searchGap_adjacent_left
    (h : CoreRepresents registers growth T) (i : Fin 4) :
    SearchGap (fun symbol => symbol = blankSymbol)
      (fun symbol => symbol = boundarySymbol i.castSucc)
      (atLogical growth T (lastGapOffset registers i))
      (OrientedMarkerTape.orientDirection growth .left)
      (RegisterLayout.values registers i) := by
  constructor
  · intro k hk
    rw [atLogical_apply_offset]
    let remainder := RegisterLayout.values registers i - 1 - k
    have hremainder : remainder < RegisterLayout.values registers i := by
      dsimp [remainder]
      omega
    have hblank := h.gap_blank i remainder hremainder
    have hnext := CounterLayout.boundaryPos_succ
      (RegisterLayout.values registers) i
    have hposition : (lastGapOffset registers i : Int) +
          FullTM0.Tape.offset .left k =
        (firstGapOffset registers i + remainder : Nat) := by
      simp only [lastGapOffset, firstGapOffset, FullTM0.Tape.offset_left]
      rw [hnext]
      dsimp [remainder]
      omega
    rw [hposition]
    exact hblank
  · rw [atLogical_apply_offset]
    have hboundary := h.boundary i.castSucc
    have hnext := CounterLayout.boundaryPos_succ
      (RegisterLayout.values registers) i
    have hposition : (lastGapOffset registers i : Int) +
          FullTM0.Tape.offset .left (RegisterLayout.values registers i) =
        boundaryOffset registers i.castSucc := by
      simp only [lastGapOffset, boundaryOffset,
        FullTM0.Tape.offset_left, Fin.val_castSucc]
      push_cast
      rw [hnext]
      push_cast
      omega
    rw [hposition]
    exact hboundary

end CoreRepresents

namespace TaggedCoreRepresents

variable {numTags : Nat} {registers : Registers}
variable {growth : Turing.Dir} {returnTag : Fin numTags}
variable {T : FullTM0.Tape (Symbol numTags)}

theorem tagAt (h : TaggedCoreRepresents registers growth returnTag T) :
    T 0 = tagSymbol returnTag := by
  simpa only [logicalTape_apply, physicalCoord_zero] using h.tag

theorem read_tag (h : TaggedCoreRepresents registers growth returnTag T) :
    T.read = tagSymbol returnTag := by
  simpa [FullTM0.Tape.read] using h.tagAt

theorem searchGap_tag
    (h : TaggedCoreRepresents registers growth returnTag T)
    (direction : Turing.Dir) :
    SearchGap (fun symbol => symbol = blankSymbol)
      (Target.anyTag : Target numTags).Matches T direction 0 := by
  rw [SearchGap.zero]
  exact ⟨returnTag, h.tagAt⟩

end TaggedCoreRepresents

namespace PrefixRepresents

variable {numTags : Nat} {registers : Registers}
variable {growth : Turing.Dir} {returnTag : Fin numTags} {limit : Nat}
variable {T : FullTM0.Tape (Symbol numTags)}

/-- Every genuine finite framed representation has the corresponding
target-free prefix representation. -/
theorem ofFramed {spec : Spec numTags}
    (h : FramedMarkerTape.Represents spec T) :
    PrefixRepresents spec.registers spec.growth spec.returnTag
      spec.outerDistance T where
  toTaggedCoreRepresents :=
    { toCoreRepresents := ⟨h.core⟩
      tag := h.tag }
  core_before_limit := spec.core_before_target
  runway := h.runway

theorem runwayAt
    (h : PrefixRepresents registers growth returnTag limit T)
    {position : Nat} (hcore : layoutEnd registers < position)
    (hlimit : position < limit) :
    T (physicalCoord growth position) = blankSymbol := by
  simpa using h.runway position hcore hlimit

end PrefixRepresents

end


end CounterControlCoreFrame
end Hooper
end Kari
end LeanWang
