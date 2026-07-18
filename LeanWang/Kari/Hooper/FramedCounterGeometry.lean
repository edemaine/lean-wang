/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Kari.Hooper.FramedMarkerTape
import LeanWang.Kari.Hooper.OrientedMarkerTape
import LeanWang.Kari.Hooper.MarkerSchedule
import LeanWang.Kari.Hooper.AnchoredCounterGeometry

/-!
# Counter updates inside a finite tagged frame

This file isolates the arithmetic and tape geometry needed when the marker
controller changes one register of a nested counter.  Incrementing a register
moves the far boundary one cell toward the suspended outer target.  A
successful decrement moves it one cell back toward the return tag and must
clear the old far-boundary cell.

The update operations below are extensional specifications of the tapes
produced by the oriented marker schedules.  They preserve the physical
orientation, return tag, outer target, and every cell past the rewritten
finite core.  A later compiler module can connect its finite rule tables to
these specifications without reproving the frame arithmetic.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace FramedCounterGeometry

open Turing CounterMachine
open BoundedMarkerProgram FramedMarkerTape

/-! ## Far-boundary arithmetic -/

/-- Every register increment moves boundary `4` outward by one cell. -/
@[simp]
theorem layoutEnd_increment (registers : Registers) (register : Register) :
    layoutEnd (registers.increment register) = layoutEnd registers + 1 := by
  cases register <;>
    simp [layoutEnd, RegisterLayout.clockBoundary_eq,
      Registers.increment, Registers.set, Registers.get] <;>
    omega

/-- A positive register decrement moves boundary `4` inward by one cell. -/
theorem layoutEnd_decrement_add_one (registers : Registers)
    (register : Register) (hpositive : 0 < registers.get register) :
    layoutEnd (registers.decrement register) + 1 = layoutEnd registers := by
  cases register <;>
    simp_all [layoutEnd, RegisterLayout.clockBoundary_eq,
      Registers.decrement, Registers.set, Registers.get] <;>
    omega

theorem layoutEnd_decrement_lt (registers : Registers)
    (register : Register) (hpositive : 0 < registers.get register) :
    layoutEnd (registers.decrement register) < layoutEnd registers := by
  rw [← layoutEnd_decrement_add_one registers register hpositive]
  exact Nat.lt_succ_self _

/-! ## Updating the abstract frame -/

/-- Replace the register payload of a frame, retaining all outer data. -/
def updateSpec {numTags : Nat} (spec : Spec numTags) (registers : Registers)
    (hcore : layoutEnd registers < spec.outerDistance) : Spec numTags where
  growth := spec.growth
  returnTag := spec.returnTag
  registers := registers
  outerDistance := spec.outerDistance
  outerTarget := spec.outerTarget
  core_before_target := hcore

/-- Frame after a safe increment.  The explicit room hypothesis is exactly
the condition under which the final outward boundary shift does not collide
with the suspended outer target. -/
def incrementSpec {numTags : Nat} (spec : Spec numTags)
    (register : Register)
    (hroom : layoutEnd (spec.registers.increment register) <
      spec.outerDistance) : Spec numTags :=
  updateSpec spec (spec.registers.increment register) hroom

/-- Frame after a positive decrement.  No extra room hypothesis is needed,
because the finite core becomes strictly shorter. -/
def decrementSpec {numTags : Nat} (spec : Spec numTags)
    (register : Register) (hpositive : 0 < spec.registers.get register) :
    Spec numTags :=
  updateSpec spec (spec.registers.decrement register)
    (lt_trans (layoutEnd_decrement_lt spec.registers register hpositive)
      spec.core_before_target)

@[simp] theorem updateSpec_growth {numTags : Nat} (spec : Spec numTags)
    (registers : Registers)
    (hcore : layoutEnd registers < spec.outerDistance) :
    (updateSpec spec registers hcore).growth = spec.growth := rfl

@[simp] theorem updateSpec_returnTag {numTags : Nat} (spec : Spec numTags)
    (registers : Registers)
    (hcore : layoutEnd registers < spec.outerDistance) :
    (updateSpec spec registers hcore).returnTag = spec.returnTag := rfl

@[simp] theorem updateSpec_registers {numTags : Nat} (spec : Spec numTags)
    (registers : Registers)
    (hcore : layoutEnd registers < spec.outerDistance) :
    (updateSpec spec registers hcore).registers = registers := rfl

@[simp] theorem updateSpec_outerDistance {numTags : Nat} (spec : Spec numTags)
    (registers : Registers)
    (hcore : layoutEnd registers < spec.outerDistance) :
    (updateSpec spec registers hcore).outerDistance = spec.outerDistance := rfl

@[simp] theorem updateSpec_outerTarget {numTags : Nat} (spec : Spec numTags)
    (registers : Registers)
    (hcore : layoutEnd registers < spec.outerDistance) :
    (updateSpec spec registers hcore).outerTarget = spec.outerTarget := rfl

/-! ## Pointwise tape updates -/

/-- Write one symbol at a nonnegative logical coordinate, independent of the
physical orientation of the nested frame. -/
def writeLogical {numTags : Nat} (growth : Turing.Dir)
    (T : FullTM0.Tape (Symbol numTags)) (position : Nat)
    (symbol : Symbol numTags) : FullTM0.Tape (Symbol numTags) :=
  Function.update T (physicalCoord growth position) symbol

@[simp]
theorem writeLogical_at {numTags : Nat} (growth : Turing.Dir)
    (T : FullTM0.Tape (Symbol numTags)) (position : Nat)
    (symbol : Symbol numTags) :
    logicalTape growth (writeLogical growth T position symbol) position =
      symbol := by
  simp [logicalTape_apply, writeLogical]

theorem writeLogical_of_ne {numTags : Nat} (growth : Turing.Dir)
    (T : FullTM0.Tape (Symbol numTags)) (position other : Nat)
    (symbol : Symbol numTags) (hne : other ≠ position) :
    logicalTape growth (writeLogical growth T position symbol) other =
      logicalTape growth T other := by
  rw [logicalTape_apply, logicalTape_apply]
  apply Function.update_of_ne
  intro hphysical
  apply hne
  have hlogical := physicalCoord_injective growth hphysical
  exact_mod_cast hlogical

/-- Extensional tape specification after a noncolliding increment. -/
noncomputable def incrementTape {numTags : Nat} (spec : Spec numTags)
    (register : Register) (T : FullTM0.Tape (Symbol numTags)) :
    FullTM0.Tape (Symbol numTags) :=
  install (spec.registers.increment register) spec.growth spec.returnTag T

/-- Clear the cell vacated by the old far boundary. -/
def clearOldLayoutEnd {numTags : Nat} (spec : Spec numTags)
    (T : FullTM0.Tape (Symbol numTags)) : FullTM0.Tape (Symbol numTags) :=
  writeLogical spec.growth T (layoutEnd spec.registers) blankSymbol

/-- Extensional tape specification after a positive decrement.  Installing
the shorter core alone would expose the old boundary `4`; clearing that one
vacated cell makes it the first blank of the enlarged runway. -/
noncomputable def decrementTape {numTags : Nat} (spec : Spec numTags)
    (register : Register) (T : FullTM0.Tape (Symbol numTags)) :
    FullTM0.Tape (Symbol numTags) :=
  install (spec.registers.decrement register) spec.growth spec.returnTag
    (clearOldLayoutEnd spec T)

@[simp]
theorem logicalTape_incrementTape {numTags : Nat} (spec : Spec numTags)
    (register : Register) (T : FullTM0.Tape (Symbol numTags)) :
    logicalTape spec.growth (incrementTape spec register T) =
      logicalOverlay (spec.registers.increment register) spec.returnTag
        (logicalTape spec.growth T) := by
  simp [incrementTape]

@[simp]
theorem logicalTape_decrementTape {numTags : Nat} (spec : Spec numTags)
    (register : Register) (T : FullTM0.Tape (Symbol numTags)) :
    logicalTape spec.growth (decrementTape spec register T) =
      logicalOverlay (spec.registers.decrement register) spec.returnTag
        (logicalTape spec.growth (clearOldLayoutEnd spec T)) := by
  simp [decrementTape]

@[simp]
theorem incrementTape_tag {numTags : Nat} (spec : Spec numTags)
    (register : Register) (T : FullTM0.Tape (Symbol numTags)) :
    logicalTape spec.growth (incrementTape spec register T) 0 =
      tagSymbol spec.returnTag := by
  simpa [incrementTape] using install_tag
    (spec.registers.increment register) spec.growth spec.returnTag T

@[simp]
theorem decrementTape_tag {numTags : Nat} (spec : Spec numTags)
    (register : Register) (T : FullTM0.Tape (Symbol numTags)) :
    logicalTape spec.growth (decrementTape spec register T) 0 =
      tagSymbol spec.returnTag := by
  simpa [decrementTape] using install_tag
    (spec.registers.decrement register) spec.growth spec.returnTag
      (clearOldLayoutEnd spec T)

/-- The collision-free increment endpoint has boundary `4` at the updated
far anchor, in either physical orientation. -/
theorem incrementTape_boundary_four {numTags : Nat} (spec : Spec numTags)
    (register : Register) (T : FullTM0.Tape (Symbol numTags))
    (_hroom : layoutEnd (spec.registers.increment register) <
      spec.outerDistance) :
    logicalTape spec.growth (incrementTape spec register T)
        (layoutEnd (spec.registers.increment register)) = boundarySymbol 4 := by
  have hcore := install_core (numTags := numTags)
    (spec.registers.increment register) spec.growth spec.returnTag T
    (RegisterLayout.clockBoundary (spec.registers.increment register))
    (le_refl _)
  have hsymbol : coreSymbol (numTags := numTags)
      (spec.registers.increment register)
        (RegisterLayout.clockBoundary (spec.registers.increment register)) =
      boundarySymbol 4 := by
    simpa [RegisterLayout.clockBoundary] using coreSymbol_boundary
      (numTags := numTags) (spec.registers.increment register) (4 : Fin 5)
  rw [hsymbol] at hcore
  simpa [incrementTape, layoutEnd] using hcore

/-- The positive-decrement endpoint has boundary `4` at the updated inward
anchor, in either physical orientation. -/
theorem decrementTape_boundary_four {numTags : Nat} (spec : Spec numTags)
    (register : Register) (T : FullTM0.Tape (Symbol numTags))
    (_hpositive : 0 < spec.registers.get register) :
    logicalTape spec.growth (decrementTape spec register T)
        (layoutEnd (spec.registers.decrement register)) = boundarySymbol 4 := by
  have hcore := install_core (numTags := numTags)
    (spec.registers.decrement register) spec.growth spec.returnTag
    (clearOldLayoutEnd spec T)
    (RegisterLayout.clockBoundary (spec.registers.decrement register))
    (le_refl _)
  have hsymbol : coreSymbol (numTags := numTags)
      (spec.registers.decrement register)
        (RegisterLayout.clockBoundary (spec.registers.decrement register)) =
      boundarySymbol 4 := by
    simpa [RegisterLayout.clockBoundary] using coreSymbol_boundary
      (numTags := numTags) (spec.registers.decrement register) (4 : Fin 5)
  rw [hsymbol] at hcore
  simpa [decrementTape, layoutEnd] using hcore

/-- A noncolliding increment is pointwise invisible strictly past its new
far boundary. -/
theorem incrementTape_of_layoutEnd_lt {numTags : Nat} (spec : Spec numTags)
    (register : Register) (T : FullTM0.Tape (Symbol numTags))
    {position : Nat}
    (hposition : layoutEnd (spec.registers.increment register) < position) :
    logicalTape spec.growth (incrementTape spec register T) position =
      logicalTape spec.growth T position := by
  simpa [incrementTape] using install_of_layoutEnd_lt
    (spec.registers.increment register) spec.growth spec.returnTag T hposition

/-- A positive decrement clears exactly the vacated old far-boundary cell. -/
theorem decrementTape_old_layoutEnd_blank {numTags : Nat}
    (spec : Spec numTags) (register : Register)
    (T : FullTM0.Tape (Symbol numTags))
    (hpositive : 0 < spec.registers.get register) :
    logicalTape spec.growth (decrementTape spec register T)
        (layoutEnd spec.registers) = blankSymbol := by
  have hpast : layoutEnd (spec.registers.decrement register) <
      layoutEnd spec.registers :=
    layoutEnd_decrement_lt spec.registers register hpositive
  rw [show logicalTape spec.growth (decrementTape spec register T)
      (layoutEnd spec.registers) =
        logicalTape spec.growth (clearOldLayoutEnd spec T)
          (layoutEnd spec.registers) by
    simpa [decrementTape] using install_of_layoutEnd_lt
      (spec.registers.decrement register) spec.growth spec.returnTag
        (clearOldLayoutEnd spec T) hpast]
  exact writeLogical_at spec.growth T (layoutEnd spec.registers) blankSymbol

/-- Strictly past the old far boundary, a positive decrement is pointwise
invisible. -/
theorem decrementTape_of_old_layoutEnd_lt {numTags : Nat}
    (spec : Spec numTags) (register : Register)
    (T : FullTM0.Tape (Symbol numTags))
    (hpositive : 0 < spec.registers.get register) {position : Nat}
    (hposition : layoutEnd spec.registers < position) :
    logicalTape spec.growth (decrementTape spec register T) position =
      logicalTape spec.growth T position := by
  have hnew : layoutEnd (spec.registers.decrement register) < position :=
    lt_trans (layoutEnd_decrement_lt spec.registers register hpositive)
      hposition
  rw [show logicalTape spec.growth (decrementTape spec register T) position =
      logicalTape spec.growth (clearOldLayoutEnd spec T) position by
    simpa [decrementTape] using install_of_layoutEnd_lt
      (spec.registers.decrement register) spec.growth spec.returnTag
        (clearOldLayoutEnd spec T) hnew]
  simpa [clearOldLayoutEnd] using writeLogical_of_ne spec.growth T
    (layoutEnd spec.registers) position blankSymbol (Nat.ne_of_gt hposition)

/-! ## Preservation of framed representations -/

/-- Installing the incremented canonical core preserves a frame whenever
there is still at least one strict cell of separation from its target. -/
theorem incrementTape_represents {numTags : Nat} {spec : Spec numTags}
    {T : FullTM0.Tape (Symbol numTags)} (h : Represents spec T)
    (register : Register)
    (hroom : layoutEnd (spec.registers.increment register) <
      spec.outerDistance) :
    Represents (incrementSpec spec register hroom)
      (incrementTape spec register T) := by
  constructor
  · simpa [incrementSpec, updateSpec, incrementTape] using
      install_tag (spec.registers.increment register) spec.growth
        spec.returnTag T
  · intro position hposition
    simpa [incrementSpec, updateSpec, incrementTape] using
      install_core (spec.registers.increment register) spec.growth
        spec.returnTag T position hposition
  · intro position hcore htarget
    have hnew : layoutEnd (spec.registers.increment register) < position :=
      hcore
    have hold : layoutEnd spec.registers < position := by
      rw [layoutEnd_increment] at hnew
      omega
    change logicalTape spec.growth (incrementTape spec register T) position =
      blankSymbol
    change position < spec.outerDistance at htarget
    rw [show logicalTape spec.growth (incrementTape spec register T) position =
        logicalTape spec.growth T position by
      simpa [incrementTape] using install_of_layoutEnd_lt
        (spec.registers.increment register) spec.growth spec.returnTag T hnew]
    exact h.runway position hold htarget
  · change spec.outerTarget.Matches
      (logicalTape spec.growth (incrementTape spec register T)
        spec.outerDistance)
    rw [show logicalTape spec.growth (incrementTape spec register T)
        spec.outerDistance = logicalTape spec.growth T spec.outerDistance by
      simpa [incrementTape] using install_of_layoutEnd_lt
        (spec.registers.increment register) spec.growth spec.returnTag T hroom]
    exact h.target

/-- A positive decrement preserves the frame, with the old far boundary
becoming the first blank cell of the enlarged runway. -/
theorem decrementTape_represents {numTags : Nat} {spec : Spec numTags}
    {T : FullTM0.Tape (Symbol numTags)} (h : Represents spec T)
    (register : Register) (hpositive : 0 < spec.registers.get register) :
    Represents (decrementSpec spec register hpositive)
      (decrementTape spec register T) := by
  constructor
  · simpa [decrementSpec, updateSpec, decrementTape] using
      install_tag (spec.registers.decrement register) spec.growth
        spec.returnTag (clearOldLayoutEnd spec T)
  · intro position hposition
    simpa [decrementSpec, updateSpec, decrementTape] using
      install_core (spec.registers.decrement register) spec.growth
        spec.returnTag (clearOldLayoutEnd spec T) position hposition
  · intro position hcore htarget
    have hnew : layoutEnd (spec.registers.decrement register) < position :=
      hcore
    change logicalTape spec.growth (decrementTape spec register T) position =
      blankSymbol
    change position < spec.outerDistance at htarget
    rw [show logicalTape spec.growth (decrementTape spec register T) position =
        logicalTape spec.growth (clearOldLayoutEnd spec T) position by
      simpa [decrementTape] using install_of_layoutEnd_lt
        (spec.registers.decrement register) spec.growth spec.returnTag
          (clearOldLayoutEnd spec T) hnew]
    by_cases hvacated : position = layoutEnd spec.registers
    · subst position
      exact writeLogical_at spec.growth T (layoutEnd spec.registers)
        blankSymbol
    · rw [show logicalTape spec.growth (clearOldLayoutEnd spec T) position =
          logicalTape spec.growth T position by
        simpa [clearOldLayoutEnd] using
          writeLogical_of_ne spec.growth T (layoutEnd spec.registers)
            position blankSymbol hvacated]
      have hold : layoutEnd spec.registers < position := by
        have hstep := layoutEnd_decrement_add_one spec.registers register
          hpositive
        omega
      exact h.runway position hold htarget
  · have hne : spec.outerDistance ≠ layoutEnd spec.registers :=
      Nat.ne_of_gt spec.core_before_target
    change spec.outerTarget.Matches
      (logicalTape spec.growth (decrementTape spec register T)
        spec.outerDistance)
    rw [show logicalTape spec.growth (decrementTape spec register T)
        spec.outerDistance =
          logicalTape spec.growth (clearOldLayoutEnd spec T)
            spec.outerDistance by
      simpa [decrementTape] using install_of_layoutEnd_lt
        (spec.registers.decrement register) spec.growth spec.returnTag
          (clearOldLayoutEnd spec T)
          (lt_trans
            (layoutEnd_decrement_lt spec.registers register hpositive)
            spec.core_before_target)]
    rw [show logicalTape spec.growth (clearOldLayoutEnd spec T)
          spec.outerDistance = logicalTape spec.growth T spec.outerDistance by
      simpa [clearOldLayoutEnd] using
        writeLogical_of_ne spec.growth T (layoutEnd spec.registers)
          spec.outerDistance blankSymbol hne]
    exact h.target

/-! ## Safe growth versus collision -/

/-- The far destination of every register increment is independent of the
selected register. -/
theorem increment_layoutEnd_eq_succ {numTags : Nat} (spec : Spec numTags)
    (register : Register) :
    layoutEnd (spec.registers.increment register) =
      layoutEnd spec.registers + 1 :=
  layoutEnd_increment spec.registers register

/-- Because the old core is strictly before the target, the final outward
shift of an increment has exactly two geometric outcomes: another runway
blank remains, or the shifted boundary reaches the outer target cell. -/
theorem increment_has_room_or_collision {numTags : Nat}
    (spec : Spec numTags) (register : Register) :
    layoutEnd (spec.registers.increment register) < spec.outerDistance ∨
      layoutEnd (spec.registers.increment register) = spec.outerDistance := by
  have hbefore := spec.core_before_target
  rw [layoutEnd_increment]
  omega

/-- Collision is precisely adjacency of the old far boundary and the outer
target. -/
theorem increment_collision_iff {numTags : Nat} (spec : Spec numTags)
    (register : Register) :
    layoutEnd (spec.registers.increment register) = spec.outerDistance ↔
      layoutEnd spec.registers + 1 = spec.outerDistance := by
  rw [layoutEnd_increment]

/-- In the noncolliding branch, the first newly consumed cell is a runway
blank of the old frame. -/
theorem increment_destination_blank {numTags : Nat} {spec : Spec numTags}
    {T : FullTM0.Tape (Symbol numTags)} (h : Represents spec T)
    (register : Register)
    (hroom : layoutEnd (spec.registers.increment register) <
      spec.outerDistance) :
    logicalTape spec.growth T
        (layoutEnd (spec.registers.increment register)) = blankSymbol := by
  have hpast : layoutEnd spec.registers <
      layoutEnd (spec.registers.increment register) := by
    rw [layoutEnd_increment]
    omega
  exact h.runway _ hpast hroom

/-- In the collision branch, that same physical destination carries the
suspended outer target.  The target symbol is not assumed to be a particular
boundary because cleanup commands also search for arbitrary tags. -/
theorem increment_destination_matches_of_collision {numTags : Nat}
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T) (register : Register)
    (hcollision : layoutEnd (spec.registers.increment register) =
      spec.outerDistance) :
    spec.outerTarget.Matches
      (logicalTape spec.growth T
        (layoutEnd (spec.registers.increment register))) := by
  rw [hcollision]
  exact h.target

/-! ## Extensional cleanup -/

/-- Clear a finite prefix in ordinary logical coordinates. -/
def clearLogicalPrefix {numTags : Nat} (last : Nat)
    (T : FullTM0.Tape (Symbol numTags)) : FullTM0.Tape (Symbol numTags) :=
  fun position =>
    if 0 ≤ position ∧ position ≤ last then blankSymbol else T position

/-- Extensional result of cleanup: erase the return tag and all five inner
boundaries, while preserving every cell past the old boundary `4`. -/
def cleanupTape {numTags : Nat} (spec : Spec numTags)
    (T : FullTM0.Tape (Symbol numTags)) : FullTM0.Tape (Symbol numTags) :=
  logicalTape spec.growth
    (clearLogicalPrefix (layoutEnd spec.registers)
      (logicalTape spec.growth T))

@[simp]
theorem logicalTape_cleanupTape {numTags : Nat} (spec : Spec numTags)
    (T : FullTM0.Tape (Symbol numTags)) :
    logicalTape spec.growth (cleanupTape spec T) =
      clearLogicalPrefix (layoutEnd spec.registers)
        (logicalTape spec.growth T) := by
  simp [cleanupTape]

@[simp]
theorem cleanupTape_blank {numTags : Nat} (spec : Spec numTags)
    (T : FullTM0.Tape (Symbol numTags)) (position : Nat)
    (hposition : position ≤ layoutEnd spec.registers) :
    logicalTape spec.growth (cleanupTape spec T) position = blankSymbol := by
  rw [logicalTape_cleanupTape]
  simp [clearLogicalPrefix, hposition]

theorem cleanupTape_of_layoutEnd_lt {numTags : Nat} (spec : Spec numTags)
    (T : FullTM0.Tape (Symbol numTags)) {position : Nat}
    (hposition : layoutEnd spec.registers < position) :
    logicalTape spec.growth (cleanupTape spec T) position =
      logicalTape spec.growth T position := by
  rw [logicalTape_cleanupTape]
  rw [clearLogicalPrefix, if_neg]
  intro hinterval
  have hle : position ≤ layoutEnd spec.registers := by
    exact_mod_cast hinterval.2
  omega

/-- Cleanup restores the complete suspended search gap from the erased tag
cell to the outer target.  This is the frame-level statement used when a
nested collision returns control to its caller. -/
theorem cleanupTape_searchGap {numTags : Nat} {spec : Spec numTags}
    {T : FullTM0.Tape (Symbol numTags)} (h : Represents spec T) :
    SearchGap (fun symbol => symbol = blankSymbol) spec.outerTarget.Matches
      (cleanupTape spec T) spec.growth spec.outerDistance := by
  constructor
  · intro k hk
    have hcoordinate :
        (cleanupTape spec T)
            (FullTM0.Tape.offset spec.growth k) =
          logicalTape spec.growth (cleanupTape spec T) k := by
      simpa only [physicalCoord_nat] using
        (logicalTape_apply spec.growth (cleanupTape spec T) (k : Int)).symm
    rw [hcoordinate]
    by_cases hprefix : k ≤ layoutEnd spec.registers
    · exact cleanupTape_blank spec T k hprefix
    · rw [cleanupTape_of_layoutEnd_lt spec T (Nat.lt_of_not_ge hprefix)]
      exact h.runway k (Nat.lt_of_not_ge hprefix) hk
  · have hcoordinate :
        (cleanupTape spec T)
            (FullTM0.Tape.offset spec.growth spec.outerDistance) =
          logicalTape spec.growth (cleanupTape spec T)
            spec.outerDistance := by
      rw [← physicalCoord_nat]
      exact (logicalTape_apply spec.growth (cleanupTape spec T)
        spec.outerDistance).symm
    rw [hcoordinate]
    rw [cleanupTape_of_layoutEnd_lt spec T spec.core_before_target]
    exact h.target

end FramedCounterGeometry
end Hooper
end Kari
end LeanWang
