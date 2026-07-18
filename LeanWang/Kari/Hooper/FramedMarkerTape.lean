/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Kari.Hooper.BoundedMarkerProgram
import LeanWang.Kari.Hooper.CanonicalInitializer
import LeanWang.Kari.Hooper.OrientedMarkerTape

/-!
# Finite tagged frames around an oriented marker core

A failed bounded search leaves a physical return tag at its launch point and
starts a canonical five-boundary counter layout immediately beyond that tag.
The layout may grow either rightward or leftward.  After boundary `4`, a
finite blank runway separates the nested core from the suspended outer
search's target.

`Spec` records just this finite inspected interval.  `Represents spec tape`
constrains the tag, canonical core, runway, and outer target, but deliberately
says nothing about any other tape cell.  Thus the same finite frame can live
inside an otherwise arbitrary bi-infinite tape.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace FramedMarkerTape

open Turing CounterMachine
open BoundedMarkerProgram

/-! ## Logical and physical coordinates -/

/-- Map a signed logical coordinate of a right-growing diagram to its physical
coordinate in the selected growth orientation. -/
def physicalCoord (growth : Turing.Dir) (logical : Int) : Int :=
  match growth with
  | .right => logical
  | .left => -logical

@[simp] theorem physicalCoord_right (logical : Int) :
    physicalCoord .right logical = logical :=
  rfl

@[simp] theorem physicalCoord_left (logical : Int) :
    physicalCoord .left logical = -logical :=
  rfl

@[simp] theorem physicalCoord_zero (growth : Turing.Dir) :
    physicalCoord growth 0 = 0 := by
  cases growth <;> rfl

@[simp] theorem physicalCoord_neg (growth : Turing.Dir) (logical : Int) :
    physicalCoord growth (-logical) = -physicalCoord growth logical := by
  cases growth <;> simp [physicalCoord]

theorem physicalCoord_injective (growth : Turing.Dir) :
    Function.Injective (physicalCoord growth) := by
  cases growth
  · intro first second h
    simpa [physicalCoord] using congrArg Neg.neg h
  · exact fun _ _ h => h

@[simp] theorem physicalCoord_nat (growth : Turing.Dir) (distance : Nat) :
    physicalCoord growth (distance : Int) =
      FullTM0.Tape.offset growth distance := by
  cases growth <;> simp [physicalCoord]

@[simp] theorem physicalCoord_succ (growth : Turing.Dir) (logical : Int) :
    physicalCoord growth (logical + 1) =
      physicalCoord growth logical + FullTM0.Tape.delta growth := by
  cases growth <;> simp [physicalCoord, add_comm]

/-- View a physically oriented tape in ordinary right-growing logical
coordinates.  Reflection is its own inverse, so this is also the operation
used to orient a logical tape physically. -/
def logicalTape {numTags : Nat} (growth : Turing.Dir)
    (T : FullTM0.Tape (Symbol numTags)) : FullTM0.Tape (Symbol numTags) :=
  OrientedMarkerTape.orientTape growth T

@[simp] theorem logicalTape_apply {numTags : Nat} (growth : Turing.Dir)
    (T : FullTM0.Tape (Symbol numTags)) (logical : Int) :
    logicalTape growth T logical = T (physicalCoord growth logical) := by
  cases growth <;> rfl

@[simp] theorem logicalTape_involutive {numTags : Nat} (growth : Turing.Dir)
    (T : FullTM0.Tape (Symbol numTags)) :
    logicalTape growth (logicalTape growth T) = T := by
  cases growth <;>
    simp [logicalTape, OrientedMarkerTape.orientTape]

/-- Recenter a physical tape at a nonnegative logical coordinate. -/
def atLogical {numTags : Nat} (growth : Turing.Dir)
    (T : FullTM0.Tape (Symbol numTags)) (logical : Nat) :
    FullTM0.Tape (Symbol numTags) :=
  T.moveN growth logical

@[simp] theorem atLogical_read {numTags : Nat} (growth : Turing.Dir)
    (T : FullTM0.Tape (Symbol numTags)) (logical : Nat) :
    (atLogical growth T logical).read = logicalTape growth T logical := by
  cases growth <;>
    simp [atLogical, logicalTape, OrientedMarkerTape.orientTape,
      FullTM0.Tape.read]

/-- Evaluating a recentered physical tape in an oriented direction is the
same as evaluating its logical view at the corresponding signed offset. -/
theorem atLogical_apply_offset {numTags : Nat} (growth logicalDirection : Turing.Dir)
    (T : FullTM0.Tape (Symbol numTags)) (origin distance : Nat) :
    atLogical growth T origin
        (FullTM0.Tape.offset
          (OrientedMarkerTape.orientDirection growth logicalDirection)
          distance) =
      logicalTape growth T
        ((origin : Int) + FullTM0.Tape.offset logicalDirection distance) := by
  cases growth <;> cases logicalDirection <;>
    simp [atLogical, logicalTape, OrientedMarkerTape.orientTape,
      OrientedMarkerTape.orientDirection, FullTM0.Tape.moveN,
      FullTM0.Tape.offset] <;> congr 1 <;> ring

/-! ## The finite canonical interval -/

/-- Logical coordinate of the last cell of the five-boundary core. -/
def layoutEnd (registers : Registers) : Nat :=
  RegisterLayout.clockBoundary registers + 1

/-- Logical coordinate of one labelled boundary.  Boundary `0` is at `1`,
immediately after the return tag at logical coordinate `0`. -/
def boundaryOffset (registers : Registers) (label : Fin 5) : Nat :=
  CounterLayout.boundaryPos (RegisterLayout.values registers) label + 1

/-- Logical coordinate of the first cell in register gap `i`. -/
def firstGapOffset (registers : Registers) (i : Fin 4) : Nat :=
  CounterLayout.boundaryPos (RegisterLayout.values registers) i + 2

/-- Logical coordinate of the last cell in register gap `i`.  For an empty
gap this is the left boundary coordinate, matching distance-zero search
semantics. -/
def lastGapOffset (registers : Registers) (i : Fin 4) : Nat :=
  CounterLayout.boundaryPos (RegisterLayout.values registers) (i + 1)

@[simp] theorem boundaryOffset_zero (registers : Registers) :
    boundaryOffset registers 0 = 1 := by
  simp [boundaryOffset]

@[simp] theorem boundaryOffset_four (registers : Registers) :
    boundaryOffset registers 4 = layoutEnd registers :=
  rfl

/-- Native tagged-alphabet symbol at one unshifted canonical core position. -/
noncomputable def coreSymbol {numTags : Nat} (registers : Registers)
    (position : Nat) : Symbol numTags :=
  baseSymbol (MarkerMachine.encodeSymbol
    (MarkerTape.canonicalTape registers position))

@[simp] theorem coreSymbol_boundary {numTags : Nat} (registers : Registers)
    (label : Fin 5) :
    coreSymbol (numTags := numTags) registers
        (CounterLayout.boundaryPos (RegisterLayout.values registers) label) =
      boundarySymbol label := by
  change baseSymbol (MarkerMachine.encodeSymbol
      (MarkerTape.canonicalTape registers
        (MarkerTape.boundaryPosition registers label))) =
    baseSymbol (MarkerMachine.boundarySymbol label)
  rw [MarkerTape.canonicalTape_boundary]
  rfl

@[simp] theorem coreSymbol_gapInterior {numTags : Nat}
    (registers : Registers) (i : Fin 4) (k : Nat)
    (hk : k < RegisterLayout.values registers i) :
    coreSymbol (numTags := numTags) registers
        (CounterLayout.boundaryPos (RegisterLayout.values registers) i + 1 + k) =
      blankSymbol := by
  change baseSymbol (MarkerMachine.encodeSymbol
      (MarkerTape.canonicalTape registers
        (CounterLayout.boundaryPos (RegisterLayout.values registers) i + 1 + k))) =
    baseSymbol MarkerMachine.blankSymbol
  rw [show MarkerTape.canonicalTape registers
      (CounterLayout.boundaryPos (RegisterLayout.values registers) i + 1 + k) =
      .blank by
    simpa using MarkerTape.canonicalTape_gapInterior registers i k hk]
  rfl

/-- Boundary labels occur at unique canonical positions, now stated directly
in the native tagged alphabet. -/
theorem coreSymbol_eq_boundary_iff {numTags : Nat} (registers : Registers)
    (position : Nat) (label : Fin 5) :
    coreSymbol (numTags := numTags) registers position = boundarySymbol label ↔
      position = CounterLayout.boundaryPos
        (RegisterLayout.values registers) label := by
  constructor
  · intro h
    have hbase := baseSymbol_injective h
    have hmarker : MarkerTape.canonicalTape registers position =
        .boundary label :=
      (MarkerMachine.encodeSymbol_eq_boundary_iff _ label).1
        (by simpa [boundarySymbol] using hbase)
    have hposition :=
      (MarkerTape.canonicalTape_eq_boundary_iff registers position label).1
        hmarker
    have hposition' : (position : Int) =
        CounterLayout.boundaryPos (RegisterLayout.values registers) label := by
      simpa [MarkerTape.boundaryPosition] using hposition
    exact_mod_cast hposition'
  · rintro rfl
    exact coreSymbol_boundary registers label

/-! ## Local frame representation -/

/-- Finite data remembered by one suspended bounded search. -/
structure Spec (numTags : Nat) where
  growth : Turing.Dir
  returnTag : Fin numTags
  registers : Registers
  outerDistance : Nat
  outerTarget : Target numTags
  core_before_target : layoutEnd registers < outerDistance

/-- Canonical frame created for a failed command.  The far-search hypothesis
ensures that the complete initializer fits strictly before the suspended
outer target. -/
noncomputable def frameSpec {numTags : Nat} (c : Nat.Partrec.Code)
    (command : Command numTags) (distance : Nat)
    (hfar : NestingMachine.bound (CanonicalInitializer.radius c) < distance) :
    Spec numTags where
  growth := command.searchDirection
  returnTag := command.returnTag
  registers := CanonicalInitializer.registers c
  outerDistance := distance
  outerTarget := command.target
  core_before_target := by
    have hend : layoutEnd (CanonicalInitializer.registers c) =
        CanonicalInitializer.radius c := by
      simp only [layoutEnd, CanonicalInitializer.radius]
      exact CanonicalInitializer.clockBoundary_registers c
    rw [hend]
    exact lt_trans (by simp [NestingMachine.bound]) hfar

/-! ## Pointwise canonical initialization -/

/-- Overlay the tag and finite canonical core in logical coordinates.  Every
negative coordinate and every coordinate after boundary `4` is inherited
pointwise from `outer`. -/
noncomputable def logicalOverlay {numTags : Nat} (registers : Registers)
    (tag : Fin numTags) (outer : FullTM0.Tape (Symbol numTags)) :
    FullTM0.Tape (Symbol numTags) :=
  fun position =>
    if position = 0 then
      tagSymbol tag
    else if 1 ≤ position ∧ position ≤ layoutEnd registers then
      coreSymbol registers (position.toNat - 1)
    else
      outer position

@[simp] theorem logicalOverlay_zero {numTags : Nat} (registers : Registers)
    (tag : Fin numTags) (outer : FullTM0.Tape (Symbol numTags)) :
    logicalOverlay registers tag outer 0 = tagSymbol tag := by
  simp [logicalOverlay]

@[simp] theorem logicalOverlay_core {numTags : Nat} (registers : Registers)
    (tag : Fin numTags) (outer : FullTM0.Tape (Symbol numTags))
    (position : Nat)
    (hposition : position ≤ RegisterLayout.clockBoundary registers) :
    logicalOverlay registers tag outer (position + 1) =
      coreSymbol registers position := by
  rw [logicalOverlay, if_neg (by omega), if_pos]
  · simp
  · constructor
    · omega
    · simp only [layoutEnd]
      exact_mod_cast Nat.add_le_add_right hposition 1

/-- The overlay is pointwise identical to the outer tape after boundary `4`.
This includes the runway and the suspended target. -/
theorem logicalOverlay_of_layoutEnd_lt {numTags : Nat}
    (registers : Registers) (tag : Fin numTags)
    (outer : FullTM0.Tape (Symbol numTags)) {position : Int}
    (hposition : (layoutEnd registers : Int) < position) :
    logicalOverlay registers tag outer position = outer position := by
  rw [logicalOverlay, if_neg (by omega), if_neg (by omega)]

/-- Physically oriented canonical initialization.  Reflection is applied
before and after the logical overlay, so `outer` is preserved in its original
physical coordinates outside the finite frame. -/
noncomputable def install {numTags : Nat} (registers : Registers)
    (growth : Turing.Dir) (tag : Fin numTags)
    (outer : FullTM0.Tape (Symbol numTags)) :
    FullTM0.Tape (Symbol numTags) :=
  logicalTape growth
    (logicalOverlay registers tag (logicalTape growth outer))

@[simp] theorem logicalTape_install {numTags : Nat} (registers : Registers)
    (growth : Turing.Dir) (tag : Fin numTags)
    (outer : FullTM0.Tape (Symbol numTags)) :
    logicalTape growth (install registers growth tag outer) =
      logicalOverlay registers tag (logicalTape growth outer) := by
  simp [install]

@[simp] theorem install_tag {numTags : Nat} (registers : Registers)
    (growth : Turing.Dir) (tag : Fin numTags)
    (outer : FullTM0.Tape (Symbol numTags)) :
    logicalTape growth (install registers growth tag outer) 0 = tagSymbol tag := by
  rw [logicalTape_install]
  exact logicalOverlay_zero registers tag (logicalTape growth outer)

@[simp] theorem install_core {numTags : Nat} (registers : Registers)
    (growth : Turing.Dir) (tag : Fin numTags)
    (outer : FullTM0.Tape (Symbol numTags)) (position : Nat)
    (hposition : position ≤ RegisterLayout.clockBoundary registers) :
    logicalTape growth (install registers growth tag outer) (position + 1) =
      coreSymbol registers position := by
  rw [logicalTape_install]
  exact logicalOverlay_core registers tag (logicalTape growth outer) position hposition

/-- Pointwise physical preservation beyond the finite initialized core. -/
theorem install_of_layoutEnd_lt {numTags : Nat} (registers : Registers)
    (growth : Turing.Dir) (tag : Fin numTags)
    (outer : FullTM0.Tape (Symbol numTags)) {position : Nat}
    (hposition : layoutEnd registers < position) :
    install registers growth tag outer (physicalCoord growth position) =
      outer (physicalCoord growth position) := by
  rw [← logicalTape_apply growth (install registers growth tag outer) position]
  rw [← logicalTape_apply growth outer position]
  rw [logicalTape_install]
  exact logicalOverlay_of_layoutEnd_lt registers tag (logicalTape growth outer)
    (by exact_mod_cast hposition)

/-- The operational initializer's intended tape, still centered on its newly
relocated tag. -/
noncomputable def initializeTape {numTags : Nat} (c : Nat.Partrec.Code)
    (command : Command numTags) (outer : FullTM0.Tape (Symbol numTags)) :
    FullTM0.Tape (Symbol numTags) :=
  install (CanonicalInitializer.registers c) command.searchDirection
    command.returnTag outer

@[simp] theorem initializeTape_read_tag {numTags : Nat} (c : Nat.Partrec.Code)
    (command : Command numTags) (outer : FullTM0.Tape (Symbol numTags)) :
    (initializeTape c command outer).read = tagSymbol command.returnTag := by
  have h := install_tag (CanonicalInitializer.registers c)
    command.searchDirection command.returnTag outer
  rw [logicalTape_apply, physicalCoord_zero] at h
  simpa only [initializeTape, FullTM0.Tape.read] using h

/-- After recentering on canonical position `position + 1`, the initialized
tape reads its exact native core symbol. -/
theorem initializeTape_core_read {numTags : Nat} (c : Nat.Partrec.Code)
    (command : Command numTags) (outer : FullTM0.Tape (Symbol numTags))
    (position : Nat)
    (hposition : position ≤ RegisterLayout.clockBoundary
      (CanonicalInitializer.registers c)) :
    (atLogical command.searchDirection (initializeTape c command outer)
      (position + 1)).read =
        coreSymbol (CanonicalInitializer.registers c) position := by
  rw [atLogical_read]
  simpa only [initializeTape, Nat.cast_add, Nat.cast_one] using install_core
    (CanonicalInitializer.registers c) command.searchDirection
      command.returnTag outer position hposition

/-- A tagged finite frame inside an otherwise arbitrary full tape. -/
structure Represents {numTags : Nat} (spec : Spec numTags)
    (T : FullTM0.Tape (Symbol numTags)) : Prop where
  tag : logicalTape spec.growth T 0 = tagSymbol spec.returnTag
  core : ∀ position ≤ RegisterLayout.clockBoundary spec.registers,
    logicalTape spec.growth T (position + 1) =
      coreSymbol spec.registers position
  runway : ∀ position, layoutEnd spec.registers < position →
    position < spec.outerDistance →
      logicalTape spec.growth T position = blankSymbol
  target : spec.outerTarget.Matches
    (logicalTape spec.growth T spec.outerDistance)

namespace Represents

variable {numTags : Nat} {spec : Spec numTags}
variable {T U : FullTM0.Tape (Symbol numTags)}

/-- Physical-coordinate form of the return-tag invariant. -/
theorem tagAt (h : Represents spec T) :
    T 0 = tagSymbol spec.returnTag := by
  simpa only [logicalTape_apply, physicalCoord_zero] using h.tag

/-- The frame is centered on its physical return tag. -/
theorem read_tag (h : Represents spec T) :
    T.read = tagSymbol spec.returnTag := by
  simpa [FullTM0.Tape.read] using h.tagAt

/-- Read one labelled canonical boundary in logical coordinates. -/
theorem boundary (h : Represents spec T) (label : Fin 5) :
    logicalTape spec.growth T (boundaryOffset spec.registers label) =
      boundarySymbol label := by
  have hlabel : (label : Nat) ≤ 4 := by omega
  have hposition :
      CounterLayout.boundaryPos (RegisterLayout.values spec.registers) label ≤
        RegisterLayout.clockBoundary spec.registers := by
    exact CounterLayout.boundaryPos_mono _ hlabel
  simpa [boundaryOffset] using
    (h.core
      (CounterLayout.boundaryPos (RegisterLayout.values spec.registers) label)
      hposition)

/-- Physical-coordinate form of `boundary`. -/
theorem boundaryAt (h : Represents spec T) (label : Fin 5) :
    T (physicalCoord spec.growth (boundaryOffset spec.registers label)) =
      boundarySymbol label := by
  simpa using h.boundary label

/-- Boundary `4` is the far anchor of the canonical nested core. -/
theorem boundary_four (h : Represents spec T) :
    logicalTape spec.growth T (layoutEnd spec.registers) = boundarySymbol 4 := by
  simpa using h.boundary (4 : Fin 5)

/-- Recentered/read form of the boundary-`4` anchor. -/
theorem read_boundary_four (h : Represents spec T) :
    (atLogical spec.growth T (layoutEnd spec.registers)).read =
      boundarySymbol 4 := by
  rw [atLogical_read]
  exact h.boundary_four

/-- Every genuine interior cell of an adjacent register gap is blank. -/
theorem gap_blank (h : Represents spec T) (i : Fin 4) (k : Nat)
    (hk : k < RegisterLayout.values spec.registers i) :
    logicalTape spec.growth T (firstGapOffset spec.registers i + k) =
      blankSymbol := by
  let position :=
    CounterLayout.boundaryPos (RegisterLayout.values spec.registers) i + 1 + k
  have hi : (i : Nat) + 1 ≤ 4 := by omega
  have hnext :
      CounterLayout.boundaryPos (RegisterLayout.values spec.registers) (i + 1) ≤
        RegisterLayout.clockBoundary spec.registers :=
    CounterLayout.boundaryPos_mono _ hi
  have hlt := CounterLayout.firstGapCell_add_lt_boundary
    (RegisterLayout.values spec.registers) i k hk
  have hposition : position ≤ RegisterLayout.clockBoundary spec.registers :=
    le_trans (Nat.le_of_lt hlt) hnext
  have hcore := h.core position hposition
  rw [coreSymbol_gapInterior spec.registers i k hk] at hcore
  have hcoordinate : firstGapOffset spec.registers i + k = position + 1 := by
    simp only [firstGapOffset, position]
    omega
  have hcoordinate' :
      (firstGapOffset spec.registers i : Int) + k = (position : Int) + 1 := by
    exact_mod_cast hcoordinate
  rw [hcoordinate']
  exact hcore

/-- Read a runway cell in physical coordinates. -/
theorem runwayAt (h : Represents spec T) {position : Nat}
    (hcore : layoutEnd spec.registers < position)
    (htarget : position < spec.outerDistance) :
    T (physicalCoord spec.growth position) = blankSymbol := by
  simpa using h.runway position hcore htarget

/-- Read the fixed outer target at its physical coordinate. -/
theorem targetAt (h : Represents spec T) :
    spec.outerTarget.Matches
      (T (physicalCoord spec.growth spec.outerDistance)) := by
  simpa using h.target

/-- Installing the canonical overlay in a genuine far search gap produces
the complete finite-frame invariant.  The original target and every runway
blank come directly from the suspended outer search; cells beyond that finite
interval remain arbitrary and untouched. -/
theorem initializeTape_represents {numTags : Nat} (c : Nat.Partrec.Code)
    (command : Command numTags) (outer : FullTM0.Tape (Symbol numTags))
    (distance : Nat)
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      command.target.Matches outer command.searchDirection distance)
    (hfar : NestingMachine.bound (CanonicalInitializer.radius c) < distance) :
    Represents (frameSpec c command distance hfar)
      (initializeTape c command outer) := by
  constructor
  · simpa [frameSpec, initializeTape] using install_tag
      (CanonicalInitializer.registers c) command.searchDirection
        command.returnTag outer
  · intro position hposition
    simpa [frameSpec, initializeTape] using install_core
      (CanonicalInitializer.registers c) command.searchDirection
        command.returnTag outer position hposition
  · intro position hcore htarget
    change layoutEnd (CanonicalInitializer.registers c) < position at hcore
    change position < distance at htarget
    change logicalTape command.searchDirection
        (initializeTape c command outer) position = blankSymbol
    rw [show logicalTape command.searchDirection
        (initializeTape c command outer) =
          logicalOverlay (CanonicalInitializer.registers c)
            command.returnTag
            (logicalTape command.searchDirection outer) by
      simp [initializeTape]]
    rw [logicalOverlay_of_layoutEnd_lt
      (CanonicalInitializer.registers c) command.returnTag
      (logicalTape command.searchDirection outer) (by exact_mod_cast hcore)]
    simpa only [logicalTape_apply, physicalCoord_nat] using hgap.blank htarget
  · change command.target.Matches
      (logicalTape command.searchDirection
        (initializeTape c command outer) distance)
    rw [show logicalTape command.searchDirection
        (initializeTape c command outer) =
          logicalOverlay (CanonicalInitializer.registers c)
            command.returnTag
            (logicalTape command.searchDirection outer) by
      simp [initializeTape]]
    have hend : layoutEnd (CanonicalInitializer.registers c) < distance :=
      (frameSpec c command distance hfar).core_before_target
    rw [logicalOverlay_of_layoutEnd_lt
      (CanonicalInitializer.registers c) command.returnTag
      (logicalTape command.searchDirection outer) (by exact_mod_cast hend)]
    simpa only [logicalTape_apply, physicalCoord_nat] using hgap.marked

/-! ## Native adjacent searches -/

/-- Starting on the return tag is a distance-zero search for an arbitrary
physical tag, independently of the chosen direction. -/
theorem searchGap_tag (h : Represents spec T) (direction : Turing.Dir) :
    SearchGap (fun symbol => symbol = blankSymbol)
      (Target.anyTag : Target numTags).Matches T direction 0 := by
  rw [SearchGap.zero]
  exact ⟨spec.returnTag, h.tagAt⟩

/-- Boundary `0` begins the core one physical growth step after the tag. -/
theorem searchGap_boundary_zero (h : Represents spec T) :
    SearchGap (fun symbol => symbol = blankSymbol)
      (fun symbol => symbol = boundarySymbol 0)
      (atLogical spec.growth T 1) spec.growth 0 := by
  rw [SearchGap.zero]
  change (atLogical spec.growth T 1).read = boundarySymbol 0
  rw [atLogical_read]
  simpa using h.boundary (0 : Fin 5)

/-- Search from the first cell of gap `i` to its right boundary.  The theorem
is native to the tagged alphabet and its physical direction is the selected
growth orientation. -/
theorem searchGap_adjacent_right (h : Represents spec T) (i : Fin 4) :
    SearchGap (fun symbol => symbol = blankSymbol)
      (fun symbol => symbol = boundarySymbol i.succ)
      (atLogical spec.growth T (firstGapOffset spec.registers i))
      (OrientedMarkerTape.orientDirection spec.growth .right)
      (RegisterLayout.values spec.registers i) := by
  constructor
  · intro k hk
    rw [atLogical_apply_offset]
    have hblank := h.gap_blank i k hk
    simpa [firstGapOffset, FullTM0.Tape.offset_right,
      Nat.cast_add] using hblank
  · rw [atLogical_apply_offset]
    have hboundary := h.boundary i.succ
    have hposition :
        firstGapOffset spec.registers i +
            RegisterLayout.values spec.registers i =
          boundaryOffset spec.registers i.succ := by
      change CounterLayout.boundaryPos
          (RegisterLayout.values spec.registers) i + 2 +
          RegisterLayout.values spec.registers i =
        CounterLayout.boundaryPos
          (RegisterLayout.values spec.registers) ((i : Nat) + 1) + 1
      rw [CounterLayout.boundaryPos_succ]
      omega
    have hposition' :
        (firstGapOffset spec.registers i : Int) +
            FullTM0.Tape.offset .right
              (RegisterLayout.values spec.registers i) =
          boundaryOffset spec.registers i.succ := by
      rw [FullTM0.Tape.offset_right]
      exact_mod_cast hposition
    rw [hposition']
    exact hboundary

/-- Search from the last cell of gap `i` back to its left boundary.  Reflection
turns this logical left move into the correct physical direction for either
orientation. -/
theorem searchGap_adjacent_left (h : Represents spec T) (i : Fin 4) :
    SearchGap (fun symbol => symbol = blankSymbol)
      (fun symbol => symbol = boundarySymbol i.castSucc)
      (atLogical spec.growth T (lastGapOffset spec.registers i))
      (OrientedMarkerTape.orientDirection spec.growth .left)
      (RegisterLayout.values spec.registers i) := by
  constructor
  · intro k hk
    rw [atLogical_apply_offset]
    let remainder := RegisterLayout.values spec.registers i - 1 - k
    have hremainder : remainder < RegisterLayout.values spec.registers i := by
      dsimp [remainder]
      omega
    have hblank := h.gap_blank i remainder hremainder
    have hnext := CounterLayout.boundaryPos_succ
      (RegisterLayout.values spec.registers) i
    have hposition :
        (lastGapOffset spec.registers i : Int) +
            FullTM0.Tape.offset .left k =
          (firstGapOffset spec.registers i + remainder : Nat) := by
      simp only [lastGapOffset, firstGapOffset,
        FullTM0.Tape.offset_left]
      rw [hnext]
      dsimp [remainder]
      omega
    rw [hposition]
    exact hblank
  · rw [atLogical_apply_offset]
    have hboundary := h.boundary i.castSucc
    have hnext := CounterLayout.boundaryPos_succ
      (RegisterLayout.values spec.registers) i
    have hposition :
        (lastGapOffset spec.registers i : Int) +
            FullTM0.Tape.offset .left
              (RegisterLayout.values spec.registers i) =
          boundaryOffset spec.registers i.castSucc := by
      simp only [lastGapOffset, boundaryOffset,
        FullTM0.Tape.offset_left, Fin.val_castSucc]
      push_cast
      rw [hnext]
      push_cast
      omega
    rw [hposition]
    exact hboundary

/-- First logical cell after the boundary-`4` anchor. -/
def runwayStart (spec : Spec numTags) : Nat :=
  layoutEnd spec.registers + 1

/-- Number of blank runway cells before the outer target. -/
def runwayDistance (spec : Spec numTags) : Nat :=
  spec.outerDistance - runwayStart spec

theorem runwayStart_le_outerDistance (spec : Spec numTags) :
    runwayStart spec ≤ spec.outerDistance := by
  have hcore := spec.core_before_target
  simp only [runwayStart]
  omega

/-- The entire blank runway is one native search gap from immediately after
boundary `4` to the fixed suspended outer target. -/
theorem searchGap_runway (h : Represents spec T) :
    SearchGap (fun symbol => symbol = blankSymbol) spec.outerTarget.Matches
      (atLogical spec.growth T (runwayStart spec))
      (OrientedMarkerTape.orientDirection spec.growth .right)
      (runwayDistance spec) := by
  constructor
  · intro k hk
    rw [atLogical_apply_offset]
    have hstart : layoutEnd spec.registers < runwayStart spec + k := by
      exact lt_of_lt_of_le (Nat.lt_succ_self _)
        (Nat.le_add_right (layoutEnd spec.registers + 1) k)
    have hsum : runwayStart spec + runwayDistance spec =
        spec.outerDistance := by
      exact Nat.add_sub_of_le (runwayStart_le_outerDistance spec)
    have htarget : runwayStart spec + k < spec.outerDistance := by
      omega
    have hblank := h.runway (runwayStart spec + k) hstart htarget
    simpa [FullTM0.Tape.offset_right, Nat.cast_add] using hblank
  · rw [atLogical_apply_offset]
    have hsum : runwayStart spec + runwayDistance spec =
        spec.outerDistance := by
      exact Nat.add_sub_of_le (runwayStart_le_outerDistance spec)
    have hposition :
        (runwayStart spec : Int) +
            FullTM0.Tape.offset .right (runwayDistance spec) =
          spec.outerDistance := by
      rw [FullTM0.Tape.offset_right]
      exact_mod_cast hsum
    rw [hposition]
    exact h.target

/-! ## Pointwise uniqueness and preservation -/

/-- Agreement on exactly the finite nonnegative interval inspected by a
frame. -/
def Agree (spec : Spec numTags)
    (T U : FullTM0.Tape (Symbol numTags)) : Prop :=
  ∀ position ≤ spec.outerDistance,
    logicalTape spec.growth T position = logicalTape spec.growth U position

namespace Agree

@[refl] theorem refl (spec : Spec numTags)
    (T : FullTM0.Tape (Symbol numTags)) : Agree spec T T := by
  intro _ _
  rfl

@[symm] theorem symm {spec : Spec numTags}
    {T U : FullTM0.Tape (Symbol numTags)} (h : Agree spec T U) :
    Agree spec U T := by
  intro position hposition
  exact (h position hposition).symm

@[trans] theorem trans {spec : Spec numTags}
    {T U V : FullTM0.Tape (Symbol numTags)}
    (hTU : Agree spec T U) (hUV : Agree spec U V) : Agree spec T V := by
  intro position hposition
  exact (hTU position hposition).trans (hUV position hposition)

end Agree

/-- Changing arbitrary cells outside the finite inspected interval preserves
the frame representation. -/
theorem of_agree (h : Represents spec T) (hagree : Agree spec T U) :
    Represents spec U := by
  constructor
  · calc
      logicalTape spec.growth U 0 = logicalTape spec.growth T 0 := by
        simpa using (hagree 0 (Nat.zero_le _)).symm
      _ = tagSymbol spec.returnTag := h.tag
  · intro position hposition
    have hinterval : position + 1 ≤ spec.outerDistance := by
      have houter := spec.core_before_target
      simp only [layoutEnd] at houter
      omega
    calc
      logicalTape spec.growth U (position + 1) =
          logicalTape spec.growth T (position + 1) := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          (hagree (position + 1) hinterval).symm
      _ = coreSymbol spec.registers position := h.core position hposition
  · intro position hcore htarget
    calc
      logicalTape spec.growth U position =
          logicalTape spec.growth T position := by
        simpa using (hagree position (Nat.le_of_lt htarget)).symm
      _ = blankSymbol := h.runway position hcore htarget
  · have heq := hagree spec.outerDistance (le_refl _)
    rw [← heq]
    exact h.target

/-- Physical-coordinate version of `of_agree`. -/
theorem of_eqOn (h : Represents spec T)
    (heq : ∀ position ≤ spec.outerDistance,
      T (physicalCoord spec.growth position) =
        U (physicalCoord spec.growth position)) :
    Represents spec U := by
  apply h.of_agree
  intro position hposition
  simpa using heq position hposition

/-- Two representations of the same frame agree pointwise before the outer
target.  This includes the tag, all five boundaries, every register gap, and
the blank runway; no assumption is made about either outside tape. -/
theorem agree_before_target (hT : Represents spec T)
    (hU : Represents spec U) {position : Nat}
    (hposition : position < spec.outerDistance) :
    logicalTape spec.growth T position =
      logicalTape spec.growth U position := by
  by_cases hzero : position = 0
  · subst position
    simpa using hT.tag.trans hU.tag.symm
  · by_cases hcore : position ≤ layoutEnd spec.registers
    · obtain ⟨corePosition, rfl⟩ :=
        Nat.exists_eq_succ_of_ne_zero hzero
      have hbound :
          corePosition ≤ RegisterLayout.clockBoundary spec.registers := by
        simpa [layoutEnd] using hcore
      simpa using (hT.core corePosition hbound).trans
        (hU.core corePosition hbound).symm
    · have hpast : layoutEnd spec.registers < position :=
        Nat.lt_of_not_ge hcore
      rw [hT.runway position hpast hposition,
        hU.runway position hpast hposition]

/-- Within the canonical interval, reading boundary label `label` uniquely
determines its pointwise coordinate. -/
theorem core_eq_boundary_iff (h : Represents spec T) {position : Nat}
    (hposition : position ≤ RegisterLayout.clockBoundary spec.registers)
    (label : Fin 5) :
    logicalTape spec.growth T (position + 1) = boundarySymbol label ↔
      position = CounterLayout.boundaryPos
        (RegisterLayout.values spec.registers) label := by
  rw [h.core position hposition]
  exact coreSymbol_eq_boundary_iff spec.registers position label

/-- Boundary targets, unlike the intentionally polymorphic `anyTag` target,
also make two representations agree at the outer endpoint. -/
theorem agree_target_of_boundary (hT : Represents spec T)
    (hU : Represents spec U) {label : Fin 5}
    (htarget : spec.outerTarget = .boundary label) :
    logicalTape spec.growth T spec.outerDistance =
      logicalTape spec.growth U spec.outerDistance := by
  have hfirst := hT.target
  have hsecond := hU.target
  rw [htarget] at hfirst hsecond
  simp only [Target.Matches] at hfirst hsecond
  exact hfirst.trans hsecond.symm

end Represents

end FramedMarkerTape
end Hooper
end Kari
end LeanWang
