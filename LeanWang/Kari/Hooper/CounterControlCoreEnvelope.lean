/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlCoreFrame
import LeanWang.Kari.Hooper.CounterControlFrameBacking

/-!
# Exact backing reconstructed from a finite counter envelope

A tagged canonical core, a blank finite runway, and a matching symbol at its
far endpoint contain all the information required by a finite Hooper frame.
The apparent extra strength of `CounterControlFrameBacking.BackedBy` can then
be recovered canonically: erase the tag and core with `cleanupTape` and use
the resulting tape as the suspended outer tape.

The central theorem is deliberately stated first for an arbitrary
`FramedMarkerTape.Spec`.  `CoreEnvelope` is the proof-friendly constructor
which assembles such a specification from independent geometric fields.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlCoreEnvelope

open Turing CounterMachine
open BoundedMarkerProgram FramedMarkerTape FramedCounterGeometry
open CounterControlCoreFrame CounterControlFrameBacking

noncomputable section

/-! ## Cleanup is the canonical exact backing -/

/-- Installing a tagged represented core over its erased tape reconstructs
the original tape exactly.  No runway or target hypothesis is needed for
this local extensional fact. -/
theorem install_cleanupTape_eq_of_taggedCore {numTags : Nat}
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : TaggedCoreRepresents spec.registers spec.growth spec.returnTag T) :
    install spec.registers spec.growth spec.returnTag (cleanupTape spec T) =
      T := by
  apply Function.Involutive.injective
    (logicalTape_involutive (numTags := numTags) spec.growth)
  rw [logicalTape_install, logicalTape_cleanupTape]
  funext position
  by_cases hzero : position = 0
  · subst position
    simp only [logicalOverlay_zero]
    simpa only [logicalTape_apply, physicalCoord_zero] using h.tag.symm
  by_cases hcore : 1 ≤ position ∧
      position ≤ layoutEnd spec.registers
  · have hnonnegative : 0 ≤ position := by omega
    obtain ⟨corePosition, rfl⟩ := Int.eq_ofNat_of_zero_le hnonnegative
    have hpositive : 0 < corePosition := by exact_mod_cast hcore.1
    obtain ⟨position, rfl⟩ :=
      Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpositive)
    have hboundNat : position + 1 ≤ layoutEnd spec.registers := by
      exact_mod_cast hcore.2
    have hbound : position ≤
        RegisterLayout.clockBoundary spec.registers := by
      apply Nat.le_of_succ_le_succ
      simpa only [layoutEnd] using hboundNat
    rw [logicalOverlay, if_neg (by omega), if_pos]
    · simpa using (h.core position hbound).symm
    · constructor <;> omega
  · have hprefix : ¬(0 ≤ position ∧
        position ≤ layoutEnd spec.registers) := by
      intro hprefix
      apply hcore
      constructor
      · omega
      · exact hprefix.2
    rw [logicalOverlay, if_neg hzero, if_neg hcore,
      clearLogicalPrefix, if_neg hprefix]

/-- Every ordinary finite representation has an honest exact backing.  The
suspended outer tape is not guessed: it is canonically reconstructed by
erasing precisely the represented tag and core. -/
theorem backedBy_cleanupTape_of_represents {numTags : Nat}
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T) :
    BackedBy spec T (cleanupTape spec T) where
  installed := (install_cleanupTape_eq_of_taggedCore
    { toCoreRepresents := ⟨h.core⟩
      tag := h.tag }).symm
  searchGap := cleanupTape_searchGap h

/-- Any exact backing of a represented tape is forced to be the cleanup
tape.  In particular, the reconstructed suspended outer tape is unique. -/
theorem backing_eq_cleanupTape {numTags : Nat}
    {spec : Spec numTags} {T outer : FullTM0.Tape (Symbol numTags)}
    (h : BackedBy spec T outer) :
    outer = cleanupTape spec T :=
  (CounterControlFrameBacking.cleanupTape_eq_outer h).symm

/-- Ordinary finite representation is equivalent to existence of an exact
backing tape. -/
theorem exists_backing_iff_represents {numTags : Nat}
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)} :
    (∃ outer, BackedBy spec T outer) ↔ Represents spec T := by
  constructor
  · rintro ⟨outer, houter⟩
    exact houter.represents
  · intro h
    exact ⟨cleanupTape spec T, backedBy_cleanupTape_of_represents h⟩

/-- Complete characterization of exact backing: representation determines
the backing tape uniquely as `cleanupTape`. -/
theorem backedBy_iff_represents_and_eq_cleanupTape {numTags : Nat}
    {spec : Spec numTags} {T outer : FullTM0.Tape (Symbol numTags)} :
    BackedBy spec T outer ↔
      Represents spec T ∧ outer = cleanupTape spec T := by
  constructor
  · intro h
    exact ⟨h.represents, backing_eq_cleanupTape h⟩
  · rintro ⟨hrepresents, rfl⟩
    exact backedBy_cleanupTape_of_represents hrepresents

@[simp] theorem backedBy_cleanupTape_iff_represents {numTags : Nat}
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)} :
    BackedBy spec T (cleanupTape spec T) ↔ Represents spec T := by
  rw [backedBy_iff_represents_and_eq_cleanupTape]
  simp

/-- Two exact backings of the same active frame coincide extensionally. -/
theorem backing_unique {numTags : Nat}
    {spec : Spec numTags}
    {T first second : FullTM0.Tape (Symbol numTags)}
    (hfirst : BackedBy spec T first) (hsecond : BackedBy spec T second) :
    first = second := by
  rw [backing_eq_cleanupTape hfirst, backing_eq_cleanupTape hsecond]

/-! ## Independent finite-envelope data -/

/-- A tagged represented core with a blank runway ending at one matching
finite target.  This is the hypothesis shape naturally obtained by scanning
outward from a validated arbitrary entry. -/
structure CoreEnvelope {numTags : Nat} (registers : Registers)
    (growth : Turing.Dir) (returnTag : Fin numTags)
    (distance : Nat) (target : Target numTags)
    (T : FullTM0.Tape (Symbol numTags)) : Prop extends
    TaggedCoreRepresents registers growth returnTag T where
  core_before_target : layoutEnd registers < distance
  runway : ∀ position, layoutEnd registers < position →
    position < distance → logicalTape growth T position = blankSymbol
  target_matches : target.Matches (logicalTape growth T distance)

/-- Frame specification determined by the finite-envelope parameters. -/
def envelopeSpec {numTags : Nat} (registers : Registers)
    (growth : Turing.Dir) (returnTag : Fin numTags)
    (distance : Nat) (target : Target numTags)
    (hcore : layoutEnd registers < distance) : Spec numTags where
  growth := growth
  returnTag := returnTag
  registers := registers
  outerDistance := distance
  outerTarget := target
  core_before_target := hcore

@[simp] theorem envelopeSpec_growth {numTags : Nat}
    (registers : Registers) (growth : Turing.Dir) (returnTag : Fin numTags)
    (distance : Nat) (target : Target numTags)
    (hcore : layoutEnd registers < distance) :
    (envelopeSpec registers growth returnTag distance target hcore).growth =
      growth := rfl

@[simp] theorem envelopeSpec_returnTag {numTags : Nat}
    (registers : Registers) (growth : Turing.Dir) (returnTag : Fin numTags)
    (distance : Nat) (target : Target numTags)
    (hcore : layoutEnd registers < distance) :
    (envelopeSpec registers growth returnTag distance target hcore).returnTag =
      returnTag := rfl

@[simp] theorem envelopeSpec_registers {numTags : Nat}
    (registers : Registers) (growth : Turing.Dir) (returnTag : Fin numTags)
    (distance : Nat) (target : Target numTags)
    (hcore : layoutEnd registers < distance) :
    (envelopeSpec registers growth returnTag distance target hcore).registers =
      registers := rfl

@[simp] theorem envelopeSpec_outerDistance {numTags : Nat}
    (registers : Registers) (growth : Turing.Dir) (returnTag : Fin numTags)
    (distance : Nat) (target : Target numTags)
    (hcore : layoutEnd registers < distance) :
    (envelopeSpec registers growth returnTag distance target hcore).outerDistance =
      distance := rfl

@[simp] theorem envelopeSpec_outerTarget {numTags : Nat}
    (registers : Registers) (growth : Turing.Dir) (returnTag : Fin numTags)
    (distance : Nat) (target : Target numTags)
    (hcore : layoutEnd registers < distance) :
    (envelopeSpec registers growth returnTag distance target hcore).outerTarget =
      target := rfl

namespace CoreEnvelope

variable {numTags : Nat} {registers : Registers}
variable {growth : Turing.Dir} {returnTag : Fin numTags}
variable {distance : Nat} {target : Target numTags}
variable {T : FullTM0.Tape (Symbol numTags)}

/-- The exact finite-frame specification carried by an envelope. -/
def spec (h : CoreEnvelope registers growth returnTag distance target T) :
    Spec numTags :=
  envelopeSpec registers growth returnTag distance target
    h.core_before_target

@[simp] theorem spec_growth
    (h : CoreEnvelope registers growth returnTag distance target T) :
    h.spec.growth = growth := rfl

@[simp] theorem spec_returnTag
    (h : CoreEnvelope registers growth returnTag distance target T) :
    h.spec.returnTag = returnTag := rfl

@[simp] theorem spec_registers
    (h : CoreEnvelope registers growth returnTag distance target T) :
    h.spec.registers = registers := rfl

@[simp] theorem spec_outerDistance
    (h : CoreEnvelope registers growth returnTag distance target T) :
    h.spec.outerDistance = distance := rfl

@[simp] theorem spec_outerTarget
    (h : CoreEnvelope registers growth returnTag distance target T) :
    h.spec.outerTarget = target := rfl

/-- The independent envelope fields assemble into the standard finite-frame
representation without any additional assumption. -/
theorem represents
    (h : CoreEnvelope registers growth returnTag distance target T) :
    Represents h.spec T where
  tag := h.tag
  core := h.core
  runway := h.runway
  target := h.target_matches

/-- Envelope fields also give the common target-free tagged prefix API. -/
theorem prefixRepresents
    (h : CoreEnvelope registers growth returnTag distance target T) :
    PrefixRepresents registers growth returnTag distance T where
  toTaggedCoreRepresents := h.toTaggedCoreRepresents
  core_before_limit := h.core_before_target
  runway := h.runway

/-- Canonically reconstructed suspended outer tape. -/
def outer (h : CoreEnvelope registers growth returnTag distance target T) :
    FullTM0.Tape (Symbol numTags) :=
  cleanupTape h.spec T

/-- A finite envelope determines an honest exact backing frame. -/
theorem backedBy
    (h : CoreEnvelope registers growth returnTag distance target T) :
    BackedBy h.spec T h.outer :=
  backedBy_cleanupTape_of_represents h.represents

/-- Extensional installation equation exposed without unpacking
`BackedBy`. -/
theorem installed
    (h : CoreEnvelope registers growth returnTag distance target T) :
    T = install registers growth returnTag h.outer := by
  simpa using h.backedBy.installed

/-- Complete suspended search gap exposed without unpacking `BackedBy`. -/
theorem searchGap
    (h : CoreEnvelope registers growth returnTag distance target T) :
    SearchGap (fun symbol => symbol = blankSymbol) target.Matches
      h.outer growth distance := by
  simpa using h.backedBy.searchGap

@[simp] theorem cleanupTape_eq_outer
    (h : CoreEnvelope registers growth returnTag distance target T) :
    cleanupTape h.spec T = h.outer := rfl

/-- The reconstructed outer tape is blank all the way from the erased tag
cell to the finite target. -/
theorem outer_blank
    (h : CoreEnvelope registers growth returnTag distance target T)
    (position : Nat) (hposition : position < distance) :
    logicalTape growth h.outer position = blankSymbol := by
  simpa using h.backedBy.outer_blank position hposition

/-- The reconstructed outer tape retains the selected target exactly at the
finite endpoint. -/
theorem outer_target
    (h : CoreEnvelope registers growth returnTag distance target T) :
    target.Matches (logicalTape growth h.outer distance) := by
  change h.spec.outerTarget.Matches
    (logicalTape h.spec.growth h.outer h.spec.outerDistance)
  have hmarked := h.backedBy.searchGap.marked
  simpa only [logicalTape_apply, physicalCoord_nat] using hmarked

/-- A tagged target-free prefix becomes a finite envelope as soon as its
endpoint is known to match a selected target. -/
theorem ofPrefix
    (h : PrefixRepresents registers growth returnTag distance T)
    (target : Target numTags)
    (htarget : target.Matches (logicalTape growth T distance)) :
    CoreEnvelope registers growth returnTag distance target T where
  toTaggedCoreRepresents := h.toTaggedCoreRepresents
  core_before_target := h.core_before_limit
  runway := h.runway
  target_matches := htarget

end CoreEnvelope

/-! ## Direct assembly APIs -/

/-- Construct exact backing directly from a tagged core, a blank runway, and
a matching finite endpoint, without first naming `CoreEnvelope`. -/
theorem backedBy_of_taggedCore_runway_target {numTags : Nat}
    {registers : Registers} {growth : Turing.Dir}
    {returnTag : Fin numTags} {distance : Nat} {target : Target numTags}
    {T : FullTM0.Tape (Symbol numTags)}
    (hcore : TaggedCoreRepresents registers growth returnTag T)
    (hbefore : layoutEnd registers < distance)
    (hrunway : ∀ position, layoutEnd registers < position →
      position < distance → logicalTape growth T position = blankSymbol)
    (htarget : target.Matches (logicalTape growth T distance)) :
    BackedBy
      (envelopeSpec registers growth returnTag distance target hbefore) T
      (cleanupTape
        (envelopeSpec registers growth returnTag distance target hbefore) T) := by
  apply backedBy_cleanupTape_of_represents
  exact
    { tag := hcore.tag
      core := hcore.core
      runway := hrunway
      target := htarget }

/-- Prefix-specialized form of exact backing reconstruction. -/
theorem backedBy_of_prefix_target {numTags : Nat}
    {registers : Registers} {growth : Turing.Dir}
    {returnTag : Fin numTags} {distance : Nat} {target : Target numTags}
    {T : FullTM0.Tape (Symbol numTags)}
    (hprefix : PrefixRepresents registers growth returnTag distance T)
    (htarget : target.Matches (logicalTape growth T distance)) :
    BackedBy
      (envelopeSpec registers growth returnTag distance target
        hprefix.core_before_limit) T
      (cleanupTape
        (envelopeSpec registers growth returnTag distance target
          hprefix.core_before_limit) T) := by
  exact (CoreEnvelope.ofPrefix hprefix target htarget).backedBy

end

end CounterControlCoreEnvelope
end Hooper
end Kari
end LeanWang
