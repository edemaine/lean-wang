/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlFrameBacking
import LeanWang.Kari.Hooper.CounterControlCoreFrame

/-!
# Counter frames with an infinite blank runway

The designated top-level counter configuration has no suspended outer search
and therefore no outer target.  Its five-boundary core is followed by blanks
forever.  `OpenRepresents` is the target-free analogue of
`FramedMarkerTape.Represents` for that configuration.

The local boundary and adjacent-gap API below mirrors precisely the finite
frame facts used by collision-free counter instructions.  Existing compiled
instruction theorems still quantify over `FramedMarkerTape.Represents`; to
apply them directly to an open frame, their common tag/core/local-runway
hypotheses must be factored out from the finite outer-target field.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlOpenFrame

open Turing CounterMachine
open BoundedMarkerProgram FramedMarkerTape FramedCounterGeometry
open CounterControlCoreFrame

noncomputable section

/-! ## Open frames and their canonical tape -/

/-- The unrestricted all-blank full tape. -/
def blankTape (numTags : Nat) : FullTM0.Tape (Symbol numTags) :=
  fun _ => blankSymbol

@[simp] theorem blankTape_apply (numTags : Nat) (position : Int) :
    blankTape numTags position = blankSymbol := rfl

/-- Canonical open tape: install a tagged counter core over the all-blank
backing tape. -/
def openTape {numTags : Nat} (registers : Registers)
    (growth : Turing.Dir) (returnTag : Fin numTags) :
    FullTM0.Tape (Symbol numTags) :=
  install registers growth returnTag (blankTape numTags)

/-- A tagged canonical counter core followed by an infinite blank runway. -/
structure OpenRepresents {numTags : Nat} (registers : Registers)
    (growth : Turing.Dir) (returnTag : Fin numTags)
    (T : FullTM0.Tape (Symbol numTags)) : Prop where
  tag : logicalTape growth T 0 = tagSymbol returnTag
  core : ∀ position ≤ RegisterLayout.clockBoundary registers,
    logicalTape growth T (position + 1) = coreSymbol registers position
  runway : ∀ position, layoutEnd registers < position →
    logicalTape growth T position = blankSymbol

namespace OpenRepresents

variable {numTags : Nat} {registers : Registers}
variable {growth : Turing.Dir} {returnTag : Fin numTags}
variable {T : FullTM0.Tape (Symbol numTags)}

/-- The canonical installation over the blank tape is an open frame. -/
theorem openTape_represents (registers : Registers) (growth : Turing.Dir)
    (returnTag : Fin numTags) :
    OpenRepresents registers growth returnTag
      (openTape registers growth returnTag) := by
  constructor
  · exact install_tag registers growth returnTag (blankTape numTags)
  · intro position hposition
    exact install_core registers growth returnTag (blankTape numTags)
      position hposition
  · intro position hpast
    rw [show logicalTape growth (openTape registers growth returnTag)
        position = logicalTape growth (blankTape numTags) position by
      simpa [openTape] using install_of_layoutEnd_lt registers growth
        returnTag (blankTape numTags) hpast]
    simp [logicalTape_apply]

/-- Forget the infinite runway while retaining the shared tagged-core API. -/
theorem toTaggedCoreRepresents
    (h : OpenRepresents registers growth returnTag T) :
    TaggedCoreRepresents registers growth returnTag T where
  toCoreRepresents := ⟨h.core⟩
  tag := h.tag

/-- An infinite blank runway supplies a target-free prefix representation at
every chosen finite limit beyond the current core. -/
theorem prefixRepresents
    (h : OpenRepresents registers growth returnTag T)
    {limit : Nat} (hlimit : layoutEnd registers < limit) :
    PrefixRepresents registers growth returnTag limit T where
  toTaggedCoreRepresents := h.toTaggedCoreRepresents
  core_before_limit := hlimit
  runway := fun position hcore _ => h.runway position hcore

/-! ## The complete target-free local geometry API -/

theorem tagAt (h : OpenRepresents registers growth returnTag T) :
    T 0 = tagSymbol returnTag :=
  h.toTaggedCoreRepresents.tagAt

theorem read_tag (h : OpenRepresents registers growth returnTag T) :
    T.read = tagSymbol returnTag :=
  h.toTaggedCoreRepresents.read_tag

theorem boundary (h : OpenRepresents registers growth returnTag T)
    (label : Fin 5) :
    logicalTape growth T (boundaryOffset registers label) =
      boundarySymbol label :=
  h.toTaggedCoreRepresents.toCoreRepresents.boundary label

theorem boundaryAt (h : OpenRepresents registers growth returnTag T)
    (label : Fin 5) :
    T (physicalCoord growth (boundaryOffset registers label)) =
      boundarySymbol label :=
  h.toTaggedCoreRepresents.toCoreRepresents.boundaryAt label

theorem boundary_four (h : OpenRepresents registers growth returnTag T) :
    logicalTape growth T (layoutEnd registers) = boundarySymbol 4 :=
  h.toTaggedCoreRepresents.toCoreRepresents.boundary_four

theorem read_boundary_four
    (h : OpenRepresents registers growth returnTag T) :
    (atLogical growth T (layoutEnd registers)).read = boundarySymbol 4 :=
  h.toTaggedCoreRepresents.toCoreRepresents.read_boundary_four

theorem gap_blank (h : OpenRepresents registers growth returnTag T)
    (i : Fin 4) (k : Nat) (hk : k < RegisterLayout.values registers i) :
    logicalTape growth T (firstGapOffset registers i + k) = blankSymbol :=
  h.toTaggedCoreRepresents.toCoreRepresents.gap_blank i k hk

theorem runwayAt (h : OpenRepresents registers growth returnTag T)
    {position : Nat} (hpast : layoutEnd registers < position) :
    T (physicalCoord growth position) = blankSymbol := by
  simpa using h.runway position hpast

theorem searchGap_tag (h : OpenRepresents registers growth returnTag T)
    (direction : Turing.Dir) :
    SearchGap (fun symbol => symbol = blankSymbol)
      (Target.anyTag : Target numTags).Matches T direction 0 :=
  h.toTaggedCoreRepresents.searchGap_tag direction

theorem searchGap_boundary_zero
    (h : OpenRepresents registers growth returnTag T) :
    SearchGap (fun symbol => symbol = blankSymbol)
      (fun symbol => symbol = boundarySymbol 0)
      (atLogical growth T 1) growth 0 :=
  h.toTaggedCoreRepresents.toCoreRepresents.searchGap_boundary_zero

theorem searchGap_adjacent_right
    (h : OpenRepresents registers growth returnTag T) (i : Fin 4) :
    SearchGap (fun symbol => symbol = blankSymbol)
      (fun symbol => symbol = boundarySymbol i.succ)
      (atLogical growth T (firstGapOffset registers i))
      (OrientedMarkerTape.orientDirection growth .right)
      (RegisterLayout.values registers i) :=
  h.toTaggedCoreRepresents.toCoreRepresents.searchGap_adjacent_right i

theorem searchGap_adjacent_left
    (h : OpenRepresents registers growth returnTag T) (i : Fin 4) :
    SearchGap (fun symbol => symbol = blankSymbol)
      (fun symbol => symbol = boundarySymbol i.castSucc)
      (atLogical growth T (lastGapOffset registers i))
      (OrientedMarkerTape.orientDirection growth .left)
      (RegisterLayout.values registers i) :=
  h.toTaggedCoreRepresents.toCoreRepresents.searchGap_adjacent_left i

/-! ## Exact extensional counter updates -/

/-- The exact increment endpoint has another open frame.  No finite room
hypothesis is needed because the runway is infinite. -/
theorem incrementTape_preserves {spec : Spec numTags}
    {T : FullTM0.Tape (Symbol numTags)}
    (h : OpenRepresents spec.registers spec.growth spec.returnTag T)
    (register : Register) :
    OpenRepresents (spec.registers.increment register) spec.growth
      spec.returnTag (incrementTape spec register T) := by
  constructor
  · exact incrementTape_tag spec register T
  · intro position hposition
    simpa [incrementTape] using install_core
      (spec.registers.increment register) spec.growth spec.returnTag T
      position hposition
  · intro position hpast
    rw [incrementTape_of_layoutEnd_lt spec register T hpast]
    apply h.runway position
    rw [layoutEnd_increment] at hpast
    omega

/-- The exact positive-decrement endpoint has another open frame; clearing
the old far boundary supplies the first new runway blank. -/
theorem decrementTape_preserves {spec : Spec numTags}
    {T : FullTM0.Tape (Symbol numTags)}
    (h : OpenRepresents spec.registers spec.growth spec.returnTag T)
    (register : Register) (hpositive : 0 < spec.registers.get register) :
    OpenRepresents (spec.registers.decrement register) spec.growth
      spec.returnTag (decrementTape spec register T) := by
  constructor
  · exact decrementTape_tag spec register T
  · intro position hposition
    simpa [decrementTape] using install_core
      (spec.registers.decrement register) spec.growth spec.returnTag
      (clearOldLayoutEnd spec T) position hposition
  · intro position hpast
    rw [show logicalTape spec.growth (decrementTape spec register T) position =
        logicalTape spec.growth (clearOldLayoutEnd spec T) position by
      simpa [decrementTape] using install_of_layoutEnd_lt
        (spec.registers.decrement register) spec.growth spec.returnTag
        (clearOldLayoutEnd spec T) hpast]
    by_cases hvacated : position = layoutEnd spec.registers
    · subst position
      exact writeLogical_at spec.growth T (layoutEnd spec.registers)
        blankSymbol
    · rw [show logicalTape spec.growth (clearOldLayoutEnd spec T) position =
          logicalTape spec.growth T position by
        simpa [clearOldLayoutEnd] using writeLogical_of_ne spec.growth T
          (layoutEnd spec.registers) position blankSymbol hvacated]
      apply h.runway position
      have hend := layoutEnd_decrement_add_one spec.registers register
        hpositive
      omega

/-! ## Canonical update equations -/

/-- Incrementing a canonical open tape yields exactly the canonical open tape
for the incremented registers. -/
theorem incrementTape_openTape (spec : Spec numTags) (register : Register) :
    incrementTape spec register
        (openTape spec.registers spec.growth spec.returnTag) =
      openTape (spec.registers.increment register) spec.growth
        spec.returnTag := by
  unfold incrementTape openTape
  exact CounterControlFrameBacking.install_over_install spec.registers
    (spec.registers.increment register) spec.growth spec.returnTag
    (blankTape numTags) (by rw [layoutEnd_increment]; omega)

private theorem logicalTape_writeLogical_apply
    (growth : Turing.Dir) (T : FullTM0.Tape (Symbol numTags))
    (source : Nat) (written : Symbol numTags) (position : Int) :
    logicalTape growth (writeLogical growth T source written) position =
      if position = source then written else logicalTape growth T position := by
  rw [logicalTape_apply, writeLogical]
  by_cases hposition : position = source
  · subst position
    simp
  · rw [Function.update_of_ne]
    · simp [hposition]
    · intro hphysical
      apply hposition
      exact physicalCoord_injective growth hphysical

/-- Positive-decrementing a canonical open tape likewise yields exactly the
canonical open tape for the decremented registers. -/
theorem decrementTape_openTape (spec : Spec numTags) (register : Register)
    (hpositive : 0 < spec.registers.get register) :
    decrementTape spec register
        (openTape spec.registers spec.growth spec.returnTag) =
      openTape (spec.registers.decrement register) spec.growth
        spec.returnTag := by
  unfold decrementTape openTape
  apply CounterControlFrameBacking.install_congr_of_uncovered
  intro position hzero houtside
  change logicalTape spec.growth
    (writeLogical spec.growth
      (install spec.registers spec.growth spec.returnTag (blankTape numTags))
      (layoutEnd spec.registers) blankSymbol) position =
    logicalTape spec.growth (blankTape numTags) position
  rw [logicalTape_writeLogical_apply]
  by_cases hsource : position = layoutEnd spec.registers
  · rw [if_pos hsource]
    simp [logicalTape_apply]
  · rw [if_neg hsource, logicalTape_install]
    unfold logicalOverlay
    rw [if_neg hzero]
    have hold : ¬(1 ≤ position ∧ position ≤ layoutEnd spec.registers) := by
      intro hold
      have hend := layoutEnd_decrement_add_one spec.registers register
        hpositive
      have hendInt :
          (layoutEnd (spec.registers.decrement register) : Int) + 1 =
            layoutEnd spec.registers := by
        exact_mod_cast hend
      have heq : position = layoutEnd spec.registers := by omega
      exact hsource heq
    rw [if_neg hold]

end OpenRepresents

end

end CounterControlOpenFrame
end Hooper
end Kari
end LeanWang
