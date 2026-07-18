/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlCleanupSemantics

/-!
# Exact backing tapes for nested counter frames

`FramedMarkerTape.Represents` deliberately records only the finite facts
needed while a counter frame is active.  Returning from a nested frame needs
one stronger invariant: the active tape is the canonical overlay on the
original suspended-search tape.  This module records that exact backing tape
and proves that initialization and both noncolliding counter updates preserve
it.  Consequently collision cleanup restores the original tape, not merely a
new tape satisfying the same search-gap predicate.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlFrameBacking

open Turing CounterMachine
open BoundedMarkerProgram FramedMarkerTape FramedCounterGeometry

noncomputable section

/-- An active counter frame together with its exact suspended outer tape.
The search-gap field is the original bounded search which caused the frame
to be installed. -/
structure BackedBy {numTags : Nat} (spec : Spec numTags)
    (T outer : FullTM0.Tape (Symbol numTags)) : Prop where
  installed :
    T = install spec.registers spec.growth spec.returnTag outer
  searchGap :
    SearchGap (fun symbol => symbol = blankSymbol)
      spec.outerTarget.Matches outer spec.growth spec.outerDistance

namespace BackedBy

variable {numTags : Nat} {spec : Spec numTags}
variable {T outer : FullTM0.Tape (Symbol numTags)}

/-- The original suspended-search tape is blank at every logical coordinate
strictly before its target. -/
theorem outer_blank (h : BackedBy spec T outer) (position : Nat)
    (hposition : position < spec.outerDistance) :
    logicalTape spec.growth outer position = blankSymbol := by
  simpa only [logicalTape_apply, physicalCoord_nat] using
    h.searchGap.blank hposition

/-- Exact backing implies the ordinary finite-frame representation. -/
theorem represents (h : BackedBy spec T outer) : Represents spec T := by
  rw [h.installed]
  constructor
  · exact install_tag spec.registers spec.growth spec.returnTag outer
  · intro position hposition
    exact install_core spec.registers spec.growth spec.returnTag outer
      position hposition
  · intro position hcore htarget
    rw [logicalTape_install]
    rw [logicalOverlay_of_layoutEnd_lt spec.registers spec.returnTag
      (logicalTape spec.growth outer) (by exact_mod_cast hcore)]
    exact h.outer_blank position htarget
  · rw [logicalTape_install]
    rw [logicalOverlay_of_layoutEnd_lt spec.registers spec.returnTag
      (logicalTape spec.growth outer)
      (by exact_mod_cast spec.core_before_target)]
    simpa only [logicalTape_apply, physicalCoord_nat] using h.searchGap.marked

end BackedBy

/-! ## Initialization -/

/-- The canonical initializer records the precise outer tape whose failed
bounded search launched the frame. -/
theorem initializeTape_backedBy {numTags : Nat} (c : Nat.Partrec.Code)
    (command : Command numTags) (outer : FullTM0.Tape (Symbol numTags))
    (distance : Nat)
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      command.target.Matches outer command.searchDirection distance)
    (hfar : NestingMachine.bound (CanonicalInitializer.radius c) < distance) :
    BackedBy (frameSpec c command distance hfar)
      (initializeTape c command outer) outer := by
  constructor
  · rfl
  · simpa [frameSpec] using hgap

/-! ## Canonical overlays absorb an older frame -/

/-- Installing a core at least as long as an already installed core erases
all evidence of the older overlay. -/
theorem install_over_install {numTags : Nat} (old new : Registers)
    (growth : Turing.Dir) (tag : Fin numTags)
    (outer : FullTM0.Tape (Symbol numTags))
    (hle : layoutEnd old ≤ layoutEnd new) :
    install new growth tag (install old growth tag outer) =
      install new growth tag outer := by
  apply Function.Involutive.injective
    (logicalTape_involutive (numTags := numTags) growth)
  simp only [logicalTape_install]
  funext position
  unfold logicalOverlay
  by_cases hzero : position = 0
  · simp [hzero]
  · simp only [hzero, ↓reduceIte]
    by_cases hnew : 1 ≤ position ∧ position ≤ layoutEnd new
    · simp [hnew]
    · have hold : ¬(1 ≤ position ∧ position ≤ layoutEnd old) := by
        intro hold
        exact hnew ⟨hold.1, hold.2.trans (by exact_mod_cast hle)⟩
      simp [hnew, hold]

/-- Canonical installation only observes its backing tape away from the tag
cell and the installed core interval. -/
theorem install_congr_of_uncovered {numTags : Nat} (registers : Registers)
    (growth : Turing.Dir) (tag : Fin numTags)
    (T U : FullTM0.Tape (Symbol numTags))
    (houtside : ∀ position : Int, position ≠ 0 →
      ¬(1 ≤ position ∧ position ≤ layoutEnd registers) →
        logicalTape growth T position = logicalTape growth U position) :
    install registers growth tag T = install registers growth tag U := by
  apply Function.Involutive.injective
    (logicalTape_involutive (numTags := numTags) growth)
  simp only [logicalTape_install]
  funext position
  unfold logicalOverlay
  by_cases hzero : position = 0
  · simp [hzero]
  · simp only [hzero, ↓reduceIte]
    by_cases hcore : 1 ≤ position ∧ position ≤ layoutEnd registers
    · simp [hcore]
    · rw [if_neg hcore, if_neg hcore]
      exact houtside position hzero hcore

private theorem logicalTape_writeLogical_apply {numTags : Nat}
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

/-! ## Preservation by counter updates -/

/-- A noncolliding increment preserves the exact original backing tape. -/
theorem incrementTape_backedBy {numTags : Nat} {spec : Spec numTags}
    {T outer : FullTM0.Tape (Symbol numTags)}
    (h : BackedBy spec T outer) (register : Register)
    (hroom : layoutEnd (spec.registers.increment register) <
      spec.outerDistance) :
    BackedBy (incrementSpec spec register hroom)
      (incrementTape spec register T) outer := by
  constructor
  · rw [h.installed]
    exact install_over_install spec.registers
      (spec.registers.increment register) spec.growth spec.returnTag outer
      (by rw [layoutEnd_increment]; omega)
  · simpa [incrementSpec, updateSpec] using h.searchGap

private theorem install_after_decrement_clear {numTags : Nat}
    {spec : Spec numTags} {T outer : FullTM0.Tape (Symbol numTags)}
    (h : BackedBy spec T outer) (register : Register)
    (hpositive : 0 < spec.registers.get register) :
    install (spec.registers.decrement register) spec.growth spec.returnTag
        (clearOldLayoutEnd spec T) =
      install (spec.registers.decrement register) spec.growth spec.returnTag
        outer := by
  apply install_congr_of_uncovered
  intro position hzero houtside
  change logicalTape spec.growth
    (writeLogical spec.growth T (layoutEnd spec.registers) blankSymbol)
      position = logicalTape spec.growth outer position
  rw [logicalTape_writeLogical_apply]
  by_cases hsource : position = layoutEnd spec.registers
  · rw [if_pos hsource]
    subst position
    symm
    exact h.outer_blank (layoutEnd spec.registers) spec.core_before_target
  · rw [if_neg hsource]
    rw [h.installed, logicalTape_install]
    unfold logicalOverlay
    rw [if_neg hzero]
    have hold : ¬(1 ≤ position ∧
        position ≤ layoutEnd spec.registers) := by
      intro hold
      have hnewEnd := layoutEnd_decrement_add_one spec.registers register
        hpositive
      have hnotNew : ¬(1 ≤ position ∧ position ≤
          layoutEnd (spec.registers.decrement register)) := houtside
      have heq : position = layoutEnd spec.registers := by
        have hnewEndInt :
            (layoutEnd (spec.registers.decrement register) : Int) + 1 =
              layoutEnd spec.registers := by
          exact_mod_cast hnewEnd
        omega
      exact hsource heq
    rw [if_neg hold]

/-- A positive decrement preserves the exact original backing tape.  The
cleared old far boundary is restored to the blank supplied by the suspended
search gap. -/
theorem decrementTape_backedBy {numTags : Nat} {spec : Spec numTags}
    {T outer : FullTM0.Tape (Symbol numTags)}
    (h : BackedBy spec T outer) (register : Register)
    (hpositive : 0 < spec.registers.get register) :
    BackedBy (decrementSpec spec register hpositive)
      (decrementTape spec register T) outer := by
  constructor
  · exact install_after_decrement_clear h register hpositive
  · simpa [decrementSpec, updateSpec] using h.searchGap

/-! ## Exact collision cleanup -/

/-- Erasing an exactly backed frame restores the original suspended-search
tape extensionally. -/
theorem cleanupTape_eq_outer {numTags : Nat} {spec : Spec numTags}
    {T outer : FullTM0.Tape (Symbol numTags)}
    (h : BackedBy spec T outer) :
    cleanupTape spec T = outer := by
  apply Function.Involutive.injective
    (logicalTape_involutive (numTags := numTags) spec.growth)
  rw [logicalTape_cleanupTape]
  funext position
  unfold clearLogicalPrefix
  by_cases hprefix : 0 ≤ position ∧ position ≤ layoutEnd spec.registers
  · rw [if_pos hprefix]
    obtain ⟨coordinate, rfl⟩ := Int.eq_ofNat_of_zero_le hprefix.1
    exact (h.outer_blank coordinate
      (lt_of_le_of_lt (by exact_mod_cast hprefix.2)
        spec.core_before_target)).symm
  · rw [if_neg hprefix, h.installed, logicalTape_install]
    unfold logicalOverlay
    by_cases hzero : position = 0
    · exact False.elim (hprefix ⟨by omega, by simp [hzero]⟩)
    · rw [if_neg hzero]
      have hcore : ¬(1 ≤ position ∧
          position ≤ layoutEnd spec.registers) := by
        intro hcore
        exact hprefix ⟨by omega, hcore.2⟩
      rw [if_neg hcore]

/-- The concrete five-boundary cleanup chain restores the original outer
tape exactly. -/
theorem afterTag_eq_outer {numTags : Nat} {spec : Spec numTags}
    {T outer : FullTM0.Tape (Symbol numTags)}
    (h : BackedBy spec T outer) :
    CounterControlCleanupSemantics.afterTag spec T = outer := by
  rw [CounterControlCleanupSemantics.afterTag_eq_cleanupTape h.represents]
  exact cleanupTape_eq_outer h

end

end CounterControlFrameBacking
end Hooper
end Kari
end LeanWang
