/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlOpenFrame

/-!
# Tag-free open counter cores

An arbitrary entry into the shared initializer can leave the controller at a
canonical logical state without establishing the saved return tag.  The
five-boundary counter core is nevertheless meaningful by itself.  This file
records the corresponding finite-prefix and infinite-runway predicates and
the exact core-only tape overlays used to update them.

Unlike `FramedMarkerTape.install`, `installCore` deliberately preserves
logical coordinate `0`.  Thus none of the lemmas below silently manufactures
a return tag.  A tagged frame forgets to these predicates, while recovering a
tagged frame remains an explicitly separate hypothesis.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlTagFreeOpen

open Turing CounterMachine
open BoundedMarkerProgram FramedMarkerTape FramedCounterGeometry
open CounterControlCoreFrame CounterControlOpenFrame

noncomputable section

/-! ## Core-only overlays -/

/-- Overlay only the five-boundary unary core.  Coordinate `0`, negative
coordinates, and coordinates past boundary `4` are inherited from `outer`. -/
noncomputable def logicalCoreOverlay {numTags : Nat} (registers : Registers)
    (outer : FullTM0.Tape (Symbol numTags)) :
    FullTM0.Tape (Symbol numTags) :=
  fun position =>
    if 1 ≤ position ∧ position ≤ layoutEnd registers then
      coreSymbol registers (position.toNat - 1)
    else
      outer position

@[simp] theorem logicalCoreOverlay_zero {numTags : Nat}
    (registers : Registers) (outer : FullTM0.Tape (Symbol numTags)) :
    logicalCoreOverlay registers outer 0 = outer 0 := by
  simp [logicalCoreOverlay]

@[simp] theorem logicalCoreOverlay_core {numTags : Nat}
    (registers : Registers) (outer : FullTM0.Tape (Symbol numTags))
    (position : Nat)
    (hposition : position ≤ RegisterLayout.clockBoundary registers) :
    logicalCoreOverlay registers outer (position + 1) =
      coreSymbol registers position := by
  rw [logicalCoreOverlay, if_pos]
  · simp
  · constructor
    · omega
    · simp only [layoutEnd]
      exact_mod_cast Nat.add_le_add_right hposition 1

theorem logicalCoreOverlay_of_layoutEnd_lt {numTags : Nat}
    (registers : Registers) (outer : FullTM0.Tape (Symbol numTags))
    {position : Int} (hposition : (layoutEnd registers : Int) < position) :
    logicalCoreOverlay registers outer position = outer position := by
  rw [logicalCoreOverlay, if_neg (by omega)]

/-- Physically oriented installation of only the canonical counter core. -/
noncomputable def installCore {numTags : Nat} (registers : Registers)
    (growth : Turing.Dir) (outer : FullTM0.Tape (Symbol numTags)) :
    FullTM0.Tape (Symbol numTags) :=
  logicalTape growth (logicalCoreOverlay registers (logicalTape growth outer))

@[simp] theorem logicalTape_installCore {numTags : Nat}
    (registers : Registers) (growth : Turing.Dir)
    (outer : FullTM0.Tape (Symbol numTags)) :
    logicalTape growth (installCore registers growth outer) =
      logicalCoreOverlay registers (logicalTape growth outer) := by
  simp [installCore]

@[simp] theorem installCore_zero {numTags : Nat} (registers : Registers)
    (growth : Turing.Dir) (outer : FullTM0.Tape (Symbol numTags)) :
    logicalTape growth (installCore registers growth outer) 0 =
      logicalTape growth outer 0 := by
  rw [logicalTape_installCore]
  exact logicalCoreOverlay_zero registers (logicalTape growth outer)

@[simp] theorem installCore_core {numTags : Nat} (registers : Registers)
    (growth : Turing.Dir) (outer : FullTM0.Tape (Symbol numTags))
    (position : Nat)
    (hposition : position ≤ RegisterLayout.clockBoundary registers) :
    logicalTape growth (installCore registers growth outer) (position + 1) =
      coreSymbol registers position := by
  rw [logicalTape_installCore]
  exact logicalCoreOverlay_core registers (logicalTape growth outer)
    position hposition

theorem installCore_of_layoutEnd_lt {numTags : Nat} (registers : Registers)
    (growth : Turing.Dir) (outer : FullTM0.Tape (Symbol numTags))
    {position : Nat} (hposition : layoutEnd registers < position) :
    logicalTape growth (installCore registers growth outer) position =
      logicalTape growth outer position := by
  rw [logicalTape_installCore]
  exact logicalCoreOverlay_of_layoutEnd_lt registers
    (logicalTape growth outer) (by exact_mod_cast hposition)

/-! ## Tag-free representations -/

/-- An exact counter core followed by blanks up to a finite limit.  No
condition is imposed on coordinate `0` or at the limit itself. -/
structure CorePrefixRepresents {numTags : Nat} (registers : Registers)
    (growth : Turing.Dir) (limit : Nat)
    (T : FullTM0.Tape (Symbol numTags)) : Prop extends
    CoreRepresents registers growth T where
  core_before_limit : layoutEnd registers < limit
  runway : ∀ position, layoutEnd registers < position →
    position < limit → logicalTape growth T position = blankSymbol

/-- An exact counter core followed by an infinite blank runway.  Logical
coordinate `0` remains completely unconstrained. -/
structure CoreOpenRepresents {numTags : Nat} (registers : Registers)
    (growth : Turing.Dir) (T : FullTM0.Tape (Symbol numTags)) : Prop extends
    CoreRepresents registers growth T where
  runway : ∀ position, layoutEnd registers < position →
    logicalTape growth T position = blankSymbol

namespace CorePrefixRepresents

variable {numTags : Nat} {registers : Registers}
variable {growth : Turing.Dir} {limit : Nat}
variable {T : FullTM0.Tape (Symbol numTags)}

/-- Forget the tag from a target-free tagged prefix. -/
theorem ofPrefix
    {returnTag : Fin numTags}
    (h : PrefixRepresents registers growth returnTag limit T) :
    CorePrefixRepresents registers growth limit T where
  toCoreRepresents := h.toCoreRepresents
  core_before_limit := h.core_before_limit
  runway := h.runway

/-- Forget both the target and the tag from a finite framed representation. -/
theorem ofFramed {spec : Spec numTags}
    (h : FramedMarkerTape.Represents spec T) :
    CorePrefixRepresents spec.registers spec.growth spec.outerDistance T :=
  ofPrefix (CounterControlCoreFrame.PrefixRepresents.ofFramed h)

theorem runwayAt
    (h : CorePrefixRepresents registers growth limit T)
    {position : Nat} (hcore : layoutEnd registers < position)
    (hlimit : position < limit) :
    T (physicalCoord growth position) = blankSymbol := by
  simpa using h.runway position hcore hlimit

end CorePrefixRepresents

namespace CoreOpenRepresents

variable {numTags : Nat} {registers : Registers}
variable {growth : Turing.Dir}
variable {T : FullTM0.Tape (Symbol numTags)}

/-- Forget the return tag from an ordinary tagged open frame. -/
theorem ofOpen {returnTag : Fin numTags}
    (h : CounterControlOpenFrame.OpenRepresents
      registers growth returnTag T) :
    CoreOpenRepresents registers growth T where
  toCoreRepresents := ⟨h.core⟩
  runway := h.runway

/-- Every finite truncation of an open core is a tag-free prefix. -/
theorem toPrefix
    (h : CoreOpenRepresents registers growth T)
    {limit : Nat} (hlimit : layoutEnd registers < limit) :
    CorePrefixRepresents registers growth limit T where
  toCoreRepresents := h.toCoreRepresents
  core_before_limit := hlimit
  runway := by
    intro position hcore _hlimit
    exact h.runway position hcore

theorem runwayAt
    (h : CoreOpenRepresents registers growth T)
    {position : Nat} (hcore : layoutEnd registers < position) :
    T (physicalCoord growth position) = blankSymbol := by
  simpa using h.runway position hcore

theorem boundary
    (h : CoreOpenRepresents registers growth T) (label : Fin 5) :
    logicalTape growth T (boundaryOffset registers label) =
      boundarySymbol label :=
  h.toCoreRepresents.boundary label

theorem read_boundary_four
    (h : CoreOpenRepresents registers growth T) :
    (atLogical growth T (layoutEnd registers)).read = boundarySymbol 4 :=
  h.toCoreRepresents.read_boundary_four

theorem gap_blank
    (h : CoreOpenRepresents registers growth T)
    (i : Fin 4) (k : Nat) (hk : k < RegisterLayout.values registers i) :
    logicalTape growth T (firstGapOffset registers i + k) = blankSymbol :=
  h.toCoreRepresents.gap_blank i k hk

theorem searchGap_adjacent_right
    (h : CoreOpenRepresents registers growth T) (i : Fin 4) :
    SearchGap (fun symbol => symbol = blankSymbol)
      (fun symbol => symbol = boundarySymbol i.succ)
      (atLogical growth T (firstGapOffset registers i))
      (OrientedMarkerTape.orientDirection growth .right)
      (RegisterLayout.values registers i) :=
  h.toCoreRepresents.searchGap_adjacent_right i

theorem searchGap_adjacent_left
    (h : CoreOpenRepresents registers growth T) (i : Fin 4) :
    SearchGap (fun symbol => symbol = blankSymbol)
      (fun symbol => symbol = boundarySymbol i.castSucc)
      (atLogical growth T (lastGapOffset registers i))
      (OrientedMarkerTape.orientDirection growth .left)
      (RegisterLayout.values registers i) :=
  h.toCoreRepresents.searchGap_adjacent_left i

end CoreOpenRepresents

/-! ## Canonical tag-free open tapes -/

/-- The all-blank full tape, named locally so this layer does not require a
return-tag parameter. -/
def blankCoreTape (numTags : Nat) : FullTM0.Tape (Symbol numTags) :=
  fun _ => blankSymbol

@[simp] theorem blankCoreTape_apply (numTags : Nat) (position : Int) :
    blankCoreTape numTags position = blankSymbol := rfl

/-- Canonical tag-free open tape: install only the counter core over blanks. -/
noncomputable def coreOpenTape {numTags : Nat} (registers : Registers)
    (growth : Turing.Dir) : FullTM0.Tape (Symbol numTags) :=
  installCore registers growth (blankCoreTape numTags)

@[simp] theorem coreOpenTape_zero {numTags : Nat} (registers : Registers)
    (growth : Turing.Dir) :
    logicalTape growth (coreOpenTape (numTags := numTags) registers growth) 0 =
      blankSymbol := by
  rw [coreOpenTape, installCore_zero]
  simp [logicalTape_apply]

theorem coreOpenTape_represents {numTags : Nat} (registers : Registers)
    (growth : Turing.Dir) :
    CoreOpenRepresents registers growth
      (coreOpenTape (numTags := numTags) registers growth) := by
  constructor
  · constructor
    intro position hposition
    exact installCore_core registers growth (blankCoreTape numTags)
      position hposition
  · intro position hpast
    change logicalTape growth
      (installCore registers growth (blankCoreTape numTags)) position =
        blankSymbol
    rw [installCore_of_layoutEnd_lt registers growth
      (blankCoreTape numTags) hpast]
    simp [logicalTape_apply]

/-! ## Normalization and compatibility with tagged installation -/

/-- Reinstalling a core already represented by the tape is a no-op, even
though coordinate `0` is arbitrary. -/
theorem installCore_eq_self_of_coreRepresents {numTags : Nat}
    {registers : Registers} {growth : Turing.Dir}
    {T : FullTM0.Tape (Symbol numTags)}
    (h : CoreRepresents registers growth T) :
    installCore registers growth T = T := by
  have hlogical : logicalTape growth (installCore registers growth T) =
      logicalTape growth T := by
    funext position
    rw [logicalTape_installCore]
    by_cases hcore : 1 ≤ position ∧ position ≤ layoutEnd registers
    · have hnonnegative : 0 ≤ position := by omega
      obtain ⟨corePosition, rfl⟩ := Int.eq_ofNat_of_zero_le hnonnegative
      have hpositive : 0 < corePosition := by exact_mod_cast hcore.1
      obtain ⟨position, rfl⟩ :=
        Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpositive)
      have hboundNat : position + 1 ≤ layoutEnd registers := by
        exact_mod_cast hcore.2
      have hbound : position ≤ RegisterLayout.clockBoundary registers := by
        apply Nat.le_of_succ_le_succ
        simpa only [layoutEnd] using hboundNat
      rw [logicalCoreOverlay, if_pos]
      · simpa using (h.core position hbound).symm
      · constructor <;> omega
    · rw [logicalCoreOverlay, if_neg hcore]
  calc
    installCore registers growth T =
        logicalTape growth (logicalTape growth
          (installCore registers growth T)) := by
      rw [logicalTape_involutive]
    _ = logicalTape growth (logicalTape growth T) :=
      congrArg (logicalTape growth) hlogical
    _ = T := logicalTape_involutive growth T

/-- Installing a longer core absorbs a shorter core-only overlay. -/
theorem installCore_over_installCore {numTags : Nat}
    (old new : Registers) (growth : Turing.Dir)
    (outer : FullTM0.Tape (Symbol numTags))
    (hle : layoutEnd old ≤ layoutEnd new) :
    installCore new growth (installCore old growth outer) =
      installCore new growth outer := by
  apply Function.Involutive.injective (logicalTape_involutive growth)
  simp only [logicalTape_installCore]
  funext position
  unfold logicalCoreOverlay
  by_cases hnew : 1 ≤ position ∧ position ≤ layoutEnd new
  · simp [hnew]
  · have hold : ¬(1 ≤ position ∧ position ≤ layoutEnd old) := by
      intro hold
      exact hnew ⟨hold.1, hold.2.trans (by exact_mod_cast hle)⟩
    simp [hnew, hold]

/-- Core installation depends on its backing tape only outside the core
interval. -/
theorem installCore_congr_of_outside {numTags : Nat}
    (registers : Registers) (growth : Turing.Dir)
    (T U : FullTM0.Tape (Symbol numTags))
    (houtside : ∀ position : Int,
      ¬(1 ≤ position ∧ position ≤ layoutEnd registers) →
        logicalTape growth T position = logicalTape growth U position) :
    installCore registers growth T = installCore registers growth U := by
  apply Function.Involutive.injective (logicalTape_involutive growth)
  simp only [logicalTape_installCore]
  funext position
  unfold logicalCoreOverlay
  by_cases hcore : 1 ≤ position ∧ position ≤ layoutEnd registers
  · simp [hcore]
  · rw [if_neg hcore, if_neg hcore]
    exact houtside position hcore

/-- With an actual tag at coordinate `0`, tagged and core-only installation
coincide extensionally. -/
theorem install_eq_installCore_of_tag {numTags : Nat}
    (registers : Registers) (growth : Turing.Dir) (tag : Fin numTags)
    (T : FullTM0.Tape (Symbol numTags))
    (htag : logicalTape growth T 0 = tagSymbol tag) :
    install registers growth tag T = installCore registers growth T := by
  apply Function.Involutive.injective (logicalTape_involutive growth)
  funext position
  rw [logicalTape_install, logicalTape_installCore]
  by_cases hzero : position = 0
  · subst position
    rw [logicalOverlay_zero, logicalCoreOverlay_zero]
    simpa only [logicalTape_apply, physicalCoord_zero] using htag.symm
  · rw [logicalOverlay, logicalCoreOverlay, if_neg hzero]

/-! ## Explicit retagging bridge -/

/-- Write a chosen saved tag at logical coordinate `0`, leaving the core and
runway alone. -/
def retag {numTags : Nat} (growth : Turing.Dir) (tag : Fin numTags)
    (T : FullTM0.Tape (Symbol numTags)) : FullTM0.Tape (Symbol numTags) :=
  writeLogical growth T 0 (tagSymbol tag)

@[simp] theorem retag_zero {numTags : Nat} (growth : Turing.Dir)
    (tag : Fin numTags) (T : FullTM0.Tape (Symbol numTags)) :
    logicalTape growth (retag growth tag T) 0 = tagSymbol tag := by
  exact writeLogical_at growth T 0 (tagSymbol tag)

theorem retag_of_pos {numTags : Nat} (growth : Turing.Dir)
    (tag : Fin numTags) (T : FullTM0.Tape (Symbol numTags))
    (position : Nat) (hpositive : 0 < position) :
    logicalTape growth (retag growth tag T) position =
      logicalTape growth T position := by
  exact writeLogical_of_ne growth T 0 position (tagSymbol tag)
    (Nat.ne_of_gt hpositive)

/-- Retagging a tag-free open core produces an ordinary tagged open frame. -/
theorem retag_openRepresents {numTags : Nat} {registers : Registers}
    {growth : Turing.Dir} {T : FullTM0.Tape (Symbol numTags)}
    (h : CoreOpenRepresents registers growth T) (tag : Fin numTags) :
    CounterControlOpenFrame.OpenRepresents registers growth tag
      (retag growth tag T) := by
  constructor
  · exact retag_zero growth tag T
  · intro position hposition
    have hretag := retag_of_pos growth tag T (position + 1) (by omega)
    rw [show logicalTape growth (retag growth tag T) (position + 1) =
          logicalTape growth T (position + 1) by
      simpa only [Nat.cast_add, Nat.cast_one] using hretag]
    exact h.core position hposition
  · intro position hpast
    rw [retag_of_pos growth tag T position (by
      have hend : 0 < layoutEnd registers := by
        simp [layoutEnd, RegisterLayout.clockBoundary_eq]
      omega)]
    exact h.runway position hpast

/-! ## Exact tag-free updates -/

/-- Core-only increment specification.  The old coordinate `0` is retained. -/
noncomputable def incrementCoreTape {numTags : Nat} (registers : Registers)
    (growth : Turing.Dir) (register : Register)
    (T : FullTM0.Tape (Symbol numTags)) : FullTM0.Tape (Symbol numTags) :=
  installCore (registers.increment register) growth T

/-- Clear the old far boundary without changing any other logical cell. -/
def clearOldCoreEnd {numTags : Nat} (registers : Registers)
    (growth : Turing.Dir) (T : FullTM0.Tape (Symbol numTags)) :
    FullTM0.Tape (Symbol numTags) :=
  writeLogical growth T (layoutEnd registers) blankSymbol

theorem logicalTape_clearOldCoreEnd_apply {numTags : Nat}
    (registers : Registers) (growth : Turing.Dir)
    (T : FullTM0.Tape (Symbol numTags)) (position : Int) :
    logicalTape growth (clearOldCoreEnd registers growth T) position =
      if position = layoutEnd registers then blankSymbol
      else logicalTape growth T position := by
  rw [logicalTape_apply, clearOldCoreEnd, writeLogical]
  by_cases hposition : position = layoutEnd registers
  · subst position
    simp
  · rw [Function.update_of_ne]
    · simp [hposition]
    · intro hphysical
      apply hposition
      exact physicalCoord_injective growth hphysical

/-- Core-only positive-decrement specification.  The vacated old far
boundary is cleared and coordinate `0` is retained. -/
noncomputable def decrementCoreTape {numTags : Nat} (registers : Registers)
    (growth : Turing.Dir) (register : Register)
    (T : FullTM0.Tape (Symbol numTags)) : FullTM0.Tape (Symbol numTags) :=
  installCore (registers.decrement register) growth
    (clearOldCoreEnd registers growth T)

@[simp] theorem incrementCoreTape_zero {numTags : Nat}
    (registers : Registers) (growth : Turing.Dir) (register : Register)
    (T : FullTM0.Tape (Symbol numTags)) :
    logicalTape growth (incrementCoreTape registers growth register T) 0 =
      logicalTape growth T 0 := by
  simpa only [incrementCoreTape] using
    installCore_zero (registers.increment register) growth T

@[simp] theorem clearOldCoreEnd_zero {numTags : Nat}
    (registers : Registers) (growth : Turing.Dir)
    (T : FullTM0.Tape (Symbol numTags)) :
    logicalTape growth (clearOldCoreEnd registers growth T) 0 =
      logicalTape growth T 0 := by
  apply writeLogical_of_ne
  simp [layoutEnd, RegisterLayout.clockBoundary_eq]

@[simp] theorem decrementCoreTape_zero {numTags : Nat}
    (registers : Registers) (growth : Turing.Dir) (register : Register)
    (T : FullTM0.Tape (Symbol numTags)) :
    logicalTape growth (decrementCoreTape registers growth register T) 0 =
      logicalTape growth T 0 := by
  calc
    logicalTape growth (decrementCoreTape registers growth register T) 0 =
        logicalTape growth (clearOldCoreEnd registers growth T) 0 := by
      simpa only [decrementCoreTape] using
        installCore_zero (registers.decrement register) growth
          (clearOldCoreEnd registers growth T)
    _ = logicalTape growth T 0 :=
      clearOldCoreEnd_zero registers growth T

theorem incrementCoreTape_preserves_open {numTags : Nat}
    {registers : Registers} {growth : Turing.Dir}
    {T : FullTM0.Tape (Symbol numTags)}
    (h : CoreOpenRepresents registers growth T) (register : Register) :
    CoreOpenRepresents (registers.increment register) growth
      (incrementCoreTape registers growth register T) := by
  constructor
  · constructor
    intro position hposition
    exact installCore_core (registers.increment register) growth T
      position hposition
  · intro position hpast
    change logicalTape growth
      (installCore (registers.increment register) growth T) position =
        blankSymbol
    rw [installCore_of_layoutEnd_lt (registers.increment register) growth T
      hpast]
    apply h.runway position
    rw [layoutEnd_increment] at hpast
    omega

theorem decrementCoreTape_preserves_open {numTags : Nat}
    {registers : Registers} {growth : Turing.Dir}
    {T : FullTM0.Tape (Symbol numTags)}
    (h : CoreOpenRepresents registers growth T) (register : Register)
    (hpositive : 0 < registers.get register) :
    CoreOpenRepresents (registers.decrement register) growth
      (decrementCoreTape registers growth register T) := by
  constructor
  · constructor
    intro position hposition
    exact installCore_core (registers.decrement register) growth
      (clearOldCoreEnd registers growth T) position hposition
  · intro position hpast
    change logicalTape growth
      (installCore (registers.decrement register) growth
        (clearOldCoreEnd registers growth T)) position = blankSymbol
    rw [installCore_of_layoutEnd_lt (registers.decrement register) growth
      (clearOldCoreEnd registers growth T) hpast]
    by_cases hvacated : position = layoutEnd registers
    · subst position
      exact writeLogical_at growth T (layoutEnd registers) blankSymbol
    · rw [show logicalTape growth (clearOldCoreEnd registers growth T)
            position = logicalTape growth T position by
          simpa [clearOldCoreEnd] using
            writeLogical_of_ne growth T (layoutEnd registers) position
              blankSymbol hvacated]
      apply h.runway position
      have hend := layoutEnd_decrement_add_one registers register hpositive
      omega

theorem incrementCoreTape_preserves_prefix {numTags : Nat}
    {registers : Registers} {growth : Turing.Dir} {limit : Nat}
    {T : FullTM0.Tape (Symbol numTags)}
    (h : CorePrefixRepresents registers growth limit T)
    (register : Register)
    (hroom : layoutEnd (registers.increment register) < limit) :
    CorePrefixRepresents (registers.increment register) growth limit
      (incrementCoreTape registers growth register T) := by
  constructor
  · constructor
    intro position hposition
    exact installCore_core (registers.increment register) growth T
      position hposition
  · exact hroom
  · intro position hpast hlimit
    change logicalTape growth
      (installCore (registers.increment register) growth T) position =
        blankSymbol
    rw [installCore_of_layoutEnd_lt (registers.increment register) growth T
      hpast]
    apply h.runway position
    · rw [layoutEnd_increment] at hpast
      omega
    · exact hlimit

theorem decrementCoreTape_preserves_prefix {numTags : Nat}
    {registers : Registers} {growth : Turing.Dir} {limit : Nat}
    {T : FullTM0.Tape (Symbol numTags)}
    (h : CorePrefixRepresents registers growth limit T)
    (register : Register) (hpositive : 0 < registers.get register) :
    CorePrefixRepresents (registers.decrement register) growth limit
      (decrementCoreTape registers growth register T) := by
  constructor
  · constructor
    intro position hposition
    exact installCore_core (registers.decrement register) growth
      (clearOldCoreEnd registers growth T) position hposition
  · exact (layoutEnd_decrement_lt registers register hpositive).trans
      h.core_before_limit
  · intro position hpast hlimit
    change logicalTape growth
      (installCore (registers.decrement register) growth
        (clearOldCoreEnd registers growth T)) position = blankSymbol
    rw [installCore_of_layoutEnd_lt (registers.decrement register) growth
      (clearOldCoreEnd registers growth T) hpast]
    by_cases hvacated : position = layoutEnd registers
    · subst position
      exact writeLogical_at growth T (layoutEnd registers) blankSymbol
    · rw [show logicalTape growth (clearOldCoreEnd registers growth T)
            position = logicalTape growth T position by
          simpa [clearOldCoreEnd] using
            writeLogical_of_ne growth T (layoutEnd registers) position
              blankSymbol hvacated]
      apply h.runway position
      · have hend := layoutEnd_decrement_add_one registers register hpositive
        omega
      · exact hlimit

/-- Incrementing the canonical tag-free open tape gives exactly the
canonical tape for the incremented registers. -/
theorem incrementCoreTape_coreOpenTape {numTags : Nat}
    (registers : Registers) (growth : Turing.Dir) (register : Register) :
    incrementCoreTape registers growth register
        (coreOpenTape (numTags := numTags) registers growth) =
      coreOpenTape (registers.increment register) growth := by
  unfold incrementCoreTape coreOpenTape
  exact installCore_over_installCore registers
    (registers.increment register) growth (blankCoreTape numTags)
    (by rw [layoutEnd_increment]; omega)

/-- Positive-decrementing the canonical tag-free open tape likewise gives
the canonical tape for the decremented registers. -/
theorem decrementCoreTape_coreOpenTape {numTags : Nat}
    (registers : Registers) (growth : Turing.Dir) (register : Register)
    (hpositive : 0 < registers.get register) :
    decrementCoreTape registers growth register
        (coreOpenTape (numTags := numTags) registers growth) =
      coreOpenTape (registers.decrement register) growth := by
  unfold decrementCoreTape coreOpenTape
  apply installCore_congr_of_outside
  intro position houtside
  rw [logicalTape_clearOldCoreEnd_apply]
  by_cases hvacated : position = layoutEnd registers
  · rw [if_pos hvacated]
    simp [logicalTape_apply]
  · rw [if_neg hvacated, logicalTape_installCore]
    unfold logicalCoreOverlay
    have hold : ¬(1 ≤ position ∧ position ≤ layoutEnd registers) := by
      intro hold
      have hend := layoutEnd_decrement_add_one registers register hpositive
      have hendInt :
          (layoutEnd (registers.decrement register) : Int) + 1 =
            layoutEnd registers := by
        exact_mod_cast hend
      have heq : position = layoutEnd registers := by omega
      exact hvacated heq
    rw [if_neg hold]

/-- On a genuinely tagged input, the core-only increment agrees with the
existing framed increment specification. -/
theorem incrementCoreTape_eq_incrementTape_of_tag {numTags : Nat}
    (spec : Spec numTags) (register : Register)
    (T : FullTM0.Tape (Symbol numTags))
    (htag : logicalTape spec.growth T 0 = tagSymbol spec.returnTag) :
    incrementCoreTape spec.registers spec.growth register T =
      incrementTape spec register T := by
  symm
  exact install_eq_installCore_of_tag
    (spec.registers.increment register) spec.growth spec.returnTag T htag

/-- The same compatibility holds for positive decrement; clearing the old
far boundary does not disturb coordinate `0`. -/
theorem decrementCoreTape_eq_decrementTape_of_tag {numTags : Nat}
    (spec : Spec numTags) (register : Register)
    (T : FullTM0.Tape (Symbol numTags))
    (htag : logicalTape spec.growth T 0 = tagSymbol spec.returnTag) :
    decrementCoreTape spec.registers spec.growth register T =
      decrementTape spec register T := by
  symm
  apply install_eq_installCore_of_tag
  simpa [clearOldCoreEnd, clearOldLayoutEnd] using
    (show logicalTape spec.growth
        (clearOldCoreEnd spec.registers spec.growth T) 0 =
          logicalTape spec.growth T 0 from
      clearOldCoreEnd_zero spec.registers spec.growth T).trans htag

end

end CounterControlTagFreeOpen
end Hooper
end Kari
end LeanWang
