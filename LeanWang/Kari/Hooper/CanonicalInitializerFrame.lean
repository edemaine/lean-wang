/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CanonicalInitializerProgram
import LeanWang.Kari.Hooper.FramedMarkerTape

namespace LeanWang
namespace Kari
namespace Hooper

open Turing CounterMachine
open BoundedMarkerProgram

noncomputable section

/-!
# Framed semantics of the canonical initializer

This file identifies the tape constructed by the finite initializer program
with the abstract oriented frame used by the nested counter simulation.
-/

namespace CanonicalInitializerFrame

open CanonicalInitializerProgram

theorem logicalTape_resultTape {numTags : Nat} (c : Nat.Partrec.Code)
    (growth : Turing.Dir) (tag : Fin numTags)
    (T : FullTM0.Tape (Symbol numTags)) :
    FramedMarkerTape.logicalTape growth (resultTape c growth tag T) =
      resultTape c .right tag
        (FramedMarkerTape.logicalTape growth T) := by
  cases growth with
  | right =>
      rfl
  | left =>
      simp [resultTape, FramedMarkerTape.logicalTape,
        OrientedMarkerTape.orientTape]

@[simp] theorem initial_boundary_zero (c : Nat.Partrec.Code) :
    MarkerTape.boundaryPosition (CanonicalInitializer.registers c) 0 = 0 := by
  simp [MarkerTape.boundaryPosition]

@[simp] theorem initial_boundary_one (c : Nat.Partrec.Code) :
    MarkerTape.boundaryPosition (CanonicalInitializer.registers c) 1 = 1 := by
  simp [MarkerTape.boundaryPosition]

@[simp] theorem initial_boundary_two (c : Nat.Partrec.Code) :
    MarkerTape.boundaryPosition (CanonicalInitializer.registers c) 2 =
      inputGap c + 2 := by
  simp [MarkerTape.boundaryPosition, inputGap]
  omega

@[simp] theorem initial_boundary_three (c : Nat.Partrec.Code) :
    MarkerTape.boundaryPosition (CanonicalInitializer.registers c) 3 =
      inputGap c + 3 := by
  simp [MarkerTape.boundaryPosition, inputGap]
  omega

@[simp] theorem initial_boundary_four (c : Nat.Partrec.Code) :
    MarkerTape.boundaryPosition (CanonicalInitializer.registers c) 4 =
      inputGap c + 4 := by
  simp [MarkerTape.boundaryPosition, inputGap]
  omega

@[simp] theorem initial_boundaryNat (c : Nat.Partrec.Code) (label : Fin 5) :
    CounterLayout.boundaryPos
        (RegisterLayout.values (CanonicalInitializer.registers c)) label =
      match label with
      | ⟨0, _⟩ => 0
      | ⟨1, _⟩ => 1
      | ⟨2, _⟩ => inputGap c + 2
      | ⟨3, _⟩ => inputGap c + 3
      | ⟨4, _⟩ => inputGap c + 4 := by
  fin_cases label <;> simp [CounterLayout.boundaryPos, inputGap] <;> omega

@[simp] theorem initial_boundaryNat_two (c : Nat.Partrec.Code) :
    CounterLayout.boundaryPos
        (RegisterLayout.values (CanonicalInitializer.registers c)) 2 =
      inputGap c + 2 := by
  simp [CounterLayout.boundaryPos, inputGap]
  omega

@[simp] theorem initial_boundaryNat_three (c : Nat.Partrec.Code) :
    CounterLayout.boundaryPos
        (RegisterLayout.values (CanonicalInitializer.registers c)) 3 =
      inputGap c + 3 := by
  simp [CounterLayout.boundaryPos, inputGap]
  omega

@[simp] theorem initial_boundaryNat_four (c : Nat.Partrec.Code) :
    CounterLayout.boundaryPos
        (RegisterLayout.values (CanonicalInitializer.registers c)) 4 =
      inputGap c + 4 := by
  simp [CounterLayout.boundaryPos, inputGap]
  omega

@[simp] theorem span_eq_inputGap (c : Nat.Partrec.Code) :
    CanonicalInitializer.span c = inputGap c + 5 :=
  rfl

@[simp] theorem layoutEnd_initial (c : Nat.Partrec.Code) :
    FramedMarkerTape.layoutEnd (CanonicalInitializer.registers c) =
      CanonicalInitializer.span c := by
  simp only [FramedMarkerTape.layoutEnd]
  exact CanonicalInitializer.clockBoundary_registers c

theorem coreSymbol_initial_blank {numTags : Nat} (c : Nat.Partrec.Code)
    (position : Nat)
    (h0 : position ≠ 0) (h1 : position ≠ 1)
    (h2 : position ≠ inputGap c + 2)
    (h3 : position ≠ inputGap c + 3)
    (h4 : position ≠ inputGap c + 4) :
    FramedMarkerTape.coreSymbol (numTags := numTags)
      (CanonicalInitializer.registers c) position = blankSymbol := by
  have hcanonical : MarkerTape.canonicalTape
      (CanonicalInitializer.registers c) position = .blank := by
    rw [MarkerTape.canonicalTape_eq_blank_iff]
    intro label
    fin_cases label
    · simpa using h0
    · simpa using h1
    · simp [MarkerTape.boundaryPosition, inputGap] at h2 ⊢
      omega
    · simp [MarkerTape.boundaryPosition, inputGap] at h3 ⊢
      omega
    · simp [MarkerTape.boundaryPosition, inputGap] at h4 ⊢
      omega
  change baseSymbol (MarkerMachine.encodeSymbol
      (MarkerTape.canonicalTape (CanonicalInitializer.registers c) position)) =
    blankSymbol
  rw [hcanonical]
  rfl

theorem coreSymbol_initial {numTags : Nat} (c : Nat.Partrec.Code)
    (position : Nat) :
    FramedMarkerTape.coreSymbol (numTags := numTags)
        (CanonicalInitializer.registers c) position =
      if position = 0 then boundarySymbol 0
      else if position = 1 then boundarySymbol 1
      else if position = inputGap c + 2 then boundarySymbol 2
      else if position = inputGap c + 3 then boundarySymbol 3
      else if position = inputGap c + 4 then boundarySymbol 4
      else blankSymbol := by
  by_cases h0 : position = 0
  · subst position
    simpa using FramedMarkerTape.coreSymbol_boundary
      (numTags := numTags) (CanonicalInitializer.registers c) 0
  by_cases h1 : position = 1
  · subst position
    simpa using FramedMarkerTape.coreSymbol_boundary
      (numTags := numTags) (CanonicalInitializer.registers c) 1
  by_cases h2 : position = inputGap c + 2
  · subst position
    simp only [if_false, h0, h1, if_true]
    rw [← initial_boundaryNat_two c]
    exact FramedMarkerTape.coreSymbol_boundary
      (numTags := numTags) (CanonicalInitializer.registers c) 2
  by_cases h3 : position = inputGap c + 3
  · subst position
    simp only [if_false, h0, h1, h2, if_true]
    rw [← initial_boundaryNat_three c]
    exact FramedMarkerTape.coreSymbol_boundary
      (numTags := numTags) (CanonicalInitializer.registers c) 3
  by_cases h4 : position = inputGap c + 4
  · subst position
    simp only [if_false, h0, h1, h2, h3, if_true]
    rw [← initial_boundaryNat_four c]
    exact FramedMarkerTape.coreSymbol_boundary
      (numTags := numTags) (CanonicalInitializer.registers c) 4
  simp [h0, h1, h2, h3, h4,
    coreSymbol_initial_blank c position h0 h1 h2 h3 h4]

theorem logicalOverlay_initial_nat {numTags : Nat}
    (c : Nat.Partrec.Code) (tag : Fin numTags)
    (T : FullTM0.Tape (Symbol numTags))
    (hblank : ∀ position ≤ CanonicalInitializer.span c,
      T position = blankSymbol) (position : Nat) :
    FramedMarkerTape.logicalOverlay (CanonicalInitializer.registers c)
        tag T position =
      if position = 0 then tagSymbol tag
      else if position = 1 then boundarySymbol 0
      else if position = 2 then boundarySymbol 1
      else if position = inputGap c + 3 then boundarySymbol 2
      else if position = inputGap c + 4 then boundarySymbol 3
      else if position = inputGap c + 5 then boundarySymbol 4
      else T position := by
  by_cases htag : position = 0
  · subst position
    simp
  by_cases hb0 : position = 1
  · subst position
    simp only [Nat.one_ne_zero, if_false, if_true]
    simpa [coreSymbol_initial] using FramedMarkerTape.logicalOverlay_core
      (CanonicalInitializer.registers c) tag T 0 (by simp)
  by_cases hb1 : position = 2
  · subst position
    simp only [if_neg (by omega : (2 : Nat) ≠ 0),
      if_neg (by omega : (2 : Nat) ≠ 1), if_true]
    simpa [coreSymbol_initial] using FramedMarkerTape.logicalOverlay_core
      (CanonicalInitializer.registers c) tag T 1 (by
        simp [RegisterLayout.clockBoundary_eq])
  by_cases hb2 : position = inputGap c + 3
  · subst position
    simp only [if_false, htag, hb0, hb1, if_true]
    convert FramedMarkerTape.logicalOverlay_core
      (CanonicalInitializer.registers c) tag T (inputGap c + 2) (by
        simp [RegisterLayout.clockBoundary_eq, inputGap]) using 1
    · congr 1
    · rw [← initial_boundaryNat_two c]
      exact (FramedMarkerTape.coreSymbol_boundary
        (numTags := numTags) (CanonicalInitializer.registers c) 2).symm
  by_cases hb3 : position = inputGap c + 4
  · subst position
    simp only [if_false, htag, hb0, hb1, hb2, if_true]
    convert FramedMarkerTape.logicalOverlay_core
      (CanonicalInitializer.registers c) tag T (inputGap c + 3) (by
        simp [RegisterLayout.clockBoundary_eq, inputGap]) using 1
    · congr 1
    · rw [← initial_boundaryNat_three c]
      exact (FramedMarkerTape.coreSymbol_boundary
        (numTags := numTags) (CanonicalInitializer.registers c) 3).symm
  by_cases hb4 : position = inputGap c + 5
  · subst position
    simp only [if_false, htag, hb0, hb1, hb2, hb3, if_true]
    convert FramedMarkerTape.logicalOverlay_core
      (CanonicalInitializer.registers c) tag T (inputGap c + 4) (by
        simp [RegisterLayout.clockBoundary_eq, inputGap]) using 1
    · congr 1
    · rw [← initial_boundaryNat_four c]
      exact (FramedMarkerTape.coreSymbol_boundary
        (numTags := numTags) (CanonicalInitializer.registers c) 4).symm
  by_cases hle : position ≤ CanonicalInitializer.span c
  · have hpositive : 0 < position := Nat.pos_of_ne_zero htag
    have hread := hblank position hle
    have hpred : position - 1 + 1 = position := by omega
    have hcoreBound : position - 1 ≤ RegisterLayout.clockBoundary
        (CanonicalInitializer.registers c) := by
      have hclock := CanonicalInitializer.clockBoundary_registers c
      omega
    have hover := FramedMarkerTape.logicalOverlay_core
      (CanonicalInitializer.registers c) tag T (position - 1) hcoreBound
    have hpredInt : ((position - 1 : Nat) : Int) + 1 = position := by
      exact_mod_cast hpred
    rw [hpredInt] at hover
    have hcoreBlank := coreSymbol_initial_blank (numTags := numTags) c
      (position - 1) (by omega) (by omega) (by omega) (by omega) (by omega)
    simp only [if_neg htag, if_neg hb0, if_neg hb1, if_neg hb2,
      if_neg hb3, if_neg hb4]
    rw [hover, hcoreBlank, hread]
  · simp only [if_neg htag, if_neg hb0, if_neg hb1, if_neg hb2,
      if_neg hb3, if_neg hb4]
    apply FramedMarkerTape.logicalOverlay_of_layoutEnd_lt
    rw [layoutEnd_initial]
    exact_mod_cast Nat.lt_of_not_ge hle

theorem logicalOverlay_initial_nat_rev {numTags : Nat}
    (c : Nat.Partrec.Code) (tag : Fin numTags)
    (T : FullTM0.Tape (Symbol numTags))
    (hblank : ∀ position ≤ CanonicalInitializer.span c,
      T position = blankSymbol) (position : Nat) :
    FramedMarkerTape.logicalOverlay (CanonicalInitializer.registers c)
        tag T position =
      if position = inputGap c + 5 then boundarySymbol 4
      else if position = inputGap c + 4 then boundarySymbol 3
      else if position = inputGap c + 3 then boundarySymbol 2
      else if position = 2 then boundarySymbol 1
      else if position = 1 then boundarySymbol 0
      else if position = 0 then tagSymbol tag
      else T position := by
  rw [logicalOverlay_initial_nat c tag T hblank position]
  by_cases htag : position = 0
  · subst position
    simp
  by_cases hb0 : position = 1
  · subst position
    simp
  by_cases hb1 : position = 2
  · subst position
    simp
  by_cases hb2 : position = inputGap c + 3
  · subst position
    simp [hb0, hb1]
  by_cases hb3 : position = inputGap c + 4
  · subst position
    simp [hb0, hb1]
  by_cases hb4 : position = inputGap c + 5
  · subst position
    simp [hb0, hb1]
  simp [htag, hb0, hb1, hb2, hb3, hb4]

theorem resultTape_right_apply {numTags : Nat}
    (c : Nat.Partrec.Code) (tag : Fin numTags)
    (T : FullTM0.Tape (Symbol numTags)) (position : Int) :
    resultTape c .right tag T position =
      if position + (inputGap c + 5) = inputGap c + 5 then boundarySymbol 4
      else if position + (inputGap c + 5) = inputGap c + 4 then boundarySymbol 3
      else if position + (inputGap c + 5) = inputGap c + 3 then boundarySymbol 2
      else if position + (inputGap c + 5) = 2 then boundarySymbol 1
      else if position + (inputGap c + 5) = 1 then boundarySymbol 0
      else if position + (inputGap c + 5) = 0 then tagSymbol tag
      else T (position + (inputGap c + 5)) := by
  have hb4 : position = 0 ↔
      position + (inputGap c + 5) = inputGap c + 5 := by omega
  have hb3 : position + 1 = 0 ↔
      position + (inputGap c + 5) = inputGap c + 4 := by omega
  have hb2 : position + 1 + 1 = 0 ↔
      position + (inputGap c + 5) = inputGap c + 3 := by omega
  have hb1 : position + 1 + 1 + ((inputGap c : Int) + 1) = 0 ↔
      position + (inputGap c + 5) = 2 := by omega
  have hb0 : position + 1 + 1 + ((inputGap c : Int) + 1) + 1 = 0 ↔
      position + (inputGap c + 5) = 1 := by omega
  have htag : position + 1 + 1 + ((inputGap c : Int) + 1) + 1 + 1 = 0 ↔
      position + (inputGap c + 5) = 0 := by omega
  simp only [resultTape, FullTM0.Tape.moveN_apply,
    FullTM0.Tape.offset_right, FullTM0.Tape.write_apply]
  push_cast
  simp only [hb4, hb3, hb2, hb1, hb0, htag]
  ring_nf

theorem resultTape_right_eq_overlay_moveN {numTags : Nat}
    (c : Nat.Partrec.Code) (tag : Fin numTags)
    (T : FullTM0.Tape (Symbol numTags))
    (hblank : ∀ position ≤ CanonicalInitializer.span c,
      T position = blankSymbol) :
    resultTape c .right tag T =
      (FramedMarkerTape.logicalOverlay (CanonicalInitializer.registers c)
        tag T).moveN .right (CanonicalInitializer.span c) := by
  funext position
  rw [resultTape_right_apply]
  simp only [FullTM0.Tape.moveN_apply, FullTM0.Tape.offset_right,
    span_eq_inputGap]
  let absolute : Int := position + (inputGap c + 5)
  change (if absolute = inputGap c + 5 then boundarySymbol 4
    else if absolute = inputGap c + 4 then boundarySymbol 3
    else if absolute = inputGap c + 3 then boundarySymbol 2
    else if absolute = 2 then boundarySymbol 1
    else if absolute = 1 then boundarySymbol 0
    else if absolute = 0 then tagSymbol tag
    else T absolute) =
      FramedMarkerTape.logicalOverlay (CanonicalInitializer.registers c)
        tag T absolute
  by_cases habsolute : 0 ≤ absolute
  · have htoNat : (absolute.toNat : Int) = absolute :=
      Int.toNat_of_nonneg habsolute
    rw [← htoNat]
    rw [logicalOverlay_initial_nat_rev c tag T hblank absolute.toNat]
    norm_cast
  · have hnegative : absolute < 0 := lt_of_not_ge habsolute
    have h5 : absolute ≠ (inputGap c : Int) + 5 := by omega
    have h4 : absolute ≠ (inputGap c : Int) + 4 := by omega
    have h3 : absolute ≠ (inputGap c : Int) + 3 := by omega
    have h2 : absolute ≠ 2 := by omega
    have h1 : absolute ≠ 1 := by omega
    have h0 : absolute ≠ 0 := by omega
    simp only [if_neg h5, if_neg h4, if_neg h3, if_neg h2,
      if_neg h1, if_neg h0]
    have hinside : ¬(1 ≤ absolute ∧
      absolute ≤ FramedMarkerTape.layoutEnd
        (CanonicalInitializer.registers c)) := by omega
    simp only [FramedMarkerTape.logicalOverlay, if_neg h0, if_neg hinside]

theorem resultTape_eq_atLogical_install {numTags : Nat}
    (c : Nat.Partrec.Code) (growth : Turing.Dir) (tag : Fin numTags)
    (outer : FullTM0.Tape (Symbol numTags))
    (hblank : ∀ position ≤ CanonicalInitializer.span c,
      (outer.moveN growth position).read = blankSymbol) :
    resultTape c growth tag outer =
      FramedMarkerTape.atLogical growth
        (FramedMarkerTape.install (CanonicalInitializer.registers c)
          growth tag outer) (CanonicalInitializer.span c) := by
  have hlogical : ∀ position ≤ CanonicalInitializer.span c,
      FramedMarkerTape.logicalTape growth outer position = blankSymbol := by
    intro position hposition
    simpa [FramedMarkerTape.atLogical] using hblank position hposition
  have hright := resultTape_right_eq_overlay_moveN c tag
    (FramedMarkerTape.logicalTape growth outer) hlogical
  apply Function.Involutive.injective
    (FramedMarkerTape.logicalTape_involutive
      (numTags := numTags) growth)
  rw [logicalTape_resultTape]
  cases growth <;>
    simpa [FramedMarkerTape.atLogical, FramedMarkerTape.logicalTape,
      FramedMarkerTape.install, OrientedMarkerTape.orientTape] using hright

theorem instructions_executes_after_clear_framed {numTags : Nat}
    (c : Nat.Partrec.Code) (command : Command numTags)
    (outer : FullTM0.Tape (Symbol numTags)) (distance : Nat)
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      command.target.Matches outer command.searchDirection distance)
    (hfar : NestingMachine.bound (CanonicalInitializer.radius c) < distance) :
    FiniteTM0Path.Executes
        (instructions c command.searchDirection command.returnTag)
        ((taggedFrameTapeNative (CanonicalInitializer.radius c) command
          outer).write blankSymbol)
        (FramedMarkerTape.atLogical command.searchDirection
          (FramedMarkerTape.initializeTape c command outer)
          (CanonicalInitializer.span c)) ∧
      FramedMarkerTape.Represents
        (FramedMarkerTape.frameSpec c command distance hfar)
        (FramedMarkerTape.initializeTape c command outer) := by
  have hblank : ∀ position ≤ CanonicalInitializer.span c,
      (outer.moveN command.searchDirection position).read = blankSymbol := by
    intro position hposition
    have hlt : position < distance := by
      have hprefix : CanonicalInitializer.span c + 1 < distance := by
        simpa [NestingMachine.bound, CanonicalInitializer.radius] using hfar
      omega
    simpa only [FullTM0.Tape.read_moveN] using hgap.blank hlt
  constructor
  · have hexec := instructions_executes_after_clear c command outer distance
      hgap hfar
    rw [resultTape_eq_atLogical_install c command.searchDirection
      command.returnTag outer hblank] at hexec
    simpa only [FramedMarkerTape.initializeTape] using hexec
  · exact FramedMarkerTape.Represents.initializeTape_represents c command
      outer distance hgap hfar

end CanonicalInitializerFrame

end

end Hooper
end Kari
end LeanWang
