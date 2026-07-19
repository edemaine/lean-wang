/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlCoreFrame
import LeanWang.Kari.Hooper.CounterControlInstructionSemantics

/-!
# Reconstructing a counter core from validation

The outward half of the mandatory validation sweep visits boundaries
`0, 1, 2, 3, 4` in order and accepts only blank cells between consecutive
labels.  Consequently a successful outward sweep on an arbitrary tape
determines four register values and reconstructs an exact canonical core.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlValidationConverse

open Turing CounterMachine
open BoundedMarkerProgram FramedMarkerTape
open CounterControlCoreFrame CounterControlInstructionSemantics
  CounterControlCoreRoutes

noncomputable section

/-- The four outward legs of `MarkerValidation.sweep`. -/
def outwardSweep : List MarkerValidation.Leg :=
  [ ⟨1, .right⟩
  , ⟨2, .right⟩
  , ⟨3, .right⟩
  , ⟨4, .right⟩
  ]

@[simp] theorem outwardSweep_length : outwardSweep.length = 4 := rfl

/-- Canonical core geometry with the head centered on boundary `0` rather
than on the adjacent saved tag. -/
structure BoundaryZeroRepresents {numTags : Nat} (registers : Registers)
    (growth : Turing.Dir) (T : FullTM0.Tape (Symbol numTags)) : Prop where
  boundary : ∀ label : Fin 5,
    logicalTape growth T
        ((CounterLayout.boundaryPos
          (RegisterLayout.values registers) label : Nat) : Int) =
      boundarySymbol label
  gap : ∀ (i : Fin 4) (k : Nat),
    k < RegisterLayout.values registers i →
      logicalTape growth T
          ((CounterLayout.boundaryPos (RegisterLayout.values registers) i +
            1 + k : Nat) : Int) = blankSymbol

namespace BoundaryZeroRepresents

variable {numTags : Nat} {registers : Registers}
variable {growth : Turing.Dir} {T : FullTM0.Tape (Symbol numTags)}

/-- Moving one logical cell outward from an arbitrary saved-tag cell turns
the boundary-zero representation into the common target-free core
representation.  No assertion about the unvalidated saved-tag symbol is
needed. -/
theorem toCoreRepresents
    (h : BoundaryZeroRepresents registers growth T) :
    CoreRepresents registers growth
      (T.move (OrientedMarkerTape.orientDirection growth .left)) := by
  constructor
  intro position hposition
  have hlogical : logicalTape growth
      (T.move (OrientedMarkerTape.orientDirection growth .left))
        (position + 1) = logicalTape growth T position := by
    cases growth <;>
      simp [logicalTape, OrientedMarkerTape.orientTape,
        OrientedMarkerTape.orientDirection, FullTM0.Tape.move]
  rw [hlogical]
  let v := RegisterLayout.values registers
  let p : Nat → Nat := CounterLayout.boundaryPos v
  have hp0 : p 0 = 0 := by simp [p]
  have hp1 : p 1 = p 0 + v 0 + 1 := by
    simpa [p] using CounterLayout.boundaryPos_succ v 0
  have hp2 : p 2 = p 1 + v 1 + 1 := by
    simpa [p] using CounterLayout.boundaryPos_succ v 1
  have hp3 : p 3 = p 2 + v 2 + 1 := by
    simpa [p] using CounterLayout.boundaryPos_succ v 2
  have hp4 : p 4 = p 3 + v 3 + 1 := by
    simpa [p] using CounterLayout.boundaryPos_succ v 3
  have hposition4 : position ≤ p 4 := by
    change position ≤ CounterLayout.boundaryPos
      (RegisterLayout.values registers) 4 at hposition
    simpa [p, v] using hposition
  by_cases h0 : position = p 0
  · rw [h0, show p 0 = CounterLayout.boundaryPos
        (RegisterLayout.values registers) (0 : Fin 5) by rfl,
      h.boundary 0]
    exact (coreSymbol_boundary registers 0).symm
  by_cases hgap0 : position < p 1
  · let k := position - (p 0 + 1)
    have hk : k < v 0 := by dsimp [k]; omega
    have hpos : position = p 0 + 1 + k := by dsimp [k]; omega
    rw [hpos, show p 0 = CounterLayout.boundaryPos
        (RegisterLayout.values registers) (0 : Fin 4) by rfl]
    exact (h.gap 0 k (by simpa [v] using hk)).trans
      (coreSymbol_gapInterior registers 0 k
        (by simpa [v] using hk)).symm
  by_cases h1 : position = p 1
  · rw [h1, show p 1 = CounterLayout.boundaryPos
        (RegisterLayout.values registers) (1 : Fin 5) by rfl,
      h.boundary 1]
    exact (coreSymbol_boundary registers 1).symm
  by_cases hgap1 : position < p 2
  · let k := position - (p 1 + 1)
    have hk : k < v 1 := by dsimp [k]; omega
    have hpos : position = p 1 + 1 + k := by dsimp [k]; omega
    rw [hpos, show p 1 = CounterLayout.boundaryPos
        (RegisterLayout.values registers) (1 : Fin 4) by rfl]
    exact (h.gap 1 k (by simpa [v] using hk)).trans
      (coreSymbol_gapInterior registers 1 k
        (by simpa [v] using hk)).symm
  by_cases h2 : position = p 2
  · rw [h2, show p 2 = CounterLayout.boundaryPos
        (RegisterLayout.values registers) (2 : Fin 5) by rfl,
      h.boundary 2]
    exact (coreSymbol_boundary registers 2).symm
  by_cases hgap2 : position < p 3
  · let k := position - (p 2 + 1)
    have hk : k < v 2 := by dsimp [k]; omega
    have hpos : position = p 2 + 1 + k := by dsimp [k]; omega
    rw [hpos, show p 2 = CounterLayout.boundaryPos
        (RegisterLayout.values registers) (2 : Fin 4) by rfl]
    exact (h.gap 2 k (by simpa [v] using hk)).trans
      (coreSymbol_gapInterior registers 2 k
        (by simpa [v] using hk)).symm
  by_cases h3 : position = p 3
  · rw [h3, show p 3 = CounterLayout.boundaryPos
        (RegisterLayout.values registers) (3 : Fin 5) by rfl,
      h.boundary 3]
    exact (coreSymbol_boundary registers 3).symm
  by_cases hgap3 : position < p 4
  · let k := position - (p 3 + 1)
    have hk : k < v 3 := by dsimp [k]; omega
    have hpos : position = p 3 + 1 + k := by dsimp [k]; omega
    rw [hpos, show p 3 = CounterLayout.boundaryPos
        (RegisterLayout.values registers) (3 : Fin 4) by rfl]
    exact (h.gap 3 k (by simpa [v] using hk)).trans
      (coreSymbol_gapInterior registers 3 k
        (by simpa [v] using hk)).symm
  have h4 : position = p 4 := by omega
  rw [h4, show p 4 = CounterLayout.boundaryPos
      (RegisterLayout.values registers) (4 : Fin 5) by rfl,
    h.boundary 4]
  exact (coreSymbol_boundary registers 4).symm

end BoundaryZeroRepresents

/-! ## Inverting the outward validation route -/

@[simp] theorem logicalTape_atLogical {numTags : Nat} (growth : Turing.Dir)
    (T : FullTM0.Tape (Symbol numTags)) (origin position : Nat) :
    logicalTape growth (atLogical growth T origin) position =
      logicalTape growth T (origin + position) := by
  cases growth <;>
    simp [logicalTape, atLogical, OrientedMarkerTape.orientTape,
      FullTM0.Tape.moveN, FullTM0.Tape.offset] <;> congr 1 <;> ring

@[simp] theorem atLogical_apply_physicalCoord {numTags : Nat}
    (growth : Turing.Dir)
    (T : FullTM0.Tape (Symbol numTags)) (origin position : Nat) :
    atLogical growth T origin (physicalCoord growth position) =
      T (physicalCoord growth (origin + position)) := by
  simpa only [logicalTape_apply] using
    logicalTape_atLogical growth T origin position

private theorem rightGap_blank {numTags : Nat} {target : Fin 5}
    (growth : Turing.Dir) (T : FullTM0.Tape (Symbol numTags))
    (origin distance k : Nat)
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary target).Matches (atLogical growth T origin)
      (OrientedMarkerTape.orientDirection growth .right) distance)
    (hk : k < distance) :
    logicalTape growth T (origin + k) = blankSymbol := by
  have hblank := hgap.blank hk
  rw [atLogical_apply_offset] at hblank
  simpa [FullTM0.Tape.offset_right, Nat.cast_add] using hblank

private theorem rightGap_boundary {numTags : Nat} {target : Fin 5}
    (growth : Turing.Dir) (T : FullTM0.Tape (Symbol numTags))
    (origin distance : Nat)
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary target).Matches (atLogical growth T origin)
      (OrientedMarkerTape.orientDirection growth .right) distance) :
    logicalTape growth T (origin + distance) = boundarySymbol target := by
  have hmarked := hgap.marked
  rw [atLogical_apply_offset] at hmarked
  simpa [Target.Matches, FullTM0.Tape.offset_right, Nat.cast_add] using hmarked

/-- Successful execution of the outward half of validation reconstructs a
unique four-register core between the observed boundary `0` and boundary
`4`.  The returned tape is centered at the reconstructed final boundary. -/
theorem outwardSweep_reconstructs
    {numTags : Nat} (growth : Turing.Dir)
    (T : FullTM0.Tape (Symbol numTags))
    (source finish : Nat)
    (hsource : (atLogical growth T source).read = boundarySymbol 0)
    (hexec : RouteExecutesAt growth T outwardSweep source finish) :
    ∃ registers : Registers,
      BoundaryZeroRepresents registers growth (atLogical growth T source) ∧
      finish = source + RegisterLayout.clockBoundary registers := by
  unfold outwardSweep at hexec
  cases hexec with
  | cons _ _ _ p1 _ hleg0 hrest0 =>
    cases hrest0 with
    | cons _ _ _ p2 _ hleg1 hrest1 =>
      cases hrest1 with
      | cons _ _ _ p3 _ hleg2 hrest2 =>
        cases hrest2 with
        | cons _ _ _ p4 _ hleg3 hrest3 =>
          cases hrest3
          change ∃ d0,
              SearchGap (fun symbol => symbol = blankSymbol)
                (Target.boundary 1).Matches
                (atLogical growth T (source + 1))
                (OrientedMarkerTape.orientDirection growth .right) d0 ∧
              p1 = source + d0 + 1 at hleg0
          change ∃ d1,
              SearchGap (fun symbol => symbol = blankSymbol)
                (Target.boundary 2).Matches
                (atLogical growth T (p1 + 1))
                (OrientedMarkerTape.orientDirection growth .right) d1 ∧
              p2 = p1 + d1 + 1 at hleg1
          change ∃ d2,
              SearchGap (fun symbol => symbol = blankSymbol)
                (Target.boundary 3).Matches
                (atLogical growth T (p2 + 1))
                (OrientedMarkerTape.orientDirection growth .right) d2 ∧
              p3 = p2 + d2 + 1 at hleg2
          change ∃ d3,
              SearchGap (fun symbol => symbol = blankSymbol)
                (Target.boundary 4).Matches
                (atLogical growth T (p3 + 1))
                (OrientedMarkerTape.orientDirection growth .right) d3 ∧
              finish = p3 + d3 + 1 at hleg3
          rcases hleg0 with ⟨d0, hgap0, hp1⟩
          rcases hleg1 with ⟨d1, hgap1, hp2⟩
          rcases hleg2 with ⟨d2, hgap2, hp3⟩
          rcases hleg3 with ⟨d3, hgap3, hp4⟩
          let registers : Registers := ⟨d0, d1, d2, d3⟩
          refine ⟨registers, ?_, ?_⟩
          · constructor
            · intro label
              rcases label with ⟨label, hlabel⟩
              have hcases : label = 0 ∨ label = 1 ∨ label = 2 ∨
                  label = 3 ∨ label = 4 := by omega
              rcases hcases with rfl | rfl | rfl | rfl | rfl
              · simpa [logicalTape_atLogical] using hsource
              · have hmark := rightGap_boundary growth T (source + 1) d0 hgap0
                rw [logicalTape_atLogical]
                simpa [registers, CounterLayout.boundaryPos,
                  Nat.cast_add, add_assoc, add_comm, add_left_comm] using hmark
              · have hmark := rightGap_boundary growth T (p1 + 1) d1 hgap1
                rw [logicalTape_atLogical]
                simpa [registers, CounterLayout.boundaryPos,
                  Nat.cast_add, hp1, add_assoc, add_comm, add_left_comm] using hmark
              · have hmark := rightGap_boundary growth T (p2 + 1) d2 hgap2
                rw [logicalTape_atLogical]
                simpa [registers, CounterLayout.boundaryPos,
                  Nat.cast_add, hp1, hp2, add_assoc, add_comm, add_left_comm]
                  using hmark
              · have hmark := rightGap_boundary growth T (p3 + 1) d3 hgap3
                rw [logicalTape_atLogical]
                simpa [registers, CounterLayout.boundaryPos,
                  Nat.cast_add, hp1, hp2, hp3, add_assoc, add_comm,
                  add_left_comm]
                  using hmark
            · intro i k hk
              rcases i with ⟨i, hi⟩
              have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
              rcases hcases with rfl | rfl | rfl | rfl
              · have hblank := rightGap_blank growth T (source + 1) d0 k
                    hgap0 (by simpa [registers] using hk)
                rw [logicalTape_atLogical]
                simpa [registers, CounterLayout.boundaryPos,
                  Nat.cast_add, add_assoc, add_comm, add_left_comm] using hblank
              · have hblank := rightGap_blank growth T (p1 + 1) d1 k
                    hgap1 (by simpa [registers] using hk)
                rw [logicalTape_atLogical]
                simpa [registers, CounterLayout.boundaryPos,
                  Nat.cast_add, hp1, add_assoc, add_comm, add_left_comm]
                  using hblank
              · have hblank := rightGap_blank growth T (p2 + 1) d2 k
                    hgap2 (by simpa [registers] using hk)
                rw [logicalTape_atLogical]
                simpa [registers, CounterLayout.boundaryPos,
                  Nat.cast_add, hp1, hp2, add_assoc, add_comm, add_left_comm]
                  using hblank
              · have hblank := rightGap_blank growth T (p3 + 1) d3 k
                    hgap3 (by simpa [registers] using hk)
                rw [logicalTape_atLogical]
                simpa [registers, CounterLayout.boundaryPos,
                  Nat.cast_add, hp1, hp2, hp3, add_assoc, add_comm,
                  add_left_comm]
                  using hblank
          · dsimp [registers]
            rw [RegisterLayout.clockBoundary_eq]
            change finish = source + (d0 + d1 + d2 + d3 + 4)
            omega

end

end CounterControlValidationConverse
end Hooper
end Kari
end LeanWang
