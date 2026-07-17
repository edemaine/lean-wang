/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamArithmetic

/-!
# Boundary conclusions for pair-cover seams

The fixed-depth face recurrence uses nearest-boundary conclusions when a
crossing and a selected witness span a hierarchy seam.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace PairCoverSeamComposition

open RedCycles RedShadeCycles RedShadePaths RedShadeGraphRefinement
  ShadedFreeLineRecurrence ShadedPlaneSignalGrid
  ShadedObstructionGeometry ShadedObstructionGeometryCover
  ShadedObstructionPairCoverRecurrence SparseFreeLinePlaneBase
  Signals.FreeCellLocal PairCoverSeamArithmetic

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

theorem exists_first_after
    {P : Nat → Prop} {start finish : Nat}
    (hstart : start < finish) (hfinish : P finish) :
    ∃ first, start < first ∧ first ≤ finish ∧ P first ∧
      ∀ value, start < value → value < first → ¬P value := by
  classical
  let Q : Nat → Prop := fun distance =>
    0 < distance ∧ start + distance ≤ finish ∧ P (start + distance)
  have existsQ : ∃ distance, Q distance := by
    refine ⟨finish - start, ?_⟩
    dsimp [Q]
    have : start + (finish - start) = finish := by omega
    exact ⟨by omega, by omega, by simpa [this] using hfinish⟩
  let distance := Nat.find existsQ
  have found : Q distance := by
    dsimp [distance]
    exact Nat.find_spec existsQ
  refine ⟨start + distance, by omega, found.2.1, found.2.2, ?_⟩
  intro value hvalueStart hvalueFirst hvalue
  have candidate : Q (value - start) := by
    dsimp [Q]
    have hsum : start + (value - start) = value := by omega
    exact ⟨by omega, by omega, by simpa [hsum] using hvalue⟩
  have minimal : distance ≤ value - start := by
    dsimp [distance]
    exact Nat.find_min' existsQ candidate
  dsimp [distance] at hvalueFirst
  omega

theorem exists_last_before
    {P : Nat → Prop} {first finish : Nat}
    (hfirst : first < finish) (hfirstP : P first) :
    ∃ last, first ≤ last ∧ last < finish ∧ P last ∧
      ∀ value, last < value → value < finish → ¬P value := by
  classical
  let Q : Nat → Prop := fun distance =>
    0 < distance ∧ distance ≤ finish - first ∧ P (finish - distance)
  have existsQ : ∃ distance, Q distance := by
    refine ⟨finish - first, ?_⟩
    dsimp [Q]
    have : finish - (finish - first) = first := by omega
    exact ⟨by omega, le_rfl, by simpa [this] using hfirstP⟩
  let distance := Nat.find existsQ
  have found : Q distance := by
    dsimp [distance]
    exact Nat.find_spec existsQ
  refine ⟨finish - distance, by omega, by omega, found.2.2, ?_⟩
  intro value hlastValue hvalueFinish hvalue
  have candidate : Q (finish - value) := by
    dsimp [Q]
    have hsub : finish - (finish - value) = value := by omega
    exact ⟨by omega, by omega, by simpa [hsub] using hvalue⟩
  have minimal : distance ≤ finish - value := by
    dsimp [distance]
    exact Nat.find_min' existsQ candidate
  dsimp [distance] at hlastValue
  omega

def VerticalBoundaryConclusion
    (indexGrid : Nat → Nat → Index)
    (shadeGrid : Nat → Nat → RedShades.State)
    (south north column row : Nat) : Prop :=
  ShadedSignals.selectedHorizontalFor
      (componentAt indexGrid column row) (quadrantAt column row)
      (shadeGrid column row) ≠ none ∨
    (∃ boundary, row < boundary ∧ boundary < quarterNorth north ∧
      ShadedSignals.selectedHorizontalFor
        (componentAt indexGrid column boundary) (quadrantAt column boundary)
        (shadeGrid column boundary) = some .north ∧
      ∀ y, row < y → y < boundary →
        ShadedSignals.selectedHorizontalFor
          (componentAt indexGrid column y) (quadrantAt column y)
          (shadeGrid column y) = none) ∨
    (∃ boundary, quarterSouth south < boundary ∧ boundary < row ∧
      ShadedSignals.selectedHorizontalFor
        (componentAt indexGrid column boundary) (quadrantAt column boundary)
        (shadeGrid column boundary) = some .south ∧
      ∀ y, boundary < y → y < row →
        ShadedSignals.selectedHorizontalFor
          (componentAt indexGrid column y) (quadrantAt column y)
          (shadeGrid column y) = none)

def HorizontalBoundaryConclusion
    (indexGrid : Nat → Nat → Index)
    (shadeGrid : Nat → Nat → RedShades.State)
    (west east column row : Nat) : Prop :=
  ShadedSignals.selectedVerticalFor
      (componentAt indexGrid column row) (quadrantAt column row)
      (shadeGrid column row) ≠ none ∨
    (∃ boundary, column < boundary ∧ boundary < quarterEast east ∧
      ShadedSignals.selectedVerticalFor
        (componentAt indexGrid boundary row) (quadrantAt boundary row)
        (shadeGrid boundary row) = some .east ∧
      ∀ x, column < x → x < boundary →
        ShadedSignals.selectedVerticalFor
          (componentAt indexGrid x row) (quadrantAt x row)
          (shadeGrid x row) = none) ∨
    (∃ boundary, quarterWest west < boundary ∧ boundary < column ∧
      ShadedSignals.selectedVerticalFor
        (componentAt indexGrid boundary row) (quadrantAt boundary row)
        (shadeGrid boundary row) = some .west ∧
      ∀ x, boundary < x → x < column →
        ShadedSignals.selectedVerticalFor
          (componentAt indexGrid x row) (quadrantAt x row)
          (shadeGrid x row) = none)


end PairCoverSeamComposition
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
