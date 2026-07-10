/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104SignalFreeCellEmbedding

/-!
The concrete free-cell geometry forces clear signal states at every selected
crossing.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace Signals
namespace FreeCrossings

open RedCycles FreeCellLocal FreeCellEmbedding

set_option maxRecDepth 20000

/-- A quarter-level signal assignment over an index grid. -/
structure ValidSignalGrid (indexGrid : Nat → Nat → Index)
    (stateGrid : Nat → Nat → State) : Prop where
  allowed : ∀ x y,
    locallyAllowed
      (indexGrid (x / 2) (y / 2), quadrantAt x y) (stateGrid x y) = true
  hmatch : ∀ x y, (stateGrid x y).east = (stateGrid (x + 1) y).west
  vmatch : ∀ x y, (stateGrid x y).north = (stateGrid x (y + 1)).south

theorem ValidSignalGrid.horizontalAllowed {indexGrid : Nat → Nat → Index}
    {stateGrid : Nat → Nat → State} (valid : ValidSignalGrid indexGrid stateGrid)
    (x y : Nat) :
    horizontalAllowed (verticalInteriorAt indexGrid x y) (stateGrid x y) = true := by
  simpa [verticalInteriorAt, componentAt] using
    horizontalAllowed_of_locallyAllowed (valid.allowed x y)

theorem ValidSignalGrid.verticalAllowed {indexGrid : Nat → Nat → Index}
    {stateGrid : Nat → Nat → State} (valid : ValidSignalGrid indexGrid stateGrid)
    (x y : Nat) :
    verticalAllowed (horizontalInteriorAt indexGrid x y) (stateGrid x y) = true := by
  simpa [horizontalInteriorAt, componentAt] using
    verticalAllowed_of_locallyAllowed (valid.allowed x y)

/-- Both horizontal edges of the selected crossing carry no signal. -/
theorem horizontal_clear
    {coarseGrid : Nat → Nat → Index} {stateGrid : Nat → Nat → State}
    {depth i j : Nat}
    (hdepth : 5 ≤ depth)
    (geometry : FreeCellEmbedding.Geometry coarseGrid depth i j)
    (valid : ValidSignalGrid (iterateRefine depth coarseGrid) stateGrid) :
    (stateGrid (freeCoordinate depth i) (freeCoordinate depth j)).west = .none ∧
      (stateGrid (freeCoordinate depth i) (freeCoordinate depth j)).east = .none := by
  let left := 8 * freeBlock depth i + 3
  let y := freeCoordinate depth j
  have hleftAllowed : horizontalAllowed (some .east) (stateGrid left y) = true := by
    have h := valid.horizontalAllowed left y
    simpa only [left, y, geometry.westBoundary] using h
  have hrightAllowed :
      horizontalAllowed (some .west) (stateGrid (left + 3) y) = true := by
    have h := valid.horizontalAllowed (left + 3) y
    have hright : left + 3 = 8 * freeBlock depth i + 6 := by
      simp [left]
    simpa only [hright, y, geometry.eastBoundary] using h
  have htransmit4 :
      (stateGrid (left + 1) y).west = (stateGrid (left + 1) y).east := by
    apply horizontal_transmits_of_allowed
    have h := valid.horizontalAllowed (left + 1) y
    have hcoord : left + 1 = 8 * freeBlock depth i + 4 := by simp [left]
    simpa only [hcoord, y, geometry.verticalClear4] using h
  have htransmit5 :
      (stateGrid (left + 2) y).west = (stateGrid (left + 2) y).east := by
    apply horizontal_transmits_of_allowed
    have h := valid.horizontalAllowed (left + 2) y
    have hcoord : left + 2 = 8 * freeBlock depth i + 5 := by simp [left]
    simpa only [hcoord, y, geometry.verticalClear5] using h
  have hflow : (stateGrid left y).east = (stateGrid (left + 3) y).west := by
    apply horizontal_flow_across (fun x => stateGrid x y) left 2
    · intro offset hoffset
      simpa [Nat.add_assoc] using valid.hmatch (left + offset) y
    · intro offset hoffset
      have hoffsetCases : offset = 0 ∨ offset = 1 := by omega
      rcases hoffsetCases with rfl | rfl
      · simpa only [Nat.zero_add] using htransmit4
      · simpa only using htransmit5
  have hends := horizontal_clear_of_inner_edges hflow
    (horizontal_interiorEast_rules hleftAllowed).2
    (horizontal_interiorWest_rules hrightAllowed).2
  have hmatch4 := valid.hmatch left y
  have hmatch5 := valid.hmatch (left + 1) y
  have hwest4 : (stateGrid (left + 1) y).west = .none :=
    hmatch4.symm.trans hends.1
  have heast4 : (stateGrid (left + 1) y).east = .none :=
    htransmit4.symm.trans hwest4
  have hwest5 : (stateGrid (left + 2) y).west = .none :=
    hmatch5.symm.trans heast4
  have heast5 : (stateGrid (left + 2) y).east = .none :=
    htransmit5.symm.trans hwest5
  have hcoord := freeCoordinate_eq depth i hdepth
  have hmod : i % 2 = 0 ∨ i % 2 = 1 := by
    have := Nat.mod_lt i (by decide : 0 < 2)
    omega
  rcases hmod with hzero | hone
  · have hselected : freeCoordinate depth i = left + 1 := by
      rw [hcoord, hzero]
    simpa only [hselected, y] using And.intro hwest4 heast4
  · have hselected : freeCoordinate depth i = left + 2 := by
      rw [hcoord, hone]
    simpa only [hselected, y] using And.intro hwest5 heast5

/-- Both vertical edges of the selected crossing carry no signal. -/
theorem vertical_clear
    {coarseGrid : Nat → Nat → Index} {stateGrid : Nat → Nat → State}
    {depth i j : Nat}
    (hdepth : 5 ≤ depth)
    (geometry : FreeCellEmbedding.Geometry coarseGrid depth i j)
    (valid : ValidSignalGrid (iterateRefine depth coarseGrid) stateGrid) :
    (stateGrid (freeCoordinate depth i) (freeCoordinate depth j)).south = .none ∧
      (stateGrid (freeCoordinate depth i) (freeCoordinate depth j)).north = .none := by
  let x := freeCoordinate depth i
  let lower := 8 * freeBlock depth j + 3
  have hlowerAllowed : verticalAllowed (some .north) (stateGrid x lower) = true := by
    have h := valid.verticalAllowed x lower
    simpa only [x, lower, geometry.southBoundary] using h
  have hupperAllowed :
      verticalAllowed (some .south) (stateGrid x (lower + 3)) = true := by
    have h := valid.verticalAllowed x (lower + 3)
    have hupper : lower + 3 = 8 * freeBlock depth j + 6 := by
      simp [lower]
    simpa only [x, hupper, geometry.northBoundary] using h
  have htransmit4 :
      (stateGrid x (lower + 1)).south = (stateGrid x (lower + 1)).north := by
    apply vertical_transmits_of_allowed
    have h := valid.verticalAllowed x (lower + 1)
    have hcoord : lower + 1 = 8 * freeBlock depth j + 4 := by simp [lower]
    simpa only [x, hcoord, geometry.horizontalClear4] using h
  have htransmit5 :
      (stateGrid x (lower + 2)).south = (stateGrid x (lower + 2)).north := by
    apply vertical_transmits_of_allowed
    have h := valid.verticalAllowed x (lower + 2)
    have hcoord : lower + 2 = 8 * freeBlock depth j + 5 := by simp [lower]
    simpa only [x, hcoord, geometry.horizontalClear5] using h
  have hflow : (stateGrid x lower).north = (stateGrid x (lower + 3)).south := by
    apply vertical_flow_across (fun y => stateGrid x y) lower 2
    · intro offset hoffset
      simpa [Nat.add_assoc] using valid.vmatch x (lower + offset)
    · intro offset hoffset
      have hoffsetCases : offset = 0 ∨ offset = 1 := by omega
      rcases hoffsetCases with rfl | rfl
      · simpa only [Nat.zero_add] using htransmit4
      · simpa only using htransmit5
  have hends := vertical_clear_of_inner_edges hflow
    (vertical_interiorNorth_rules hlowerAllowed).2
    (vertical_interiorSouth_rules hupperAllowed).2
  have hmatch4 := valid.vmatch x lower
  have hmatch5 := valid.vmatch x (lower + 1)
  have hsouth4 : (stateGrid x (lower + 1)).south = .none :=
    hmatch4.symm.trans hends.1
  have hnorth4 : (stateGrid x (lower + 1)).north = .none :=
    htransmit4.symm.trans hsouth4
  have hsouth5 : (stateGrid x (lower + 2)).south = .none :=
    hmatch5.symm.trans hnorth4
  have hnorth5 : (stateGrid x (lower + 2)).north = .none :=
    htransmit5.symm.trans hsouth5
  have hcoord := freeCoordinate_eq depth j hdepth
  have hmod : j % 2 = 0 ∨ j % 2 = 1 := by
    have := Nat.mod_lt j (by decide : 0 < 2)
    omega
  rcases hmod with hzero | hone
  · have hselected : freeCoordinate depth j = lower + 1 := by
      rw [hcoord, hzero]
    simpa only [x, hselected] using And.intro hsouth4 hnorth4
  · have hselected : freeCoordinate depth j = lower + 2 := by
      rw [hcoord, hone]
    simpa only [x, hselected] using And.intro hsouth5 hnorth5

/-- Every selected free crossing has the all-clear signal state. -/
theorem clearState_at
    {coarseGrid : Nat → Nat → Index} {stateGrid : Nat → Nat → State}
    {depth i j : Nat} (hdepth : 5 ≤ depth)
    (valid : ValidSignalGrid (iterateRefine depth coarseGrid) stateGrid) :
    stateGrid (freeCoordinate depth i) (freeCoordinate depth j) = clearState := by
  have geometry := FreeCellEmbedding.geometry coarseGrid (i := i) (j := j) hdepth
  have hh := horizontal_clear hdepth geometry valid
  have hv := vertical_clear hdepth geometry valid
  generalize hstate :
    stateGrid (freeCoordinate depth i) (freeCoordinate depth j) = state at hh hv ⊢
  rcases state with ⟨west, east, south, north⟩
  simp_all [clearState]

end FreeCrossings
end Signals
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
