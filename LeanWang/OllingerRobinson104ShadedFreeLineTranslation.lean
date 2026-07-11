/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104RefinementTranslation
import LeanWang.OllingerRobinson104ShadedLightBoardFreeLines

/-!
Translation equivariance of shaded free rows and columns.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace ShadedFreeLineTranslation

open RedCycles RedShadeCycles RedShadePaths RefinementTranslation
  ShadedPlaneSignalGrid Signals.FreeCellLocal

set_option maxRecDepth 20000

def shiftQuarterGrid {α : Type} (grid : Nat → Nat → α)
    (offsetX offsetY : Nat) : Nat → Nat → α :=
  fun x y => grid (offsetX + x) (offsetY + y)

set_option maxHeartbeats 1000000 in
-- Normalizing the dependent shade rules through both grid shifts.
theorem validShadeGrid_shift (depth : Nat) (grid : Nat → Nat → Index)
    {shadeGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid (iterateRefine depth grid) shadeGrid)
    (blockX blockY : Nat) :
    ValidShadeGrid
      (iterateRefine depth (shiftGrid grid blockX blockY))
      (shiftQuarterGrid shadeGrid
        (2 ^ (depth + 1) * blockX) (2 ^ (depth + 1) * blockY)) := by
  let quarterOffsetX := 2 ^ (depth + 1) * blockX
  let quarterOffsetY := 2 ^ (depth + 1) * blockY
  have hscale : 2 ∣ 2 ^ (depth + 1) := dvd_pow_self 2 (by omega)
  have hquadrant (x y : Nat) :
      quadrantAt (quarterOffsetX + x) (quarterOffsetY + y) =
        quadrantAt x y :=
    quadrantAt_shift (2 ^ (depth + 1)) blockX blockY x y hscale
  constructor
  · intro x y
    have hallowed := valid.allowed
      (quarterOffsetX + x) (quarterOffsetY + y)
    change RedShades.allowedFor
      (componentAt (iterateRefine depth grid)
        (quarterOffsetX + x) (quarterOffsetY + y))
      (quadrantAt (quarterOffsetX + x) (quarterOffsetY + y))
      (shadeGrid (quarterOffsetX + x) (quarterOffsetY + y)) = true at hallowed
    change RedShades.allowedFor
      (componentAt (iterateRefine depth (shiftGrid grid blockX blockY)) x y)
      (quadrantAt x y)
      (shiftQuarterGrid shadeGrid quarterOffsetX quarterOffsetY x y) = true
    rw [componentAt_iterateRefine_shift, ← hquadrant]
    exact hallowed
  · intro x y
    simpa only [shiftQuarterGrid, Nat.add_assoc] using
      valid.hmatch (quarterOffsetX + x) (quarterOffsetY + y)
  · intro x y
    simpa only [shiftQuarterGrid, Nat.add_assoc] using
      valid.vmatch (quarterOffsetX + x) (quarterOffsetY + y)

set_option maxHeartbeats 1000000 in
-- Normalizing the dependent shade and signal rules through both grid shifts.
theorem validGrid_shift (depth : Nat) (grid : Nat → Nat → Index)
    {shadeGrid : Nat → Nat → RedShades.State}
    {signalGrid : Nat → Nat → Signals.State}
    (valid : ValidGrid (iterateRefine depth grid) shadeGrid signalGrid)
    (blockX blockY : Nat) :
    ValidGrid
      (iterateRefine depth (shiftGrid grid blockX blockY))
      (shiftQuarterGrid shadeGrid
        (2 ^ (depth + 1) * blockX) (2 ^ (depth + 1) * blockY))
      (shiftQuarterGrid signalGrid
        (2 ^ (depth + 1) * blockX) (2 ^ (depth + 1) * blockY)) := by
  let quarterOffsetX := 2 ^ (depth + 1) * blockX
  let quarterOffsetY := 2 ^ (depth + 1) * blockY
  have hscale : 2 ∣ 2 ^ (depth + 1) := dvd_pow_self 2 (by omega)
  have hquadrant (x y : Nat) :
      quadrantAt (quarterOffsetX + x) (quarterOffsetY + y) =
        quadrantAt x y :=
    quadrantAt_shift (2 ^ (depth + 1)) blockX blockY x y hscale
  constructor
  · exact validShadeGrid_shift depth grid valid.shadeValid blockX blockY
  · intro x y
    have hallowed := valid.signalAllowed
      (quarterOffsetX + x) (quarterOffsetY + y)
    change ShadedSignals.locallyAllowed
      (((iterateRefine depth grid)
          ((quarterOffsetX + x) / 2) ((quarterOffsetY + y) / 2),
        quadrantAt (quarterOffsetX + x) (quarterOffsetY + y)),
        shadeGrid (quarterOffsetX + x) (quarterOffsetY + y))
      (signalGrid (quarterOffsetX + x) (quarterOffsetY + y)) = true at hallowed
    unfold ShadedSignals.locallyAllowed at hallowed ⊢
    change (Signals.horizontalAllowed
        (ShadedSignals.selectedVerticalFor
          (componentAt (iterateRefine depth grid)
            (quarterOffsetX + x) (quarterOffsetY + y))
          (quadrantAt (quarterOffsetX + x) (quarterOffsetY + y))
          (shadeGrid (quarterOffsetX + x) (quarterOffsetY + y)))
        (signalGrid (quarterOffsetX + x) (quarterOffsetY + y)) &&
      Signals.verticalAllowed
        (ShadedSignals.selectedHorizontalFor
          (componentAt (iterateRefine depth grid)
            (quarterOffsetX + x) (quarterOffsetY + y))
          (quadrantAt (quarterOffsetX + x) (quarterOffsetY + y))
          (shadeGrid (quarterOffsetX + x) (quarterOffsetY + y)))
        (signalGrid (quarterOffsetX + x) (quarterOffsetY + y))) = true at hallowed
    change (Signals.horizontalAllowed
        (ShadedSignals.selectedVerticalFor
          (componentAt (iterateRefine depth (shiftGrid grid blockX blockY)) x y)
          (quadrantAt x y)
          (shiftQuarterGrid shadeGrid quarterOffsetX quarterOffsetY x y))
        (shiftQuarterGrid signalGrid quarterOffsetX quarterOffsetY x y) &&
      Signals.verticalAllowed
        (ShadedSignals.selectedHorizontalFor
          (componentAt (iterateRefine depth (shiftGrid grid blockX blockY)) x y)
          (quadrantAt x y)
          (shiftQuarterGrid shadeGrid quarterOffsetX quarterOffsetY x y))
        (shiftQuarterGrid signalGrid quarterOffsetX quarterOffsetY x y)) = true
    rw [componentAt_iterateRefine_shift, ← hquadrant]
    exact hallowed
  · intro x y
    simpa only [shiftQuarterGrid, Nat.add_assoc] using
      valid.hmatch (quarterOffsetX + x) (quarterOffsetY + y)
  · intro x y
    simpa only [shiftQuarterGrid, Nat.add_assoc] using
      valid.vmatch (quarterOffsetX + x) (quarterOffsetY + y)

theorem cycleShade_shift_iff (shadeGrid : Nat → Nat → RedShades.State)
    (offsetX offsetY west east south north : Nat)
    (shade : RedShades.Shade) :
    CycleShade
        (shiftQuarterGrid shadeGrid (2 * offsetX) (2 * offsetY))
        west east south north shade ↔
      CycleShade shadeGrid
        (offsetX + west) (offsetX + east)
        (offsetY + south) (offsetY + north) shade := by
  have hwest : 2 * offsetX + quarterWest west =
      quarterWest (offsetX + west) := by
    simp [quarterWest]
    omega
  have heast : 2 * offsetX + quarterEast east =
      quarterEast (offsetX + east) := by
    simp [quarterEast]
    omega
  have hsouth : 2 * offsetY + quarterSouth south =
      quarterSouth (offsetY + south) := by
    simp [quarterSouth]
    omega
  have hnorth : 2 * offsetY + quarterNorth north =
      quarterNorth (offsetY + north) := by
    simp [quarterNorth]
    omega
  constructor
  · intro shaded
    constructor
    · simpa only [shiftQuarterGrid, hwest, hsouth] using shaded.southwest
    · simpa only [shiftQuarterGrid, heast, hsouth] using shaded.southeast
    · simpa only [shiftQuarterGrid, heast, hnorth] using shaded.northeast
    · simpa only [shiftQuarterGrid, hwest, hnorth] using shaded.northwest
  · intro shaded
    constructor
    · simpa only [shiftQuarterGrid, hwest, hsouth] using shaded.southwest
    · simpa only [shiftQuarterGrid, heast, hsouth] using shaded.southeast
    · simpa only [shiftQuarterGrid, heast, hnorth] using shaded.northeast
    · simpa only [shiftQuarterGrid, hwest, hnorth] using shaded.northwest

theorem isFreeRow_shift_iff (depth : Nat) (grid : Nat → Nat → Index)
    (shadeGrid : Nat → Nat → RedShades.State)
    (blockX blockY west east row : Nat) :
    IsFreeRow
        (iterateRefine depth (shiftGrid grid blockX blockY))
        (shiftQuarterGrid shadeGrid
          (2 ^ (depth + 1) * blockX) (2 ^ (depth + 1) * blockY))
        west east row ↔
      IsFreeRow (iterateRefine depth grid) shadeGrid
        (2 ^ depth * blockX + west) (2 ^ depth * blockX + east)
        (2 ^ (depth + 1) * blockY + row) := by
  let quarterOffsetX := 2 ^ (depth + 1) * blockX
  let quarterOffsetY := 2 ^ (depth + 1) * blockY
  let indexOffsetX := 2 ^ depth * blockX
  have hquarterOffsetX : quarterOffsetX = 2 * indexOffsetX := by
    dsimp [quarterOffsetX, indexOffsetX]
    rw [pow_succ]
    ac_rfl
  have hwestTranslate : quarterWest (indexOffsetX + west) =
      quarterOffsetX + quarterWest west := by
    simp [quarterWest, hquarterOffsetX]
    omega
  have heastTranslate : quarterEast (indexOffsetX + east) =
      quarterOffsetX + quarterEast east := by
    simp [quarterEast, hquarterOffsetX]
    omega
  have hscale : 2 ∣ 2 ^ (depth + 1) := dvd_pow_self 2 (by omega)
  have hquadrant (x y : Nat) :
      quadrantAt (quarterOffsetX + x) (quarterOffsetY + y) =
        quadrantAt x y := by
    exact quadrantAt_shift (2 ^ (depth + 1)) blockX blockY x y hscale
  constructor
  · intro free quarterX hwest heast
    let localX := quarterX - quarterOffsetX
    have hx : quarterOffsetX + localX = quarterX := by
      rw [hwestTranslate] at hwest
      dsimp [localX]
      omega
    have hlocalWest : quarterWest west < localX := by
      rw [hwestTranslate] at hwest
      dsimp [localX]
      omega
    have hlocalEast : localX < quarterEast east := by
      rw [heastTranslate] at heast
      dsimp [localX]
      omega
    have hfree := free localX hlocalWest hlocalEast
    rw [componentAt_iterateRefine_shift depth grid blockX blockY
      localX row] at hfree
    rw [← hquadrant localX row] at hfree
    simpa only [shiftQuarterGrid, quarterOffsetX, quarterOffsetY, hx] using hfree
  · intro free quarterX hwest heast
    have hfree := free (quarterOffsetX + quarterX) (by
      rw [hwestTranslate]
      omega) (by
      rw [heastTranslate]
      omega)
    rw [← componentAt_iterateRefine_shift depth grid blockX blockY
      quarterX row] at hfree
    rw [hquadrant quarterX row] at hfree
    simpa only [shiftQuarterGrid, quarterOffsetX, quarterOffsetY] using hfree

theorem isFreeColumn_shift_iff (depth : Nat) (grid : Nat → Nat → Index)
    (shadeGrid : Nat → Nat → RedShades.State)
    (blockX blockY south north column : Nat) :
    IsFreeColumn
        (iterateRefine depth (shiftGrid grid blockX blockY))
        (shiftQuarterGrid shadeGrid
          (2 ^ (depth + 1) * blockX) (2 ^ (depth + 1) * blockY))
        south north column ↔
      IsFreeColumn (iterateRefine depth grid) shadeGrid
        (2 ^ depth * blockY + south) (2 ^ depth * blockY + north)
        (2 ^ (depth + 1) * blockX + column) := by
  let quarterOffsetX := 2 ^ (depth + 1) * blockX
  let quarterOffsetY := 2 ^ (depth + 1) * blockY
  let indexOffsetY := 2 ^ depth * blockY
  have hquarterOffsetY : quarterOffsetY = 2 * indexOffsetY := by
    dsimp [quarterOffsetY, indexOffsetY]
    rw [pow_succ]
    ac_rfl
  have hsouthTranslate : quarterSouth (indexOffsetY + south) =
      quarterOffsetY + quarterSouth south := by
    simp [quarterSouth, hquarterOffsetY]
    omega
  have hnorthTranslate : quarterNorth (indexOffsetY + north) =
      quarterOffsetY + quarterNorth north := by
    simp [quarterNorth, hquarterOffsetY]
    omega
  have hscale : 2 ∣ 2 ^ (depth + 1) := dvd_pow_self 2 (by omega)
  have hquadrant (x y : Nat) :
      quadrantAt (quarterOffsetX + x) (quarterOffsetY + y) =
        quadrantAt x y := by
    exact quadrantAt_shift (2 ^ (depth + 1)) blockX blockY x y hscale
  constructor
  · intro free quarterY hsouth hnorth
    let localY := quarterY - quarterOffsetY
    have hy : quarterOffsetY + localY = quarterY := by
      rw [hsouthTranslate] at hsouth
      dsimp [localY]
      omega
    have hlocalSouth : quarterSouth south < localY := by
      rw [hsouthTranslate] at hsouth
      dsimp [localY]
      omega
    have hlocalNorth : localY < quarterNorth north := by
      rw [hnorthTranslate] at hnorth
      dsimp [localY]
      omega
    have hfree := free localY hlocalSouth hlocalNorth
    rw [componentAt_iterateRefine_shift depth grid blockX blockY
      column localY] at hfree
    rw [← hquadrant column localY] at hfree
    simpa only [shiftQuarterGrid, quarterOffsetX, quarterOffsetY, hy] using hfree
  · intro free quarterY hsouth hnorth
    have hfree := free (quarterOffsetY + quarterY) (by
      rw [hsouthTranslate]
      omega) (by
      rw [hnorthTranslate]
      omega)
    rw [← componentAt_iterateRefine_shift depth grid blockX blockY
      column quarterY] at hfree
    rw [hquadrant column quarterY] at hfree
    simpa only [shiftQuarterGrid, quarterOffsetX, quarterOffsetY] using hfree

end ShadedFreeLineTranslation
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
