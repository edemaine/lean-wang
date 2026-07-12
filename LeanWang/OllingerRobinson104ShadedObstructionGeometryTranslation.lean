/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104ShadedObstructionGeometryBoundedSoundness

/-!
# Translation equivariance of obstruction geometry

Local geometry in a shifted refined block transports to the corresponding
absolute quarter coordinates.  This packages the coordinate arithmetic needed
to combine the depth-four audit with larger Robinson boards.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace ShadedObstructionGeometryTranslation

open RedCycles RedShadeCycles RedShadePaths RefinementTranslation
  ShadedFreeLineTranslation
  ShadedObstructionGeometry ShadedPlaneSignalGrid Signals.FreeCellLocal

set_option maxRecDepth 20000

theorem selectedHorizontal_shift
    (depth : Nat) (grid : Nat → Nat → Index)
    (shadeGrid : Nat → Nat → RedShades.State)
    (blockX blockY x y : Nat) :
    ShadedSignals.selectedHorizontalFor
        (componentAt (iterateRefine depth (shiftGrid grid blockX blockY)) x y)
        (quadrantAt x y)
        (shiftQuarterGrid shadeGrid
          (2 ^ (depth + 1) * blockX) (2 ^ (depth + 1) * blockY) x y) =
      ShadedSignals.selectedHorizontalFor
        (componentAt (iterateRefine depth grid)
          (2 ^ (depth + 1) * blockX + x)
          (2 ^ (depth + 1) * blockY + y))
        (quadrantAt (2 ^ (depth + 1) * blockX + x)
          (2 ^ (depth + 1) * blockY + y))
        (shadeGrid (2 ^ (depth + 1) * blockX + x)
          (2 ^ (depth + 1) * blockY + y)) := by
  rw [componentAt_iterateRefine_shift]
  rw [quadrantAt_shift (2 ^ (depth + 1)) blockX blockY x y
    (dvd_pow_self 2 (by omega))]
  rfl

theorem selectedVertical_shift
    (depth : Nat) (grid : Nat → Nat → Index)
    (shadeGrid : Nat → Nat → RedShades.State)
    (blockX blockY x y : Nat) :
    ShadedSignals.selectedVerticalFor
        (componentAt (iterateRefine depth (shiftGrid grid blockX blockY)) x y)
        (quadrantAt x y)
        (shiftQuarterGrid shadeGrid
          (2 ^ (depth + 1) * blockX) (2 ^ (depth + 1) * blockY) x y) =
      ShadedSignals.selectedVerticalFor
        (componentAt (iterateRefine depth grid)
          (2 ^ (depth + 1) * blockX + x)
          (2 ^ (depth + 1) * blockY + y))
        (quadrantAt (2 ^ (depth + 1) * blockX + x)
          (2 ^ (depth + 1) * blockY + y))
        (shadeGrid (2 ^ (depth + 1) * blockX + x)
          (2 ^ (depth + 1) * blockY + y)) := by
  rw [componentAt_iterateRefine_shift]
  rw [quadrantAt_shift (2 ^ (depth + 1)) blockX blockY x y
    (dvd_pow_self 2 (by omega))]
  rfl

set_option maxHeartbeats 1000000 in
-- Four translated existential witnesses require repeated offset normalization.
theorem Geometry.translate
    {depth : Nat} {grid : Nat → Nat → Index}
    {shadeGrid : Nat → Nat → RedShades.State}
    {blockX blockY west east south north : Nat}
    (geometry : Geometry
      (iterateRefine depth (shiftGrid grid blockX blockY))
      (shiftQuarterGrid shadeGrid
        (2 ^ (depth + 1) * blockX) (2 ^ (depth + 1) * blockY))
      west east south north) :
    Geometry (iterateRefine depth grid) shadeGrid
      (2 ^ depth * blockX + west) (2 ^ depth * blockX + east)
      (2 ^ depth * blockY + south) (2 ^ depth * blockY + north) := by
  let quarterOffsetX := 2 ^ (depth + 1) * blockX
  let quarterOffsetY := 2 ^ (depth + 1) * blockY
  let indexOffsetX := 2 ^ depth * blockX
  let indexOffsetY := 2 ^ depth * blockY
  have hquarterX : quarterOffsetX = 2 * indexOffsetX := by
    dsimp [quarterOffsetX, indexOffsetX]
    rw [pow_succ]
    ac_rfl
  have hquarterY : quarterOffsetY = 2 * indexOffsetY := by
    dsimp [quarterOffsetY, indexOffsetY]
    rw [pow_succ]
    ac_rfl
  have hwest : quarterWest (indexOffsetX + west) =
      quarterOffsetX + quarterWest west := by
    simp [quarterWest, hquarterX]
    omega
  have heast : quarterEast (indexOffsetX + east) =
      quarterOffsetX + quarterEast east := by
    simp [quarterEast, hquarterX]
    omega
  have hsouth : quarterSouth (indexOffsetY + south) =
      quarterOffsetY + quarterSouth south := by
    simp [quarterSouth, hquarterY]
    omega
  have hnorth : quarterNorth (indexOffsetY + north) =
      quarterOffsetY + quarterNorth north := by
    simp [quarterNorth, hquarterY]
    omega
  constructor
  · intro column row hcolumnWest hcolumnEast hrowSouth hrowNorth
      hfreeRow hnotFreeColumn
    let localX := column - quarterOffsetX
    let localY := row - quarterOffsetY
    have hx : quarterOffsetX + localX = column := by
      dsimp [localX]
      rw [hwest] at hcolumnWest
      omega
    have hy : quarterOffsetY + localY = row := by
      dsimp [localY]
      rw [hsouth] at hrowSouth
      omega
    have localFreeRow : IsFreeRow
        (iterateRefine depth (shiftGrid grid blockX blockY))
        (shiftQuarterGrid shadeGrid quarterOffsetX quarterOffsetY)
        west east localY := by
      apply (isFreeRow_shift_iff depth grid shadeGrid blockX blockY
        west east localY).2
      simpa only [quarterOffsetX, quarterOffsetY, indexOffsetX, hx, hy] using
        hfreeRow
    have localNotFreeColumn : ¬IsFreeColumn
        (iterateRefine depth (shiftGrid grid blockX blockY))
        (shiftQuarterGrid shadeGrid quarterOffsetX quarterOffsetY)
        south north localX := by
      intro localFree
      apply hnotFreeColumn
      have globalFree := (isFreeColumn_shift_iff depth grid shadeGrid blockX blockY
        south north localX).1 localFree
      simpa only [quarterOffsetX, quarterOffsetY, indexOffsetY, hx, hy] using
        globalFree
    have localResult := geometry.verticalBoundary
      (by rw [hwest] at hcolumnWest; dsimp [localX]; omega)
      (by rw [heast] at hcolumnEast; dsimp [localX]; omega)
      (by rw [hsouth] at hrowSouth; dsimp [localY]; omega)
      (by rw [hnorth] at hrowNorth; dsimp [localY]; omega)
      localFreeRow localNotFreeColumn
    rcases localResult with hat | hupper | hlower
    · exact Or.inl (by
        simpa only [quarterOffsetX, quarterOffsetY, hx, hy,
          selectedHorizontal_shift depth grid shadeGrid blockX blockY localX localY]
          using hat)
    · rcases hupper with ⟨boundary, hlocalY, hboundary, hselected, hbetween⟩
      refine Or.inr (Or.inl ⟨quarterOffsetY + boundary, by omega, ?_, ?_, ?_⟩)
      · rw [hnorth]
        omega
      · simpa only [quarterOffsetX, quarterOffsetY, hx,
          selectedHorizontal_shift depth grid shadeGrid blockX blockY localX boundary]
          using hselected
      · intro y hry hyb
        let localCoordinate := y - quarterOffsetY
        have hlocalEq : quarterOffsetY + localCoordinate = y := by omega
        have hnone := hbetween localCoordinate (by omega) (by omega)
        simpa only [quarterOffsetX, quarterOffsetY, hx, hlocalEq,
          selectedHorizontal_shift depth grid shadeGrid blockX blockY
            localX localCoordinate]
          using hnone
    · rcases hlower with ⟨boundary, hboundary, hlocalY, hselected, hbetween⟩
      refine Or.inr (Or.inr ⟨quarterOffsetY + boundary, ?_, by omega, ?_, ?_⟩)
      · rw [hsouth]
        omega
      · simpa only [quarterOffsetX, quarterOffsetY, hx,
          selectedHorizontal_shift depth grid shadeGrid blockX blockY localX boundary]
          using hselected
      · intro y hby hyr
        let localCoordinate := y - quarterOffsetY
        have hlocalEq : quarterOffsetY + localCoordinate = y := by omega
        have hnone := hbetween localCoordinate (by omega) (by omega)
        simpa only [quarterOffsetX, quarterOffsetY, hx, hlocalEq,
          selectedHorizontal_shift depth grid shadeGrid blockX blockY
            localX localCoordinate]
          using hnone
  · intro column row hcolumnWest hcolumnEast hrowSouth hrowNorth
      hfreeColumn hnotFreeRow
    let localX := column - quarterOffsetX
    let localY := row - quarterOffsetY
    have hx : quarterOffsetX + localX = column := by
      dsimp [localX]
      rw [hwest] at hcolumnWest
      omega
    have hy : quarterOffsetY + localY = row := by
      dsimp [localY]
      rw [hsouth] at hrowSouth
      omega
    have localFreeColumn : IsFreeColumn
        (iterateRefine depth (shiftGrid grid blockX blockY))
        (shiftQuarterGrid shadeGrid quarterOffsetX quarterOffsetY)
        south north localX := by
      apply (isFreeColumn_shift_iff depth grid shadeGrid blockX blockY
        south north localX).2
      simpa only [quarterOffsetX, quarterOffsetY, indexOffsetY, hx, hy] using
        hfreeColumn
    have localNotFreeRow : ¬IsFreeRow
        (iterateRefine depth (shiftGrid grid blockX blockY))
        (shiftQuarterGrid shadeGrid quarterOffsetX quarterOffsetY)
        west east localY := by
      intro localFree
      apply hnotFreeRow
      have globalFree := (isFreeRow_shift_iff depth grid shadeGrid blockX blockY
        west east localY).1 localFree
      simpa only [quarterOffsetX, quarterOffsetY, indexOffsetX, hx, hy] using
        globalFree
    have localResult := geometry.horizontalBoundary
      (by rw [hwest] at hcolumnWest; dsimp [localX]; omega)
      (by rw [heast] at hcolumnEast; dsimp [localX]; omega)
      (by rw [hsouth] at hrowSouth; dsimp [localY]; omega)
      (by rw [hnorth] at hrowNorth; dsimp [localY]; omega)
      localFreeColumn localNotFreeRow
    rcases localResult with hat | hright | hleft
    · exact Or.inl (by
        simpa only [quarterOffsetX, quarterOffsetY, hx, hy,
          selectedVertical_shift depth grid shadeGrid blockX blockY localX localY]
          using hat)
    · rcases hright with ⟨boundary, hlocalX, hboundary, hselected, hbetween⟩
      refine Or.inr (Or.inl ⟨quarterOffsetX + boundary, by omega, ?_, ?_, ?_⟩)
      · rw [heast]
        omega
      · simpa only [quarterOffsetX, quarterOffsetY, hy,
          selectedVertical_shift depth grid shadeGrid blockX blockY boundary localY]
          using hselected
      · intro x hcx hxb
        let localCoordinate := x - quarterOffsetX
        have hlocalEq : quarterOffsetX + localCoordinate = x := by omega
        have hnone := hbetween localCoordinate (by omega) (by omega)
        simpa only [quarterOffsetX, quarterOffsetY, hy, hlocalEq,
          selectedVertical_shift depth grid shadeGrid blockX blockY
            localCoordinate localY]
          using hnone
    · rcases hleft with ⟨boundary, hboundary, hlocalX, hselected, hbetween⟩
      refine Or.inr (Or.inr ⟨quarterOffsetX + boundary, ?_, by omega, ?_, ?_⟩)
      · rw [hwest]
        omega
      · simpa only [quarterOffsetX, quarterOffsetY, hy,
          selectedVertical_shift depth grid shadeGrid blockX blockY boundary localY]
          using hselected
      · intro x hbx hxc
        let localCoordinate := x - quarterOffsetX
        have hlocalEq : quarterOffsetX + localCoordinate = x := by omega
        have hnone := hbetween localCoordinate (by omega) (by omega)
        simpa only [quarterOffsetX, quarterOffsetY, hy, hlocalEq,
          selectedVertical_shift depth grid shadeGrid blockX blockY
            localCoordinate localY]
          using hnone

/-- Every coarse coordinate contributes an absolute audited depth-four board. -/
theorem geometry_at_block
    (grid : Nat → Nat → Index)
    {shadeGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid (iterateRefine 4 grid) shadeGrid)
    (blockX blockY : Nat) :
    Geometry (iterateRefine 4 grid) shadeGrid
      (16 * blockX + 4) (16 * blockX + 12)
      (16 * blockY + 4) (16 * blockY + 12) := by
  have localGeometry :=
    ShadedObstructionGeometryBoundedSoundness.geometry_shift
      grid valid blockX blockY
  have translated := Geometry.translate localGeometry
  norm_num at translated
  exact translated

end ShadedObstructionGeometryTranslation
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
