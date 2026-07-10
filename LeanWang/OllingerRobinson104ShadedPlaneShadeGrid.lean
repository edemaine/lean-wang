/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104ShadedRoutedPlaneDecode
import LeanWang.OllingerRobinson104RedShadePaths
import LeanWang.OllingerRobinson104RedShadeCrossingBoards
import LeanWang.OllingerRobinson104IteratedEmbedding

/-!
Embed the shade layer of a final routed product plane as valid natural quarter
grids below arbitrary hierarchy coordinates.
-/

noncomputable section

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace ShadedPlaneShadeGrid

open Desubstitution ParentPlane HierarchyEmbedding RedCycles
  Signals.FreeCellLocal RedShadePaths

set_option maxRecDepth 20000

variable {T : TileSet} {seed : WangTile}
  {x : Int × Int → TileIn
    (combineWithRoutedScaffold ShadedSignals.routedScaffold T seed)}

def quarterGridOrigin (decoded : ShadedRoutedPlaneDecode.Decoded x)
    (parentOrigin : Int × Int) : Int × Int :=
  blockOrigin decoded.quarterOrigin parentOrigin

def point (decoded : ShadedRoutedPlaneDecode.Decoded x)
    (parentOrigin : Int × Int) (quarterX quarterY : Nat) : Int × Int :=
  shift (quarterGridOrigin decoded parentOrigin) quarterX quarterY

theorem quarter_at_point (decoded : ShadedRoutedPlaneDecode.Decoded x)
    (parentOrigin : Int × Int) (quarterX quarterY : Nat) :
    decoded.quarter (point decoded parentOrigin quarterX quarterY) =
      (natGridAt decoded.parent parentOrigin
          (quarterX / 2) (quarterY / 2),
        quadrantAt quarterX quarterY) := by
  let parentCoordinate :=
    shift parentOrigin (quarterX / 2 : Nat) (quarterY / 2 : Nat)
  have hcoordinate := childCoordinate decoded.quarterOrigin parentOrigin
    quarterX quarterY
  have hblocks := decoded.quarter_blocks parentCoordinate
  have hxmod : quarterX % 2 = 0 ∨ quarterX % 2 = 1 := by
    have := Nat.mod_lt quarterX (by decide : 0 < 2)
    omega
  have hymod : quarterY % 2 = 0 ∨ quarterY % 2 = 1 := by
    have := Nat.mod_lt quarterY (by decide : 0 < 2)
    omega
  rw [show point decoded parentOrigin quarterX quarterY =
      shift (blockOrigin decoded.quarterOrigin parentCoordinate)
        (quarterX % 2 : Nat) (quarterY % 2 : Nat) by
    simpa only [point, quarterGridOrigin, parentCoordinate] using hcoordinate]
  rcases hxmod with hxmod | hxmod <;> rcases hymod with hymod | hymod
  · simpa [parentCoordinate, natGridAt, quadrantAt, Quadrant.ofBits,
      hxmod, hymod, shift] using hblocks.1
  · simpa [parentCoordinate, natGridAt, quadrantAt, Quadrant.ofBits,
      hxmod, hymod] using hblocks.2.2.1
  · simpa [parentCoordinate, natGridAt, quadrantAt, Quadrant.ofBits,
      hxmod, hymod] using hblocks.2.1
  · simpa [parentCoordinate, natGridAt, quadrantAt, Quadrant.ofBits,
      hxmod, hymod] using hblocks.2.2.2

def stateGrid (decoded : ShadedRoutedPlaneDecode.Decoded x)
    (parentOrigin : Int × Int) : Nat → Nat → RedShades.State :=
  fun quarterX quarterY =>
    RedShades.shadePlane decoded.shadeBase
      (point decoded parentOrigin quarterX quarterY)

theorem stateGrid_valid (decoded : ShadedRoutedPlaneDecode.Decoded x)
    (parentOrigin : Int × Int) :
    ValidShadeGrid (natGridAt decoded.parent parentOrigin)
      (stateGrid decoded parentOrigin) := by
  constructor
  · intro quarterX quarterY
    have hallowed := RedShades.plane_locallyAllowed decoded.shadeBase
      (point decoded parentOrigin quarterX quarterY)
    change RedShades.locallyAllowed
      (decoded.quarter (point decoded parentOrigin quarterX quarterY))
      (RedShades.shadePlane decoded.shadeBase
        (point decoded parentOrigin quarterX quarterY)) = true at hallowed
    rw [quarter_at_point decoded parentOrigin quarterX quarterY] at hallowed
    simpa only [stateGrid] using hallowed
  · intro quarterX quarterY
    have hmatch := RedShades.shadePlane_hmatch decoded.shadeBase_valid
      (point decoded parentOrigin quarterX quarterY)
    have hpoint : point decoded parentOrigin (quarterX + 1) quarterY =
        ((point decoded parentOrigin quarterX quarterY).1 + 1,
          (point decoded parentOrigin quarterX quarterY).2) := by
      simp [point, quarterGridOrigin, shift]
      omega
    simpa only [stateGrid, hpoint] using hmatch
  · intro quarterX quarterY
    have hmatch := RedShades.shadePlane_vmatch decoded.shadeBase_valid
      (point decoded parentOrigin quarterX quarterY)
    have hpoint : point decoded parentOrigin quarterX (quarterY + 1) =
        ((point decoded parentOrigin quarterX quarterY).1,
          (point decoded parentOrigin quarterX quarterY).2 + 1) := by
      simp [point, quarterGridOrigin, shift]
      omega
    simpa only [stateGrid, hpoint] using hmatch

def coarseGrid (decoded : ShadedRoutedPlaneDecode.Decoded x)
    (depth : Nat) (coarseOrigin : Int × Int) : Nat → Nat → Index :=
  natGridAt (decoded.tower.plane depth).tiling coarseOrigin

def fineParentOrigin (decoded : ShadedRoutedPlaneDecode.Decoded x)
    (depth : Nat) (coarseOrigin : Int × Int) : Int × Int :=
  descendOrigin decoded.tower 0 depth coarseOrigin

theorem parentGrid_eq_iterateRefine
    (decoded : ShadedRoutedPlaneDecode.Decoded x)
    (depth : Nat) (coarseOrigin : Int × Int) :
    natGridAt decoded.parent (fineParentOrigin decoded depth coarseOrigin) =
      iterateRefine depth (coarseGrid decoded depth coarseOrigin) := by
  have h := HierarchyEmbedding.Tower.natGridAt_descendOrigin
    decoded.tower depth 0 coarseOrigin
  rw [decoded.tower.zero] at h
  simpa only [ShadedRoutedPlaneDecode.Decoded.hierarchyBase, Nat.zero_add,
    fineParentOrigin, coarseGrid] using h

theorem refined_stateGrid_valid
    (decoded : ShadedRoutedPlaneDecode.Decoded x)
    (depth : Nat) (coarseOrigin : Int × Int) :
    ValidShadeGrid (iterateRefine depth
        (coarseGrid decoded depth coarseOrigin))
      (stateGrid decoded (fineParentOrigin decoded depth coarseOrigin)) := by
  rw [← parentGrid_eq_iterateRefine decoded depth coarseOrigin]
  exact stateGrid_valid decoded _

/-- Every final routed product plane has light boards at unbounded scales. -/
theorem hasLightCycleAtLevel
    (decoded : ShadedRoutedPlaneDecode.Decoded x)
    {level : Nat} (hlevel : 1 ≤ level) (coarseOrigin : Int × Int) :
    RedShadeCrossingBoards.HasLightCycleAtLevel
      (stateGrid decoded
        (fineParentOrigin decoded (level + 2) coarseOrigin)) level := by
  exact RedShadeCrossingBoards.hasLightCycleAtLevel
    (coarseGrid decoded (level + 2) coarseOrigin) hlevel
    (refined_stateGrid_valid decoded (level + 2) coarseOrigin)

end ShadedPlaneShadeGrid
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
