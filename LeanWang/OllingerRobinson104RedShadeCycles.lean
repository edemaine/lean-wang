/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104RedShadePaths

/-!
Uniform red-wire shade on the canonical depth-two board.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace RedShadeCycles

open RedCycles Signals.FreeCellLocal RedShadePaths

set_option maxRecDepth 20000

def fixedGrid (parent : Index) : Nat → Nat → Index :=
  iterateRefine 2 (fun _ _ => parent)

/-- Quarter-level red-path geometry of the universal depth-two board. -/
structure FixedGeometry (parent : Index) : Prop where
  southwestEast : RedShades.cornerEast
    (components (fixedGrid parent (3 / 2) (3 / 2))).2.1
      (quadrantAt 3 3) = true
  southwestNorth : RedShades.cornerNorth
    (components (fixedGrid parent (3 / 2) (3 / 2))).2.1
      (quadrantAt 3 3) = true
  southeastWest : RedShades.cornerWest
    (componentAt (fixedGrid parent) 6 3) (quadrantAt 6 3) = true
  southeastNorth : RedShades.cornerNorth
    (componentAt (fixedGrid parent) 6 3) (quadrantAt 6 3) = true
  northeastWest : RedShades.cornerWest
    (componentAt (fixedGrid parent) 6 6) (quadrantAt 6 6) = true
  northeastSouth : RedShades.cornerSouth
    (componentAt (fixedGrid parent) 6 6) (quadrantAt 6 6) = true
  northwestEast : RedShades.cornerEast
    (componentAt (fixedGrid parent) 3 6) (quadrantAt 3 6) = true
  northwestSouth : RedShades.cornerSouth
    (componentAt (fixedGrid parent) 3 6) (quadrantAt 3 6) = true
  south4 : RedShades.hasHorizontal
    (componentAt (fixedGrid parent) 4 3) (quadrantAt 4 3) = true
  south5 : RedShades.hasHorizontal
    (componentAt (fixedGrid parent) 5 3) (quadrantAt 5 3) = true
  north4 : RedShades.hasHorizontal
    (componentAt (fixedGrid parent) 4 6) (quadrantAt 4 6) = true
  north5 : RedShades.hasHorizontal
    (componentAt (fixedGrid parent) 5 6) (quadrantAt 5 6) = true
  west4 : RedShades.hasVertical
    (componentAt (fixedGrid parent) 3 4) (quadrantAt 3 4) = true
  west5 : RedShades.hasVertical
    (componentAt (fixedGrid parent) 3 5) (quadrantAt 3 5) = true
  east4 : RedShades.hasVertical
    (componentAt (fixedGrid parent) 6 4) (quadrantAt 6 4) = true
  east5 : RedShades.hasVertical
    (componentAt (fixedGrid parent) 6 5) (quadrantAt 6 5) = true

set_option linter.style.nativeDecide false in
theorem fixedGeometry (parent : Index) : FixedGeometry parent := by
  refine {
    southwestEast := ?_
    southwestNorth := ?_
    southeastWest := ?_
    southeastNorth := ?_
    northeastWest := ?_
    northeastSouth := ?_
    northwestEast := ?_
    northwestSouth := ?_
    south4 := ?_
    south5 := ?_
    north4 := ?_
    north5 := ?_
    west4 := ?_
    west5 := ?_
    east4 := ?_
    east5 := ?_
  }
  all_goals revert parent; native_decide

/-- Corner shades carried by one canonical depth-two board. -/
structure FixedCycleShade (stateGrid : Nat → Nat → RedShades.State)
    (shade : RedShades.Shade) : Prop where
  southwest : (stateGrid 3 3).east = some shade
  southeast : (stateGrid 6 3).west = some shade
  northeast : (stateGrid 6 6).west = some shade
  northwest : (stateGrid 3 6).east = some shade

/-- A shade on one edge of the canonical board propagates to every corner. -/
theorem fixedCycleShade (parent : Index)
    {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid (fixedGrid parent) stateGrid)
    (shade : RedShades.Shade)
    (hshade : (stateGrid 3 3).east = some shade) :
    FixedCycleShade stateGrid shade := by
  have geometry := fixedGeometry parent
  exact (by
    refine ⟨hshade, ?_, ?_, ?_⟩
    · calc
        (stateGrid 6 3).west = (stateGrid 5 3).east :=
          (valid.hmatch 5 3).symm
        _ = (stateGrid 5 3).west :=
          (valid.horizontal_eq 5 3 geometry.south5).symm
        _ = (stateGrid 4 3).east := (valid.hmatch 4 3).symm
        _ = (stateGrid 4 3).west :=
          (valid.horizontal_eq 4 3 geometry.south4).symm
        _ = (stateGrid 3 3).east := (valid.hmatch 3 3).symm
        _ = some shade := hshade
    · have hseNorth : (stateGrid 6 3).north = some shade := by
        rw [← valid.west_north_corner_eq 6 3
          geometry.southeastWest geometry.southeastNorth]
        exact (by
          calc
            (stateGrid 6 3).west = (stateGrid 5 3).east :=
              (valid.hmatch 5 3).symm
            _ = (stateGrid 5 3).west :=
              (valid.horizontal_eq 5 3 geometry.south5).symm
            _ = (stateGrid 4 3).east := (valid.hmatch 4 3).symm
            _ = (stateGrid 4 3).west :=
              (valid.horizontal_eq 4 3 geometry.south4).symm
            _ = (stateGrid 3 3).east := (valid.hmatch 3 3).symm
            _ = some shade := hshade)
      calc
        (stateGrid 6 6).west = (stateGrid 6 6).south :=
          valid.west_south_corner_eq 6 6
            geometry.northeastWest geometry.northeastSouth
        _ = (stateGrid 6 5).north := (valid.vmatch 6 5).symm
        _ = (stateGrid 6 5).south :=
          (valid.vertical_eq 6 5 geometry.east5).symm
        _ = (stateGrid 6 4).north := (valid.vmatch 6 4).symm
        _ = (stateGrid 6 4).south :=
          (valid.vertical_eq 6 4 geometry.east4).symm
        _ = (stateGrid 6 3).north := (valid.vmatch 6 3).symm
        _ = some shade := hseNorth
    · have hneWest : (stateGrid 6 6).west = some shade := by
        calc
          (stateGrid 6 6).west = (stateGrid 6 6).south :=
            valid.west_south_corner_eq 6 6
              geometry.northeastWest geometry.northeastSouth
          _ = (stateGrid 6 5).north := (valid.vmatch 6 5).symm
          _ = (stateGrid 6 5).south :=
            (valid.vertical_eq 6 5 geometry.east5).symm
          _ = (stateGrid 6 4).north := (valid.vmatch 6 4).symm
          _ = (stateGrid 6 4).south :=
            (valid.vertical_eq 6 4 geometry.east4).symm
          _ = (stateGrid 6 3).north := (valid.vmatch 6 3).symm
          _ = (stateGrid 6 3).west :=
            (valid.west_north_corner_eq 6 3
              geometry.southeastWest geometry.southeastNorth).symm
          _ = (stateGrid 5 3).east := (valid.hmatch 5 3).symm
          _ = (stateGrid 5 3).west :=
            (valid.horizontal_eq 5 3 geometry.south5).symm
          _ = (stateGrid 4 3).east := (valid.hmatch 4 3).symm
          _ = (stateGrid 4 3).west :=
            (valid.horizontal_eq 4 3 geometry.south4).symm
          _ = (stateGrid 3 3).east := (valid.hmatch 3 3).symm
          _ = some shade := hshade
      calc
        (stateGrid 3 6).east = (stateGrid 4 6).west := valid.hmatch 3 6
        _ = (stateGrid 4 6).east :=
          valid.horizontal_eq 4 6 geometry.north4
        _ = (stateGrid 5 6).west := valid.hmatch 4 6
        _ = (stateGrid 5 6).east :=
          valid.horizontal_eq 5 6 geometry.north5
        _ = (stateGrid 6 6).west := valid.hmatch 5 6
        _ = some shade := hneWest
  )

end RedShadeCycles
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
