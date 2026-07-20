/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.ShadedSubstitutionPlane

/-!
# Canonical carrier geometry in shaded substitution squares

This module presents the routed roles of a canonical shaded supertile directly
in terms of its nearest-border interval paths.  It is the local interface used
by the recursive Cartesian-grid decomposition.
-/

noncomputable section

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace ShadedCarrierSquareGeometry

open ShadedSubstitution
open ShadedSubstitutionPlane

/-- Canonical horizontal signal on an edge of a supertile row. -/
def horizontalEdge (level : Nat) (root : Node) (y position : Nat) :
    Signals.Flow :=
  ShadedSignalRectangle.intervalEdge
    (fun x => rowInterior level root x y) (side level) position

/-- Canonical vertical signal on an edge of a supertile column. -/
def verticalEdge (level : Nat) (root : Node) (x position : Nat) :
    Signals.Flow :=
  ShadedSignalRectangle.intervalEdge
    (fun y => columnInterior level root x y) (side level) position

@[simp] theorem site_west (level : Nat) (root : Node) (x y : Nat) :
    (site level root x y).2.west = horizontalEdge level root y x := by
  rfl

@[simp] theorem site_east (level : Nat) (root : Node) (x y : Nat) :
    (site level root x y).2.east = horizontalEdge level root y (x + 1) := by
  rfl

@[simp] theorem site_south (level : Nat) (root : Node) (x y : Nat) :
    (site level root x y).2.south = verticalEdge level root x y := by
  rfl

@[simp] theorem site_north (level : Nat) (root : Node) (x y : Nat) :
    (site level root x y).2.north = verticalEdge level root x (y + 1) := by
  rfl

/-- A site belongs to a horizontal carrier exactly when its two horizontal
canonical signal edges are clear. -/
theorem isHorizontalCarrier_tileRectangle_iff
    (level : Nat) (root : Node) (i j : Fin (side level)) :
    (ShadedSignals.routedScaffold.role
      (tileRectangle level root i j)).isHorizontalCarrier = true ↔
      horizontalEdge level root j i = .none ∧
        horizontalEdge level root j (i.val + 1) = .none := by
  rw [routedRole_tileRectangle,
    ShadedSignals.isHorizontalCarrier_routeRole_tile_iff]
  rfl

/-- A site belongs to a vertical carrier exactly when its two vertical
canonical signal edges are clear. -/
theorem isVerticalCarrier_tileRectangle_iff
    (level : Nat) (root : Node) (i j : Fin (side level)) :
    (ShadedSignals.routedScaffold.role
      (tileRectangle level root i j)).isVerticalCarrier = true ↔
      verticalEdge level root i j = .none ∧
        verticalEdge level root i (j.val + 1) = .none := by
  rw [routedRole_tileRectangle,
    ShadedSignals.isVerticalCarrier_routeRole_tile_iff]
  rfl

end ShadedCarrierSquareGeometry
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang

end
