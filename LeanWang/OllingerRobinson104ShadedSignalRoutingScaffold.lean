/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104ShadedSignals
import LeanWang.OllingerRobinson104SignalRoutingScaffold

/-!
Role-sensitive payload routing over the corrected shaded obstruction layer.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace ShadedSignals

open Signals

set_option maxRecDepth 20000

theorem isClear_tile_eq_true_iff (site : Site) :
    isClear (tile site) = true ↔ site.2 = clearState := by
  rcases site with ⟨base, signal⟩
  rcases signal with ⟨west, east, south, north⟩
  cases west <;> cases east <;> cases south <;> cases north <;>
    simp [isClear, edgeFlowCode, tile, Signals.State.tile, Flow.code,
      clearState, WangTile.product]

theorem routeRole_tile_eq_active_iff (site : Site) :
    routeRole (tile site) = .active ↔ site.2 = clearState := by
  rw [Signals.routeRole_eq_active_iff, isClear_tile_eq_true_iff]

theorem routeRole_tile_ne_corner (site : Site) :
    routeRole (tile site) ≠ .corner :=
  Signals.routeRole_ne_corner _

/-- Final shaded Robinson scaffold with directional payload channels. -/
@[irreducible] def routedScaffold : RoutedScaffold where
  tiles := tileSet
  role := routeRole
  role_primrec := Signals.routeRole_primrec

@[simp] theorem routedScaffold_tiles : routedScaffold.tiles = tileSet := by
  unfold routedScaffold
  rfl

@[simp] theorem routedScaffold_role : routedScaffold.role = routeRole := by
  unfold routedScaffold
  rfl

end ShadedSignals
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
