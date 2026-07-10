/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104StableTilesCertificate

/-! Propositional interface to the substitution-derived finite certificate. -/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104

theorem derivedTile_mem_derivedTileSet (depth : Nat) (index : Index) :
    derivedTile depth index ∈ derivedTileSet depth := by
  simp only [derivedTileSet, List.mem_eraseDups]
  exact List.mem_map.2 ⟨index, List.mem_finRange index, rfl⟩

theorem derivedChildRectangle_valid_one (parent : Index) :
    ValidRectangle (derivedTileSet 1) (derivedChildRectangle 1 parent) := by
  have hparent := List.all_eq_true.1 depthOneStableAndValid.2.2
    parent (List.mem_finRange parent)
  exact of_decide_eq_true hparent

theorem hMatches_derived_one_iff_child
    (left right : Index) :
    WangTile.HMatches (derivedTile 1 left) (derivedTile 1 right) ↔
      DerivedChildHMatches 1 left right := by
  have hleft := List.all_eq_true.1 depthOneStableAndValid.1
    left (List.mem_finRange left)
  have hright := List.all_eq_true.1 hleft right (List.mem_finRange right)
  exact of_decide_eq_true hright

theorem vMatches_derived_one_iff_child
    (lower upper : Index) :
    WangTile.VMatches (derivedTile 1 lower) (derivedTile 1 upper) ↔
      DerivedChildVMatches 1 lower upper := by
  have hlower := List.all_eq_true.1 depthOneStableAndValid.2.1
    lower (List.mem_finRange lower)
  have hupper := List.all_eq_true.1 hlower upper (List.mem_finRange upper)
  exact of_decide_eq_true hupper

end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
