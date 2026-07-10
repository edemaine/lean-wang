/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104SignalScaffold

/-!
Decode a plane tiling combined with the concrete signal scaffold.

The decoder retains both product layers. Its scaffold layer is a valid signal
tiling and therefore yields a corrected-Ollinger hierarchy. At every clear
site the retained payload belongs to the supplied tileset, and at the
distinguished clear corner it equals the supplied seed.
-/

noncomputable section

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace Signals
namespace CombinedPlaneDecode

open Quarters QuarterRegrouping ParentPlane

set_option maxRecDepth 20000

theorem exists_base_payload {T : TileSet} {seed : WangTile}
    (wang : TileIn (combineWithScaffold scaffold T seed)) :
    ∃ base : TileIn tileSet, ∃ payload : WangTile,
      (isClear base.1 = true →
        payload ∈ T ∧ (base.1 = cornerTile → payload = seed)) ∧
      WangTile.product base.1 payload = wang.1 := by
  rcases mem_combineWithScaffold_iff.1 wang.2 with
    ⟨base, hbase, payload, hactive, _hinactive, hproduct⟩
  have hbase' : base ∈ tileSet := by
    simpa only [scaffold_tiles] using hbase
  refine ⟨⟨base, hbase'⟩, payload, ?_, hproduct⟩
  intro hclear
  have hscaffoldActive : scaffold.active base = true := by
    simpa only [scaffold_active] using hclear
  have hpayload := hactive hscaffoldActive
  refine ⟨hpayload.1, ?_⟩
  intro hcorner
  exact hpayload.2 (by simpa only [scaffold_corner] using hcorner)

/-- Both decoded layers of a combined plane tiling. -/
structure Decoded {T : TileSet} {seed : WangTile}
    (x : Int × Int → TileIn (combineWithScaffold scaffold T seed)) where
  base : Int × Int → TileIn tileSet
  payload : Int × Int → WangTile
  product : ∀ p, WangTile.product (base p).1 (payload p) = (x p).1
  active_payload : ∀ p, isClear (base p).1 = true →
    payload p ∈ T ∧ ((base p).1 = cornerTile → payload p = seed)
  base_valid : ValidPlaneTiling tileSet base

@[irreducible] noncomputable def baseAt {T : TileSet} {seed : WangTile}
    (x : Int × Int → TileIn (combineWithScaffold scaffold T seed))
    (p : Int × Int) : TileIn tileSet :=
  Classical.choose (exists_base_payload (x p))

@[irreducible] noncomputable def payloadAt {T : TileSet} {seed : WangTile}
    (x : Int × Int → TileIn (combineWithScaffold scaffold T seed))
    (p : Int × Int) : WangTile :=
  Classical.choose (Classical.choose_spec (exists_base_payload (x p)))

theorem baseAt_active_payload {T : TileSet} {seed : WangTile}
    (x : Int × Int → TileIn (combineWithScaffold scaffold T seed))
    (p : Int × Int) :
    isClear (baseAt x p).1 = true →
      payloadAt x p ∈ T ∧ ((baseAt x p).1 = cornerTile → payloadAt x p = seed) := by
  unfold baseAt payloadAt
  exact (Classical.choose_spec
    (Classical.choose_spec (exists_base_payload (x p)))).1

theorem baseAt_product {T : TileSet} {seed : WangTile}
    (x : Int × Int → TileIn (combineWithScaffold scaffold T seed))
    (p : Int × Int) :
    WangTile.product (baseAt x p).1 (payloadAt x p) = (x p).1 := by
  unfold baseAt payloadAt
  exact (Classical.choose_spec
    (Classical.choose_spec (exists_base_payload (x p)))).2

theorem baseAt_valid {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold scaffold T seed)}
    (hx : ValidPlaneTiling (combineWithScaffold scaffold T seed) x) :
    ValidPlaneTiling tileSet (baseAt x) := by
  constructor
  · intro p
    have hproduct : WangTile.HMatches
        (WangTile.product (baseAt x p).1 (payloadAt x p))
        (WangTile.product
          (baseAt x (p.1 + 1, p.2)).1
          (payloadAt x (p.1 + 1, p.2))) := by
      rw [baseAt_product, baseAt_product]
      exact hx.1 p
    exact (WangTile.HMatches_product_iff _ _ _ _).1 hproduct |>.1
  · intro p
    have hproduct : WangTile.VMatches
        (WangTile.product (baseAt x p).1 (payloadAt x p))
        (WangTile.product
          (baseAt x (p.1, p.2 + 1)).1
          (payloadAt x (p.1, p.2 + 1))) := by
      rw [baseAt_product, baseAt_product]
      exact hx.2 p
    exact (WangTile.VMatches_product_iff _ _ _ _).1 hproduct |>.1

/-- Decode a valid combined plane while retaining its payload layer. -/
noncomputable def decode {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold scaffold T seed)}
    (hx : ValidPlaneTiling (combineWithScaffold scaffold T seed) x) :
    Decoded x where
  base := baseAt x
  payload := payloadAt x
  product := baseAt_product x
  active_payload := baseAt_active_payload x
  base_valid := baseAt_valid hx

namespace Decoded

variable {T : TileSet} {seed : WangTile}
  {x : Int × Int → TileIn (combineWithScaffold scaffold T seed)}

def quarter (decoded : Decoded x) : QuarterPlane :=
  quarterPlane decoded.base

theorem quarter_valid (decoded : Decoded x) :
    ValidQuarterPlane decoded.quarter :=
  quarterPlane_valid decoded.base_valid

noncomputable def quarterOrigin (decoded : Decoded x) : Int × Int :=
  Classical.choose (exists_southwest_origin decoded.quarter_valid)

theorem quarterOrigin_phase (decoded : Decoded x) :
    phaseAt decoded.quarter decoded.quarterOrigin = .southwest :=
  Classical.choose_spec (exists_southwest_origin decoded.quarter_valid)

def parent (decoded : Decoded x) : Desubstitution.IndexPlane :=
  macroPlane decoded.quarter decoded.quarterOrigin

theorem parent_valid (decoded : Decoded x) :
    Desubstitution.ValidIndexPlane decoded.parent :=
  QuarterPlaneDecode.macroPlane_valid
    decoded.quarter_valid decoded.quarterOrigin_phase

def hierarchyBase (decoded : Decoded x) : Hierarchy.ValidPlane :=
  ⟨decoded.parent, decoded.parent_valid⟩

noncomputable def tower (decoded : Decoded x) :
    Hierarchy.Tower decoded.hierarchyBase :=
  Hierarchy.tower decoded.hierarchyBase

theorem quarter_blocks (decoded : Decoded x) (k : Int × Int) :
    decoded.quarter (blockOrigin decoded.quarterOrigin k) =
        (decoded.parent k, .southwest) ∧
      decoded.quarter (Desubstitution.shift
        (blockOrigin decoded.quarterOrigin k) 1 0) =
          (decoded.parent k, .southeast) ∧
      decoded.quarter (Desubstitution.shift
        (blockOrigin decoded.quarterOrigin k) 0 1) =
          (decoded.parent k, .northwest) ∧
      decoded.quarter (Desubstitution.shift
        (blockOrigin decoded.quarterOrigin k) 1 1) =
          (decoded.parent k, .northeast) :=
  block_spec decoded.quarter_valid decoded.quarterOrigin_phase k

end Decoded

end CombinedPlaneDecode
end Signals
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
