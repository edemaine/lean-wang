/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Scaffold.Routed

/-!
Decode plane tilings of a role-sensitive routed scaffold product.

The decoder retains both product layers, proves that both layers match across
the plane, and exposes the payload restriction imposed by every routing role.
-/

noncomputable section

namespace LeanWang
namespace RoutedPlaneDecode

variable {S : RoutedScaffold} {T : TileSet} {seed : WangTile}

def baseAt
    (x : Int × Int → TileIn (combineWithRoutedScaffold S T seed))
    (p : Int × Int) : TileIn S.tiles :=
  ⟨(x p).1.productBase, by
    rcases mem_combineWithRoutedScaffold_iff.1 (x p).2 with
      ⟨base, hbase, payload, _hpayload, hproduct⟩
    simpa [← hproduct] using hbase⟩

def payloadAt
    (x : Int × Int → TileIn (combineWithRoutedScaffold S T seed))
    (p : Int × Int) : WangTile :=
  (x p).1.productPayload

theorem payloadAt_allowed
    (x : Int × Int → TileIn (combineWithRoutedScaffold S T seed))
    (p : Int × Int) :
    payloadAt x p ∈ routedPayloads S T seed (baseAt x p).1 := by
  rcases mem_combineWithRoutedScaffold_iff.1 (x p).2 with
    ⟨base, _hbase, payload, hpayload, hproduct⟩
  simpa [baseAt, payloadAt, ← hproduct] using hpayload

theorem baseAt_product
    (x : Int × Int → TileIn (combineWithRoutedScaffold S T seed))
    (p : Int × Int) :
    WangTile.product (baseAt x p).1 (payloadAt x p) = (x p).1 := by
  exact WangTile.product_projections (x p).1

/-- Both decoded layers of a valid routed product plane. -/
structure Decoded
    (x : Int × Int → TileIn (combineWithRoutedScaffold S T seed)) where
  base : Int × Int → TileIn S.tiles
  payload : Int × Int → WangTile
  product : ∀ p, WangTile.product (base p).1 (payload p) = (x p).1
  payload_allowed : ∀ p,
    payload p ∈ routedPayloads S T seed (base p).1
  base_valid : ValidPlaneTiling S.tiles base
  payload_hmatch : ∀ p,
    WangTile.HMatches (payload p) (payload (p.1 + 1, p.2))
  payload_vmatch : ∀ p,
    WangTile.VMatches (payload p) (payload (p.1, p.2 + 1))

def decode
    {x : Int × Int → TileIn (combineWithRoutedScaffold S T seed)}
    (hx : ValidPlaneTiling (combineWithRoutedScaffold S T seed) x) :
    Decoded x where
  base := baseAt x
  payload := payloadAt x
  product := baseAt_product x
  payload_allowed := payloadAt_allowed x
  base_valid := by
    constructor
    · intro p
      exact (hx.1 p).productBase
    · intro p
      exact (hx.2 p).productBase
  payload_hmatch := by
    intro p
    exact (hx.1 p).productPayload
  payload_vmatch := by
    intro p
    exact (hx.2 p).productPayload

namespace Decoded

variable {x : Int × Int → TileIn (combineWithRoutedScaffold S T seed)}

theorem horizontal_wire (decoded : Decoded x) (p : Int × Int)
    (hrole : S.role (decoded.base p).1 = .horizontal) :
    decoded.payload p ∈ completePayloads T ∧
      (decoded.payload p).w = (decoded.payload p).e := by
  have hallowed := decoded.payload_allowed p
  rw [mem_routedPayloads_iff] at hallowed
  simpa only [hrole] using hallowed

theorem vertical_wire (decoded : Decoded x) (p : Int × Int)
    (hrole : S.role (decoded.base p).1 = .vertical) :
    decoded.payload p ∈ completePayloads T ∧
      (decoded.payload p).s = (decoded.payload p).n := by
  have hallowed := decoded.payload_allowed p
  rw [mem_routedPayloads_iff] at hallowed
  simpa only [hrole] using hallowed

theorem active_tile (decoded : Decoded x) (p : Int × Int)
    (hrole : S.role (decoded.base p).1 = .active) :
    decoded.payload p ∈ T := by
  have hallowed := decoded.payload_allowed p
  rw [mem_routedPayloads_iff] at hallowed
  simpa only [hrole] using hallowed

theorem corner_seed (decoded : Decoded x) (p : Int × Int)
    (hrole : S.role (decoded.base p).1 = .corner) :
    decoded.payload p ∈ T ∧ decoded.payload p = seed := by
  have hallowed := decoded.payload_allowed p
  rw [mem_routedPayloads_iff] at hallowed
  simpa only [hrole] using hallowed

end Decoded
end RoutedPlaneDecode
end LeanWang
