/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.ShadedSignalRoutingScaffold
import LeanWang.Robinson.Scaffold.Routed.PlaneDecode

/-!
# Decoding the final shaded routed product

The generic routed-product decoder separates any product tiling into a valid
scaffold plane and a globally edge-matching payload plane.  This specialization
then peels the corrected shaded scaffold through its own representations:
shaded tile, red-shade quarter tile, regrouped corrected parent tile, and the
infinite desubstitution tower.

The resulting `Decoded` object is the common context for the geometric half of
the reduction.  It retains the generic payload-role consequences while also
exposing the corrected parent hierarchy in which arbitrarily large Robinson
boards and free grids are found.
-/

noncomputable section

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace ShadedRoutedPlaneDecode

open Quarters QuarterRegrouping ParentPlane

set_option maxRecDepth 20000

variable {T : TileSet} {seed : WangTile}

structure Decoded
    (x : Int × Int → TileIn
      (combineWithRoutedScaffold ShadedSignals.routedScaffold T seed)) where
  routed : RoutedPlaneDecode.Decoded x

/- The definitions below successively forget layers of the same base tiling.
Each validity theorem is the bridge required by the next decoding stage. -/

noncomputable def decode
    {x : Int × Int → TileIn
      (combineWithRoutedScaffold ShadedSignals.routedScaffold T seed)}
    (hx : ValidPlaneTiling
      (combineWithRoutedScaffold ShadedSignals.routedScaffold T seed) x) :
    Decoded x :=
  ⟨RoutedPlaneDecode.decode hx⟩

namespace Decoded

variable {x : Int × Int → TileIn
  (combineWithRoutedScaffold ShadedSignals.routedScaffold T seed)}

def base (decoded : Decoded x) :
    Int × Int → TileIn ShadedSignals.tileSet :=
  fun p => ⟨(decoded.routed.base p).1, by
    simpa only [ShadedSignals.routedScaffold_tiles] using
      (decoded.routed.base p).2⟩

theorem base_valid (decoded : Decoded x) :
    ValidPlaneTiling ShadedSignals.tileSet decoded.base := by
  constructor
  · intro p
    exact decoded.routed.base_valid.1 p
  · intro p
    exact decoded.routed.base_valid.2 p

def payload (decoded : Decoded x) : Int × Int → WangTile :=
  decoded.routed.payload

def shadeBase (decoded : Decoded x) :
    Int × Int → TileIn RedShades.tileSet :=
  ShadedSignals.basePlane decoded.base

theorem shadeBase_valid (decoded : Decoded x) :
    ValidPlaneTiling RedShades.tileSet decoded.shadeBase :=
  ShadedSignals.basePlane_valid decoded.base_valid

def quarter (decoded : Decoded x) : QuarterPlane :=
  ShadedSignals.quarterPlane decoded.base

theorem quarter_valid (decoded : Decoded x) :
    ValidQuarterPlane decoded.quarter :=
  ShadedSignals.quarterPlane_valid decoded.base_valid

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

theorem active_payload (decoded : Decoded x) (p : Int × Int)
    (hrole : ShadedSignals.routeRole (decoded.base p).1 = .active) :
    decoded.payload p ∈ T := by
  apply decoded.routed.active_tile p
  simpa only [ShadedSignals.routedScaffold_role, base] using hrole

theorem corner_payload (decoded : Decoded x) (p : Int × Int)
    (hrole : ShadedSignals.routeRole (decoded.base p).1 = .corner) :
    decoded.payload p ∈ T ∧ decoded.payload p = seed := by
  apply decoded.routed.corner_seed p
  simpa only [ShadedSignals.routedScaffold_role, base] using hrole

theorem horizontal_payload_wire (decoded : Decoded x) (p : Int × Int)
    (hrole : ShadedSignals.routeRole (decoded.base p).1 = .horizontal) :
    decoded.payload p ∈ completePayloads T ∧
      (decoded.payload p).w = (decoded.payload p).e := by
  apply decoded.routed.horizontal_wire p
  simpa only [ShadedSignals.routedScaffold_role, base] using hrole

theorem vertical_payload_wire (decoded : Decoded x) (p : Int × Int)
    (hrole : ShadedSignals.routeRole (decoded.base p).1 = .vertical) :
    decoded.payload p ∈ completePayloads T ∧
      (decoded.payload p).s = (decoded.payload p).n := by
  apply decoded.routed.vertical_wire p
  simpa only [ShadedSignals.routedScaffold_role, base] using hrole

theorem payload_hmatch (decoded : Decoded x) (p : Int × Int) :
    WangTile.HMatches (decoded.payload p)
      (decoded.payload (p.1 + 1, p.2)) :=
  decoded.routed.payload_hmatch p

theorem payload_vmatch (decoded : Decoded x) (p : Int × Int) :
    WangTile.VMatches (decoded.payload p)
      (decoded.payload (p.1, p.2 + 1)) :=
  decoded.routed.payload_vmatch p

end Decoded
end ShadedRoutedPlaneDecode
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
