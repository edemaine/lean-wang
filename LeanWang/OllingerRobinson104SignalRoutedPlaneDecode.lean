/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104SignalRoutingScaffold
import LeanWang.RoutedPlaneDecode

/-!
Specialize routed-product plane decoding to the Robinson signal scaffold.

Besides retaining payload routing facts, this recovers the corrected quarter
plane, its parent index plane, and an infinite desubstitution hierarchy.
-/

noncomputable section

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace Signals
namespace RoutedSignalPlaneDecode

open Quarters QuarterRegrouping ParentPlane

set_option maxRecDepth 20000

variable {T : TileSet} {seed : WangTile}

/-- A routed product plane together with its generic two-layer decoding. -/
structure Decoded
    (x : Int × Int → TileIn
      (combineWithRoutedScaffold routedScaffold T seed)) where
  routed : RoutedPlaneDecode.Decoded x

noncomputable def decode
    {x : Int × Int → TileIn
      (combineWithRoutedScaffold routedScaffold T seed)}
    (hx : ValidPlaneTiling
      (combineWithRoutedScaffold routedScaffold T seed) x) :
    Decoded x :=
  ⟨RoutedPlaneDecode.decode hx⟩

namespace Decoded

variable {x : Int × Int → TileIn
  (combineWithRoutedScaffold routedScaffold T seed)}

/-- The scaffold layer, with its concrete signal-tileset type exposed. -/
def base (decoded : Decoded x) : Int × Int → TileIn tileSet :=
  fun p => ⟨(decoded.routed.base p).1, by
    simpa only [routedScaffold_tiles] using (decoded.routed.base p).2⟩

theorem base_valid (decoded : Decoded x) :
    ValidPlaneTiling tileSet decoded.base := by
  constructor
  · intro p
    exact decoded.routed.base_valid.1 p
  · intro p
    exact decoded.routed.base_valid.2 p

def payload (decoded : Decoded x) : Int × Int → WangTile :=
  decoded.routed.payload

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

theorem active_payload (decoded : Decoded x) (p : Int × Int)
    (hrole : routeRole (decoded.base p).1 = .active) :
    decoded.payload p ∈ T := by
  apply decoded.routed.active_tile p
  simpa only [routedScaffold_role, base] using hrole

theorem horizontal_payload_wire (decoded : Decoded x) (p : Int × Int)
    (hrole : routeRole (decoded.base p).1 = .horizontal) :
    decoded.payload p ∈ completePayloads T ∧
      (decoded.payload p).w = (decoded.payload p).e := by
  apply decoded.routed.horizontal_wire p
  simpa only [routedScaffold_role, base] using hrole

theorem vertical_payload_wire (decoded : Decoded x) (p : Int × Int)
    (hrole : routeRole (decoded.base p).1 = .vertical) :
    decoded.payload p ∈ completePayloads T ∧
      (decoded.payload p).s = (decoded.payload p).n := by
  apply decoded.routed.vertical_wire p
  simpa only [routedScaffold_role, base] using hrole

theorem payload_hmatch (decoded : Decoded x) (p : Int × Int) :
    WangTile.HMatches (decoded.payload p)
      (decoded.payload (p.1 + 1, p.2)) :=
  decoded.routed.payload_hmatch p

theorem payload_vmatch (decoded : Decoded x) (p : Int × Int) :
    WangTile.VMatches (decoded.payload p)
      (decoded.payload (p.1, p.2 + 1)) :=
  decoded.routed.payload_vmatch p

end Decoded
end RoutedSignalPlaneDecode
end Signals
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
