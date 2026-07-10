/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104ShadedPlaneShadeGrid

/-!
Embed the obstruction-signal layer of a final shaded routed plane on the same
natural quarter grid as its red-shade layer.
-/

noncomputable section

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace ShadedPlaneSignalGrid

open HierarchyEmbedding RedCycles RedShadePaths ShadedPlaneShadeGrid
  Signals.FreeCellLocal

set_option maxRecDepth 20000

variable {T : TileSet} {seed : WangTile}
  {x : Int × Int → TileIn
    (combineWithRoutedScaffold ShadedSignals.routedScaffold T seed)}

/-- A compatible shade and obstruction-signal assignment over a quarter grid. -/
structure ValidGrid (indexGrid : Nat → Nat → Index)
    (shadeGrid : Nat → Nat → RedShades.State)
    (signalGrid : Nat → Nat → Signals.State) : Prop where
  shadeValid : ValidShadeGrid indexGrid shadeGrid
  signalAllowed : ∀ quarterX quarterY,
    ShadedSignals.locallyAllowed
      ((indexGrid (quarterX / 2) (quarterY / 2),
          quadrantAt quarterX quarterY),
        shadeGrid quarterX quarterY)
      (signalGrid quarterX quarterY) = true
  hmatch : ∀ quarterX quarterY,
    (signalGrid quarterX quarterY).east =
      (signalGrid (quarterX + 1) quarterY).west
  vmatch : ∀ quarterX quarterY,
    (signalGrid quarterX quarterY).north =
      (signalGrid quarterX (quarterY + 1)).south

/-- Signal states on the natural quarter grid below a parent coordinate. -/
def signalGrid (decoded : ShadedRoutedPlaneDecode.Decoded x)
    (parentOrigin : Int × Int) : Nat → Nat → Signals.State :=
  fun quarterX quarterY =>
    ShadedSignals.signalPlane decoded.base
      (point decoded parentOrigin quarterX quarterY)

theorem shadeGrid_eq_decode (decoded : ShadedRoutedPlaneDecode.Decoded x)
    (parentOrigin : Int × Int) (quarterX quarterY : Nat) :
    stateGrid decoded parentOrigin quarterX quarterY =
      (ShadedSignals.decode
        (decoded.base (point decoded parentOrigin quarterX quarterY))).1.2 := by
  simpa only [stateGrid, ShadedRoutedPlaneDecode.Decoded.shadeBase] using
    ShadedSignals.shadePlane_basePlane decoded.base
      (point decoded parentOrigin quarterX quarterY)

theorem quarterGrid_eq_decode
    (decoded : ShadedRoutedPlaneDecode.Decoded x)
    (parentOrigin : Int × Int) (quarterX quarterY : Nat) :
    decoded.quarter (point decoded parentOrigin quarterX quarterY) =
      (ShadedSignals.decode
        (decoded.base (point decoded parentOrigin quarterX quarterY))).1.1 := by
  simpa only [ShadedRoutedPlaneDecode.Decoded.quarter,
    ShadedSignals.quarterPlane] using
      ShadedSignals.quarterPlane_basePlane decoded.base
        (point decoded parentOrigin quarterX quarterY)

theorem valid (decoded : ShadedRoutedPlaneDecode.Decoded x)
    (parentOrigin : Int × Int) :
    ValidGrid (natGridAt decoded.parent parentOrigin)
      (stateGrid decoded parentOrigin) (signalGrid decoded parentOrigin) := by
  constructor
  · exact stateGrid_valid decoded parentOrigin
  · intro quarterX quarterY
    let p := point decoded parentOrigin quarterX quarterY
    have hallowed := ShadedSignals.decode_signalAllowed (decoded.base p)
    have hquarter := quarter_at_point decoded parentOrigin quarterX quarterY
    rw [← hquarter]
    rw [quarterGrid_eq_decode, shadeGrid_eq_decode]
    simpa only [p, signalGrid, ShadedSignals.signalPlane] using hallowed
  · intro quarterX quarterY
    have hmatch := ShadedSignals.signalPlane_hmatch decoded.base_valid
      (point decoded parentOrigin quarterX quarterY)
    have hpoint : point decoded parentOrigin (quarterX + 1) quarterY =
        ((point decoded parentOrigin quarterX quarterY).1 + 1,
          (point decoded parentOrigin quarterX quarterY).2) := by
      simp [point, quarterGridOrigin, Desubstitution.shift]
      omega
    simpa only [signalGrid, hpoint] using hmatch
  · intro quarterX quarterY
    have hmatch := ShadedSignals.signalPlane_vmatch decoded.base_valid
      (point decoded parentOrigin quarterX quarterY)
    have hpoint : point decoded parentOrigin quarterX (quarterY + 1) =
        ((point decoded parentOrigin quarterX quarterY).1,
          (point decoded parentOrigin quarterX quarterY).2 + 1) := by
      simp [point, quarterGridOrigin, Desubstitution.shift]
      omega
    simpa only [signalGrid, hpoint] using hmatch

end ShadedPlaneSignalGrid
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
