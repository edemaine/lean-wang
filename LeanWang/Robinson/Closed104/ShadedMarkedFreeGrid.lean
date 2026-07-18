/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.ShadedFreeGrid
import LeanWang.Robinson.Closed104.ShadedSignalRoutingScaffold

/-! A free grid whose lower-left crossing carries the routed marker. -/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace SparseFreeLinePlaneMarkedGrid

open RedShadeCycles ShadedFreeGrid Signals.FreeCellLocal

structure MarkedFreeGrid
    (indexGrid : Nat → Nat → Index)
    (shadeGrid : Nat → Nat → RedShades.State)
    (west east south north size : Nat) where
  grid : FreeGrid indexGrid shadeGrid west east south north size
  positive : 0 < size
  lowerLeftMarker :
    (indexGrid (grid.columnAt ⟨0, positive⟩ / 2)
        (grid.rowAt ⟨0, positive⟩ / 2),
      quadrantAt (grid.columnAt ⟨0, positive⟩)
        (grid.rowAt ⟨0, positive⟩)) ∈
      ShadedSignals.markerQuarters

end SparseFreeLinePlaneMarkedGrid
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
