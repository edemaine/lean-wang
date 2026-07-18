/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.OrientedLightHorizontalGeometry
import LeanWang.Robinson.Closed104.OrientedLightVerticalGeometry

/-!
# Robinson obstruction geometry from oriented light wires

The height minimum principle orients the nearest light-wire boundary in all
four directions.  Together, the vertical and horizontal results supply the
geometric hypothesis needed by the routed-signal obstruction theorem.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace OrientedLightGeometry

open OrientedRedCycles RedShadeCycles RedShadePaths ShadedPlaneSignalGrid

variable {indexGrid : Nat -> Nat -> Index}
  {stateGrid : Nat -> Nat -> RedShades.State}
  {west east south north : Nat}

/-- A valid light Robinson board has the outward-facing nearest boundaries
required by the obstruction-signal argument. -/
theorem CycleShade.geometry
    (shaded : CycleShade stateGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidShadeGrid indexGrid stateGrid) :
    ShadedObstructionGeometry.Geometry
      indexGrid stateGrid west east south north where
  verticalBoundary :=
    OrientedLightVerticalGeometry.CycleShade.verticalBoundary
      shaded cycle valid
  horizontalBoundary :=
    OrientedLightHorizontalGeometry.CycleShade.horizontalBoundary
      shaded cycle valid

end OrientedLightGeometry
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
