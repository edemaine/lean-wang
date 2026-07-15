/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamCreatedBoundaryPaths
import LeanWang.OllingerRobinson104PairCoverSeamPathEvenBase
import LeanWang.OllingerRobinson104PairCoverSeamPathTranslation

/-!
# Finite base for created-boundary seam paths

The cached even depth-one path audit already checks every wrong-facing query,
independently of whether its selected boundary is retained or newly created.
This module exposes that certificate through the narrower created-boundary
interface used by the all-depth target recurrence.
-/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamCreatedBoundaryBase

open PairCoverSeamCreatedBoundaryPaths PairCoverSeamPathEvenBase
  PairCoverSeamPathTranslation

/-- The cached even path audit is the depth-zero created-boundary seed. -/
theorem evenBase : CreatedBoundaryPathsAt .even 0 := by
  constructor
  · intro grid parentX parentY column row boundary
      columnWest columnEast rowSouth rowNorth boundarySouth boundaryNorth
      wrongFacing notFits _createdBoundary
    exact BoundedPaths.verticalSeamPath boundedPaths grid parentX parentY
      columnWest columnEast rowSouth rowNorth boundarySouth boundaryNorth
      wrongFacing notFits
  · intro grid parentX parentY column row boundary
      columnWest columnEast rowSouth rowNorth boundaryWest boundaryEast
      wrongFacing notFits _createdBoundary
    exact BoundedPaths.horizontalSeamPath boundedPaths grid parentX parentY
      columnWest columnEast rowSouth rowNorth boundaryWest boundaryEast
      wrongFacing notFits

end PairCoverSeamCreatedBoundaryBase
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
