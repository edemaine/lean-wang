/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamComposition
import LeanWang.OllingerRobinson104PairCoverSeamPathFaces
import LeanWang.OllingerRobinson104ShadedObstructionPairCoverForward

/-!
# Connect finite seam facts to the routed scaffold

The local seam development is kept independent of the unbounded free-grid
construction.  Only this final adapter imports both proof layers.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace PairCoverSeamForward

open ShadedFreeLineRecurrence PairCoverSeamComposition
  PairCoverSeamPathBoundedBase PairCoverSeamPathFaces
  ShadedObstructionPairCoverRecurrence

theorem forcesRoutedFixedCornerSquares_of_boundarySeams
    (seams : BoundarySeams) :
    ForcesRoutedFixedCornerSquares ShadedSignals.routedScaffold :=
  forcesRoutedFixedCornerSquares_of_containedSeamCover
    (containedSeamCover_of_boundarySeams seams)

theorem forcesRoutedFixedCornerSquares_of_boundaryFaces
    (verticalFaces : VerticalBoundaryFaces)
    (horizontalFaces : HorizontalBoundaryFaces) :
    ForcesRoutedFixedCornerSquares ShadedSignals.routedScaffold :=
  forcesRoutedFixedCornerSquares_of_boundarySeams
    (boundarySeams_of_faces verticalFaces horizontalFaces)

/-- Proof-producing bounded seam certificates at every hierarchy scale imply
the routed scaffold's forward square-forcing property. -/
theorem forcesRoutedFixedCornerSquares_of_boundedPaths
    (paths : ∀ (phase : Phase) (depth : Nat), BoundedPaths phase depth) :
    ForcesRoutedFixedCornerSquares ShadedSignals.routedScaffold :=
  forcesRoutedFixedCornerSquares_of_boundaryFaces
    (BoundedPaths.verticalBoundaryFaces paths)
    (BoundedPaths.horizontalBoundaryFaces paths)

end PairCoverSeamForward
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
