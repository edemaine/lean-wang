/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104ShadedObstructionGeometryTranslation

/-!
# Local covers suffice for global obstruction

To block a mixed free/nonfree crossing in a large Robinson board, it is enough
to find one smaller audited board containing that crossing.  The smaller board
must stay inside the globally free direction and remain nonfree in the other
direction.  This is the exact localization invariant needed from the hierarchy.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace ShadedObstructionGeometryCover

open RedShadeCycles ShadedObstructionGeometry ShadedPayloadCorridors
  ShadedPlaneSignalGrid

set_option maxRecDepth 20000

/-- Every mixed crossing is captured by a smaller board carrying geometry. -/
structure LocalCover
    (indexGrid : Nat → Nat → Index)
    (shadeGrid : Nat → Nat → RedShades.State)
    (west east south north : Nat) : Prop where
  vertical : ∀ {column row : Nat},
    quarterWest west < column → column < quarterEast east →
    quarterSouth south < row → row < quarterNorth north →
    ¬IsFreeColumn indexGrid shadeGrid south north column →
      ∃ localWest localEast localSouth localNorth,
        quarterWest west ≤ quarterWest localWest ∧
        quarterEast localEast ≤ quarterEast east ∧
        quarterWest localWest < column ∧ column < quarterEast localEast ∧
        quarterSouth localSouth < row ∧ row < quarterNorth localNorth ∧
        ¬IsFreeColumn indexGrid shadeGrid localSouth localNorth column ∧
        Geometry indexGrid shadeGrid
          localWest localEast localSouth localNorth
  horizontal : ∀ {column row : Nat},
    quarterWest west < column → column < quarterEast east →
    quarterSouth south < row → row < quarterNorth north →
    ¬IsFreeRow indexGrid shadeGrid west east row →
      ∃ localWest localEast localSouth localNorth,
        quarterSouth south ≤ quarterSouth localSouth ∧
        quarterNorth localNorth ≤ quarterNorth north ∧
        quarterWest localWest < column ∧ column < quarterEast localEast ∧
        quarterSouth localSouth < row ∧ row < quarterNorth localNorth ∧
        ¬IsFreeRow indexGrid shadeGrid localWest localEast row ∧
        Geometry indexGrid shadeGrid
          localWest localEast localSouth localNorth

theorem LocalCover.crossingObstruction
    {indexGrid : Nat → Nat → Index}
    {shadeGrid : Nat → Nat → RedShades.State}
    {signalGrid : Nat → Nat → Signals.State}
    {west east south north : Nat}
    (cover : LocalCover indexGrid shadeGrid west east south north)
    (valid : ValidGrid indexGrid shadeGrid signalGrid) :
    CrossingObstruction indexGrid shadeGrid signalGrid
      west east south north := by
  constructor
  · intro column row hwest heast hsouth hnorth hfreeRow hnotFreeColumn
    rcases cover.vertical hwest heast hsouth hnorth hnotFreeColumn with
      ⟨localWest, localEast, localSouth, localNorth,
        houterWest, houterEast, hlocalWest, hlocalEast,
        hlocalSouth, hlocalNorth, hlocalNotFree, geometry⟩
    have localFree : IsFreeRow indexGrid shadeGrid localWest localEast row := by
      intro x hxWest hxEast
      exact hfreeRow x
        (houterWest.trans_lt hxWest)
        (hxEast.trans_le houterEast)
    exact (geometry.crossingObstruction valid).verticalBlocked
      hlocalWest hlocalEast hlocalSouth hlocalNorth localFree hlocalNotFree
  · intro column row hwest heast hsouth hnorth hfreeColumn hnotFreeRow
    rcases cover.horizontal hwest heast hsouth hnorth hnotFreeRow with
      ⟨localWest, localEast, localSouth, localNorth,
        houterSouth, houterNorth, hlocalWest, hlocalEast,
        hlocalSouth, hlocalNorth, hlocalNotFree, geometry⟩
    have localFree : IsFreeColumn indexGrid shadeGrid
        localSouth localNorth column := by
      intro y hySouth hyNorth
      exact hfreeColumn y
        (houterSouth.trans_lt hySouth)
        (hyNorth.trans_le houterNorth)
    exact (geometry.crossingObstruction valid).horizontalBlocked
      hlocalWest hlocalEast hlocalSouth hlocalNorth localFree hlocalNotFree

end ShadedObstructionGeometryCover
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
