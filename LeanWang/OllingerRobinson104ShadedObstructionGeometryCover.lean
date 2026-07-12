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

open RedCycles RedShadeCycles RedShadePaths ShadedObstructionGeometry
  ShadedPayloadCorridors
  ShadedPlaneSignalGrid Signals.FreeCellLocal

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

/-- A hierarchy can localize a crossing together with any selected witness. -/
structure PairCover
    (indexGrid : Nat → Nat → Index)
    (shadeGrid : Nat → Nat → RedShades.State)
    (west east south north : Nat) : Prop where
  vertical : ∀ {column row boundary : Nat},
    quarterWest west < column → column < quarterEast east →
    quarterSouth south < row → row < quarterNorth north →
    quarterSouth south < boundary → boundary < quarterNorth north →
    ShadedSignals.selectedHorizontalFor
      (componentAt indexGrid column boundary) (quadrantAt column boundary)
      (shadeGrid column boundary) ≠ none →
      ∃ localWest localEast localSouth localNorth,
        quarterWest west ≤ quarterWest localWest ∧
        quarterEast localEast ≤ quarterEast east ∧
        quarterWest localWest < column ∧ column < quarterEast localEast ∧
        quarterSouth localSouth < row ∧ row < quarterNorth localNorth ∧
        quarterSouth localSouth < boundary ∧
        boundary < quarterNorth localNorth ∧
        Geometry indexGrid shadeGrid
          localWest localEast localSouth localNorth
  horizontal : ∀ {column row boundary : Nat},
    quarterWest west < column → column < quarterEast east →
    quarterSouth south < row → row < quarterNorth north →
    quarterWest west < boundary → boundary < quarterEast east →
    ShadedSignals.selectedVerticalFor
      (componentAt indexGrid boundary row) (quadrantAt boundary row)
      (shadeGrid boundary row) ≠ none →
      ∃ localWest localEast localSouth localNorth,
        quarterSouth south ≤ quarterSouth localSouth ∧
        quarterNorth localNorth ≤ quarterNorth north ∧
        quarterWest localWest < column ∧ column < quarterEast localEast ∧
        quarterSouth localSouth < row ∧ row < quarterNorth localNorth ∧
        quarterWest localWest < boundary ∧
        boundary < quarterEast localEast ∧
        Geometry indexGrid shadeGrid
          localWest localEast localSouth localNorth

/-- One geometry board covers every coordinate pair in its own interior. -/
theorem pairCover_of_geometry
    {indexGrid : Nat → Nat → Index}
    {shadeGrid : Nat → Nat → RedShades.State}
    {west east south north : Nat}
    (geometry : Geometry indexGrid shadeGrid west east south north) :
    PairCover indexGrid shadeGrid west east south north := by
  constructor
  · intro column row boundary hwest heast hsouth hnorth
      hboundarySouth hboundaryNorth _
    exact ⟨west, east, south, north, le_rfl, le_rfl,
      hwest, heast, hsouth, hnorth, hboundarySouth, hboundaryNorth, geometry⟩
  · intro column row boundary hwest heast hsouth hnorth
      hboundaryWest hboundaryEast _
    exact ⟨west, east, south, north, le_rfl, le_rfl,
      hwest, heast, hsouth, hnorth, hboundaryWest, hboundaryEast, geometry⟩

/-- Every translated depth-four audit block supplies a local pair cover. -/
theorem pairCover_at_block
    (grid : Nat → Nat → Index)
    {shadeGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid (iterateRefine 4 grid) shadeGrid)
    (blockX blockY : Nat) :
    PairCover (iterateRefine 4 grid) shadeGrid
      (16 * blockX + 4) (16 * blockX + 12)
      (16 * blockY + 4) (16 * blockY + 12) :=
  pairCover_of_geometry
    (ShadedObstructionGeometryTranslation.geometry_at_block
      grid valid blockX blockY)

set_option maxHeartbeats 1000000 in
-- Extracting finite selected-boundary witnesses unfolds both free predicates.
theorem PairCover.localCover
    {indexGrid : Nat → Nat → Index}
    {shadeGrid : Nat → Nat → RedShades.State}
    {west east south north : Nat}
    (cover : PairCover indexGrid shadeGrid west east south north) :
    LocalCover indexGrid shadeGrid west east south north := by
  classical
  constructor
  · intro column row hwest heast hsouth hnorth hnotFree
    have witness : ∃ boundary,
        quarterSouth south < boundary ∧ boundary < quarterNorth north ∧
        ShadedSignals.selectedHorizontalFor
          (componentAt indexGrid column boundary) (quadrantAt column boundary)
          (shadeGrid column boundary) ≠ none := by
      by_contra hnone
      apply hnotFree
      intro boundary hboundarySouth hboundaryNorth
      by_contra hselected
      exact hnone ⟨boundary, hboundarySouth, hboundaryNorth, hselected⟩
    rcases witness with
      ⟨boundary, hboundarySouth, hboundaryNorth, hselected⟩
    rcases cover.vertical hwest heast hsouth hnorth hboundarySouth
      hboundaryNorth hselected with
      ⟨localWest, localEast, localSouth, localNorth,
        houterWest, houterEast, hlocalWest, hlocalEast,
        hlocalSouth, hlocalNorth, hboundaryLocalSouth,
        hboundaryLocalNorth, geometry⟩
    refine ⟨localWest, localEast, localSouth, localNorth,
      houterWest, houterEast, hlocalWest, hlocalEast,
      hlocalSouth, hlocalNorth, ?_, geometry⟩
    intro free
    exact hselected
      (free boundary hboundaryLocalSouth hboundaryLocalNorth)
  · intro column row hwest heast hsouth hnorth hnotFree
    have witness : ∃ boundary,
        quarterWest west < boundary ∧ boundary < quarterEast east ∧
        ShadedSignals.selectedVerticalFor
          (componentAt indexGrid boundary row) (quadrantAt boundary row)
          (shadeGrid boundary row) ≠ none := by
      by_contra hnone
      apply hnotFree
      intro boundary hboundaryWest hboundaryEast
      by_contra hselected
      exact hnone ⟨boundary, hboundaryWest, hboundaryEast, hselected⟩
    rcases witness with
      ⟨boundary, hboundaryWest, hboundaryEast, hselected⟩
    rcases cover.horizontal hwest heast hsouth hnorth hboundaryWest
      hboundaryEast hselected with
      ⟨localWest, localEast, localSouth, localNorth,
        houterSouth, houterNorth, hlocalWest, hlocalEast,
        hlocalSouth, hlocalNorth, hboundaryLocalWest,
        hboundaryLocalEast, geometry⟩
    refine ⟨localWest, localEast, localSouth, localNorth,
      houterSouth, houterNorth, hlocalWest, hlocalEast,
      hlocalSouth, hlocalNorth, ?_, geometry⟩
    intro free
    exact hselected
      (free boundary hboundaryLocalWest hboundaryLocalEast)
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
