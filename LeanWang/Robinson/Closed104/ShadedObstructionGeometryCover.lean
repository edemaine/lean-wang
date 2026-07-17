/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.ShadedObstructionGeometryTranslation

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
  ShadedPlaneSignalGrid RefinementTranslation ShadedFreeLineTranslation
  Signals.FreeCellLocal

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

/-- A pair cover whose returned geometry stays inside the ambient board in
both axes.  The recurrence uses this stronger invariant; the final obstruction
argument only needs the asymmetric `PairCover` projection. -/
structure ContainedPairCover
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
        quarterSouth south ≤ quarterSouth localSouth ∧
        quarterNorth localNorth ≤ quarterNorth north ∧
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
        quarterWest west ≤ quarterWest localWest ∧
        quarterEast localEast ≤ quarterEast east ∧
        quarterSouth south ≤ quarterSouth localSouth ∧
        quarterNorth localNorth ≤ quarterNorth north ∧
        quarterWest localWest < column ∧ column < quarterEast localEast ∧
        quarterSouth localSouth < row ∧ row < quarterNorth localNorth ∧
        quarterWest localWest < boundary ∧
        boundary < quarterEast localEast ∧
        Geometry indexGrid shadeGrid
          localWest localEast localSouth localNorth

theorem ContainedPairCover.toPairCover
    {indexGrid : Nat → Nat → Index}
    {shadeGrid : Nat → Nat → RedShades.State}
    {west east south north : Nat}
    (cover : ContainedPairCover indexGrid shadeGrid west east south north) :
    PairCover indexGrid shadeGrid west east south north := by
  constructor
  · intro column row boundary hwest heast hsouth hnorth
      hboundarySouth hboundaryNorth hselected
    rcases cover.vertical hwest heast hsouth hnorth hboundarySouth
      hboundaryNorth hselected with
      ⟨localWest, localEast, localSouth, localNorth,
        houterWest, houterEast, _, _, hlocalWest, hlocalEast,
        hlocalSouth, hlocalNorth, hboundaryLocalSouth,
        hboundaryLocalNorth, geometry⟩
    exact ⟨localWest, localEast, localSouth, localNorth,
      houterWest, houterEast, hlocalWest, hlocalEast,
      hlocalSouth, hlocalNorth, hboundaryLocalSouth,
      hboundaryLocalNorth, geometry⟩
  · intro column row boundary hwest heast hsouth hnorth
      hboundaryWest hboundaryEast hselected
    rcases cover.horizontal hwest heast hsouth hnorth hboundaryWest
      hboundaryEast hselected with
      ⟨localWest, localEast, localSouth, localNorth,
        _, _, houterSouth, houterNorth, hlocalWest, hlocalEast,
        hlocalSouth, hlocalNorth, hboundaryLocalWest,
        hboundaryLocalEast, geometry⟩
    exact ⟨localWest, localEast, localSouth, localNorth,
      houterSouth, houterNorth, hlocalWest, hlocalEast,
      hlocalSouth, hlocalNorth, hboundaryLocalWest,
      hboundaryLocalEast, geometry⟩

/-- One geometry board is a fully contained pair cover of itself. -/
theorem containedPairCover_of_geometry
    {indexGrid : Nat → Nat → Index}
    {shadeGrid : Nat → Nat → RedShades.State}
    {west east south north : Nat}
    (geometry : Geometry indexGrid shadeGrid west east south north) :
    ContainedPairCover indexGrid shadeGrid west east south north := by
  constructor
  · intro column row boundary hwest heast hsouth hnorth
      hboundarySouth hboundaryNorth _
    exact ⟨west, east, south, north,
      le_rfl, le_rfl, le_rfl, le_rfl,
      hwest, heast, hsouth, hnorth,
      hboundarySouth, hboundaryNorth, geometry⟩
  · intro column row boundary hwest heast hsouth hnorth
      hboundaryWest hboundaryEast _
    exact ⟨west, east, south, north,
      le_rfl, le_rfl, le_rfl, le_rfl,
      hwest, heast, hsouth, hnorth,
      hboundaryWest, hboundaryEast, geometry⟩

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

/-- A family of smaller pair covers assembles into a larger pair cover when
each queried coordinate pair lies in one member of the family.  Vertical
queries only require horizontal containment in the large board, and
horizontal queries only require vertical containment, exactly matching the
asymmetric localization conditions in `PairCover`. -/
theorem PairCover.of_subcovers
    {indexGrid : Nat → Nat → Index}
    {shadeGrid : Nat → Nat → RedShades.State}
    {west east south north : Nat}
    (verticalSubcover : ∀ {column row boundary : Nat},
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
        PairCover indexGrid shadeGrid
          localWest localEast localSouth localNorth)
    (horizontalSubcover : ∀ {column row boundary : Nat},
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
        PairCover indexGrid shadeGrid
          localWest localEast localSouth localNorth) :
    PairCover indexGrid shadeGrid west east south north := by
  constructor
  · intro column row boundary hwest heast hsouth hnorth
      hboundarySouth hboundaryNorth hselected
    rcases verticalSubcover hwest heast hsouth hnorth hboundarySouth
      hboundaryNorth hselected with
      ⟨localWest, localEast, localSouth, localNorth,
        houterWest, houterEast, hlocalWest, hlocalEast,
        hlocalSouth, hlocalNorth, hboundaryLocalSouth,
        hboundaryLocalNorth, cover⟩
    rcases cover.vertical hlocalWest hlocalEast hlocalSouth hlocalNorth
      hboundaryLocalSouth hboundaryLocalNorth hselected with
      ⟨geometryWest, geometryEast, geometrySouth, geometryNorth,
        hgeometryWest, hgeometryEast, hgeometryColumnWest,
        hgeometryColumnEast, hgeometryRowSouth, hgeometryRowNorth,
        hgeometryBoundarySouth, hgeometryBoundaryNorth, geometry⟩
    exact ⟨geometryWest, geometryEast, geometrySouth, geometryNorth,
      houterWest.trans hgeometryWest, hgeometryEast.trans houterEast,
      hgeometryColumnWest, hgeometryColumnEast,
      hgeometryRowSouth, hgeometryRowNorth,
      hgeometryBoundarySouth, hgeometryBoundaryNorth, geometry⟩
  · intro column row boundary hwest heast hsouth hnorth
      hboundaryWest hboundaryEast hselected
    rcases horizontalSubcover hwest heast hsouth hnorth hboundaryWest
      hboundaryEast hselected with
      ⟨localWest, localEast, localSouth, localNorth,
        houterSouth, houterNorth, hlocalWest, hlocalEast,
        hlocalSouth, hlocalNorth, hboundaryLocalWest,
        hboundaryLocalEast, cover⟩
    rcases cover.horizontal hlocalWest hlocalEast hlocalSouth hlocalNorth
      hboundaryLocalWest hboundaryLocalEast hselected with
      ⟨geometryWest, geometryEast, geometrySouth, geometryNorth,
        hgeometrySouth, hgeometryNorth, hgeometryColumnWest,
        hgeometryColumnEast, hgeometryRowSouth, hgeometryRowNorth,
        hgeometryBoundaryWest, hgeometryBoundaryEast, geometry⟩
    exact ⟨geometryWest, geometryEast, geometrySouth, geometryNorth,
      houterSouth.trans hgeometrySouth, hgeometryNorth.trans houterNorth,
      hgeometryColumnWest, hgeometryColumnEast,
      hgeometryRowSouth, hgeometryRowNorth,
      hgeometryBoundaryWest, hgeometryBoundaryEast, geometry⟩

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

/-- Every translated depth-four audit block supplies the fully contained
recurrence invariant. -/
theorem containedPairCover_at_block
    (grid : Nat → Nat → Index)
    {shadeGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid (iterateRefine 4 grid) shadeGrid)
    (blockX blockY : Nat) :
    ContainedPairCover (iterateRefine 4 grid) shadeGrid
      (16 * blockX + 4) (16 * blockX + 12)
      (16 * blockY + 4) (16 * blockY + 12) :=
  containedPairCover_of_geometry
    (ShadedObstructionGeometryTranslation.geometry_at_block
      grid valid blockX blockY)

set_option maxHeartbeats 1000000 in
-- Translating both quantified coordinates and returned geometry witnesses.
/-- Pair covers are equivariant under a refined-grid block translation. -/
theorem PairCover.translate
    {depth : Nat} {grid : Nat → Nat → Index}
    {shadeGrid : Nat → Nat → RedShades.State}
    {blockX blockY west east south north : Nat}
    (cover : PairCover
      (iterateRefine depth (shiftGrid grid blockX blockY))
      (shiftQuarterGrid shadeGrid
        (2 ^ (depth + 1) * blockX) (2 ^ (depth + 1) * blockY))
      west east south north) :
    PairCover (iterateRefine depth grid) shadeGrid
      (2 ^ depth * blockX + west) (2 ^ depth * blockX + east)
      (2 ^ depth * blockY + south) (2 ^ depth * blockY + north) := by
  let quarterOffsetX := 2 ^ (depth + 1) * blockX
  let quarterOffsetY := 2 ^ (depth + 1) * blockY
  let indexOffsetX := 2 ^ depth * blockX
  let indexOffsetY := 2 ^ depth * blockY
  have hquarterX : quarterOffsetX = 2 * indexOffsetX := by
    dsimp [quarterOffsetX, indexOffsetX]
    rw [pow_succ]
    ac_rfl
  have hquarterY : quarterOffsetY = 2 * indexOffsetY := by
    dsimp [quarterOffsetY, indexOffsetY]
    rw [pow_succ]
    ac_rfl
  have quarterWest_add (value : Nat) :
      quarterWest (indexOffsetX + value) =
        quarterOffsetX + quarterWest value := by
    simp [quarterWest, hquarterX]
    omega
  have quarterEast_add (value : Nat) :
      quarterEast (indexOffsetX + value) =
        quarterOffsetX + quarterEast value := by
    simp [quarterEast, hquarterX]
    omega
  have quarterSouth_add (value : Nat) :
      quarterSouth (indexOffsetY + value) =
        quarterOffsetY + quarterSouth value := by
    simp [quarterSouth, hquarterY]
    omega
  have quarterNorth_add (value : Nat) :
      quarterNorth (indexOffsetY + value) =
        quarterOffsetY + quarterNorth value := by
    simp [quarterNorth, hquarterY]
    omega
  have hwest : quarterWest (indexOffsetX + west) =
      quarterOffsetX + quarterWest west := quarterWest_add west
  have heast : quarterEast (indexOffsetX + east) =
      quarterOffsetX + quarterEast east := quarterEast_add east
  have hsouth : quarterSouth (indexOffsetY + south) =
      quarterOffsetY + quarterSouth south := quarterSouth_add south
  have hnorth : quarterNorth (indexOffsetY + north) =
      quarterOffsetY + quarterNorth north := quarterNorth_add north
  constructor
  · intro column row boundary hcolumnWest hcolumnEast hrowSouth hrowNorth
      hboundarySouth hboundaryNorth hselected
    have hcolumnWest' : quarterOffsetX + quarterWest west < column := by
      rw [← hwest]
      simpa [indexOffsetX] using hcolumnWest
    have hcolumnEast' : column < quarterOffsetX + quarterEast east := by
      rw [← heast]
      simpa [indexOffsetX] using hcolumnEast
    have hrowSouth' : quarterOffsetY + quarterSouth south < row := by
      rw [← hsouth]
      simpa [indexOffsetY] using hrowSouth
    have hrowNorth' : row < quarterOffsetY + quarterNorth north := by
      rw [← hnorth]
      simpa [indexOffsetY] using hrowNorth
    have hboundarySouth' : quarterOffsetY + quarterSouth south < boundary := by
      rw [← hsouth]
      simpa [indexOffsetY] using hboundarySouth
    have hboundaryNorth' : boundary < quarterOffsetY + quarterNorth north := by
      rw [← hnorth]
      simpa [indexOffsetY] using hboundaryNorth
    let localX := column - quarterOffsetX
    let localY := row - quarterOffsetY
    let localBoundary := boundary - quarterOffsetY
    have hx : quarterOffsetX + localX = column := by
      dsimp [localX]
      omega
    have hy : quarterOffsetY + localY = row := by
      dsimp [localY]
      omega
    have hb : quarterOffsetY + localBoundary = boundary := by
      dsimp [localBoundary]
      omega
    have localSelected : ShadedSignals.selectedHorizontalFor
        (componentAt (iterateRefine depth (shiftGrid grid blockX blockY))
          localX localBoundary)
        (quadrantAt localX localBoundary)
        (shiftQuarterGrid shadeGrid quarterOffsetX quarterOffsetY
          localX localBoundary) ≠ none := by
      simpa only [quarterOffsetX, quarterOffsetY, hx, hb,
        ShadedObstructionGeometryTranslation.selectedHorizontal_shift
          depth grid shadeGrid blockX blockY localX localBoundary] using hselected
    rcases cover.vertical (column := localX) (row := localY)
        (boundary := localBoundary)
        (by omega)
        (by omega)
        (by omega)
        (by omega)
        (by omega)
        (by omega)
        localSelected with
      ⟨localWest, localEast, localSouth, localNorth,
        houterWest, houterEast, hlocalWest, hlocalEast,
        hlocalSouth, hlocalNorth, hlocalBoundarySouth,
        hlocalBoundaryNorth, geometry⟩
    refine ⟨indexOffsetX + localWest, indexOffsetX + localEast,
      indexOffsetY + localSouth, indexOffsetY + localNorth,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · change quarterWest (indexOffsetX + west) ≤
        quarterWest (indexOffsetX + localWest)
      rw [quarterWest_add, quarterWest_add]
      omega
    · change quarterEast (indexOffsetX + localEast) ≤
        quarterEast (indexOffsetX + east)
      rw [quarterEast_add, quarterEast_add]
      omega
    · rw [quarterWest_add, ← hx]
      omega
    · rw [quarterEast_add, ← hx]
      omega
    · rw [quarterSouth_add, ← hy]
      omega
    · rw [quarterNorth_add, ← hy]
      omega
    · rw [quarterSouth_add, ← hb]
      omega
    · rw [quarterNorth_add, ← hb]
      omega
    · exact ShadedObstructionGeometryTranslation.Geometry.translate geometry
  · intro column row boundary hcolumnWest hcolumnEast hrowSouth hrowNorth
      hboundaryWest hboundaryEast hselected
    have hcolumnWest' : quarterOffsetX + quarterWest west < column := by
      rw [← hwest]
      simpa [indexOffsetX] using hcolumnWest
    have hcolumnEast' : column < quarterOffsetX + quarterEast east := by
      rw [← heast]
      simpa [indexOffsetX] using hcolumnEast
    have hrowSouth' : quarterOffsetY + quarterSouth south < row := by
      rw [← hsouth]
      simpa [indexOffsetY] using hrowSouth
    have hrowNorth' : row < quarterOffsetY + quarterNorth north := by
      rw [← hnorth]
      simpa [indexOffsetY] using hrowNorth
    have hboundaryWest' : quarterOffsetX + quarterWest west < boundary := by
      rw [← hwest]
      simpa [indexOffsetX] using hboundaryWest
    have hboundaryEast' : boundary < quarterOffsetX + quarterEast east := by
      rw [← heast]
      simpa [indexOffsetX] using hboundaryEast
    let localX := column - quarterOffsetX
    let localY := row - quarterOffsetY
    let localBoundary := boundary - quarterOffsetX
    have hx : quarterOffsetX + localX = column := by
      dsimp [localX]
      omega
    have hy : quarterOffsetY + localY = row := by
      dsimp [localY]
      omega
    have hb : quarterOffsetX + localBoundary = boundary := by
      dsimp [localBoundary]
      omega
    have localSelected : ShadedSignals.selectedVerticalFor
        (componentAt (iterateRefine depth (shiftGrid grid blockX blockY))
          localBoundary localY)
        (quadrantAt localBoundary localY)
        (shiftQuarterGrid shadeGrid quarterOffsetX quarterOffsetY
          localBoundary localY) ≠ none := by
      simpa only [quarterOffsetX, quarterOffsetY, hb, hy,
        ShadedObstructionGeometryTranslation.selectedVertical_shift
          depth grid shadeGrid blockX blockY localBoundary localY] using hselected
    rcases cover.horizontal (column := localX) (row := localY)
        (boundary := localBoundary)
        (by omega)
        (by omega)
        (by omega)
        (by omega)
        (by omega)
        (by omega)
        localSelected with
      ⟨localWest, localEast, localSouth, localNorth,
        houterSouth, houterNorth, hlocalWest, hlocalEast,
        hlocalSouth, hlocalNorth, hlocalBoundaryWest,
        hlocalBoundaryEast, geometry⟩
    refine ⟨indexOffsetX + localWest, indexOffsetX + localEast,
      indexOffsetY + localSouth, indexOffsetY + localNorth,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · change quarterSouth (indexOffsetY + south) ≤
        quarterSouth (indexOffsetY + localSouth)
      rw [quarterSouth_add, quarterSouth_add]
      omega
    · change quarterNorth (indexOffsetY + localNorth) ≤
        quarterNorth (indexOffsetY + north)
      rw [quarterNorth_add, quarterNorth_add]
      omega
    · rw [quarterWest_add, ← hx]
      omega
    · rw [quarterEast_add, ← hx]
      omega
    · rw [quarterSouth_add, ← hy]
      omega
    · rw [quarterNorth_add, ← hy]
      omega
    · rw [quarterWest_add, ← hb]
      omega
    · rw [quarterEast_add, ← hb]
      omega
    · exact ShadedObstructionGeometryTranslation.Geometry.translate geometry

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
