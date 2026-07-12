/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104ShadedObstructionGeometryBaseSoundness
import LeanWang.OllingerRobinson104BorderCoverage

/-!
# Semantic obstruction geometry for every depth-four parent block

The native audit is indexed by canonical border states.  Canonicalization
preserves the thick red component, which is the only part observed by shade
validity, selected borders, free lines, and obstruction geometry.  This file
transports the audited result back to an arbitrary corrected parent tile.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace ShadedObstructionGeometryBase

open OrientedRedCycles RedShadeCycles RedShadePaths ShadedPlaneSignalGrid
  ShadedObstructionGeometry Signals.FreeCellLocal

set_option maxRecDepth 20000

set_option maxHeartbeats 1000000 in
-- Reducing the dependent local-allowance fields requires unfolding both grids.
theorem validShadeGrid_congr
    {first second : Nat → Nat → Index}
    {stateGrid : Nat → Nat → RedShades.State}
    (same : BorderGeometry.SameComponents first second)
    (valid : ValidShadeGrid second stateGrid) :
    ValidShadeGrid first stateGrid where
  allowed := by
    intro x y
    have hallowed := valid.allowed x y
    change RedShades.allowedFor (componentAt second x y) (quadrantAt x y)
      (stateGrid x y) = true at hallowed
    change RedShades.allowedFor (componentAt first x y) (quadrantAt x y)
      (stateGrid x y) = true
    rw [same x y]
    exact hallowed
  hmatch := valid.hmatch
  vmatch := valid.vmatch

theorem selectedHorizontalFor_congr
    {first second : Nat → Nat → Index}
    (same : BorderGeometry.SameComponents first second)
    (stateGrid : Nat → Nat → RedShades.State) (x y : Nat) :
    ShadedSignals.selectedHorizontalFor
        (componentAt first x y) (quadrantAt x y) (stateGrid x y) =
      ShadedSignals.selectedHorizontalFor
        (componentAt second x y) (quadrantAt x y) (stateGrid x y) := by
  rw [same x y]

theorem selectedVerticalFor_congr
    {first second : Nat → Nat → Index}
    (same : BorderGeometry.SameComponents first second)
    (stateGrid : Nat → Nat → RedShades.State) (x y : Nat) :
    ShadedSignals.selectedVerticalFor
        (componentAt first x y) (quadrantAt x y) (stateGrid x y) =
      ShadedSignals.selectedVerticalFor
        (componentAt second x y) (quadrantAt x y) (stateGrid x y) := by
  rw [same x y]

theorem isFreeRow_congr
    {first second : Nat → Nat → Index}
    (same : BorderGeometry.SameComponents first second)
    (stateGrid : Nat → Nat → RedShades.State)
    (west east row : Nat) :
    IsFreeRow first stateGrid west east row ↔
      IsFreeRow second stateGrid west east row := by
  constructor <;> intro free quarterX hwest heast
  · simpa only [selectedVerticalFor_congr same stateGrid quarterX row] using
      free quarterX hwest heast
  · simpa only [selectedVerticalFor_congr same stateGrid quarterX row] using
      free quarterX hwest heast

theorem isFreeColumn_congr
    {first second : Nat → Nat → Index}
    (same : BorderGeometry.SameComponents first second)
    (stateGrid : Nat → Nat → RedShades.State)
    (south north column : Nat) :
    IsFreeColumn first stateGrid south north column ↔
      IsFreeColumn second stateGrid south north column := by
  constructor <;> intro free quarterY hsouth hnorth
  · simpa only [selectedHorizontalFor_congr same stateGrid column quarterY] using
      free quarterY hsouth hnorth
  · simpa only [selectedHorizontalFor_congr same stateGrid column quarterY] using
      free quarterY hsouth hnorth

theorem geometry_congr
    {first second : Nat → Nat → Index}
    {stateGrid : Nat → Nat → RedShades.State}
    {west east south north : Nat}
    (same : BorderGeometry.SameComponents first second)
    (geometry : Geometry first stateGrid west east south north) :
    Geometry second stateGrid west east south north := by
  constructor
  · intro column row hwest heast hsouth hnorth hfreeRow hnotFreeColumn
    have hfreeRowFirst :=
      (isFreeRow_congr same stateGrid west east row).2 hfreeRow
    have hnotFreeColumnFirst :
        ¬IsFreeColumn first stateGrid south north column := by
      intro free
      exact hnotFreeColumn
        ((isFreeColumn_congr same stateGrid south north column).1 free)
    rcases geometry.verticalBoundary hwest heast hsouth hnorth
      hfreeRowFirst hnotFreeColumnFirst with hat | hupper | hlower
    · exact Or.inl (by
        simpa only [selectedHorizontalFor_congr same stateGrid column row] using hat)
    · rcases hupper with ⟨boundary, hrb, hbn, hselected, hbetween⟩
      exact Or.inr (Or.inl ⟨boundary, hrb, hbn, by
        simpa only [selectedHorizontalFor_congr same stateGrid column boundary]
          using hselected, by
        intro y hry hyb
        simpa only [selectedHorizontalFor_congr same stateGrid column y] using
          hbetween y hry hyb⟩)
    · rcases hlower with ⟨boundary, hsb, hbr, hselected, hbetween⟩
      exact Or.inr (Or.inr ⟨boundary, hsb, hbr, by
        simpa only [selectedHorizontalFor_congr same stateGrid column boundary]
          using hselected, by
        intro y hby hyr
        simpa only [selectedHorizontalFor_congr same stateGrid column y] using
          hbetween y hby hyr⟩)
  · intro column row hwest heast hsouth hnorth hfreeColumn hnotFreeRow
    have hfreeColumnFirst :=
      (isFreeColumn_congr same stateGrid south north column).2 hfreeColumn
    have hnotFreeRowFirst : ¬IsFreeRow first stateGrid west east row := by
      intro free
      exact hnotFreeRow ((isFreeRow_congr same stateGrid west east row).1 free)
    rcases geometry.horizontalBoundary hwest heast hsouth hnorth
      hfreeColumnFirst hnotFreeRowFirst with hat | hright | hleft
    · exact Or.inl (by
        simpa only [selectedVerticalFor_congr same stateGrid column row] using hat)
    · rcases hright with ⟨boundary, hcb, hbe, hselected, hbetween⟩
      exact Or.inr (Or.inl ⟨boundary, hcb, hbe, by
        simpa only [selectedVerticalFor_congr same stateGrid boundary row]
          using hselected, by
        intro x hcx hxb
        simpa only [selectedVerticalFor_congr same stateGrid x row] using
          hbetween x hcx hxb⟩)
    · rcases hleft with ⟨boundary, hwb, hbc, hselected, hbetween⟩
      exact Or.inr (Or.inr ⟨boundary, hwb, hbc, by
        simpa only [selectedVerticalFor_congr same stateGrid boundary row]
          using hselected, by
        intro x hbx hxc
        simpa only [selectedVerticalFor_congr same stateGrid x row] using
          hbetween x hbx hxc⟩)

theorem geometry
    (parent : Index)
    {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid
      (ShadedFreeLineGraphBase.localGrid parent) stateGrid)
    (parentLight : Bool)
    (shaded : CycleShade stateGrid 4 12 4 12
      (if parentLight then .light else .dark)) :
    Geometry (ShadedFreeLineGraphBase.localGrid parent) stateGrid 4 12 4 12 := by
  let canonical := BorderSubstitution.canonicalIndex parent
  have same : BorderGeometry.SameComponents
      (ShadedFreeLineGraphBase.localGrid canonical)
      (ShadedFreeLineGraphBase.localGrid parent) := by
    simpa [ShadedFreeLineRecurrence.localGrid,
      ShadedFreeLineRecurrence.refinementDepth,
      ShadedFreeLineRecurrence.Phase.extra,
      ShadedFreeLineGraphBase.localGrid] using
      BorderCoverage.sameComponents_localGrid_canonicalIndex
        ShadedFreeLineRecurrence.Phase.even 1 parent
  have validCanonical : ValidShadeGrid
      (ShadedFreeLineGraphBase.localGrid canonical) stateGrid :=
    validShadeGrid_congr same valid
  have cycleCanonical : CycleOn
      (ShadedFreeLineGraphBase.localGrid canonical) 4 12 4 12 := by
    simpa [ShadedFreeLineRecurrence.localGrid,
      ShadedFreeLineRecurrence.refinementDepth,
      ShadedFreeLineRecurrence.Phase.extra,
      ShadedFreeLineRecurrence.west, ShadedFreeLineRecurrence.east,
      ShadedFreeLineRecurrence.scale, ShadedFreeLineRecurrence.Phase.factor,
      ShadedFreeLineGraphBase.localGrid] using
      ShadedFreeLineRecurrence.canonicalCycle
        ShadedFreeLineRecurrence.Phase.even 1 canonical
  exact geometry_congr same
    (ShadedObstructionGeometryBaseSoundness.geometry_canonical parent
      validCanonical parentLight cycleCanonical shaded)

end ShadedObstructionGeometryBase
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
