/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104SparseFreeLineLocalTransport
import LeanWang.OllingerRobinson104ShadedFreeLineProjectionCandidates

/-!
# Assembling sparse ancestors into projection witnesses

Exact old-segment ancestors, supplied by the finite macrocell checks, are
combined here with retained live certificates.  The result is the graph-level
projection object consumed by the Robinson free-line recurrence.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace SparseFreeLineLocalProjection

open RedCycles RedShadeCycles RedShadeGraph RedShadeGraphRefinement
  ShadedFreeLineGraph ShadedFreeLinePatternRefinement
  ShadedFreeLineProjectionCandidates Signals.FreeCellLocal

set_option maxRecDepth 20000

theorem sparseCoordinate_lt_iff {first second : Nat} :
    sparseCoordinate first < sparseCoordinate second ↔ first < second := by
  constructor
  · intro hsparse
    by_contra hlt
    have hle : second ≤ first := Nat.le_of_not_gt hlt
    rcases hle.eq_or_lt with rfl | hstrict
    · exact (Nat.lt_irrefl _ hsparse)
    · exact (Nat.not_lt_of_ge
        (Nat.le_of_lt (sparseCoordinate_strictMono hstrict)) hsparse)
  · exact sparseCoordinate_strictMono

theorem live_endpoint_of_verticalInterior
    {grid : Nat → Nat → Index} {x y : Nat}
    (interior : Signals.verticalInterior?
      (componentAt grid x y) (quadrantAt x y) ≠ none) :
    portPresent grid ⟨x, y, .south⟩ = true ∨
      portPresent grid ⟨x, y, .north⟩ = true := by
  generalize hcomponent : componentAt grid x y = component at *
  generalize hquadrant : quadrantAt x y = quadrant at *
  cases component <;> cases quadrant <;>
    simp_all [Signals.verticalInterior?, portPresent, RedShades.hasSouth,
      RedShades.hasNorth, RedShades.hasVertical, RedShades.cornerSouth,
      RedShades.cornerNorth]

theorem live_endpoint_of_horizontalInterior
    {grid : Nat → Nat → Index} {x y : Nat}
    (interior : Signals.horizontalInterior?
      (componentAt grid x y) (quadrantAt x y) ≠ none) :
    portPresent grid ⟨x, y, .west⟩ = true ∨
      portPresent grid ⟨x, y, .east⟩ = true := by
  generalize hcomponent : componentAt grid x y = component at *
  generalize hquadrant : quadrantAt x y = quadrant at *
  cases component <;> cases quadrant <;>
    simp_all [Signals.horizontalInterior?, portPresent, RedShades.hasWest,
      RedShades.hasEast, RedShades.hasHorizontal, RedShades.cornerWest,
      RedShades.cornerEast]

theorem projectsTo_of_backedCandidate
    {grid : Nat → Nat → Index} {west east south north : Nat}
    {candidate : Candidate} {target : Port}
    (backed : candidate.BackedBy (grid := grid) (west := west) (east := east)
      (south := south) (north := north))
    (odd : candidate.parity = true)
    (tail : Path (iterateRefine 2 grid) (sparsePort candidate.port)
      target false)
    (targetLive : portPresent (iterateRefine 2 grid) target = true) :
    Nonempty (ProjectsTo (grid := grid) (west := west) (east := east)
      (south := south) (north := north) target) := by
  rcases backed with ⟨source, sourceParity, head⟩
  refine ⟨{
    source := source
    path := ?_
    targetLive := targetLive
  }⟩
  have sourceOdd : source.parity = true := sourceParity.trans odd
  simpa [sourceOdd] using Path.trans head tail

/-- Every required fine vertical segment has an exact sparse old ancestor. -/
def VerticalSparseAncestors (grid : Nat → Nat → Index)
    (oldRow fineRow : Nat) : Prop :=
  ∀ x, Signals.verticalInterior?
      (componentAt (iterateRefine 2 grid) x fineRow)
      (quadrantAt x fineRow) ≠ none →
    ∃ oldX, sparseCoordinate oldX = x ∧
      Signals.verticalInterior?
        (componentAt grid oldX oldRow) (quadrantAt oldX oldRow) ≠ none

/-- Every required fine horizontal segment has an exact sparse old ancestor. -/
def HorizontalSparseAncestors (grid : Nat → Nat → Index)
    (oldColumn fineColumn : Nat) : Prop :=
  ∀ y, Signals.horizontalInterior?
      (componentAt (iterateRefine 2 grid) fineColumn y)
      (quadrantAt fineColumn y) ≠ none →
    ∃ oldY, sparseCoordinate oldY = y ∧
      Signals.horizontalInterior?
        (componentAt grid oldColumn oldY) (quadrantAt oldColumn oldY) ≠ none

/-- Sparse vertical ancestors project one retained old row to the fine row. -/
theorem verticalProjectionAt_of_sparseAncestors
    {grid : Nat → Nat → Index} {west east south north oldRow fineRow : Nat}
    (row : LiveRowCertificate grid west east south north oldRow)
    (coordinate : fineRow = sparseCoordinate oldRow)
    (ancestors : VerticalSparseAncestors grid oldRow fineRow) :
    VerticalProjectionAt grid west east south north fineRow := by
  intro x hwest heast interior
  rcases ancestors x interior with ⟨oldX, oldCoordinate, oldInterior⟩
  have oldWest : quarterWest west < oldX := by
    rw [← sparseCoordinate_lt_iff]
    simpa [oldCoordinate] using hwest
  have oldEast : oldX < quarterEast east := by
    rw [← sparseCoordinate_lt_iff]
    simpa [oldCoordinate] using heast
  rcases live_endpoint_of_verticalInterior oldInterior with oldLive | oldLive
  · let candidate : Candidate := ⟨⟨oldX, oldRow, .south⟩, true⟩
    have backed := backedBy_row row oldWest oldEast oldInterior
      (candidatePort := candidate.port) (Or.inl (by rfl)) (by
        simpa [candidate] using oldLive)
    have targetLive : portPresent (iterateRefine 2 grid)
        ⟨x, fineRow, .south⟩ = true := by
      have sparseLive : portPresent (iterateRefine 2 grid)
          (sparsePort ⟨oldX, oldRow, .south⟩) = true := by
        rw [portPresent_sparse]
        exact oldLive
      simpa only [sparsePort, oldCoordinate, coordinate] using sparseLive
    left
    apply projectsTo_of_backedCandidate backed (by rfl) _ targetLive
    simpa [candidate, sparsePort, oldCoordinate, coordinate] using
      (Path.refl (indexGrid := iterateRefine 2 grid)
        ⟨x, fineRow, .south⟩)
  · let candidate : Candidate := ⟨⟨oldX, oldRow, .north⟩, true⟩
    have backed := backedBy_row row oldWest oldEast oldInterior
      (candidatePort := candidate.port) (Or.inr (by rfl)) (by
        simpa [candidate] using oldLive)
    have targetLive : portPresent (iterateRefine 2 grid)
        ⟨x, fineRow, .north⟩ = true := by
      have sparseLive : portPresent (iterateRefine 2 grid)
          (sparsePort ⟨oldX, oldRow, .north⟩) = true := by
        rw [portPresent_sparse]
        exact oldLive
      simpa only [sparsePort, oldCoordinate, coordinate] using sparseLive
    right
    apply projectsTo_of_backedCandidate backed (by rfl) _ targetLive
    simpa [candidate, sparsePort, oldCoordinate, coordinate] using
      (Path.refl (indexGrid := iterateRefine 2 grid)
        ⟨x, fineRow, .north⟩)

/-- Sparse horizontal ancestors project one retained old column to the fine column. -/
theorem horizontalProjectionAt_of_sparseAncestors
    {grid : Nat → Nat → Index} {west east south north oldColumn fineColumn : Nat}
    (column : LiveColumnCertificate grid west east south north oldColumn)
    (coordinate : fineColumn = sparseCoordinate oldColumn)
    (ancestors : HorizontalSparseAncestors grid oldColumn fineColumn) :
    HorizontalProjectionAt grid west east south north fineColumn := by
  intro y hsouth hnorth interior
  rcases ancestors y interior with ⟨oldY, oldCoordinate, oldInterior⟩
  have oldSouth : quarterSouth south < oldY := by
    rw [← sparseCoordinate_lt_iff]
    simpa [oldCoordinate] using hsouth
  have oldNorth : oldY < quarterNorth north := by
    rw [← sparseCoordinate_lt_iff]
    simpa [oldCoordinate] using hnorth
  rcases live_endpoint_of_horizontalInterior oldInterior with oldLive | oldLive
  · let candidate : Candidate := ⟨⟨oldColumn, oldY, .west⟩, true⟩
    have backed := backedBy_column column oldSouth oldNorth oldInterior
      (candidatePort := candidate.port) (Or.inl (by rfl)) (by
        simpa [candidate] using oldLive)
    have targetLive : portPresent (iterateRefine 2 grid)
        ⟨fineColumn, y, .west⟩ = true := by
      have sparseLive : portPresent (iterateRefine 2 grid)
          (sparsePort ⟨oldColumn, oldY, .west⟩) = true := by
        rw [portPresent_sparse]
        exact oldLive
      simpa only [sparsePort, oldCoordinate, coordinate] using sparseLive
    left
    apply projectsTo_of_backedCandidate backed (by rfl) _ targetLive
    simpa [candidate, sparsePort, oldCoordinate, coordinate] using
      (Path.refl (indexGrid := iterateRefine 2 grid)
        ⟨fineColumn, y, .west⟩)
  · let candidate : Candidate := ⟨⟨oldColumn, oldY, .east⟩, true⟩
    have backed := backedBy_column column oldSouth oldNorth oldInterior
      (candidatePort := candidate.port) (Or.inr (by rfl)) (by
        simpa [candidate] using oldLive)
    have targetLive : portPresent (iterateRefine 2 grid)
        ⟨fineColumn, y, .east⟩ = true := by
      have sparseLive : portPresent (iterateRefine 2 grid)
          (sparsePort ⟨oldColumn, oldY, .east⟩) = true := by
        rw [portPresent_sparse]
        exact oldLive
      simpa only [sparsePort, oldCoordinate, coordinate] using sparseLive
    right
    apply projectsTo_of_backedCandidate backed (by rfl) _ targetLive
    simpa [candidate, sparsePort, oldCoordinate, coordinate] using
      (Path.refl (indexGrid := iterateRefine 2 grid)
        ⟨fineColumn, y, .east⟩)

end SparseFreeLineLocalProjection
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
