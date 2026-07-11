/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104BorderGeometry
import LeanWang.OllingerRobinson104ShadedFreeLineRecurrence

/-!
# Border-state quotient of shaded free-line coverage

This module removes proof-valued source certificates from the executable
coverage obligation and reduces its parent alphabet from 104 indices to the 56
reachable thin/thick border states.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace BorderCoverage

open RedCycles RedShadeCycles RedShadeGraph RedShadeGraphRefinement
  RedShadeGraphSearch RedShadeGraphWeightedSearch
  ShadedFreeLineGraph ShadedFreeLineProjectionCandidates
  ShadedFreeLineProjectionSourceLists ShadedFreeLineRecurrence
  ShadedFreeLineOffsets ShadedFreeLinePatternRefinement
  Signals.FreeCellLocal

set_option maxRecDepth 100000

def RawReached (grid : Nat → Nat → Index) (candidates : List Candidate)
    (width height fuel : Nat) (target : Port) : Prop :=
  ∃ node ∈ exploreFastWeightedReach (iterateRefine 2 grid)
      width height fuel (candidates.map Candidate.weightedStart),
    node.parity = true ∧ node.current = target ∧
      portPresent (iterateRefine 2 grid) target = true

def RawCovers (grid : Nat → Nat → Index) (west east south north : Nat)
    (candidates : List Candidate) (fineOffsets : List Nat)
    (fineCoordinate : Nat → Nat) : Prop :=
  ∃ width height fuel,
    (∀ offset ∈ fineOffsets, ∀ x,
      quarterWest (4 * west) < x → x < quarterEast (4 * east) →
      Signals.verticalInterior?
        (componentAt (iterateRefine 2 grid) x (fineCoordinate offset))
        (quadrantAt x (fineCoordinate offset)) ≠ none →
      RawReached grid candidates width height fuel
          ⟨x, fineCoordinate offset, .south⟩ ∨
        RawReached grid candidates width height fuel
          ⟨x, fineCoordinate offset, .north⟩) ∧
    (∀ offset ∈ fineOffsets, ∀ y,
      quarterSouth (4 * south) < y → y < quarterNorth (4 * north) →
      Signals.horizontalInterior?
        (componentAt (iterateRefine 2 grid) (fineCoordinate offset) y)
        (quadrantAt (fineCoordinate offset) y) ≠ none →
      RawReached grid candidates width height fuel
          ⟨fineCoordinate offset, y, .west⟩ ∨
        RawReached grid candidates width height fuel
          ⟨fineCoordinate offset, y, .east⟩)

def RawCoverageAt (phase : Phase) (depth : Nat) (parent : Index) : Prop :=
  RawCovers (ShadedFreeLineRecurrence.localGrid phase depth parent)
    (west phase depth) (east phase depth)
    (west phase depth) (east phase depth)
    (patternCandidates (ShadedFreeLineRecurrence.localGrid phase depth parent)
      (west phase depth) (east phase depth)
      (west phase depth) (east phase depth)
      (freeOffsets depth) (lineCoordinate phase depth))
    (freeOffsets (depth + 1)) (lineCoordinate phase (depth + 1))

theorem patternFamily_covers_iff_raw
    {phase : Phase} {depth : Nat} {parent : Index}
    (rows : ∀ offset ∈ freeOffsets depth,
      LiveRowCertificate (ShadedFreeLineRecurrence.localGrid phase depth parent)
        (west phase depth) (east phase depth)
        (west phase depth) (east phase depth)
        (lineCoordinate phase depth offset))
    (columns : ∀ offset ∈ freeOffsets depth,
      LiveColumnCertificate (ShadedFreeLineRecurrence.localGrid phase depth parent)
        (west phase depth) (east phase depth)
        (west phase depth) (east phase depth)
        (lineCoordinate phase depth offset)) :
    (patternFamily (canonicalCycle phase depth parent)
      (freeOffsets depth) (lineCoordinate phase depth) rows columns).CoversPattern
        (freeOffsets (depth + 1)) (lineCoordinate phase (depth + 1)) ↔
      RawCoverageAt phase depth parent := by
  rfl

theorem coverageStep_of_rawCoverage
    (coverage : ∀ phase depth parent, RawCoverageAt phase depth parent) :
    CoverageStep := by
  intro phase depth parent rows columns
  exact (patternFamily_covers_iff_raw rows columns).2
    (coverage phase depth parent)

theorem rawReached_iff_of_congr
    {first second : Nat → Nat → Index}
    (sameFine : BorderGeometry.SameComponents
      (iterateRefine 2 first) (iterateRefine 2 second))
    {firstCandidates secondCandidates : List Candidate}
    (candidates : firstCandidates = secondCandidates)
    (width height fuel : Nat) (target : Port) :
    RawReached first firstCandidates width height fuel target ↔
      RawReached second secondCandidates width height fuel target := by
  unfold RawReached
  rw [candidates,
    BorderGeometry.exploreFastWeightedReach_congr sameFine width height fuel,
    BorderGeometry.portPresent_congr sameFine target]

theorem rawCovers_of_congr
    {first second : Nat → Nat → Index}
    (sameFine : BorderGeometry.SameComponents
      (iterateRefine 2 first) (iterateRefine 2 second))
    {firstCandidates secondCandidates : List Candidate}
    (candidates : firstCandidates = secondCandidates)
    {west east south north : Nat} {fineOffsets : List Nat}
    {fineCoordinate : Nat → Nat}
    (coverage : RawCovers first west east south north firstCandidates
      fineOffsets fineCoordinate) :
    RawCovers second west east south north secondCandidates
      fineOffsets fineCoordinate := by
  rcases coverage with ⟨width, height, fuel, vertical, horizontal⟩
  refine ⟨width, height, fuel, ?_, ?_⟩
  · intro offset hoffset x hwest heast interior
    have firstInterior : Signals.verticalInterior?
        (componentAt (iterateRefine 2 first) x (fineCoordinate offset))
        (quadrantAt x (fineCoordinate offset)) ≠ none := by
      simpa [sameFine x (fineCoordinate offset)] using interior
    rcases vertical offset hoffset x hwest heast firstInterior with
      reached | reached
    · exact Or.inl ((rawReached_iff_of_congr sameFine candidates
        width height fuel _).1 reached)
    · exact Or.inr ((rawReached_iff_of_congr sameFine candidates
        width height fuel _).1 reached)
  · intro offset hoffset y hsouth hnorth interior
    have firstInterior : Signals.horizontalInterior?
        (componentAt (iterateRefine 2 first) (fineCoordinate offset) y)
        (quadrantAt (fineCoordinate offset) y) ≠ none := by
      simpa [sameFine (fineCoordinate offset) y] using interior
    rcases horizontal offset hoffset y hsouth hnorth firstInterior with
      reached | reached
    · exact Or.inl ((rawReached_iff_of_congr sameFine candidates
        width height fuel _).1 reached)
    · exact Or.inr ((rawReached_iff_of_congr sameFine candidates
        width height fuel _).1 reached)

theorem sameComponents_localGrid_canonicalIndex
    (phase : Phase) (depth : Nat) (parent : Index) :
    BorderGeometry.SameComponents
      (ShadedFreeLineRecurrence.localGrid phase depth
        (BorderSubstitution.canonicalIndex parent))
      (ShadedFreeLineRecurrence.localGrid phase depth parent) := by
  change BorderGeometry.SameComponents
    (iterateRefine (refinementDepth phase depth)
      (fun _ _ => BorderSubstitution.canonicalIndex parent))
    (iterateRefine (refinementDepth phase depth) (fun _ _ => parent))
  have same := BorderGeometry.sameComponents_iterateRefine_canonicalizeGrid
    (refinementDepth phase depth) (fun _ _ => parent)
  have gridEquality : (fun _ _ => BorderSubstitution.canonicalIndex parent) =
      BorderSubstitution.canonicalizeGrid (fun _ _ => parent) := by
    funext x y
    rfl
  rw [gridEquality]
  exact same

theorem sameComponents_fineLocalGrid_canonicalIndex
    (phase : Phase) (depth : Nat) (parent : Index) :
    BorderGeometry.SameComponents
      (iterateRefine 2
        (ShadedFreeLineRecurrence.localGrid phase depth
          (BorderSubstitution.canonicalIndex parent)))
      (iterateRefine 2
        (ShadedFreeLineRecurrence.localGrid phase depth parent)) := by
  change BorderGeometry.SameComponents
    (iterateRefine 2 (iterateRefine (refinementDepth phase depth)
      (fun _ _ => BorderSubstitution.canonicalIndex parent)))
    (iterateRefine 2 (iterateRefine (refinementDepth phase depth)
      (fun _ _ => parent)))
  rw [PlaneRedBoards.iterateRefine_add,
    PlaneRedBoards.iterateRefine_add]
  have same := BorderGeometry.sameComponents_iterateRefine_canonicalizeGrid
    (2 + refinementDepth phase depth) (fun _ _ => parent)
  have gridEquality : (fun _ _ => BorderSubstitution.canonicalIndex parent) =
      BorderSubstitution.canonicalizeGrid (fun _ _ => parent) := by
    funext x y
    rfl
  rw [gridEquality]
  exact same

theorem rawCoverageAt_of_canonicalIndex
    {phase : Phase} {depth : Nat} {parent : Index}
    (coverage : RawCoverageAt phase depth
      (BorderSubstitution.canonicalIndex parent)) :
    RawCoverageAt phase depth parent := by
  apply rawCovers_of_congr
    (sameComponents_fineLocalGrid_canonicalIndex phase depth parent)
  · exact BorderGeometry.patternCandidates_congr
      (sameComponents_localGrid_canonicalIndex phase depth parent)
      (west phase depth) (east phase depth)
      (west phase depth) (east phase depth)
      (freeOffsets depth) (lineCoordinate phase depth)
  · exact coverage

/-- It suffices to prove coverage for the 56 canonical border states. -/
def CanonicalCoverage : Prop :=
  ∀ phase depth state, state ∈ BorderSubstitution.states →
    RawCoverageAt phase depth (BorderSubstitution.representative state)

theorem rawCoverage_of_canonicalCoverage
    (coverage : CanonicalCoverage) :
    ∀ phase depth parent, RawCoverageAt phase depth parent := by
  intro phase depth parent
  exact rawCoverageAt_of_canonicalIndex
    (coverage phase depth (BorderSubstitution.indexState parent)
      (BorderSubstitution.indexState_mem_states parent))

theorem coverageStep_of_canonicalCoverage
    (coverage : CanonicalCoverage) : CoverageStep :=
  coverageStep_of_rawCoverage (rawCoverage_of_canonicalCoverage coverage)

end BorderCoverage
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
