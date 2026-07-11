/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104BorderCoverage

/-!
# Executable audits for border-state coverage

The Boolean checker performs one weighted flood and checks every live target
in a finite rectangle. Its soundness theorem packages a successful audit as
the proof-free coverage proposition used by the recurrence quotient.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace BorderCoverageAudit

open RedCycles RedShadeCycles RedShadeGraph RedShadeGraphRefinement
  RedShadeGraphSearch RedShadeGraphWeightedSearch
  ShadedFreeLineOffsets ShadedFreeLineProjectionCandidates
  ShadedFreeLineProjectionSourceLists ShadedFreeLineRecurrence
  BorderCoverage Signals.FreeCellLocal

set_option maxRecDepth 100000

def reachedCheck (grid : Nat → Nat → Index) (nodes : List ReachNode)
    (target : Port) : Bool :=
  portPresent (iterateRefine 2 grid) target &&
    nodes.any fun node => node.parity && decide (node.current = target)

theorem reachedCheck_sound
    {grid : Nat → Nat → Index} {candidates : List Candidate}
    {width height fuel : Nat} {nodes : List ReachNode} {target : Port}
    (hnodes : nodes = exploreFastWeightedReach (iterateRefine 2 grid)
      width height fuel (candidates.map Candidate.weightedStart))
    (reached : reachedCheck grid nodes target = true) :
    RawReached grid candidates width height fuel target := by
  simp only [reachedCheck, Bool.and_eq_true, List.any_eq_true,
    decide_eq_true_eq] at reached
  rcases reached.2 with ⟨node, hnode, hparity, hcurrent⟩
  refine ⟨node, ?_, hparity, hcurrent, reached.1⟩
  simpa [hnodes] using hnode

def coverageCheck (grid : Nat → Nat → Index)
    (west east south north : Nat) (candidates : List Candidate)
    (fineOffsets : List Nat) (fineCoordinate : Nat → Nat)
    (width height fuel : Nat) : Bool :=
  let nodes := exploreFastWeightedReach (iterateRefine 2 grid)
    width height fuel (candidates.map Candidate.weightedStart)
  let vertical := fineOffsets.all fun offset =>
    (List.range width).all fun x =>
      let required :=
        decide (quarterWest (4 * west) < x) &&
        decide (x < quarterEast (4 * east)) &&
        (Signals.verticalInterior?
          (componentAt (iterateRefine 2 grid) x (fineCoordinate offset))
          (quadrantAt x (fineCoordinate offset))).isSome
      !required ||
        reachedCheck grid nodes ⟨x, fineCoordinate offset, .south⟩ ||
        reachedCheck grid nodes ⟨x, fineCoordinate offset, .north⟩
  let horizontal := fineOffsets.all fun offset =>
    (List.range height).all fun y =>
      let required :=
        decide (quarterSouth (4 * south) < y) &&
        decide (y < quarterNorth (4 * north)) &&
        (Signals.horizontalInterior?
          (componentAt (iterateRefine 2 grid) (fineCoordinate offset) y)
          (quadrantAt (fineCoordinate offset) y)).isSome
      !required ||
        reachedCheck grid nodes ⟨fineCoordinate offset, y, .west⟩ ||
        reachedCheck grid nodes ⟨fineCoordinate offset, y, .east⟩
  vertical && horizontal

set_option linter.flexible false in
set_option maxHeartbeats 1000000 in
-- Normalizing the nested executable bounded quantifiers.
theorem coverageCheck_sound
    {grid : Nat → Nat → Index} {west east south north : Nat}
    {candidates : List Candidate} {fineOffsets : List Nat}
    {fineCoordinate : Nat → Nat} {width height fuel : Nat}
    (hwidth : quarterEast (4 * east) ≤ width)
    (hheight : quarterNorth (4 * north) ≤ height)
    (checked : coverageCheck grid west east south north candidates
      fineOffsets fineCoordinate width height fuel = true) :
    RawCovers grid west east south north candidates
      fineOffsets fineCoordinate := by
  let nodes := exploreFastWeightedReach (iterateRefine 2 grid)
    width height fuel (candidates.map Candidate.weightedStart)
  have hnodes : nodes = exploreFastWeightedReach (iterateRefine 2 grid)
      width height fuel (candidates.map Candidate.weightedStart) := rfl
  simp only [coverageCheck, Bool.and_eq_true, List.all_eq_true,
    List.mem_range] at checked
  refine ⟨width, height, fuel, ?_, ?_⟩
  · intro offset hoffset x hwest heast interior
    have hx : x < width := lt_of_lt_of_le heast hwidth
    have covered := checked.1 offset hoffset x hx
    have hinterior : (Signals.verticalInterior?
        (componentAt (iterateRefine 2 grid) x (fineCoordinate offset))
        (quadrantAt x (fineCoordinate offset))).isSome = true := by
      exact Option.isSome_iff_ne_none.mpr interior
    simp [hwest, heast, hinterior] at covered
    rcases covered with covered | covered
    · apply Or.inl
      apply reachedCheck_sound hnodes
      simpa [nodes] using covered
    · apply Or.inr
      apply reachedCheck_sound hnodes
      simpa [nodes] using covered
  · intro offset hoffset y hsouth hnorth interior
    have hy : y < height := lt_of_lt_of_le hnorth hheight
    have covered := checked.2 offset hoffset y hy
    have hinterior : (Signals.horizontalInterior?
        (componentAt (iterateRefine 2 grid) (fineCoordinate offset) y)
        (quadrantAt (fineCoordinate offset) y)).isSome = true := by
      exact Option.isSome_iff_ne_none.mpr interior
    simp [hsouth, hnorth, hinterior] at covered
    rcases covered with covered | covered
    · apply Or.inl
      apply reachedCheck_sound hnodes
      simpa [nodes] using covered
    · apply Or.inr
      apply reachedCheck_sound hnodes
      simpa [nodes] using covered

def auditWidth (phase : Phase) (depth : Nat) : Nat :=
  quarterEast (4 * east phase depth) + 1

def auditHeight (phase : Phase) (depth : Nat) : Nat :=
  quarterNorth (4 * east phase depth) + 1

def auditFuel (phase : Phase) (depth : Nat) : Nat :=
  8 * auditWidth phase depth * auditHeight phase depth + 1

def audit (phase : Phase) (depth : Nat) (parent : Index) : Bool :=
  let grid := ShadedFreeLineRecurrence.localGrid phase depth parent
  coverageCheck grid
    (west phase depth) (east phase depth)
    (west phase depth) (east phase depth)
    (patternCandidates grid
      (west phase depth) (east phase depth)
      (west phase depth) (east phase depth)
      (freeOffsets depth) (lineCoordinate phase depth))
    (freeOffsets (depth + 1)) (lineCoordinate phase (depth + 1))
    (auditWidth phase depth) (auditHeight phase depth)
    (auditFuel phase depth)

theorem rawCoverageAt_of_audit
    {phase : Phase} {depth : Nat} {parent : Index}
    (checked : audit phase depth parent = true) :
    RawCoverageAt phase depth parent := by
  refine coverageCheck_sound
    (width := auditWidth phase depth) (height := auditHeight phase depth)
    (fuel := auditFuel phase depth) ?_ ?_ ?_
  · simp [auditWidth]
  · simp [auditHeight]
  · exact checked

end BorderCoverageAudit
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
