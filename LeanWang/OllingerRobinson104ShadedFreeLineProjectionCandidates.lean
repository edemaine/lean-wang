/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104ShadedFreeLinePatternRefinement

/-!
# Executable source candidates for whole-pattern projection

Finite audits enumerate source ports, while retained row and column
certificates choose their actual endpoint propositionally. A live candidate on
the same perpendicular segment is evenly connected to that chosen endpoint,
so executable candidates can soundly stand in for proof-carrying sources.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace ShadedFreeLineProjectionCandidates

open OrientedRedCycles RedCycles RedShadeCycles RedShadeGraph RedShadeGraphBoards
  RedShadeGraphRefinement RedShadeGraphSearch RedShadeGraphWeightedSearch ShadedFreeLineGraph
  ShadedFreeLinePatternRefinement Signals.FreeCellLocal

set_option maxRecDepth 20000

structure Candidate where
  port : Port
  parity : Bool
deriving DecidableEq, Repr

def Candidate.weightedStart (candidate : Candidate) : WeightedStart where
  port := sparsePort candidate.port
  parity := candidate.parity

def Candidate.BackedBy
    {grid : Nat → Nat → Index} {west east south north : Nat}
    (candidate : Candidate) : Prop :=
  ∃ source : WeightedSource grid west east south north,
    source.parity = candidate.parity ∧
      Path (iterateRefine 2 grid) (sparsePort source.port)
        (sparsePort candidate.port) false

theorem hasVertical_of_interior_of_live_ports
    {grid : Nat → Nat → Index} {x y : Nat}
    (interior : Signals.verticalInterior?
      (componentAt grid x y) (quadrantAt x y) ≠ none)
    (southLive : portPresent grid ⟨x, y, .south⟩ = true)
    (northLive : portPresent grid ⟨x, y, .north⟩ = true) :
    RedShades.hasVertical
      (componentAt grid x y) (quadrantAt x y) = true := by
  generalize hcomponent : componentAt grid x y = component at *
  generalize hquadrant : quadrantAt x y = quadrant at *
  cases component <;> cases quadrant <;>
    simp_all [Signals.verticalInterior?, portPresent, RedShades.hasVertical,
      RedShades.hasSouth, RedShades.hasNorth, RedShades.cornerSouth,
      RedShades.cornerNorth]

theorem hasHorizontal_of_interior_of_live_ports
    {grid : Nat → Nat → Index} {x y : Nat}
    (interior : Signals.horizontalInterior?
      (componentAt grid x y) (quadrantAt x y) ≠ none)
    (westLive : portPresent grid ⟨x, y, .west⟩ = true)
    (eastLive : portPresent grid ⟨x, y, .east⟩ = true) :
    RedShades.hasHorizontal
      (componentAt grid x y) (quadrantAt x y) = true := by
  generalize hcomponent : componentAt grid x y = component at *
  generalize hquadrant : quadrantAt x y = quadrant at *
  cases component <;> cases quadrant <;>
    simp_all [Signals.horizontalInterior?, portPresent, RedShades.hasHorizontal,
      RedShades.hasWest, RedShades.hasEast, RedShades.cornerWest,
      RedShades.cornerEast]

theorem backedBy_cycle
    {grid : Nat → Nat → Index} {west east south north : Nat}
    (cycle : CycleOn grid west east south north) {port : Port}
    (onCycle : OnCycle west east south north port) :
    Candidate.BackedBy (grid := grid) (west := west) (east := east)
      (south := south) (north := north) ⟨port, false⟩ := by
  exact ⟨WeightedSource.ofCycle cycle onCycle, rfl, Path.refl _⟩

theorem backedBy_row
    {grid : Nat → Nat → Index} {west east south north row x : Nat}
    (certificate : LiveRowCertificate grid west east south north row)
    (hwest : quarterWest west < x) (heast : x < quarterEast east)
    (interior : Signals.verticalInterior?
      (componentAt grid x row) (quadrantAt x row) ≠ none)
    {candidatePort : Port}
    (candidateEndpoint : candidatePort = ⟨x, row, .south⟩ ∨
      candidatePort = ⟨x, row, .north⟩)
    (candidateLive : portPresent grid candidatePort = true) :
    Candidate.BackedBy (grid := grid) (west := west) (east := east)
      (south := south) (north := north) ⟨candidatePort, true⟩ := by
  rcases certificate x hwest heast interior with
    ⟨source, sourceOdd, sourceEndpoint⟩
  refine ⟨source, sourceOdd, ?_⟩
  rcases sourceEndpoint with sourceEndpoint | sourceEndpoint <;>
    rcases candidateEndpoint with candidateEndpoint | candidateEndpoint
  · rw [sourceEndpoint, candidateEndpoint]
    exact Path.refl _
  · have vertical := hasVertical_of_interior_of_live_ports interior
      (by simpa [sourceEndpoint] using source.portLive)
      (by simpa [candidateEndpoint] using candidateLive)
    have coarse := Path.ofLink (Link.vertical x row vertical)
    have sourceLive : portPresent grid ⟨x, row, .south⟩ = true := by
      simpa [sourceEndpoint] using source.portLive
    have targetLive : portPresent grid ⟨x, row, .north⟩ = true := by
      simpa [candidateEndpoint] using candidateLive
    simpa [sourceEndpoint, candidateEndpoint] using
      path_refine_sparse coarse sourceLive targetLive
  · have vertical := hasVertical_of_interior_of_live_ports interior
      (by simpa [candidateEndpoint] using candidateLive)
      (by simpa [sourceEndpoint] using source.portLive)
    have coarse := Path.ofLink (Link.symm (Link.vertical x row vertical))
    have sourceLive : portPresent grid ⟨x, row, .north⟩ = true := by
      simpa [sourceEndpoint] using source.portLive
    have targetLive : portPresent grid ⟨x, row, .south⟩ = true := by
      simpa [candidateEndpoint] using candidateLive
    simpa [sourceEndpoint, candidateEndpoint] using
      path_refine_sparse coarse sourceLive targetLive
  · rw [sourceEndpoint, candidateEndpoint]
    exact Path.refl _

theorem backedBy_column
    {grid : Nat → Nat → Index} {west east south north column y : Nat}
    (certificate : LiveColumnCertificate grid west east south north column)
    (hsouth : quarterSouth south < y) (hnorth : y < quarterNorth north)
    (interior : Signals.horizontalInterior?
      (componentAt grid column y) (quadrantAt column y) ≠ none)
    {candidatePort : Port}
    (candidateEndpoint : candidatePort = ⟨column, y, .west⟩ ∨
      candidatePort = ⟨column, y, .east⟩)
    (candidateLive : portPresent grid candidatePort = true) :
    Candidate.BackedBy (grid := grid) (west := west) (east := east)
      (south := south) (north := north) ⟨candidatePort, true⟩ := by
  rcases certificate y hsouth hnorth interior with
    ⟨source, sourceOdd, sourceEndpoint⟩
  refine ⟨source, sourceOdd, ?_⟩
  rcases sourceEndpoint with sourceEndpoint | sourceEndpoint <;>
    rcases candidateEndpoint with candidateEndpoint | candidateEndpoint
  · rw [sourceEndpoint, candidateEndpoint]
    exact Path.refl _
  · have horizontal := hasHorizontal_of_interior_of_live_ports interior
      (by simpa [sourceEndpoint] using source.portLive)
      (by simpa [candidateEndpoint] using candidateLive)
    have coarse := Path.ofLink (Link.horizontal column y horizontal)
    have sourceLive : portPresent grid ⟨column, y, .west⟩ = true := by
      simpa [sourceEndpoint] using source.portLive
    have targetLive : portPresent grid ⟨column, y, .east⟩ = true := by
      simpa [candidateEndpoint] using candidateLive
    simpa [sourceEndpoint, candidateEndpoint] using
      path_refine_sparse coarse sourceLive targetLive
  · have horizontal := hasHorizontal_of_interior_of_live_ports interior
      (by simpa [candidateEndpoint] using candidateLive)
      (by simpa [sourceEndpoint] using source.portLive)
    have coarse := Path.ofLink (Link.symm (Link.horizontal column y horizontal))
    have sourceLive : portPresent grid ⟨column, y, .east⟩ = true := by
      simpa [sourceEndpoint] using source.portLive
    have targetLive : portPresent grid ⟨column, y, .west⟩ = true := by
      simpa [candidateEndpoint] using candidateLive
    simpa [sourceEndpoint, candidateEndpoint] using
      path_refine_sparse coarse sourceLive targetLive
  · rw [sourceEndpoint, candidateEndpoint]
    exact Path.refl _

structure Family (grid : Nat → Nat → Index)
    (west east south north : Nat) where
  candidates : List Candidate
  backed : ∀ candidate ∈ candidates,
    Candidate.BackedBy (grid := grid) (west := west) (east := east)
      (south := south) (north := north) candidate

def Family.append
    {grid : Nat → Nat → Index} {west east south north : Nat}
    (first second : Family grid west east south north) :
    Family grid west east south north where
  candidates := first.candidates ++ second.candidates
  backed := by
    intro candidate hcandidate
    rcases List.mem_append.1 hcandidate with hcandidate | hcandidate
    · exact first.backed candidate hcandidate
    · exact second.backed candidate hcandidate

def Family.cycle
    {grid : Nat → Nat → Index} {west east south north : Nat}
    (cycle : CycleOn grid west east south north) (ports : List Port)
    (onCycle : ∀ port ∈ ports, OnCycle west east south north port) :
    Family grid west east south north where
  candidates := ports.map fun port => ⟨port, false⟩
  backed := by
    intro candidate hcandidate
    rcases List.mem_map.1 hcandidate with ⟨port, hport, rfl⟩
    exact backedBy_cycle cycle (onCycle port hport)

def Family.row
    {grid : Nat → Nat → Index} {west east south north row : Nat}
    (certificate : LiveRowCertificate grid west east south north row)
    (ports : List Port)
    (valid : ∀ port ∈ ports,
      ∃ x, quarterWest west < x ∧ x < quarterEast east ∧
        Signals.verticalInterior?
          (componentAt grid x row) (quadrantAt x row) ≠ none ∧
        (port = ⟨x, row, .south⟩ ∨ port = ⟨x, row, .north⟩) ∧
        portPresent grid port = true) :
    Family grid west east south north where
  candidates := ports.map fun port => ⟨port, true⟩
  backed := by
    intro candidate hcandidate
    rcases List.mem_map.1 hcandidate with ⟨port, hport, rfl⟩
    rcases valid port hport with
      ⟨x, hwest, heast, interior, endpoint, live⟩
    exact backedBy_row certificate hwest heast interior endpoint live

def Family.column
    {grid : Nat → Nat → Index} {west east south north column : Nat}
    (certificate : LiveColumnCertificate grid west east south north column)
    (ports : List Port)
    (valid : ∀ port ∈ ports,
      ∃ y, quarterSouth south < y ∧ y < quarterNorth north ∧
        Signals.horizontalInterior?
          (componentAt grid column y) (quadrantAt column y) ≠ none ∧
        (port = ⟨column, y, .west⟩ ∨ port = ⟨column, y, .east⟩) ∧
        portPresent grid port = true) :
    Family grid west east south north where
  candidates := ports.map fun port => ⟨port, true⟩
  backed := by
    intro candidate hcandidate
    rcases List.mem_map.1 hcandidate with ⟨port, hport, rfl⟩
    rcases valid port hport with
      ⟨y, hsouth, hnorth, interior, endpoint, live⟩
    exact backedBy_column certificate hsouth hnorth interior endpoint live

/-- A total-odd node reached from backed executable candidates projects. -/
theorem projectsTo_of_candidateNode
    {grid : Nat → Nat → Index} {west east south north : Nat}
    (candidates : List Candidate)
    (backed : ∀ candidate ∈ candidates,
      Candidate.BackedBy (grid := grid) (west := west) (east := east)
        (south := south) (north := north) candidate)
    {width height fuel : Nat} {node : Node} {target : Port}
    (hnode : node ∈ exploreFastWeighted (iterateRefine 2 grid)
      width height fuel (candidates.map Candidate.weightedStart))
    (hparity : node.parity = true) (hcurrent : node.current = target)
    (targetLive : portPresent (iterateRefine 2 grid) target = true) :
    Nonempty (ProjectsTo (grid := grid) (west := west) (east := east)
      (south := south) (north := north) target) := by
  rcases exploreFastWeighted_sound hnode with
    ⟨start, hstart, _horigin, tail⟩
  rcases List.mem_map.1 hstart with ⟨candidate, hcandidates, rfl⟩
  rcases backed candidate hcandidates with ⟨source, sourceParity, head⟩
  refine ⟨{
    source := source
    path := ?_
    targetLive := targetLive
  }⟩
  rw [hcurrent] at tail
  have path := Path.trans head tail
  simpa [Candidate.weightedStart, sourceParity, hparity] using path

theorem projectsTo_of_familyNode
    {grid : Nat → Nat → Index} {west east south north : Nat}
    (family : Family grid west east south north)
    {width height fuel : Nat} {node : Node} {target : Port}
    (hnode : node ∈ exploreFastWeighted (iterateRefine 2 grid)
      width height fuel (family.candidates.map Candidate.weightedStart))
    (hparity : node.parity = true) (hcurrent : node.current = target)
    (targetLive : portPresent (iterateRefine 2 grid) target = true) :
    Nonempty (ProjectsTo (grid := grid) (west := west) (east := east)
      (south := south) (north := north) target) :=
  projectsTo_of_candidateNode family.candidates family.backed hnode
    hparity hcurrent targetLive

end ShadedFreeLineProjectionCandidates
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
