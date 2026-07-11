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
  RedShadeGraphSearchSoundness
  RedShadeGraphWeightedSearch
  RedShadeGraphTranslation
  RefinementTranslation
  BorderCoverageLocalAudit
  ShadedFreeLineGraph ShadedFreeLinePatternRefinement
  ShadedFreeLineProjectionCandidates Signals.FreeCellLocal
  SparseFreeLineLocalStates

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
      RedShades.cornerNorth, Quadrant.xBit]

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
      RedShades.cornerEast, Quadrant.yBit]

theorem verticalInterior_of_live_endpoint
    {grid : Nat → Nat → Index} {x y : Nat}
    (live : portPresent grid ⟨x, y, .south⟩ = true ∨
      portPresent grid ⟨x, y, .north⟩ = true) :
    Signals.verticalInterior?
      (componentAt grid x y) (quadrantAt x y) ≠ none := by
  generalize hcomponent : componentAt grid x y = component at *
  generalize hquadrant : quadrantAt x y = quadrant at *
  cases component <;> cases quadrant <;>
    simp_all [Signals.verticalInterior?, portPresent, RedShades.hasSouth,
      RedShades.hasNorth, RedShades.hasVertical, RedShades.cornerSouth,
      RedShades.cornerNorth, Quadrant.xBit]

theorem horizontalInterior_of_live_endpoint
    {grid : Nat → Nat → Index} {x y : Nat}
    (live : portPresent grid ⟨x, y, .west⟩ = true ∨
      portPresent grid ⟨x, y, .east⟩ = true) :
    Signals.horizontalInterior?
      (componentAt grid x y) (quadrantAt x y) ≠ none := by
  generalize hcomponent : componentAt grid x y = component at *
  generalize hquadrant : quadrantAt x y = quadrant at *
  cases component <;> cases quadrant <;>
    simp_all [Signals.horizontalInterior?, portPresent, RedShades.hasWest,
      RedShades.hasEast, RedShades.hasHorizontal, RedShades.cornerWest,
      RedShades.cornerEast, Quadrant.yBit]

theorem projectsTo_north_of_verticalInterior
    {grid : Nat → Nat → Index} {west east south north x y : Nat}
    (interior : Signals.verticalInterior?
      (componentAt (iterateRefine 2 grid) x y) (quadrantAt x y) ≠ none)
    (northLive : portPresent (iterateRefine 2 grid) ⟨x, y, .north⟩ = true)
    (projected :
      Nonempty (ProjectsTo (grid := grid) (west := west) (east := east)
        (south := south) (north := north) ⟨x, y, .south⟩) ∨
      Nonempty (ProjectsTo (grid := grid) (west := west) (east := east)
        (south := south) (north := north) ⟨x, y, .north⟩)) :
    Nonempty (ProjectsTo (grid := grid) (west := west) (east := east)
      (south := south) (north := north) ⟨x, y, .north⟩) := by
  rcases projected with projected | projected
  · rcases projected with ⟨projection⟩
    have vertical := hasVertical_of_interior_of_live_ports interior
      projection.targetLive northLive
    exact ⟨projection.transEven
      (Path.ofLink (Link.vertical x y vertical)) northLive⟩
  · exact projected

theorem projectsTo_south_of_verticalInterior
    {grid : Nat → Nat → Index} {west east south north x y : Nat}
    (interior : Signals.verticalInterior?
      (componentAt (iterateRefine 2 grid) x y) (quadrantAt x y) ≠ none)
    (southLive : portPresent (iterateRefine 2 grid) ⟨x, y, .south⟩ = true)
    (projected :
      Nonempty (ProjectsTo (grid := grid) (west := west) (east := east)
        (south := south) (north := north) ⟨x, y, .south⟩) ∨
      Nonempty (ProjectsTo (grid := grid) (west := west) (east := east)
        (south := south) (north := north) ⟨x, y, .north⟩)) :
    Nonempty (ProjectsTo (grid := grid) (west := west) (east := east)
      (south := south) (north := north) ⟨x, y, .south⟩) := by
  rcases projected with projected | projected
  · exact projected
  · rcases projected with ⟨projection⟩
    have vertical := hasVertical_of_interior_of_live_ports interior
      southLive projection.targetLive
    exact ⟨projection.transEven
      (Path.ofLink (Link.symm (Link.vertical x y vertical))) southLive⟩

theorem projectsTo_east_of_horizontalInterior
    {grid : Nat → Nat → Index} {west east south north x y : Nat}
    (interior : Signals.horizontalInterior?
      (componentAt (iterateRefine 2 grid) x y) (quadrantAt x y) ≠ none)
    (eastLive : portPresent (iterateRefine 2 grid) ⟨x, y, .east⟩ = true)
    (projected :
      Nonempty (ProjectsTo (grid := grid) (west := west) (east := east)
        (south := south) (north := north) ⟨x, y, .west⟩) ∨
      Nonempty (ProjectsTo (grid := grid) (west := west) (east := east)
        (south := south) (north := north) ⟨x, y, .east⟩)) :
    Nonempty (ProjectsTo (grid := grid) (west := west) (east := east)
      (south := south) (north := north) ⟨x, y, .east⟩) := by
  rcases projected with projected | projected
  · rcases projected with ⟨projection⟩
    have horizontal := hasHorizontal_of_interior_of_live_ports interior
      projection.targetLive eastLive
    exact ⟨projection.transEven
      (Path.ofLink (Link.horizontal x y horizontal)) eastLive⟩
  · exact projected

theorem projectsTo_west_of_horizontalInterior
    {grid : Nat → Nat → Index} {west east south north x y : Nat}
    (interior : Signals.horizontalInterior?
      (componentAt (iterateRefine 2 grid) x y) (quadrantAt x y) ≠ none)
    (westLive : portPresent (iterateRefine 2 grid) ⟨x, y, .west⟩ = true)
    (projected :
      Nonempty (ProjectsTo (grid := grid) (west := west) (east := east)
        (south := south) (north := north) ⟨x, y, .west⟩) ∨
      Nonempty (ProjectsTo (grid := grid) (west := west) (east := east)
        (south := south) (north := north) ⟨x, y, .east⟩)) :
    Nonempty (ProjectsTo (grid := grid) (west := west) (east := east)
      (south := south) (north := north) ⟨x, y, .west⟩) := by
  rcases projected with projected | projected
  · exact projected
  · rcases projected with ⟨projection⟩
    have horizontal := hasHorizontal_of_interior_of_live_ports interior
      westLive projection.targetLive
    exact ⟨projection.transEven
      (Path.ofLink (Link.symm (Link.horizontal x y horizontal))) westLive⟩

/-- A projected old vertical segment follows its north refinement connector. -/
theorem projectsTo_refineNorth
    {grid : Nat → Nat → Index} {west east south north oldX oldRow : Nat}
    (previous : VerticalProjectionAt grid west east south north oldRow)
    (oldWest : quarterWest (4 * west) < oldX)
    (oldEast : oldX < quarterEast (4 * east))
    (oldInterior : Signals.verticalInterior?
      (componentAt (iterateRefine 2 grid) oldX oldRow)
      (quadrantAt oldX oldRow) ≠ none)
    (oldNorthLive : portPresent (iterateRefine 2 grid)
      ⟨oldX, oldRow, .north⟩ = true)
    (refinedNorthLive : portPresent (iterateRefine 2 (iterateRefine 2 grid))
      (refinedPort ⟨oldX, oldRow, .north⟩) = true) :
    Nonempty (ProjectsTo (grid := iterateRefine 2 grid)
      (west := 4 * west) (east := 4 * east)
      (south := 4 * south) (north := 4 * north)
      (refinedPort ⟨oldX, oldRow, .north⟩)) := by
  have projected := previous oldX oldWest oldEast oldInterior
  rcases projectsTo_north_of_verticalInterior oldInterior oldNorthLive projected with
    ⟨projection⟩
  exact ⟨projection.refineEndpoint refinedNorthLive⟩

/-- A projected old horizontal segment follows its east refinement connector. -/
theorem projectsTo_refineEast
    {grid : Nat → Nat → Index} {west east south north oldColumn oldY : Nat}
    (previous : HorizontalProjectionAt grid west east south north oldColumn)
    (oldSouth : quarterSouth (4 * south) < oldY)
    (oldNorth : oldY < quarterNorth (4 * north))
    (oldInterior : Signals.horizontalInterior?
      (componentAt (iterateRefine 2 grid) oldColumn oldY)
      (quadrantAt oldColumn oldY) ≠ none)
    (oldEastLive : portPresent (iterateRefine 2 grid)
      ⟨oldColumn, oldY, .east⟩ = true)
    (refinedEastLive : portPresent (iterateRefine 2 (iterateRefine 2 grid))
      (refinedPort ⟨oldColumn, oldY, .east⟩) = true) :
    Nonempty (ProjectsTo (grid := iterateRefine 2 grid)
      (west := 4 * west) (east := 4 * east)
      (south := 4 * south) (north := 4 * north)
      (refinedPort ⟨oldColumn, oldY, .east⟩)) := by
  have projected := previous oldY oldSouth oldNorth oldInterior
  rcases projectsTo_east_of_horizontalInterior oldInterior oldEastLive projected with
    ⟨projection⟩
  exact ⟨projection.refineEndpoint refinedEastLive⟩

theorem alignedRowStart_backed
    {grid : Nat → Nat → Index} {west east south north oldRow : Nat}
    (row : LiveRowCertificate grid west east south north oldRow)
    (hodd : oldRow % 2 = 1) (blockX localX : Nat)
    (hwest : quarterWest (4 * west) < 8 * blockX + localX)
    (heast : 8 * blockX + localX < quarterEast (4 * east))
    {start : WeightedStart}
    (hstart : start ∈ alignedRowStarts
      (grid blockX (oldRow / 2)) 1 localX) :
    ∃ candidate : Candidate,
      candidate.parity = true ∧
      candidate.BackedBy (grid := grid) (west := west) (east := east)
        (south := south) (north := north) ∧
      translatePort start.port (8 * blockX) (8 * (oldRow / 2)) =
        sparsePort candidate.port := by
  rcases mem_alignedRowStarts hstart with
    ⟨sourceX, hsourceX, sourceCoordinate, startOdd,
      endpoints⟩
  have oldRowEq : 2 * (oldRow / 2) + 1 = oldRow := by
    have hdecompose := Nat.mod_add_div oldRow 2
    omega
  have sparseOldRow : sparseCoordinate oldRow = 8 * (oldRow / 2) + 1 := by
    simp [sparseCoordinate, macroOrigin, localCoordinate, hodd]
  let oldX := 2 * blockX + sourceX
  have oldCoordinate : sparseCoordinate oldX = 8 * blockX + localX := by
    rw [SparseFreeLineLocalTransport.sparseCoordinate_two_block
      blockX sourceX hsourceX, sourceCoordinate]
  have oldWest : quarterWest west < oldX := by
    rw [← sparseCoordinate_lt_iff]
    simpa [oldCoordinate] using hwest
  have oldEast : oldX < quarterEast east := by
    rw [← sparseCoordinate_lt_iff]
    simpa [oldCoordinate] using heast
  rcases endpoints with endpoint | endpoint
  · let candidate : Candidate := ⟨⟨oldX, oldRow, .south⟩, true⟩
    have candidateLive : portPresent grid candidate.port = true := by
      have localLive := endpoint.2
      rw [SparseFreeLineLocalTransport.portPresent_old_block
        grid blockX (oldRow / 2) ⟨sourceX, 1, .south⟩
        hsourceX (show (1 : Nat) < 2 by decide)] at localLive
      simpa only [candidate, oldX, translatePort, oldRowEq] using localLive
    have interior : Signals.verticalInterior?
        (componentAt grid oldX oldRow) (quadrantAt oldX oldRow) ≠ none :=
      verticalInterior_of_live_endpoint (Or.inl candidateLive)
    have backed : candidate.BackedBy (grid := grid) (west := west) (east := east)
        (south := south) (north := north) :=
      backedBy_row row oldWest oldEast interior (Or.inl rfl) candidateLive
    refine ⟨candidate, rfl, backed, ?_⟩
    rw [endpoint.1]
    simp only [candidate, oldX, sparsePort, translatePort, sparseOldRow]
    rw [SparseFreeLineLocalTransport.sparseCoordinate_two_block
      blockX sourceX hsourceX]
    simp [sparseCoordinate, macroOrigin, localCoordinate]
  · let candidate : Candidate := ⟨⟨oldX, oldRow, .north⟩, true⟩
    have candidateLive : portPresent grid candidate.port = true := by
      have localLive := endpoint.2
      rw [SparseFreeLineLocalTransport.portPresent_old_block
        grid blockX (oldRow / 2) ⟨sourceX, 1, .north⟩
        hsourceX (show (1 : Nat) < 2 by decide)] at localLive
      simpa only [candidate, oldX, translatePort, oldRowEq] using localLive
    have interior : Signals.verticalInterior?
        (componentAt grid oldX oldRow) (quadrantAt oldX oldRow) ≠ none :=
      verticalInterior_of_live_endpoint (Or.inr candidateLive)
    have backed : candidate.BackedBy (grid := grid) (west := west) (east := east)
        (south := south) (north := north) :=
      backedBy_row row oldWest oldEast interior (Or.inr rfl) candidateLive
    refine ⟨candidate, rfl, backed, ?_⟩
    rw [endpoint.1]
    simp only [candidate, oldX, sparsePort, translatePort, sparseOldRow]
    rw [SparseFreeLineLocalTransport.sparseCoordinate_two_block
      blockX sourceX hsourceX]
    simp [sparseCoordinate, macroOrigin, localCoordinate]

theorem alignedColumnStart_backed
    {grid : Nat → Nat → Index} {west east south north oldColumn : Nat}
    (column : LiveColumnCertificate grid west east south north oldColumn)
    (hodd : oldColumn % 2 = 1) (blockY localY : Nat)
    (hsouth : quarterSouth (4 * south) < 8 * blockY + localY)
    (hnorth : 8 * blockY + localY < quarterNorth (4 * north))
    {start : WeightedStart}
    (hstart : start ∈ alignedColumnStarts
      (grid (oldColumn / 2) blockY) 1 localY) :
    ∃ candidate : Candidate,
      candidate.parity = true ∧
      candidate.BackedBy (grid := grid) (west := west) (east := east)
        (south := south) (north := north) ∧
      translatePort start.port (8 * (oldColumn / 2)) (8 * blockY) =
        sparsePort candidate.port := by
  rcases mem_alignedColumnStarts hstart with
    ⟨sourceY, hsourceY, sourceCoordinate, startOdd, endpoints⟩
  have oldColumnEq : 2 * (oldColumn / 2) + 1 = oldColumn := by
    have hdecompose := Nat.mod_add_div oldColumn 2
    omega
  have sparseOldColumn :
      sparseCoordinate oldColumn = 8 * (oldColumn / 2) + 1 := by
    simp [sparseCoordinate, macroOrigin, localCoordinate, hodd]
  let oldY := 2 * blockY + sourceY
  have oldCoordinate : sparseCoordinate oldY = 8 * blockY + localY := by
    rw [SparseFreeLineLocalTransport.sparseCoordinate_two_block
      blockY sourceY hsourceY, sourceCoordinate]
  have oldSouth : quarterSouth south < oldY := by
    rw [← sparseCoordinate_lt_iff]
    simpa [oldCoordinate] using hsouth
  have oldNorth : oldY < quarterNorth north := by
    rw [← sparseCoordinate_lt_iff]
    simpa [oldCoordinate] using hnorth
  rcases endpoints with endpoint | endpoint
  · let candidate : Candidate := ⟨⟨oldColumn, oldY, .west⟩, true⟩
    have candidateLive : portPresent grid candidate.port = true := by
      have localLive := endpoint.2
      rw [SparseFreeLineLocalTransport.portPresent_old_block
        grid (oldColumn / 2) blockY ⟨1, sourceY, .west⟩
        (show (1 : Nat) < 2 by decide) hsourceY] at localLive
      simpa only [candidate, oldY, translatePort, oldColumnEq] using localLive
    have interior : Signals.horizontalInterior?
        (componentAt grid oldColumn oldY) (quadrantAt oldColumn oldY) ≠ none :=
      horizontalInterior_of_live_endpoint (Or.inl candidateLive)
    have backed : candidate.BackedBy (grid := grid) (west := west) (east := east)
        (south := south) (north := north) :=
      backedBy_column column oldSouth oldNorth interior (Or.inl rfl) candidateLive
    refine ⟨candidate, rfl, backed, ?_⟩
    rw [endpoint.1]
    simp only [candidate, oldY, sparsePort, translatePort, sparseOldColumn]
    rw [SparseFreeLineLocalTransport.sparseCoordinate_two_block
      blockY sourceY hsourceY]
    simp [sparseCoordinate, macroOrigin, localCoordinate]
  · let candidate : Candidate := ⟨⟨oldColumn, oldY, .east⟩, true⟩
    have candidateLive : portPresent grid candidate.port = true := by
      have localLive := endpoint.2
      rw [SparseFreeLineLocalTransport.portPresent_old_block
        grid (oldColumn / 2) blockY ⟨1, sourceY, .east⟩
        (show (1 : Nat) < 2 by decide) hsourceY] at localLive
      simpa only [candidate, oldY, translatePort, oldColumnEq] using localLive
    have interior : Signals.horizontalInterior?
        (componentAt grid oldColumn oldY) (quadrantAt oldColumn oldY) ≠ none :=
      horizontalInterior_of_live_endpoint (Or.inr candidateLive)
    have backed : candidate.BackedBy (grid := grid) (west := west) (east := east)
        (south := south) (north := north) :=
      backedBy_column column oldSouth oldNorth interior (Or.inr rfl) candidateLive
    refine ⟨candidate, rfl, backed, ?_⟩
    rw [endpoint.1]
    simp only [candidate, oldY, sparsePort, translatePort, sparseOldColumn]
    rw [SparseFreeLineLocalTransport.sparseCoordinate_two_block
      blockY sourceY hsourceY]
    simp [sparseCoordinate, macroOrigin, localCoordinate]

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

/-- A bounded route from any backed local candidate yields a global projection. -/
theorem projectsTo_of_boundedLocalRoute
    {grid : Nat → Nat → Index} {west east south north : Nat}
    (blockX blockY : Nat) {candidate : Candidate} {start : WeightedStart}
    {target : Port}
    (backed : candidate.BackedBy (grid := grid) (west := west) (east := east)
      (south := south) (north := north))
    (startCoordinate : translatePort start.port (8 * blockX) (8 * blockY) =
      sparsePort candidate.port)
    (startParity : start.parity = candidate.parity)
    (path : BoundedPath (fineGrid (grid blockX blockY)) 8 8
      start.port target (Bool.xor start.parity true))
    (htargetX : target.x < 8) (htargetY : target.y < 8)
    (targetLive : portPresent (fineGrid (grid blockX blockY)) target = true) :
    Nonempty (ProjectsTo (grid := grid) (west := west) (east := east)
      (south := south) (north := north)
      (translatePort target (8 * blockX) (8 * blockY))) := by
  have translated := SparseFreeLineLocalTransport.boundedPath_two_block
    grid blockX blockY path
  have tail : Path (iterateRefine 2 grid) (sparsePort candidate.port)
      (translatePort target (8 * blockX) (8 * blockY))
      (Bool.xor candidate.parity true) := by
    rw [← startCoordinate]
    simpa only [startParity] using translated
  have globalLive : portPresent (iterateRefine 2 grid)
      (translatePort target (8 * blockX) (8 * blockY)) = true := by
    rw [SparseFreeLineLocalTransport.portPresent_two_block
      grid blockX blockY target htargetX htargetY] at targetLive
    exact targetLive
  rcases backed with ⟨source, sourceParity, head⟩
  refine ⟨{
    source := source
    path := ?_
    targetLive := globalLive
  }⟩
  simpa only [sourceParity, Bool.false_xor] using Path.trans head tail

/-- Local starts embed in a global source family after macrocell translation. -/
def StartsEmbed
    {grid : Nat → Nat → Index} {west east south north : Nat}
    (family : Family grid west east south north)
    (blockX blockY : Nat) (starts : List WeightedStart) : Prop :=
  ∀ start ∈ starts, ∃ candidate ∈ family.candidates,
    translatePort start.port (8 * blockX) (8 * blockY) =
      sparsePort candidate.port ∧
    start.parity = candidate.parity

def localStart (candidate : Candidate)
    (offsetX offsetY : Nat) : WeightedStart where
  port := ⟨sparseCoordinate candidate.port.x - offsetX,
    sparseCoordinate candidate.port.y - offsetY, candidate.port.side⟩
  parity := candidate.parity

/-- Backed candidates whose sparse copies lie inside one bounded window. -/
def localizedStarts (candidates : List Candidate)
    (offsetX offsetY width height : Nat) : List WeightedStart :=
  (candidates.filter fun candidate => decide
    (offsetX ≤ sparseCoordinate candidate.port.x ∧
      sparseCoordinate candidate.port.x < offsetX + width ∧
      offsetY ≤ sparseCoordinate candidate.port.y ∧
      sparseCoordinate candidate.port.y < offsetY + height)).map
        fun candidate => localStart candidate offsetX offsetY

theorem mem_localizedStarts
    {candidates : List Candidate} {offsetX offsetY width height : Nat}
    {start : WeightedStart} (hstart : start ∈
      localizedStarts candidates offsetX offsetY width height) :
    ∃ candidate ∈ candidates,
      offsetX ≤ sparseCoordinate candidate.port.x ∧
      sparseCoordinate candidate.port.x < offsetX + width ∧
      offsetY ≤ sparseCoordinate candidate.port.y ∧
      sparseCoordinate candidate.port.y < offsetY + height ∧
      start = localStart candidate offsetX offsetY := by
  rw [localizedStarts, List.mem_map] at hstart
  rcases hstart with ⟨candidate, hcandidate, rfl⟩
  simp only [List.mem_filter, decide_eq_true_eq] at hcandidate
  exact ⟨candidate, hcandidate.1, hcandidate.2.1, hcandidate.2.2.1,
    hcandidate.2.2.2.1, hcandidate.2.2.2.2, rfl⟩

theorem localizedStarts_inBounds
    (candidates : List Candidate) (offsetX offsetY width height : Nat) :
    ∀ start ∈ localizedStarts candidates offsetX offsetY width height,
      PortInBounds start.port width height := by
  intro start hstart
  rcases mem_localizedStarts hstart with
    ⟨candidate, _hcandidate, hxLower, hxUpper, hyLower, hyUpper, rfl⟩
  rcases candidate with ⟨⟨x, y, side⟩, parity⟩
  change offsetX ≤ sparseCoordinate x at hxLower
  change sparseCoordinate x < offsetX + width at hxUpper
  change offsetY ≤ sparseCoordinate y at hyLower
  change sparseCoordinate y < offsetY + height at hyUpper
  have hxEq : offsetX + (sparseCoordinate x - offsetX) =
      sparseCoordinate x := Nat.add_sub_of_le hxLower
  have hyEq : offsetY + (sparseCoordinate y - offsetY) =
      sparseCoordinate y := Nat.add_sub_of_le hyLower
  simp only [localStart, PortInBounds]
  constructor <;> omega

theorem localizedStarts_embed
    {grid : Nat → Nat → Index} {west east south north : Nat}
    (family : Family grid west east south north)
    (blockX blockY width height : Nat) :
    StartsEmbed family blockX blockY
      (localizedStarts family.candidates
        (8 * blockX) (8 * blockY) width height) := by
  intro start hstart
  rcases mem_localizedStarts hstart with
    ⟨candidate, hcandidate, hxLower, _hxUpper, hyLower, _hyUpper, rfl⟩
  refine ⟨candidate, hcandidate, ?_, rfl⟩
  rcases candidate with ⟨⟨x, y, side⟩, parity⟩
  change 8 * blockX ≤ sparseCoordinate x at hxLower
  change 8 * blockY ≤ sparseCoordinate y at hyLower
  simp only [localStart, translatePort, sparsePort]
  rw [Nat.add_sub_of_le hxLower, Nat.add_sub_of_le hyLower]

/-- A checked local route projects whenever all of its starts embed globally. -/
theorem projectsTo_of_boundedLocalRoute_of_family
    {grid : Nat → Nat → Index} {west east south north : Nat}
    (family : Family grid west east south north)
    (blockX blockY : Nat) {starts : List WeightedStart} {target : Port}
    (embed : StartsEmbed family blockX blockY starts)
    (route : BoundedLocalRoute (grid blockX blockY) starts target)
    (htargetX : target.x < 8) (htargetY : target.y < 8) :
    Nonempty (ProjectsTo (grid := grid) (west := west) (east := east)
      (south := south) (north := north)
      (translatePort target (8 * blockX) (8 * blockY))) := by
  rcases route with ⟨start, hstart, path, targetLive⟩
  rcases embed start hstart with
    ⟨candidate, hcandidate, startCoordinate, startParity⟩
  exact projectsTo_of_boundedLocalRoute blockX blockY
    (family.backed candidate hcandidate) startCoordinate startParity
    path htargetX htargetY targetLive

/-- A bounded route searched directly in a shifted multi-macrocell neighborhood. -/
def ShiftedBoundedRoute
    (grid : Nat → Nat → Index) (blockX blockY width height : Nat)
    (starts : List WeightedStart) (target : Port) : Prop :=
  BoundedRouteIn (iterateRefine 2 (shiftGrid grid blockX blockY))
    width height starts target

/-- A multi-macrocell route projects once its local starts embed in the family. -/
theorem projectsTo_of_shiftedBoundedRoute_of_family
    {grid : Nat → Nat → Index} {west east south north : Nat}
    (family : Family grid west east south north)
    (blockX blockY width height : Nat)
    {starts : List WeightedStart} {target : Port}
    (embed : StartsEmbed family blockX blockY starts)
    (route : ShiftedBoundedRoute grid blockX blockY width height starts target) :
    Nonempty (ProjectsTo (grid := grid) (west := west) (east := east)
      (south := south) (north := north)
      (translatePort target (8 * blockX) (8 * blockY))) := by
  rcases route with ⟨start, hstart, path, targetLive⟩
  rcases embed start hstart with
    ⟨candidate, hcandidate, startCoordinate, startParity⟩
  have translated := SparseFreeLineLocalTransport.boundedPath_shift
    grid blockX blockY path
  have tail : Path (iterateRefine 2 grid) (sparsePort candidate.port)
      (translatePort target (8 * blockX) (8 * blockY))
      (Bool.xor candidate.parity true) := by
    rw [← startCoordinate]
    simpa only [startParity] using translated
  have globalLive : portPresent (iterateRefine 2 grid)
      (translatePort target (8 * blockX) (8 * blockY)) = true := by
    rw [SparseFreeLineLocalTransport.portPresent_shift] at targetLive
    exact targetLive
  rcases family.backed candidate hcandidate with
    ⟨source, sourceParity, head⟩
  refine ⟨{
    source := source
    path := ?_
    targetLive := globalLive
  }⟩
  simpa only [sourceParity, Bool.false_xor] using Path.trans head tail

/-- Aligned bounded row routes project an odd retained row to a local target row. -/
theorem verticalProjectionAt_of_alignedChecks
    {grid : Nat → Nat → Index} {west east south north oldRow targetY : Nat}
    (row : LiveRowCertificate grid west east south north oldRow)
    (hodd : oldRow % 2 = 1) (htargetY : targetY < 8)
    (checks : ∀ blockX, alignedRowCheck
      (grid blockX (oldRow / 2)) 1 targetY = true) :
    VerticalProjectionAt grid west east south north
      (8 * (oldRow / 2) + targetY) := by
  intro x hwest heast interior
  let blockX := x / 8
  let localX := x % 8
  have hlocalX : localX < 8 := Nat.mod_lt _ (by decide)
  have hx : 8 * blockX + localX = x := by
    have hdecompose := Nat.mod_add_div x 8
    dsimp [blockX, localX]
    omega
  have localInterior : Signals.verticalInterior?
      (componentAt (fineGrid (grid blockX (oldRow / 2))) localX targetY)
      (quadrantAt localX targetY) ≠ none := by
    have transported := interior
    rw [← hx] at transported
    rw [Signals.FreeCellEmbedding.componentAt_two_block
      grid 0 blockX (oldRow / 2) localX targetY hlocalX htargetY] at transported
    rw [Signals.FreeCellEmbedding.quadrantAt_block] at transported
    change Signals.verticalInterior?
      (componentAt (iterateRefine 2
        (fun _ _ => grid blockX (oldRow / 2))) localX targetY)
      (quadrantAt localX targetY) ≠ none
    simpa [iterateRefine] using transported
  have hwestLocal : quarterWest (4 * west) < 8 * blockX + localX := by
    simpa only [hx] using hwest
  have heastLocal : 8 * blockX + localX < quarterEast (4 * east) := by
    simpa only [hx] using heast
  have covered := alignedRowCheck_bounded_sound (checks blockX)
    localX hlocalX localInterior
  rcases covered with route | route
  · left
    rcases route with ⟨start, hstart, path, targetLive⟩
    rcases alignedRowStart_backed row hodd blockX localX
        hwestLocal heastLocal hstart with
      ⟨candidate, candidateOdd, backed, startCoordinate⟩
    have startOdd : start.parity = true := by
      rcases mem_alignedRowStarts hstart with ⟨_, _, _, odd, _⟩
      exact odd
    have translated := SparseFreeLineLocalTransport.boundedPath_two_block
      grid blockX (oldRow / 2) path
    have targetCoordinate : translatePort ⟨localX, targetY, .south⟩
        (8 * blockX) (8 * (oldRow / 2)) =
        ⟨x, 8 * (oldRow / 2) + targetY, .south⟩ := by
      simp only [translatePort]
      rw [hx]
    have tail : Path (iterateRefine 2 grid) (sparsePort candidate.port)
        ⟨x, 8 * (oldRow / 2) + targetY, .south⟩ false := by
      rw [← startCoordinate, ← targetCoordinate]
      simpa only [startOdd, Bool.true_xor, Bool.not_true] using translated
    have globalLive : portPresent (iterateRefine 2 grid)
        ⟨x, 8 * (oldRow / 2) + targetY, .south⟩ = true := by
      rw [SparseFreeLineLocalTransport.portPresent_two_block
        grid blockX (oldRow / 2) ⟨localX, targetY, .south⟩
        hlocalX htargetY] at targetLive
      rw [targetCoordinate] at targetLive
      exact targetLive
    exact projectsTo_of_backedCandidate backed candidateOdd tail globalLive
  · right
    rcases route with ⟨start, hstart, path, targetLive⟩
    rcases alignedRowStart_backed row hodd blockX localX
        hwestLocal heastLocal hstart with
      ⟨candidate, candidateOdd, backed, startCoordinate⟩
    have startOdd : start.parity = true := by
      rcases mem_alignedRowStarts hstart with ⟨_, _, _, odd, _⟩
      exact odd
    have translated := SparseFreeLineLocalTransport.boundedPath_two_block
      grid blockX (oldRow / 2) path
    have targetCoordinate : translatePort ⟨localX, targetY, .north⟩
        (8 * blockX) (8 * (oldRow / 2)) =
        ⟨x, 8 * (oldRow / 2) + targetY, .north⟩ := by
      simp only [translatePort]
      rw [hx]
    have tail : Path (iterateRefine 2 grid) (sparsePort candidate.port)
        ⟨x, 8 * (oldRow / 2) + targetY, .north⟩ false := by
      rw [← startCoordinate, ← targetCoordinate]
      simpa only [startOdd, Bool.true_xor, Bool.not_true] using translated
    have globalLive : portPresent (iterateRefine 2 grid)
        ⟨x, 8 * (oldRow / 2) + targetY, .north⟩ = true := by
      rw [SparseFreeLineLocalTransport.portPresent_two_block
        grid blockX (oldRow / 2) ⟨localX, targetY, .north⟩
        hlocalX htargetY] at targetLive
      rw [targetCoordinate] at targetLive
      exact targetLive
    exact projectsTo_of_backedCandidate backed candidateOdd tail globalLive

/-- Aligned bounded column routes project an odd retained column locally. -/
theorem horizontalProjectionAt_of_alignedChecks
    {grid : Nat → Nat → Index} {west east south north oldColumn targetX : Nat}
    (column : LiveColumnCertificate grid west east south north oldColumn)
    (hodd : oldColumn % 2 = 1) (htargetX : targetX < 8)
    (checks : ∀ blockY, alignedColumnCheck
      (grid (oldColumn / 2) blockY) 1 targetX = true) :
    HorizontalProjectionAt grid west east south north
      (8 * (oldColumn / 2) + targetX) := by
  intro y hsouth hnorth interior
  let blockY := y / 8
  let localY := y % 8
  have hlocalY : localY < 8 := Nat.mod_lt _ (by decide)
  have hy : 8 * blockY + localY = y := by
    have hdecompose := Nat.mod_add_div y 8
    dsimp [blockY, localY]
    omega
  have localInterior : Signals.horizontalInterior?
      (componentAt (fineGrid (grid (oldColumn / 2) blockY)) targetX localY)
      (quadrantAt targetX localY) ≠ none := by
    have transported := interior
    rw [← hy] at transported
    rw [Signals.FreeCellEmbedding.componentAt_two_block
      grid 0 (oldColumn / 2) blockY targetX localY htargetX hlocalY] at transported
    rw [Signals.FreeCellEmbedding.quadrantAt_block] at transported
    change Signals.horizontalInterior?
      (componentAt (iterateRefine 2
        (fun _ _ => grid (oldColumn / 2) blockY)) targetX localY)
      (quadrantAt targetX localY) ≠ none
    simpa [iterateRefine] using transported
  have hsouthLocal : quarterSouth (4 * south) < 8 * blockY + localY := by
    simpa only [hy] using hsouth
  have hnorthLocal : 8 * blockY + localY < quarterNorth (4 * north) := by
    simpa only [hy] using hnorth
  have covered := alignedColumnCheck_bounded_sound (checks blockY)
    localY hlocalY localInterior
  rcases covered with route | route
  · left
    rcases route with ⟨start, hstart, path, targetLive⟩
    rcases alignedColumnStart_backed column hodd blockY localY
        hsouthLocal hnorthLocal hstart with
      ⟨candidate, candidateOdd, backed, startCoordinate⟩
    have startOdd : start.parity = true := by
      rcases mem_alignedColumnStarts hstart with ⟨_, _, _, odd, _⟩
      exact odd
    have translated := SparseFreeLineLocalTransport.boundedPath_two_block
      grid (oldColumn / 2) blockY path
    have targetCoordinate : translatePort ⟨targetX, localY, .west⟩
        (8 * (oldColumn / 2)) (8 * blockY) =
        ⟨8 * (oldColumn / 2) + targetX, y, .west⟩ := by
      simp only [translatePort]
      rw [hy]
    have tail : Path (iterateRefine 2 grid) (sparsePort candidate.port)
        ⟨8 * (oldColumn / 2) + targetX, y, .west⟩ false := by
      rw [← startCoordinate, ← targetCoordinate]
      simpa only [startOdd, Bool.true_xor, Bool.not_true] using translated
    have globalLive : portPresent (iterateRefine 2 grid)
        ⟨8 * (oldColumn / 2) + targetX, y, .west⟩ = true := by
      rw [SparseFreeLineLocalTransport.portPresent_two_block
        grid (oldColumn / 2) blockY ⟨targetX, localY, .west⟩
        htargetX hlocalY] at targetLive
      rw [targetCoordinate] at targetLive
      exact targetLive
    exact projectsTo_of_backedCandidate backed candidateOdd tail globalLive
  · right
    rcases route with ⟨start, hstart, path, targetLive⟩
    rcases alignedColumnStart_backed column hodd blockY localY
        hsouthLocal hnorthLocal hstart with
      ⟨candidate, candidateOdd, backed, startCoordinate⟩
    have startOdd : start.parity = true := by
      rcases mem_alignedColumnStarts hstart with ⟨_, _, _, odd, _⟩
      exact odd
    have translated := SparseFreeLineLocalTransport.boundedPath_two_block
      grid (oldColumn / 2) blockY path
    have targetCoordinate : translatePort ⟨targetX, localY, .east⟩
        (8 * (oldColumn / 2)) (8 * blockY) =
        ⟨8 * (oldColumn / 2) + targetX, y, .east⟩ := by
      simp only [translatePort]
      rw [hy]
    have tail : Path (iterateRefine 2 grid) (sparsePort candidate.port)
        ⟨8 * (oldColumn / 2) + targetX, y, .east⟩ false := by
      rw [← startCoordinate, ← targetCoordinate]
      simpa only [startOdd, Bool.true_xor, Bool.not_true] using translated
    have globalLive : portPresent (iterateRefine 2 grid)
        ⟨8 * (oldColumn / 2) + targetX, y, .east⟩ = true := by
      rw [SparseFreeLineLocalTransport.portPresent_two_block
        grid (oldColumn / 2) blockY ⟨targetX, localY, .east⟩
        htargetX hlocalY] at targetLive
      rw [targetCoordinate] at targetLive
      exact targetLive
    exact projectsTo_of_backedCandidate backed candidateOdd tail globalLive

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

/-- Every segment on a vertical exit copy comes from a live old north endpoint. -/
def VerticalExitAncestors (grid : Nat → Nat → Index)
    (oldRow fineRow : Nat) : Prop :=
  ∀ x, Signals.verticalInterior?
      (componentAt (iterateRefine 2 grid) x fineRow)
      (quadrantAt x fineRow) ≠ none →
    ∃ oldX, sparseCoordinate oldX = x ∧
      Signals.verticalInterior?
        (componentAt grid oldX oldRow) (quadrantAt oldX oldRow) ≠ none ∧
      portPresent grid ⟨oldX, oldRow, .north⟩ = true ∧
      portPresent (iterateRefine 2 grid) ⟨x, fineRow, .north⟩ = true

/-- Every segment on a horizontal exit copy comes from a live old east endpoint. -/
def HorizontalExitAncestors (grid : Nat → Nat → Index)
    (oldColumn fineColumn : Nat) : Prop :=
  ∀ y, Signals.horizontalInterior?
      (componentAt (iterateRefine 2 grid) fineColumn y)
      (quadrantAt fineColumn y) ≠ none →
    ∃ oldY, sparseCoordinate oldY = y ∧
      Signals.horizontalInterior?
        (componentAt grid oldColumn oldY) (quadrantAt oldColumn oldY) ≠ none ∧
      portPresent grid ⟨oldColumn, oldY, .east⟩ = true ∧
      portPresent (iterateRefine 2 grid) ⟨fineColumn, y, .east⟩ = true

/-- The exact sparse part of a vertical projection repeats at the next scale. -/
theorem verticalProjectionAt_refineSparse
    {grid : Nat → Nat → Index} {west east south north oldRow fineRow : Nat}
    (previous : VerticalProjectionAt grid west east south north oldRow)
    (coordinate : fineRow = sparseCoordinate oldRow)
    (ancestors : VerticalSparseAncestors
      (iterateRefine 2 grid) oldRow fineRow) :
    VerticalProjectionAt (iterateRefine 2 grid)
      (4 * west) (4 * east) (4 * south) (4 * north) fineRow := by
  intro x hwest heast interior
  rcases ancestors x interior with ⟨oldX, oldCoordinate, oldInterior⟩
  have oldWest : quarterWest (4 * west) < oldX := by
    rw [← sparseCoordinate_lt_iff]
    simpa [oldCoordinate] using hwest
  have oldEast : oldX < quarterEast (4 * east) := by
    rw [← sparseCoordinate_lt_iff]
    simpa [oldCoordinate] using heast
  rcases previous oldX oldWest oldEast oldInterior with projected | projected
  · left
    rcases projected with ⟨projection⟩
    refine ⟨?_⟩
    simpa [sparsePort, oldCoordinate, coordinate] using projection.refineSparse
  · right
    rcases projected with ⟨projection⟩
    refine ⟨?_⟩
    simpa [sparsePort, oldCoordinate, coordinate] using projection.refineSparse

/-- The exact sparse part of a horizontal projection repeats at the next scale. -/
theorem horizontalProjectionAt_refineSparse
    {grid : Nat → Nat → Index} {west east south north oldColumn fineColumn : Nat}
    (previous : HorizontalProjectionAt grid west east south north oldColumn)
    (coordinate : fineColumn = sparseCoordinate oldColumn)
    (ancestors : HorizontalSparseAncestors
      (iterateRefine 2 grid) oldColumn fineColumn) :
    HorizontalProjectionAt (iterateRefine 2 grid)
      (4 * west) (4 * east) (4 * south) (4 * north) fineColumn := by
  intro y hsouth hnorth interior
  rcases ancestors y interior with ⟨oldY, oldCoordinate, oldInterior⟩
  have oldSouth : quarterSouth (4 * south) < oldY := by
    rw [← sparseCoordinate_lt_iff]
    simpa [oldCoordinate] using hsouth
  have oldNorth : oldY < quarterNorth (4 * north) := by
    rw [← sparseCoordinate_lt_iff]
    simpa [oldCoordinate] using hnorth
  rcases previous oldY oldSouth oldNorth oldInterior with projected | projected
  · left
    rcases projected with ⟨projection⟩
    refine ⟨?_⟩
    simpa [sparsePort, oldCoordinate, coordinate] using projection.refineSparse
  · right
    rcases projected with ⟨projection⟩
    refine ⟨?_⟩
    simpa [sparsePort, oldCoordinate, coordinate] using projection.refineSparse

/-- The north-going exit copy of a projected vertical line repeats at the next scale. -/
theorem verticalProjectionAt_refineExit
    {grid : Nat → Nat → Index} {west east south north oldRow fineRow : Nat}
    (previous : VerticalProjectionAt grid west east south north oldRow)
    (coordinate : fineRow = exitCoordinate oldRow)
    (ancestors : VerticalExitAncestors
      (iterateRefine 2 grid) oldRow fineRow) :
    VerticalProjectionAt (iterateRefine 2 grid)
      (4 * west) (4 * east) (4 * south) (4 * north) fineRow := by
  intro x hwest heast interior
  rcases ancestors x interior with
    ⟨oldX, oldCoordinate, oldInterior, oldNorthLive, refinedNorthLive⟩
  have oldWest : quarterWest (4 * west) < oldX := by
    rw [← sparseCoordinate_lt_iff]
    simpa [oldCoordinate] using hwest
  have oldEast : oldX < quarterEast (4 * east) := by
    rw [← sparseCoordinate_lt_iff]
    simpa [oldCoordinate] using heast
  have targetCoordinate :
      refinedPort ⟨oldX, oldRow, .north⟩ = ⟨x, fineRow, .north⟩ := by
    simp only [refinedPort]
    rw [oldCoordinate, ← coordinate]
  right
  rw [← targetCoordinate]
  exact projectsTo_refineNorth previous oldWest oldEast oldInterior
    oldNorthLive (by rw [targetCoordinate]; exact refinedNorthLive)

/-- The east-going exit copy of a projected horizontal line repeats at the next scale. -/
theorem horizontalProjectionAt_refineExit
    {grid : Nat → Nat → Index}
    {west east south north oldColumn fineColumn : Nat}
    (previous : HorizontalProjectionAt grid west east south north oldColumn)
    (coordinate : fineColumn = exitCoordinate oldColumn)
    (ancestors : HorizontalExitAncestors
      (iterateRefine 2 grid) oldColumn fineColumn) :
    HorizontalProjectionAt (iterateRefine 2 grid)
      (4 * west) (4 * east) (4 * south) (4 * north) fineColumn := by
  intro y hsouth hnorth interior
  rcases ancestors y interior with
    ⟨oldY, oldCoordinate, oldInterior, oldEastLive, refinedEastLive⟩
  have oldSouth : quarterSouth (4 * south) < oldY := by
    rw [← sparseCoordinate_lt_iff]
    simpa [oldCoordinate] using hsouth
  have oldNorth : oldY < quarterNorth (4 * north) := by
    rw [← sparseCoordinate_lt_iff]
    simpa [oldCoordinate] using hnorth
  have targetCoordinate :
      refinedPort ⟨oldColumn, oldY, .east⟩ = ⟨fineColumn, y, .east⟩ := by
    simp only [refinedPort]
    rw [oldCoordinate, ← coordinate]
  right
  rw [← targetCoordinate]
  exact projectsTo_refineEast previous oldSouth oldNorth oldInterior
    oldEastLive (by rw [targetCoordinate]; exact refinedEastLive)

/-- Per-macrocell endpoint checks give exact ancestors on a north exit row. -/
theorem verticalExitAncestors_of_checks
    {grid : Nat → Nat → Index} {oldRow : Nat}
    (hodd : oldRow % 2 = 1)
    (checks : ∀ blockX,
      verticalNorthCheck 1 7 (grid blockX (oldRow / 2)) = true) :
    VerticalExitAncestors grid oldRow (exitCoordinate oldRow) := by
  intro x interior
  let blockX := x / 8
  let localX := x % 8
  let blockY := oldRow / 2
  have hlocalX : localX < 8 := Nat.mod_lt _ (by decide)
  have hx : 8 * blockX + localX = x := by
    have := Nat.mod_add_div x 8
    dsimp [blockX, localX]
    omega
  have holdRow : 2 * blockY + 1 = oldRow := by
    have := Nat.mod_add_div oldRow 2
    dsimp [blockY]
    omega
  have hfineRow : 8 * blockY + 7 = exitCoordinate oldRow := by
    simp [exitCoordinate, macroOrigin, localCoordinate, blockY, hodd]
  have localInterior : Signals.verticalInterior?
      (componentAt (iterateRefine 2 grid)
        (8 * blockX + localX) (8 * blockY + 7))
      (quadrantAt (8 * blockX + localX) (8 * blockY + 7)) ≠ none := by
    simpa [hx, hfineRow] using interior
  rcases SparseFreeLineLocalTransport.verticalNorthAncestor_two_block
      grid blockX blockY 1 7 localX (by decide) (by decide) hlocalX
      (checks blockX) localInterior with
    ⟨sourceX, hsourceX, sourceCoordinate, sourceInterior,
      oldLive, targetLive⟩
  refine ⟨2 * blockX + sourceX, ?_, ?_, ?_, ?_⟩
  · simpa [hx] using sourceCoordinate
  · simpa [holdRow] using sourceInterior
  · simpa [holdRow] using oldLive
  · simpa [hx, hfineRow] using targetLive

/-- Per-macrocell endpoint checks give exact ancestors on an east exit column. -/
theorem horizontalExitAncestors_of_checks
    {grid : Nat → Nat → Index} {oldColumn : Nat}
    (hodd : oldColumn % 2 = 1)
    (checks : ∀ blockY,
      horizontalEastCheck 1 7 (grid (oldColumn / 2) blockY) = true) :
    HorizontalExitAncestors grid oldColumn (exitCoordinate oldColumn) := by
  intro y interior
  let blockX := oldColumn / 2
  let blockY := y / 8
  let localY := y % 8
  have hlocalY : localY < 8 := Nat.mod_lt _ (by decide)
  have hy : 8 * blockY + localY = y := by
    have := Nat.mod_add_div y 8
    dsimp [blockY, localY]
    omega
  have holdColumn : 2 * blockX + 1 = oldColumn := by
    have := Nat.mod_add_div oldColumn 2
    dsimp [blockX]
    omega
  have hfineColumn : 8 * blockX + 7 = exitCoordinate oldColumn := by
    simp [exitCoordinate, macroOrigin, localCoordinate, blockX, hodd]
  have localInterior : Signals.horizontalInterior?
      (componentAt (iterateRefine 2 grid)
        (8 * blockX + 7) (8 * blockY + localY))
      (quadrantAt (8 * blockX + 7) (8 * blockY + localY)) ≠ none := by
    simpa [hy, hfineColumn] using interior
  rcases SparseFreeLineLocalTransport.horizontalEastAncestor_two_block
      grid blockX blockY 1 7 localY (by decide) (by decide) hlocalY
      (checks blockY) localInterior with
    ⟨sourceY, hsourceY, sourceCoordinate, sourceInterior,
      oldLive, targetLive⟩
  refine ⟨2 * blockY + sourceY, ?_, ?_, ?_, ?_⟩
  · simpa [hy] using sourceCoordinate
  · simpa [holdColumn] using sourceInterior
  · simpa [holdColumn] using oldLive
  · simpa [hy, hfineColumn] using targetLive

/-- Checked upper-row exits instantiate the recursive vertical projection. -/
theorem verticalProjectionAt_refineExit_of_checks
    {grid : Nat → Nat → Index} {west east south north oldRow : Nat}
    (previous : VerticalProjectionAt grid west east south north oldRow)
    (hodd : oldRow % 2 = 1)
    (checks : ∀ blockX,
      verticalNorthCheck 1 7
        (iterateRefine 2 grid blockX (oldRow / 2)) = true) :
    VerticalProjectionAt (iterateRefine 2 grid)
      (4 * west) (4 * east) (4 * south) (4 * north)
      (exitCoordinate oldRow) :=
  verticalProjectionAt_refineExit previous rfl
    (verticalExitAncestors_of_checks hodd checks)

/-- Checked right-column exits instantiate the recursive horizontal projection. -/
theorem horizontalProjectionAt_refineExit_of_checks
    {grid : Nat → Nat → Index} {west east south north oldColumn : Nat}
    (previous : HorizontalProjectionAt grid west east south north oldColumn)
    (hodd : oldColumn % 2 = 1)
    (checks : ∀ blockY,
      horizontalEastCheck 1 7
        (iterateRefine 2 grid (oldColumn / 2) blockY) = true) :
    HorizontalProjectionAt (iterateRefine 2 grid)
      (4 * west) (4 * east) (4 * south) (4 * north)
      (exitCoordinate oldColumn) :=
  horizontalProjectionAt_refineExit previous rfl
    (horizontalExitAncestors_of_checks hodd checks)

/-- Per-macrocell vertical checks give exact ancestors on a sparse row. -/
theorem verticalSparseAncestors_of_checks
    {grid : Nat → Nat → Index} {oldRow : Nat}
    (checks : ∀ blockX,
      verticalCheck (oldRow % 2) (oldRow % 2)
        (grid blockX (oldRow / 2)) = true) :
    VerticalSparseAncestors grid oldRow (sparseCoordinate oldRow) := by
  intro x interior
  let blockX := x / 8
  let localX := x % 8
  let blockY := oldRow / 2
  let localY := oldRow % 2
  have hlocalX : localX < 8 := Nat.mod_lt _ (by decide)
  have hlocalY : localY < 2 := Nat.mod_lt _ (by decide)
  have hx : 8 * blockX + localX = x := by
    have := Nat.mod_add_div x 8
    dsimp [blockX, localX]
    omega
  have holdRow : 2 * blockY + localY = oldRow := by
    have := Nat.mod_add_div oldRow 2
    dsimp [blockY, localY]
    omega
  have hfineRow : 8 * blockY + localY = sparseCoordinate oldRow := by
    simp [sparseCoordinate, macroOrigin, localCoordinate, blockY, localY]
  have checked : verticalCheck localY localY
      (iterateRefine 0 grid blockX blockY) = true := by
    change verticalCheck localY localY (grid blockX blockY) = true
    simpa [blockX, blockY, localY] using checks blockX
  have localInterior : Signals.verticalInterior?
      (componentAt (iterateRefine (0 + 2) grid)
        (8 * blockX + localX) (8 * blockY + localY))
      (quadrantAt (8 * blockX + localX) (8 * blockY + localY)) ≠ none := by
    simpa [hx, hfineRow] using interior
  rcases SparseFreeLineLocalTransport.verticalAncestor_two_block
      grid 0 blockX blockY localY localY localX
      hlocalY (by omega) hlocalX checked localInterior with
    ⟨sourceX, hsourceX, sourceCoordinate, sourceInterior⟩
  refine ⟨2 * blockX + sourceX, ?_, ?_⟩
  · simpa [hx] using sourceCoordinate
  · change Signals.verticalInterior?
        (componentAt grid (2 * blockX + sourceX) (2 * blockY + localY))
        (quadrantAt (2 * blockX + sourceX) (2 * blockY + localY)) ≠ none
      at sourceInterior
    simpa [holdRow] using sourceInterior

/-- Per-macrocell horizontal checks give exact ancestors on a sparse column. -/
theorem horizontalSparseAncestors_of_checks
    {grid : Nat → Nat → Index} {oldColumn : Nat}
    (checks : ∀ blockY,
      horizontalCheck (oldColumn % 2) (oldColumn % 2)
        (grid (oldColumn / 2) blockY) = true) :
    HorizontalSparseAncestors grid oldColumn (sparseCoordinate oldColumn) := by
  intro y interior
  let blockX := oldColumn / 2
  let localX := oldColumn % 2
  let blockY := y / 8
  let localY := y % 8
  have hlocalX : localX < 2 := Nat.mod_lt _ (by decide)
  have hlocalY : localY < 8 := Nat.mod_lt _ (by decide)
  have hy : 8 * blockY + localY = y := by
    have := Nat.mod_add_div y 8
    dsimp [blockY, localY]
    omega
  have holdColumn : 2 * blockX + localX = oldColumn := by
    have := Nat.mod_add_div oldColumn 2
    dsimp [blockX, localX]
    omega
  have hfineColumn : 8 * blockX + localX = sparseCoordinate oldColumn := by
    simp [sparseCoordinate, macroOrigin, localCoordinate, blockX, localX]
  have checked : horizontalCheck localX localX
      (iterateRefine 0 grid blockX blockY) = true := by
    change horizontalCheck localX localX (grid blockX blockY) = true
    simpa [blockX, blockY, localX] using checks blockY
  have localInterior : Signals.horizontalInterior?
      (componentAt (iterateRefine (0 + 2) grid)
        (8 * blockX + localX) (8 * blockY + localY))
      (quadrantAt (8 * blockX + localX) (8 * blockY + localY)) ≠ none := by
    simpa [hy, hfineColumn] using interior
  rcases SparseFreeLineLocalTransport.horizontalAncestor_two_block
      grid 0 blockX blockY localX localX localY
      hlocalX (by omega) hlocalY checked localInterior with
    ⟨sourceY, hsourceY, sourceCoordinate, sourceInterior⟩
  refine ⟨2 * blockY + sourceY, ?_, ?_⟩
  · simpa [hy] using sourceCoordinate
  · change Signals.horizontalInterior?
        (componentAt grid (2 * blockX + localX) (2 * blockY + sourceY))
        (quadrantAt (2 * blockX + localX) (2 * blockY + sourceY)) ≠ none
      at sourceInterior
    simpa [holdColumn] using sourceInterior

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

/-- Local sparse row checks and an old live certificate give the fine projection. -/
theorem verticalProjectionAt_of_checks
    {grid : Nat → Nat → Index} {west east south north oldRow : Nat}
    (row : LiveRowCertificate grid west east south north oldRow)
    (checks : ∀ blockX,
      verticalCheck (oldRow % 2) (oldRow % 2)
        (grid blockX (oldRow / 2)) = true) :
    VerticalProjectionAt grid west east south north (sparseCoordinate oldRow) :=
  verticalProjectionAt_of_sparseAncestors row rfl
    (verticalSparseAncestors_of_checks checks)

/-- Local sparse column checks and an old live certificate give the fine projection. -/
theorem horizontalProjectionAt_of_checks
    {grid : Nat → Nat → Index} {west east south north oldColumn : Nat}
    (column : LiveColumnCertificate grid west east south north oldColumn)
    (checks : ∀ blockY,
      horizontalCheck (oldColumn % 2) (oldColumn % 2)
        (grid (oldColumn / 2) blockY) = true) :
    HorizontalProjectionAt grid west east south north
      (sparseCoordinate oldColumn) :=
  horizontalProjectionAt_of_sparseAncestors column rfl
    (horizontalSparseAncestors_of_checks checks)

/-- A vertical projection is exactly a refined live-row certificate. -/
theorem liveRowCertificate_of_verticalProjectionAt
    {grid : Nat → Nat → Index} {west east south north row : Nat}
    (projection : VerticalProjectionAt grid west east south north row) :
    LiveRowCertificate (iterateRefine 2 grid)
      (4 * west) (4 * east) (4 * south) (4 * north) row := by
  intro x hwest heast interior
  rcases projection x hwest heast interior with projected | projected
  · rcases projected with ⟨projected⟩
    exact ⟨projected.weightedSource, rfl, Or.inl rfl⟩
  · rcases projected with ⟨projected⟩
    exact ⟨projected.weightedSource, rfl, Or.inr rfl⟩

/-- A horizontal projection is exactly a refined live-column certificate. -/
theorem liveColumnCertificate_of_horizontalProjectionAt
    {grid : Nat → Nat → Index} {west east south north column : Nat}
    (projection : HorizontalProjectionAt grid west east south north column) :
    LiveColumnCertificate (iterateRefine 2 grid)
      (4 * west) (4 * east) (4 * south) (4 * north) column := by
  intro y hsouth hnorth interior
  rcases projection y hsouth hnorth interior with projected | projected
  · rcases projected with ⟨projected⟩
    exact ⟨projected.weightedSource, rfl, Or.inl rfl⟩
  · rcases projected with ⟨projected⟩
    exact ⟨projected.weightedSource, rfl, Or.inr rfl⟩

end SparseFreeLineLocalProjection
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
