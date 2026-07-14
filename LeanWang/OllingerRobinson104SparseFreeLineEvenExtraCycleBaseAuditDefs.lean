/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104SparseFreeLineEvenExtraBaseAuditCheck

/-!
# Finite cycle-only even-extra base check definitions

The exceptional even-phase child does not need the old sparse rows or columns
at the first recursive depth. This audit starts only from the enclosing red
cycle and checks the complete exceptional row and column. Its canonical states
are chunked so the expensive searches compile in parallel.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace SparseFreeLineEvenExtraCycleBaseAudit

open RedShadeGraph RedShadeGraphRefinement RedShadeGraphSearch
  RedShadeGraphWeightedSearch ShadedFreeLineProjectionCandidates
  ShadedFreeLineProjectionSourceLists Signals.FreeCellLocal
  SparseFreeLineEvenExtraBaseAudit

set_option maxRecDepth 20000

def candidates : List Candidate :=
  (cyclePorts 4 12 4 12).map fun port => ⟨port, false⟩

def starts : List WeightedStart :=
  candidates.map fun candidate =>
    let fine := sparsePort candidate.port
    ⟨⟨fine.x - 32, fine.y - 32, fine.side⟩, candidate.parity⟩

def nodes (parent : Index) : List ReachNode :=
  exploreFastWeightedReach (searchGrid parent) 65 65 33801 starts

def reached (parent : Index) (found : List ReachNode) (target : Port) : Bool :=
  portPresent (searchGrid parent) target &&
    found.any fun node => node.parity && decide (node.current = target)

def verticalCheck (parent : Index) (found : List ReachNode) : Bool :=
  (List.range 62).all fun delta =>
    let x := 2 + delta
    let required := (Signals.verticalInterior?
      (componentAt (searchGrid parent) x 40) (quadrantAt x 40)).isSome
    !required || reached parent found ⟨x, 40, .south⟩ ||
      reached parent found ⟨x, 40, .north⟩

def horizontalCheck (parent : Index) (found : List ReachNode) : Bool :=
  (List.range 62).all fun delta =>
    let y := 2 + delta
    let required := (Signals.horizontalInterior?
      (componentAt (searchGrid parent) 40 y) (quadrantAt 40 y)).isSome
    !required || reached parent found ⟨40, y, .west⟩ ||
      reached parent found ⟨40, y, .east⟩

def check (parent : Index) : Bool :=
  let found := nodes parent
  verticalCheck parent found && horizontalCheck parent found

abbrev ChunkComplete (chunk : Fin 8) : Prop :=
  ∀ state ∈ SparseFreeLineEvenExtraBaseAudit.stateChunk chunk,
    check (BorderSubstitution.representative state) = true

end SparseFreeLineEvenExtraCycleBaseAudit
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
