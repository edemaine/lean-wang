/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104BorderCoverageAudit
import LeanWang.OllingerRobinson104SparseFreeLineProjectionStep

/-!
# Finite even-extra whole-pattern base check

The exceptional even-phase child is not projected by its predecessor line
alone. This audit uses the enclosing cycle and both sparse rows and columns on
the first even board. Translation to the board box gives a `65 x 65` search.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace SparseFreeLineEvenExtraBaseAudit

open RedCycles RedShadeGraph RedShadeGraphRefinement RedShadeGraphSearch
  RedShadeGraphWeightedSearch ShadedFreeLineProjectionCandidates
  ShadedFreeLineProjectionSourceLists ShadedFreeLineRecurrence
  SparseFreeLineOffsets Signals.FreeCellLocal RefinementTranslation

set_option maxRecDepth 20000

def oldGrid (parent : Index) : Nat → Nat → Index :=
  localGrid .even 1 parent

def candidates (parent : Index) : List Candidate :=
  patternCandidates (oldGrid parent) 4 12 4 12 (offsets 1)
    (lineCoordinate .even 1)

def starts (parent : Index) : List WeightedStart :=
  (candidates parent).map fun candidate =>
    let fine := sparsePort candidate.port
    ⟨⟨fine.x - 32, fine.y - 32, fine.side⟩, candidate.parity⟩

def searchGrid (parent : Index) : Nat → Nat → Index :=
  iterateRefine 2 (shiftGrid (oldGrid parent) 4 4)

def nodes (parent : Index) : List ReachNode :=
  exploreFastWeightedReach (searchGrid parent) 65 65 33801 (starts parent)

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

set_option linter.style.nativeDecide false in
/-- The complete old sparse pattern reaches the exceptional child. -/
theorem canonical_complete :
    ∀ state ∈ BorderSubstitution.states,
      check (BorderSubstitution.representative state) = true := by
  native_decide

end SparseFreeLineEvenExtraBaseAudit
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
