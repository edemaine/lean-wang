/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.BorderGeometry
import LeanWang.Robinson.Closed104.SparseFreeLineSideHalfAudit

/-!
# Finite odd-extra base graph check

The recursive side-half quotient starts with the first odd extra line already
available. This module checks the exceptional depth-zero bridge from the odd
pivot to that first extra line. The full enclosing cycle, pivot row, and pivot
column are searched together in the translated `33 x 33` board box.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace SparseFreeLineOddExtraBaseAudit

open RedCycles RedShadeCycles RedShadeGraph RedShadeGraphRefinement
  RedShadeGraphSearch RedShadeGraphSearchSoundness RedShadeGraphTranslation
  RedShadeGraphWeightedSearch RefinementTranslation Signals.FreeCellLocal
  ShadedFreeLineProjectionCandidates ShadedFreeLineProjectionSourceLists
  ShadedFreeLineRecurrence SparseFreeLineOffsets BorderCoverageLocalAudit
  BorderGeometry

set_option maxRecDepth 20000

def oldGrid (parent : Index) : Nat → Nat → Index :=
  localGrid .odd 0 parent

def candidates (parent : Index) : List Candidate :=
  patternCandidates (oldGrid parent) 2 6 2 6 [pivot 0]
    (lineCoordinate .odd 0)

/-- Sparse candidates translated by the lower board-box corner. -/
def starts (parent : Index) : List WeightedStart :=
  (candidates parent).map fun candidate =>
    let fine := sparsePort candidate.port
    ⟨⟨fine.x - 16, fine.y - 16, fine.side⟩, candidate.parity⟩

def searchGrid (parent : Index) : Nat → Nat → Index :=
  iterateRefine 2 (shiftGrid (oldGrid parent) 2 2)

def nodes (parent : Index) : List Node :=
  exploreFastWeighted (searchGrid parent) 33 33 5000 (starts parent)

def reached (parent : Index) (nodes : List Node) (target : Port) : Bool :=
  portPresent (searchGrid parent) target &&
    nodes.any fun node => node.parity && decide (node.current = target)

def verticalCheck (parent : Index) (nodes : List Node) : Bool :=
  (List.range 30).all fun delta =>
    let x := 2 + delta
    let required := (Signals.verticalInterior?
      (componentAt (searchGrid parent) x 19) (quadrantAt x 19)).isSome
    !required || reached parent nodes ⟨x, 19, .south⟩ ||
      reached parent nodes ⟨x, 19, .north⟩

def horizontalCheck (parent : Index) (nodes : List Node) : Bool :=
  (List.range 30).all fun delta =>
    let y := 2 + delta
    let required := (Signals.horizontalInterior?
      (componentAt (searchGrid parent) 19 y) (quadrantAt 19 y)).isSome
    !required || reached parent nodes ⟨19, y, .west⟩ ||
      reached parent nodes ⟨19, y, .east⟩

def check (parent : Index) : Bool :=
  let found := nodes parent
  verticalCheck parent found && horizontalCheck parent found

set_option linter.style.nativeDecide false in
/-- One finite flood suffices for both orientations in every canonical state. -/
theorem canonical_complete :
    ∀ state ∈ BorderSubstitution.states,
      check (BorderSubstitution.representative state) = true := by
  native_decide

end SparseFreeLineOddExtraBaseAudit
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
