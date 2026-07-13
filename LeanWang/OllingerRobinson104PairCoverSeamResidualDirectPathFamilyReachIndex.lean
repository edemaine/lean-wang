/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathFamilySearch

/-!
# Dense lookup for finite family floods

The endpoint audits query the same family flood many times.  This module builds
a dense array from graph-state codes to positions in the retained node list.
Every lookup re-reads that list position and checks the exact endpoint, so the
array itself is only an accelerator and requires no trusted mutation invariant.
-/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamResidualDirectPathFamilyReachIndex

open RedCycles RedShadeGraph RedShadeGraphSearch RedShadeGraphRefinement
  PairCoverSeamResidualDirectPathFamilySearch

set_option maxRecDepth 20000

def insertReachIndex (width : Nat) (table : Array (Option Nat))
    (entry : ReachNode × Nat) : Array (Option Nat) :=
  if entry.1.parity then table
  else table.setIfInBounds (stateCode width entry.1.state) (some entry.2)

/-- Constant-time candidate lookup for the even part of a retained flood. -/
def reachIndex (width : Nat) (found : List ReachNode) : Array (Option Nat) :=
  found.zipIdx.foldl (insertReachIndex width)
    (Array.replicate (width * width * 8) none)

/-- Validate one index candidate against the retained flood. -/
def validatesReach (found : List ReachNode) (candidate : Option Nat)
    (target : Port) : Bool :=
  match candidate with
  | none => false
  | some index =>
      match found[index]? with
      | none => false
      | some node => !node.parity && decide (node.current = target)

/-- Indexed counterpart of `reaches`. -/
def indexedReaches (root : Nat → Nat → Index) (outerLevel width : Nat)
    (found : List ReachNode) (index : Array (Option Nat))
    (target : Port) : Bool :=
  portPresent (iterateRefine (outerLevel + 2) root) target &&
    validatesReach found
      (index[stateCode width (target, false)]?.join) target

theorem validatesReach_sound
    {found : List ReachNode} {candidate : Option Nat} {target : Port}
    (checked : validatesReach found candidate target = true) :
    ∃ node ∈ found,
      Bool.not node.parity = true ∧ node.current = target := by
  cases candidate with
  | none => simp [validatesReach] at checked
  | some index =>
      cases hnode : found[index]? with
      | none => simp [validatesReach, hnode] at checked
      | some node =>
          simp only [validatesReach, hnode, Bool.and_eq_true,
            decide_eq_true_eq] at checked
          exact ⟨node, List.mem_of_getElem? hnode, checked⟩

set_option maxHeartbeats 1000000 in
-- Simplifying the retained-node existential exceeds the default limit.
/-- Indexed acceptance implies the original witness-retaining predicate. -/
theorem indexedReaches_sound
    {root : Nat → Nat → Index} {outerLevel width : Nat}
    {found : List ReachNode} {index : Array (Option Nat)} {target : Port}
    (checked : indexedReaches root outerLevel width found index target = true) :
    reaches root outerLevel found target = true := by
  simp only [indexedReaches, Bool.and_eq_true] at checked
  rcases validatesReach_sound checked.2 with
    ⟨node, nodeMember, nodeEven, nodeTarget⟩
  simp only [reaches, Bool.and_eq_true, List.any_eq_true,
    decide_eq_true_eq]
  exact ⟨checked.1, node, nodeMember, nodeEven, nodeTarget⟩

end PairCoverSeamResidualDirectPathFamilyReachIndex
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
