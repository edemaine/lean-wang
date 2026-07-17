/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.PairCoverSeamPathSemantics
import LeanWang.Robinson.Closed104.PairCoverSeamPathBoundedSearch

/-!
# Reusable seam-path query search

Shared exhaustive query checkers and their bounded and unbounded soundness.
The phase/depth-specific base-search instance is kept separately in
`LeanWang.Robinson.Closed104.PairCoverSeamPathBaseAudit`.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace PairCoverSeamPathBaseAudit

open RedCycles RedShadeCycles RedShadeGraph
  ShadedFreeLineRecurrence
  PairCoverSeamArithmetic
  PairCoverSeamPathSearch PairCoverSeamShadePaths
  Signals.FreeCellLocal BorderGeometry

set_option maxRecDepth 20000

def verticalQueriesCheck (grid : Nat → Nat → Index)
    (size fuel fallbackFuel west east column boundary : Nat)
    (queries : List Nat) : Bool :=
  match queries with
  | [] => true
  | _ =>
      let found := verticalReachCover grid size size fuel
        west east column boundary queries
      let missing := queries.filter fun row =>
        !verticalReachSeamCheck grid west east column row boundary found
      let fallback := match missing with
        | [] => []
        | _ => verticalReachCover grid size size fallbackFuel
            west east column boundary missing
      queries.all fun row =>
        verticalReachSeamCheck grid west east column row boundary found ||
          verticalReachSeamCheck grid west east column row boundary fallback

def horizontalQueriesCheck (grid : Nat → Nat → Index)
    (size fuel fallbackFuel south north row boundary : Nat)
    (queries : List Nat) : Bool :=
  match queries with
  | [] => true
  | _ =>
      let found := horizontalReachCover grid size size fuel
        south north row boundary queries
      let missing := queries.filter fun column =>
        !horizontalReachSeamCheck grid south north row column boundary found
      let fallback := match missing with
        | [] => []
        | _ => horizontalReachCover grid size size fallbackFuel
            south north row boundary missing
      queries.all fun column =>
        horizontalReachSeamCheck grid south north row column boundary found ||
          horizontalReachSeamCheck grid south north row column boundary fallback

theorem verticalQueriesCheck_sound
    {grid : Nat → Nat → Index}
    {size fuel fallbackFuel west east column boundary row : Nat}
    {queries : List Nat} (hrow : row ∈ queries)
    (checked : verticalQueriesCheck grid size fuel fallbackFuel
      west east column boundary queries = true) :
    VerticalSeamPath grid west east column row boundary := by
  cases hqueries : queries with
  | nil => simp [hqueries] at hrow
  | cons first rest =>
      subst queries
      simp only [verticalQueriesCheck] at checked
      simp only [List.all_eq_true] at checked
      have rowChecked := checked row hrow
      simp only [Bool.or_eq_true] at rowChecked
      rcases rowChecked with hfound | hfallback
      · exact verticalReachCover_check_sound hfound
      · let missing := (first :: rest).filter fun query =>
          !verticalReachSeamCheck grid west east column query boundary
            (verticalReachCover grid size size fuel
              west east column boundary (first :: rest))
        change verticalReachSeamCheck grid west east column row boundary
          (match missing with
            | [] => []
            | _ => verticalReachCover grid size size fallbackFuel
                west east column boundary missing) = true at hfallback
        cases hmissing : missing with
        | nil => simp [hmissing, verticalReachSeamCheck] at hfallback
        | cons query queries =>
            apply verticalReachCover_check_sound
            simpa [hmissing] using hfallback

theorem horizontalQueriesCheck_sound
    {grid : Nat → Nat → Index}
    {size fuel fallbackFuel south north row boundary column : Nat}
    {queries : List Nat} (hcolumn : column ∈ queries)
    (checked : horizontalQueriesCheck grid size fuel fallbackFuel
      south north row boundary queries = true) :
    HorizontalSeamPath grid south north row column boundary := by
  cases hqueries : queries with
  | nil => simp [hqueries] at hcolumn
  | cons first rest =>
      subst queries
      simp only [horizontalQueriesCheck] at checked
      simp only [List.all_eq_true] at checked
      have columnChecked := checked column hcolumn
      simp only [Bool.or_eq_true] at columnChecked
      rcases columnChecked with hfound | hfallback
      · exact horizontalReachCover_check_sound hfound
      · let missing := (first :: rest).filter fun query =>
          !horizontalReachSeamCheck grid south north row query boundary
            (horizontalReachCover grid size size fuel
              south north row boundary (first :: rest))
        change horizontalReachSeamCheck grid south north row column boundary
          (match missing with
            | [] => []
            | _ => horizontalReachCover grid size size fallbackFuel
                south north row boundary missing) = true at hfallback
        cases hmissing : missing with
        | nil => simp [hmissing, horizontalReachSeamCheck] at hfallback
        | cons query queries =>
            apply horizontalReachCover_check_sound
            simpa [hmissing] using hfallback

end PairCoverSeamPathBaseAudit

namespace PairCoverSeamPathBoundedBase

open RedCycles RedShadeCycles RedShadeGraph RedShadeGraphSearch
  RedShadeGraphSearchSoundness BorderGeometry
  PairCoverSeamShadePaths PairCoverSeamPathSearch
  PairCoverSeamPathBoundedSearch PairCoverSeamPathBaseAudit
  PairCoverSeamArithmetic ShadedFreeLineRecurrence Signals.FreeCellLocal

set_option maxRecDepth 20000

theorem verticalReachSeamCheck_bounded_sound_of_paths
    {grid : Nat → Nat → Index} {size west east column row boundary : Nat}
    {found : List ReachNode}
    (paths : ∀ node ∈ found,
      BoundedPath grid size size (horizontalPort grid column boundary)
        node.current node.parity)
    (checked : verticalReachSeamCheck grid west east
      column row boundary found = true) :
    BoundedVerticalSeamPath grid size west east column row boundary := by
  simp only [verticalReachSeamCheck, List.any_eq_true,
    Bool.and_eq_true] at checked
  rcases checked with ⟨node, hnode, hparity, htarget⟩
  have nodeParity : node.parity = false :=
    Bool.eq_false_of_not_eq_true' hparity
  have pathFalse : BoundedPath grid size size
      (horizontalPort grid column boundary) node.current false := by
    simpa [nodeParity] using paths node hnode
  exact boundedVerticalSeamPath_of_target pathFalse htarget

theorem horizontalReachSeamCheck_bounded_sound_of_paths
    {grid : Nat → Nat → Index} {size south north row column boundary : Nat}
    {found : List ReachNode}
    (paths : ∀ node ∈ found,
      BoundedPath grid size size (verticalPort grid boundary row)
        node.current node.parity)
    (checked : horizontalReachSeamCheck grid south north
      row column boundary found = true) :
    BoundedHorizontalSeamPath grid size south north row column boundary := by
  simp only [horizontalReachSeamCheck, List.any_eq_true,
    Bool.and_eq_true] at checked
  rcases checked with ⟨node, hnode, hparity, htarget⟩
  have nodeParity : node.parity = false :=
    Bool.eq_false_of_not_eq_true' hparity
  have pathFalse : BoundedPath grid size size
      (verticalPort grid boundary row) node.current false := by
    simpa [nodeParity] using paths node hnode
  exact boundedHorizontalSeamPath_of_target pathFalse htarget

theorem verticalQueriesCheck_bounded_sound
    {grid : Nat → Nat → Index}
    {size fuel fallbackFuel west east column boundary row : Nat}
    {queries : List Nat} (hrow : row ∈ queries)
    (startBound : PortInBounds (horizontalPort grid column boundary) size size)
    (checked : verticalQueriesCheck grid size fuel fallbackFuel
      west east column boundary queries = true) :
    BoundedVerticalSeamPath grid size west east column row boundary := by
  cases hqueries : queries with
  | nil => simp [hqueries] at hrow
  | cons first rest =>
      subst queries
      simp only [verticalQueriesCheck] at checked
      simp only [List.all_eq_true] at checked
      have rowChecked := checked row hrow
      simp only [Bool.or_eq_true] at rowChecked
      rcases rowChecked with hfound | hfallback
      · exact verticalReachSeamCheck_bounded_sound_of_paths
          (fun _ hnode => verticalReachCover_node_bounded_sound startBound hnode)
          hfound
      · let missing := (first :: rest).filter fun query =>
          !verticalReachSeamCheck grid west east column query boundary
            (verticalReachCover grid size size fuel
              west east column boundary (first :: rest))
        change verticalReachSeamCheck grid west east column row boundary
          (match missing with
            | [] => []
            | _ => verticalReachCover grid size size fallbackFuel
                west east column boundary missing) = true at hfallback
        cases hmissing : missing with
        | nil => simp [hmissing, verticalReachSeamCheck] at hfallback
        | cons query queries =>
            apply verticalReachSeamCheck_bounded_sound_of_paths
              (fun _ hnode => verticalReachCover_node_bounded_sound startBound hnode)
            simpa [hmissing] using hfallback

theorem horizontalQueriesCheck_bounded_sound
    {grid : Nat → Nat → Index}
    {size fuel fallbackFuel south north row boundary column : Nat}
    {queries : List Nat} (hcolumn : column ∈ queries)
    (startBound : PortInBounds (verticalPort grid boundary row) size size)
    (checked : horizontalQueriesCheck grid size fuel fallbackFuel
      south north row boundary queries = true) :
    BoundedHorizontalSeamPath grid size south north row column boundary := by
  cases hqueries : queries with
  | nil => simp [hqueries] at hcolumn
  | cons first rest =>
      subst queries
      simp only [horizontalQueriesCheck] at checked
      simp only [List.all_eq_true] at checked
      have columnChecked := checked column hcolumn
      simp only [Bool.or_eq_true] at columnChecked
      rcases columnChecked with hfound | hfallback
      · exact horizontalReachSeamCheck_bounded_sound_of_paths
          (fun _ hnode => horizontalReachCover_node_bounded_sound startBound hnode)
          hfound
      · let missing := (first :: rest).filter fun query =>
          !horizontalReachSeamCheck grid south north row query boundary
            (horizontalReachCover grid size size fuel
              south north row boundary (first :: rest))
        change horizontalReachSeamCheck grid south north row column boundary
          (match missing with
            | [] => []
            | _ => horizontalReachCover grid size size fallbackFuel
                south north row boundary missing) = true at hfallback
        cases hmissing : missing with
        | nil => simp [hmissing, horizontalReachSeamCheck] at hfallback
        | cons query queries =>
            apply horizontalReachSeamCheck_bounded_sound_of_paths
              (fun _ hnode => horizontalReachCover_node_bounded_sound startBound hnode)
            simpa [hmissing] using hfallback

end PairCoverSeamPathBoundedBase
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
