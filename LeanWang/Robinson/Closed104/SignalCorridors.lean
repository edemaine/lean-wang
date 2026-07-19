/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.Signals

/-!
One-dimensional consequences of Robinson's obstruction-signal rules.

Between consecutive red boundaries a signal is transmitted unchanged. If the
two facing boundary edges are both inner edges, neither can emit and the
corridor is clear. If either facing edge is outer, that edge is required to
carry a signal and the corridor is obstructed.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace Signals

open QuarterGeometry

theorem horizontalAllowed_of_locallyAllowed {site : Quarters.QuarterIndex}
    {state : State} (h : locallyAllowed site state = true) :
    horizontalAllowed
      (verticalInterior? (components site.1).2.1 site.2) state = true := by
  have hparts :
      horizontalAllowed
          (verticalInterior? (components site.1).2.1 site.2) state = true ∧
        verticalAllowed
          (horizontalInterior? (components site.1).2.1 site.2) state = true := by
    simpa [locallyAllowed] using h
  exact hparts.1

theorem verticalAllowed_of_locallyAllowed {site : Quarters.QuarterIndex}
    {state : State} (h : locallyAllowed site state = true) :
    verticalAllowed
      (horizontalInterior? (components site.1).2.1 site.2) state = true := by
  have hparts :
      horizontalAllowed
          (verticalInterior? (components site.1).2.1 site.2) state = true ∧
        verticalAllowed
          (horizontalInterior? (components site.1).2.1 site.2) state = true := by
    simpa [locallyAllowed] using h
  exact hparts.2

theorem horizontal_transmits_of_allowed {state : State}
    (h : horizontalAllowed none state = true) :
    state.west = state.east := by
  simpa [horizontalAllowed] using of_decide_eq_true h

theorem vertical_transmits_of_allowed {state : State}
    (h : verticalAllowed none state = true) :
    state.south = state.north := by
  simpa [verticalAllowed] using of_decide_eq_true h

theorem horizontal_interiorEast_rules {state : State}
    (h : horizontalAllowed (some .east) state = true) :
    state.west ≠ .none ∧ state.east ≠ .forward := by
  simpa [horizontalAllowed] using of_decide_eq_true h

theorem horizontal_interiorWest_rules {state : State}
    (h : horizontalAllowed (some .west) state = true) :
    state.east ≠ .none ∧ state.west ≠ .backward := by
  simpa [horizontalAllowed] using of_decide_eq_true h

theorem vertical_interiorNorth_rules {state : State}
    (h : verticalAllowed (some .north) state = true) :
    state.south ≠ .none ∧ state.north ≠ .forward := by
  simpa [verticalAllowed] using of_decide_eq_true h

theorem vertical_interiorSouth_rules {state : State}
    (h : verticalAllowed (some .south) state = true) :
    state.north ≠ .none ∧ state.south ≠ .backward := by
  simpa [verticalAllowed] using of_decide_eq_true h

/-- Matching edges and transmitting intermediate cells preserve any value
across a one-dimensional corridor. -/
theorem value_across {α β : Type*}
    (state : Nat → α) (outgoing incoming : α → β) (start count : Nat)
    (hmatch : ∀ i, i ≤ count →
      outgoing (state (start + i)) = incoming (state (start + i + 1)))
    (htransmit : ∀ i, i < count →
      incoming (state (start + i + 1)) = outgoing (state (start + i + 1))) :
    outgoing (state start) = incoming (state (start + count + 1)) := by
  induction count with
  | zero => simpa using hmatch 0 (by omega)
  | succ count ih =>
      have hprefix := ih
        (fun i hi => hmatch i (by omega))
        (fun i hi => htransmit i (by omega))
      calc
        outgoing (state start) = incoming (state (start + count + 1)) := hprefix
        _ = outgoing (state (start + count + 1)) := htransmit count (by omega)
        _ = incoming (state (start + (count + 1) + 1)) := by
          simpa [Nat.add_assoc] using hmatch (count + 1) (by omega)

/-- Endpoint form of `value_across`, with matching and transmission hypotheses
stated directly on the open interval. -/
theorem value_between {α β : Type*}
    (state : Nat → α) (outgoing incoming : α → β)
    {start finish : Nat} (hlt : start < finish)
    (hmatch : ∀ position, start ≤ position → position < finish →
      outgoing (state position) = incoming (state (position + 1)))
    (htransmit : ∀ position, start < position → position < finish →
      incoming (state position) = outgoing (state position)) :
    outgoing (state start) = incoming (state finish) := by
  have hflow := value_across state outgoing incoming
    start (finish - start - 1)
    (fun offset _ => hmatch (start + offset) (by omega) (by omega))
    (fun offset _ => htransmit (start + offset + 1) (by omega) (by omega))
  have hend : start + (finish - start - 1) + 1 = finish := by omega
  simpa only [hend] using hflow

/-- Two horizontal inner edges cannot support a signal between them. -/
theorem horizontal_clear_of_inner_edges {left right : State}
    (hflow : left.east = right.west)
    (hleft : left.east ≠ .forward)
    (hright : right.west ≠ .backward) :
    left.east = .none ∧ right.west = .none := by
  have hcases : left.east = .none ∨
      left.east = .forward ∨ left.east = .backward := by
    cases left.east <;> simp
  rcases hcases with hnone | hforward | hbackward
  · exact ⟨hnone, hflow.symm.trans hnone⟩
  · exact False.elim (hleft hforward)
  · exact False.elim (hright (hflow.symm.trans hbackward))

/-- An outer edge at the left end obstructs the whole horizontal corridor. -/
theorem horizontal_obstructed_of_left_outer {left right : State}
    (hflow : left.east = right.west) (houter : left.east ≠ .none) :
    left.east ≠ .none ∧ right.west ≠ .none := by
  exact ⟨houter, hflow ▸ houter⟩

/-- An outer edge at the right end obstructs the whole horizontal corridor. -/
theorem horizontal_obstructed_of_right_outer {left right : State}
    (hflow : left.east = right.west) (houter : right.west ≠ .none) :
    left.east ≠ .none ∧ right.west ≠ .none := by
  exact ⟨hflow.symm ▸ houter, houter⟩

/-- Two vertical inner edges cannot support a signal between them. -/
theorem vertical_clear_of_inner_edges {lower upper : State}
    (hflow : lower.north = upper.south)
    (hlower : lower.north ≠ .forward)
    (hupper : upper.south ≠ .backward) :
    lower.north = .none ∧ upper.south = .none := by
  have hcases : lower.north = .none ∨
      lower.north = .forward ∨ lower.north = .backward := by
    cases lower.north <;> simp
  rcases hcases with hnone | hforward | hbackward
  · exact ⟨hnone, hflow.symm.trans hnone⟩
  · exact False.elim (hlower hforward)
  · exact False.elim (hupper (hflow.symm.trans hbackward))

/-- An outer edge at the lower end obstructs the whole vertical corridor. -/
theorem vertical_obstructed_of_lower_outer {lower upper : State}
    (hflow : lower.north = upper.south) (houter : lower.north ≠ .none) :
    lower.north ≠ .none ∧ upper.south ≠ .none := by
  exact ⟨houter, hflow ▸ houter⟩

/-- An outer edge at the upper end obstructs the whole vertical corridor. -/
theorem vertical_obstructed_of_upper_outer {lower upper : State}
    (hflow : lower.north = upper.south) (houter : upper.south ≠ .none) :
    lower.north ≠ .none ∧ upper.south ≠ .none := by
  exact ⟨hflow.symm ▸ houter, houter⟩

theorem signalPlane_hmatch {x : Int × Int → TileIn tileSet}
    (hx : ValidPlaneTiling tileSet x) (p : Int × Int) :
    (signalPlane x p).east =
      (signalPlane x (p.1 + 1, p.2)).west := by
  apply Flow.code_injective
  simpa [WangTile.HMatches, State.tile] using (signalPlane_matches hx).1 p

theorem signalPlane_vmatch {x : Int × Int → TileIn tileSet}
    (hx : ValidPlaneTiling tileSet x) (p : Int × Int) :
    (signalPlane x p).north =
      (signalPlane x (p.1, p.2 + 1)).south := by
  apply Flow.code_injective
  simpa [WangTile.VMatches, State.tile] using (signalPlane_matches hx).2 p

end Signals
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
