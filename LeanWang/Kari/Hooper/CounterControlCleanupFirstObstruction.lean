/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.BoundedMarkerProgram

/-!
# First-obstruction geometry after counter cleanup

The counter-control return transition erases the tag under its head and moves
one cell in the direction of the resumed search.  Thus a first nonblank cell
at positive distance `distance` before that move is the first nonblank cell at
distance `distance - 1` afterwards.

This file isolates the small piece of search geometry needed to turn that
observation into an exact statement about any generated resumed search.  In
particular, the target recognized by the resumed command need not be known in
advance: every bounded-marker target is nonblank, so uniqueness of the first
nonblank distance determines its search gap.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlCleanupFirstObstruction

open Turing
open BoundedMarkerProgram

universe u

namespace SearchGap

variable {Γ : Type u}
variable {IsBlank IsMark IsMark' : Γ → Prop}
variable {T : FullTM0.Tape Γ} {direction : Turing.Dir}
variable {distance first : Nat}

/-- A search gap remains valid when its target predicate is weakened. -/
theorem map_mark
    (h : Hooper.SearchGap IsBlank IsMark T direction distance)
    (hmark : ∀ symbol, IsMark symbol → IsMark' symbol) :
    Hooper.SearchGap IsBlank IsMark' T direction distance :=
  ⟨h.1, hmark _ h.2⟩

/-- Two search gaps whose blank and target predicates are disjoint must have
the same distance. -/
theorem distance_unique
    (hdisjoint : ∀ symbol, IsBlank symbol → IsMark symbol → False)
    (hfirst : Hooper.SearchGap IsBlank IsMark T direction first)
    (hdistance : Hooper.SearchGap IsBlank IsMark T direction distance) :
    first = distance := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact hdisjoint _ (hdistance.blank hlt) hfirst.marked
  · exact hdisjoint _ (hfirst.blank hlt) hdistance.marked

/-- A positive gap loses exactly one unit of distance after moving once
towards its target. -/
theorem tail_sub_one
    (h : Hooper.SearchGap IsBlank IsMark T direction distance)
    (hpositive : 0 < distance) :
    Hooper.SearchGap IsBlank IsMark (T.move direction) direction
      (distance - 1) := by
  have hdistance : distance = (distance - 1) + 1 := by omega
  rw [hdistance] at h
  exact h.tail

/-- If `first` is the first nonblank position on the original tape, then any
nonblank-target search gap after one move has distance `first - 1`. -/
theorem distance_eq_sub_one_of_first_nonblank
    {blank : Γ}
    (hfirst : Hooper.SearchGap (fun symbol => symbol = blank)
      (fun symbol => symbol ≠ blank) T direction first)
    (hpositive : 0 < first)
    (hdistance : Hooper.SearchGap (fun symbol => symbol = blank) IsMark
      (T.move direction) direction distance)
    (hmark : ∀ symbol, IsMark symbol → symbol ≠ blank) :
    distance = first - 1 := by
  have hfirst' := tail_sub_one hfirst hpositive
  have hdistance' := map_mark hdistance hmark
  exact distance_unique
    (fun _ hblank hnonblank => hnonblank hblank)
    hdistance' hfirst'

end SearchGap

/-- Specialized form for generated bounded-marker targets: their matches are
always nonblank, so the resumed search distance is forced by the first
nonblank obstruction before the return move. -/
theorem target_distance_eq_sub_one_of_first_nonblank
    {numTags : Nat} {T : FullTM0.Tape (Symbol numTags)}
    {direction : Turing.Dir} {first distance : Nat}
    {target : Target numTags}
    (hfirst : Hooper.SearchGap (fun symbol => symbol = blankSymbol)
      (fun symbol => symbol ≠ blankSymbol) T direction first)
    (hpositive : 0 < first)
    (hdistance : Hooper.SearchGap (fun symbol => symbol = blankSymbol)
      target.Matches (T.move direction) direction distance) :
    distance = first - 1 := by
  exact SearchGap.distance_eq_sub_one_of_first_nonblank
    hfirst hpositive hdistance fun symbol hmatch hblank =>
      target_not_blank target (hblank ▸ hmatch)

end CounterControlCleanupFirstObstruction
end Hooper
end Kari
end LeanWang
