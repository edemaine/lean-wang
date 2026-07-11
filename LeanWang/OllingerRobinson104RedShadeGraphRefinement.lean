/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104RedShadeGraphRefinementAudit
import LeanWang.OllingerRobinson104RedShadeGraphSearchSoundness

/-!
Proof-facing two-substitution red-path refinement lemmas.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace RedShadeGraphRefinement

open RedShadeGraph RedShadeGraphSearch RedShadeGraphSearchSoundness
  Signals.FreeCellLocal

set_option maxRecDepth 20000

set_option maxHeartbeats 1000000 in
-- Projecting one parent from the native all-parent connector table.
theorem completeFor_eq_true (parent : Index) : completeFor parent = true := by
  have hall : ∀ candidate ∈ List.finRange 104,
      completeFor candidate = true := by
    simpa [complete, List.all_eq_true] using complete_eq_true
  exact hall parent (List.mem_finRange parent)

set_option linter.style.nativeDecide false in
/-- Two substitutions retain the old quarter component at local coordinates. -/
theorem componentAt_fineGrid_southwest (parent : Index)
    {x y : Nat} (hx : x < 2) (hy : y < 2) :
    componentAt (fineGrid parent) x y = componentAt (coarseGrid parent) x y := by
  have hxCases : x = 0 ∨ x = 1 := by omega
  have hyCases : y = 0 ∨ y = 1 := by omega
  rcases hxCases with rfl | rfl <;> rcases hyCases with rfl | rfl <;>
    revert parent <;> native_decide

theorem connectorMoves?_eq_some_iff
    (parent : Index) (side : ExitSide) (offset : Nat)
    (moves : List CertificateMove) :
    connectorMoves? parent side offset = some moves ↔
      connectorSearch parent side offset =
        some (externalPort side offset, false, moves) := by
  unfold connectorMoves?
  cases hsearch : connectorSearch parent side offset with
  | none => simp
  | some result =>
      rcases result with ⟨finish, parity, foundMoves⟩
      cases parity
      · by_cases hfinish : finish = externalPort side offset
        · subst finish
          simp
        · simp [hfinish]
      · simp

theorem connectorMoves_exists (parent : Index) (side : ExitSide)
    {offset : Nat} (hoffset : offset < 2)
    (hpresent : portPresent (coarseGrid parent)
      (internalPort side offset) = true) :
    ∃ moves, connectorSearch parent side offset =
      some (externalPort side offset, false, moves) := by
  have hcomplete := completeFor_eq_true parent
  simp only [completeFor, List.all_eq_true] at hcomplete
  have hside : side ∈ exitSides := by cases side <;> simp [exitSides]
  have hoffsetMem : offset ∈ List.range 2 := by simpa using hoffset
  have hcase := hcomplete side hside offset hoffsetMem
  rw [hpresent] at hcase
  simp only [if_true] at hcase
  cases hconnector : connectorMoves? parent side offset with
  | none => simp [hconnector] at hcase
  | some moves =>
      exact ⟨moves,
        (connectorMoves?_eq_some_iff parent side offset moves).1 hconnector⟩

/-- A live old east/north port reaches the same external macro port evenly. -/
theorem connectorPath (parent : Index) (side : ExitSide)
    {offset : Nat} (hoffset : offset < 2)
    (hpresent : portPresent (coarseGrid parent)
      (internalPort side offset) = true) :
    Path (fineGrid parent) (internalPort side offset)
      (externalPort side offset) false := by
  rcases connectorMoves_exists parent side hoffset hpresent with
    ⟨moves, hsearch⟩
  exact search_sound hsearch

end RedShadeGraphRefinement
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
