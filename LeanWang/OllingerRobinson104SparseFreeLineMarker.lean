/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104SparseFreeLineEvenOddLocalStep

/-!
# The recursive marked free line

The distinguished Figure 18 marker lies at offset `7` in the checked even
depth-one board.  It is immediately southwest of the retained sparse family,
and follows the odd main-child recurrence at every later depth.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace SparseFreeLineMarker

open RedCycles RedShadeGraphRefinement ShadedFreeLineGraph
  ShadedFreeLineGraphBase ShadedFreeLinePatternRefinement
  ShadedFreeLineOffsets ShadedFreeLineRecurrence SparseFreeLineOffsets
  SparseFreeLineEvenOddLocalStep Signals.FreeCellLocal

set_option maxRecDepth 20000

/-- Offset of the distinguished marker line at a positive even depth. -/
def markerOffset (depth : Nat) : Nat :=
  2 * 4 ^ depth - 1

@[simp] theorem markerOffset_one : markerOffset 1 = 7 := by
  norm_num [markerOffset]

theorem markerOffset_mod_four (depth : Nat) :
    markerOffset (depth + 1) % 4 = 3 := by
  unfold markerOffset
  rw [pow_succ]
  have hpositive : 0 < 4 ^ depth := pow_pos (by decide) _
  omega

theorem markerOffset_mod_two_ne_zero (depth : Nat) :
    markerOffset (depth + 1) % 2 ≠ 0 := by
  have hmod := congrArg (fun value : Nat => value % 2)
    (markerOffset_mod_four depth)
  rw [Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 4)] at hmod
  norm_num at hmod
  omega

theorem mainChild_markerOffset (depth : Nat) :
    mainChild (markerOffset (depth + 1)) = markerOffset (depth + 2) := by
  rw [mainChild, if_neg (markerOffset_mod_two_ne_zero depth)]
  unfold markerOffset
  rw [pow_succ, pow_succ]
  have hpositive : 0 < 4 ^ depth := pow_pos (by decide) _
  omega

theorem lineCoordinate_markerOffset (depth : Nat) :
    lineCoordinate .even (depth + 1) (markerOffset (depth + 1)) =
      4 ^ (depth + 2) := by
  rw [BorderCoverageOffsets.lineCoordinate_even]
  unfold markerOffset
  rw [pow_succ, pow_succ]
  have hpositive : 0 < 4 ^ depth := pow_pos (by decide) _
  omega

/-- The finite depth-one audit includes the marked row and column. -/
theorem baseCertificates (parent : Index) :
    LiveRowCertificate (localGrid .even 1 parent)
        (west .even 1) (east .even 1) (west .even 1) (east .even 1)
        (lineCoordinate .even 1 (markerOffset 1)) ∧
      LiveColumnCertificate (localGrid .even 1 parent)
        (west .even 1) (east .even 1) (west .even 1) (east .even 1)
        (lineCoordinate .even 1 (markerOffset 1)) := by
  have hmem : markerOffset 1 ∈ freeOffsets 1 := by
    rw [markerOffset_one, freeOffsets_one]
    simp
  exact ⟨
    (ShadedFreeLineRecurrence.graphHolds_even_one parent).1 _ hmem,
    (ShadedFreeLineRecurrence.graphHolds_even_one parent).2 _ hmem⟩

/-- The marked row and column survive at every positive even depth. -/
theorem certificates (extra : Nat) (parent : Index) :
    LiveRowCertificate (localGrid .even (extra + 1) parent)
        (west .even (extra + 1)) (east .even (extra + 1))
        (west .even (extra + 1)) (east .even (extra + 1))
        (lineCoordinate .even (extra + 1) (markerOffset (extra + 1))) ∧
      LiveColumnCertificate (localGrid .even (extra + 1) parent)
        (west .even (extra + 1)) (east .even (extra + 1))
        (west .even (extra + 1)) (east .even (extra + 1))
        (lineCoordinate .even (extra + 1) (markerOffset (extra + 1))) := by
  induction extra with
  | zero => simpa using baseCertificates parent
  | succ extra ih =>
      have next := mainChildStep extra parent
        (markerOffset_mod_four extra) ih.1 ih.2
      rw [mainChild_markerOffset extra] at next
      simpa [Nat.add_assoc] using next

set_option linter.style.nativeDecide false in
theorem markerSouthwest_refines (index : Index)
    (hmarker : (index, Quadrant.southwest) ∈
      ShadedSignals.markerQuarters) :
    (southwestChild (southwestChild index), Quadrant.southwest) ∈
      ShadedSignals.markerQuarters := by
  revert index
  native_decide

/-- The full tile index at the recursively marked crossing remains marked. -/
theorem markerIndex (extra : Nat) (parent : Index) :
    (localGrid .even (extra + 1) parent
        (2 * 4 ^ (extra + 1)) (2 * 4 ^ (extra + 1)),
      Quadrant.southwest) ∈ ShadedSignals.markerQuarters := by
  induction extra with
  | zero =>
      change
        (iterateRefine 4 (fun _ _ => parent) 8 8, Quadrant.southwest) ∈
          ShadedSignals.markerQuarters
      have base := ShadedFreeLineGraphBase.markerQuarter_at_sixteen parent
      change
        (iterateRefine 4 (fun _ _ => parent) 8 8, Quadrant.southwest) ∈
          ShadedSignals.markerQuarters at base
      exact base
  | succ extra ih =>
      rw [show extra + 1 + 1 = (extra + 1) + 1 by omega,
        localGrid_succ]
      change
        (refineIndexGrid (refineIndexGrid (localGrid .even (extra + 1) parent))
            (2 * 4 ^ (extra + 2)) (2 * 4 ^ (extra + 2)),
          Quadrant.southwest) ∈ ShadedSignals.markerQuarters
      rw [show 2 * 4 ^ (extra + 2) =
          2 * (2 * (2 * 4 ^ (extra + 1))) by
        rw [pow_succ]
        omega]
      simp only [refineIndexGrid_even_even]
      exact markerSouthwest_refines _ ih

/-- The quarter at the marked row/column crossing remains a marker quarter. -/
theorem markerQuarter (extra : Nat) (parent : Index) :
    let coordinate :=
      lineCoordinate .even (extra + 1) (markerOffset (extra + 1))
    (localGrid .even (extra + 1) parent
        (coordinate / 2) (coordinate / 2),
      quadrantAt coordinate coordinate) ∈ ShadedSignals.markerQuarters := by
  dsimp only
  rw [lineCoordinate_markerOffset]
  have hpower : 4 ^ (extra + 2) = 2 * (2 * 4 ^ (extra + 1)) := by
    rw [pow_succ]
    omega
  have hhalf : 4 ^ (extra + 2) / 2 = 2 * 4 ^ (extra + 1) := by
    rw [hpower]
    omega
  have hquadrant :
      quadrantAt (4 ^ (extra + 2)) (4 ^ (extra + 2)) =
        Quadrant.southwest := by
    rw [hpower]
    simp [Signals.FreeCellLocal.quadrantAt, Quadrant.ofBits]
  rw [hhalf, hquadrant]
  exact markerIndex extra parent

end SparseFreeLineMarker
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
