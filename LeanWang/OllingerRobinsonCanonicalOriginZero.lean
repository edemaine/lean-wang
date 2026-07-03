/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinsonFigure13Data

/-!
Bridges between canonical Robinson free-site recognition and origin-zero
Figure 18 recognizability targets.

The concrete Figure 13 transcription file is large.  These theorem-facing
bridges live in a small downstream module so the scaffold target can evolve
without forcing a full recheck of the audited transcription data.
-/

namespace LeanWang
namespace OllingerRobinson

/--
Canonical free-site active/corner recognition supplies the origin-zero decoded
site window target.  For a requested `n × n` origin-zero window, choose a
Robinson square level whose canonical free-site grid has side at least `n`;
the canonical coordinates are `0, ..., freeGridSide level - 1`.
-/
theorem
    hasFigure18OriginZeroCombinedActiveCornerWindowsForTable_of_canonicalFreeSiteRectActiveCorner
    {table : Figure18RoleTable}
    (hactiveCorner :
      HasFigure18RobinsonBoardCanonicalFreeSiteRectActiveCornerForTable table) :
    HasFigure18OriginZeroCombinedActiveCornerWindowsForTable table := by
  intro T seed x hx n _hn
  rcases RobinsonSquare.exists_level_with_payload_capacity n with
    ⟨level, hlevel⟩
  rcases hactiveCorner x hx with ⟨activeCorner⟩
  constructor
  · intro i j
    have hi : i.val < RobinsonSquare.freeGridSide level :=
      Nat.lt_of_lt_of_le i.isLt hlevel
    have hj : j.val < RobinsonSquare.freeGridSide level :=
      Nat.lt_of_lt_of_le j.isLt hlevel
    have hactive :
        CellRole.isActive
          (table.roleAtSite
            (table.combinedSite
              (x ((i.val : Int), (j.val : Int))))) = true := by
      simpa [RobinsonBoardSignalGeometry.canonical] using
        (activeCorner level).1 ⟨i.val, hi⟩ ⟨j.val, hj⟩
    simpa using hactive
  · have hcornerAtOrigin :
        table.combinedSite (x (0, 0)) = table.cornerSite := by
      simpa [RobinsonBoardSignalGeometry.canonical] using
        (activeCorner level).2
    rw [hcornerAtOrigin]
    exact table.roleAtSite_corner

/--
Canonical free-site active/corner recognition supplies origin-zero decoded-site
windows for a concrete active-site/corner-site list.
-/
theorem
    hasFigure18OriginZeroCombinedActiveCornerWindows_of_canonicalFreeSiteRectActiveCorner
    {activeSites : List Figure18Site} {cornerSite : Figure18Site}
    (hactiveCorner :
      HasFigure18RobinsonBoardCanonicalFreeSiteRectActiveCorner
        activeSites cornerSite) :
    HasFigure18OriginZeroCombinedActiveCornerWindows activeSites cornerSite :=
  hasFigure18OriginZeroCombinedActiveCornerWindowsForTable_of_canonicalFreeSiteRectActiveCorner
    hactiveCorner

end OllingerRobinson
end LeanWang
