/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinsonFigure13Transcription
import LeanWang.Theorems

/-!
Finite obstruction for the current Figure 18 scaffold transcription.

The exhaustive row checker in `OllingerRobinsonFigure13Transcription` reports
that the subdivided Figure 13 tiles allow no compatible `3 x 3` square. This
file connects that Boolean certificate to the propositional tiling interfaces.
In particular, routing a payload through these scaffold tiles cannot repair
the obstruction: every combined tiling projects to a scaffold tiling.
-/

namespace LeanWang
namespace OllingerRobinson

namespace Figure18Site

private theorem three_site_row_mem_compatibleRows
    (a b c : Figure18Site)
    (hab : hCompatible a b = true)
    (hbc : hCompatible b c = true) :
    [a, b, c] ∈ compatibleRows 3 := by
  simp [compatibleRows, rowTailsAfter, mem_all, hab, hbc]

private theorem three_site_rowsVCompatible
    (a b c d e f : Figure18Site)
    (had : vCompatible a d = true)
    (hbe : vCompatible b e = true)
    (hcf : vCompatible c f = true) :
    rowsVCompatible [a, b, c] [d, e, f] = true := by
  simp [rowsVCompatible, had, hbe, hcf]

private theorem three_rows_mem_rowStackTops
    (south middle north : List Figure18Site)
    (hsouth : south ∈ compatibleRows 3)
    (hmiddle : middle ∈ compatibleRows 3)
    (hnorth : north ∈ compatibleRows 3)
    (hsm : rowsVCompatible south middle = true)
    (hmn : rowsVCompatible middle north = true) :
    north ∈ rowStackTops 3 2 := by
  have hmiddleStack : middle ∈ rowStackTops 3 1 := by
    rw [rowStackTops, List.mem_flatMap]
    exact ⟨south, by simpa [rowStackTops] using hsouth,
      List.mem_filter.2 ⟨hmiddle, hsm⟩⟩
  rw [rowStackTops, List.mem_flatMap]
  exact ⟨middle, hmiddleStack, List.mem_filter.2 ⟨hnorth, hmn⟩⟩

/-- A valid `3 x 3` Figure 18 scaffold square makes the finite row checker succeed. -/
theorem hasRectangleStackBool_three_three_eq_true_of_validRectangle
    {rect : Rectangle 3 3}
    (hrect : ValidRectangle figure18ScaffoldTiles rect) :
    hasRectangleStackBool 3 3 = true := by
  classical
  have hsite : ∀ i : Fin 3, ∀ j : Fin 3,
      ∃ site : Figure18Site, site.tile = rect i j := by
    intro i j
    rcases exists_site_of_mem_figure18ScaffoldTiles (hrect.1 i j) with
      ⟨site, _hmem, htile⟩
    exact ⟨site, htile⟩
  let siteAt : Fin 3 → Fin 3 → Figure18Site := fun i j => Classical.choose (hsite i j)
  have siteAt_tile (i : Fin 3) (j : Fin 3) :
      (siteAt i j).tile = rect i j :=
    Classical.choose_spec (hsite i j)
  let west : Fin 3 := ⟨0, by decide⟩
  let center : Fin 3 := ⟨1, by decide⟩
  let east : Fin 3 := ⟨2, by decide⟩
  let south : Fin 3 := ⟨0, by decide⟩
  let middle : Fin 3 := ⟨1, by decide⟩
  let north : Fin 3 := ⟨2, by decide⟩
  let row (j : Fin 3) : List Figure18Site :=
    [siteAt west j, siteAt center j, siteAt east j]
  have hh (j : Fin 3) :
      hCompatible (siteAt west j) (siteAt center j) = true ∧
        hCompatible (siteAt center j) (siteAt east j) = true := by
    constructor
    · apply hCompatible_of_hMatches
      rw [siteAt_tile, siteAt_tile]
      simpa [west, center] using hrect.2.1 west j (by decide)
    · apply hCompatible_of_hMatches
      rw [siteAt_tile, siteAt_tile]
      simpa [center, east] using hrect.2.1 center j (by decide)
  have hv (i : Fin 3) :
      vCompatible (siteAt i south) (siteAt i middle) = true ∧
        vCompatible (siteAt i middle) (siteAt i north) = true := by
    constructor
    · apply vCompatible_of_vMatches
      rw [siteAt_tile, siteAt_tile]
      simpa [south, middle] using hrect.2.2 i south (by decide)
    · apply vCompatible_of_vMatches
      rw [siteAt_tile, siteAt_tile]
      simpa [middle, north] using hrect.2.2 i middle (by decide)
  have hrow (j : Fin 3) : row j ∈ compatibleRows 3 := by
    exact three_site_row_mem_compatibleRows _ _ _ (hh j).1 (hh j).2
  have hsouthMiddle : rowsVCompatible (row south) (row middle) = true := by
    exact three_site_rowsVCompatible _ _ _ _ _ _
      (hv west).1 (hv center).1 (hv east).1
  have hmiddleNorth : rowsVCompatible (row middle) (row north) = true := by
    exact three_site_rowsVCompatible _ _ _ _ _ _
      (hv west).2 (hv center).2 (hv east).2
  have hnorthStack : row north ∈ rowStackTops 3 2 :=
    three_rows_mem_rowStackTops _ _ _
      (hrow south) (hrow middle) (hrow north) hsouthMiddle hmiddleNorth
  have hne : rowStackTops 3 2 ≠ [] := List.ne_nil_of_mem hnorthStack
  simp [hasRectangleStackBool, hne]

/-- The current subdivided Figure 13 transcription admits no valid `3 x 3` square. -/
theorem not_tileableSquare_figure18ScaffoldTiles_three :
    ¬ TileableSquare figure18ScaffoldTiles 3 := by
  rintro ⟨rect, hrect⟩
  have htrue := hasRectangleStackBool_three_three_eq_true_of_validRectangle hrect
  rw [hasRectangleStackBool_three_three_eq_false] at htrue
  contradiction

end Figure18Site

/-- The current Figure 18 scaffold transcription is not a standalone plane tileset. -/
theorem not_tilesPlane_figure18ScaffoldTiles :
    ¬ TilesPlane figure18ScaffoldTiles := by
  intro hplane
  exact Figure18Site.not_tileableSquare_figure18ScaffoldTiles_three
    (tileableSquare_of_tilesPlane hplane 3)

/-- No payload can overcome the finite obstruction in the current scaffold base layer. -/
theorem not_tilesPlane_combineWithFigure18Scaffold
    (S : Scaffold) (hS : S.tiles = figure18ScaffoldTiles)
    (T : TileSet) (seed : WangTile) :
    ¬ TilesPlane (combineWithScaffold S T seed) := by
  intro hcombined
  apply not_tilesPlane_figure18ScaffoldTiles
  rw [← hS]
  exact tilesPlane_scaffold_of_tilesPlane_combineWithScaffold hcombined

end OllingerRobinson
end LeanWang
