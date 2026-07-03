/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinsonFigure13Data

/-!
Finite obstruction checks for candidate Figure 13/Figure 16 scaffold
interfaces.

These facts are kept in a leaf module so the large audited Figure 13 data module
does not need to replay diagnostic `native_decide` proofs on ordinary imports.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace LayeredFigure18ScaffoldData
namespace ConcreteData

set_option maxRecDepth 10000

/-- Index-level form of `blackBlockAtSite_no_hBoundary`. -/
theorem blackBlockAtIndex_no_hBoundary
    (left right : Fin 92) :
    decide (((LayerComponent.black (blackComponentAt left)).block).hBoundaryMatches
      ((LayerComponent.black (blackComponentAt right)).block)) = false := by
  decide +revert

/-- Index-level form of `blackBlockAtSite_no_vBoundary`. -/
theorem blackBlockAtIndex_no_vBoundary
    (lower upper : Fin 92) :
    decide (((LayerComponent.black (blackComponentAt lower)).block).vBoundaryMatches
      ((LayerComponent.black (blackComponentAt upper)).block)) = false := by
  decide +revert

/--
Diagnostic obstruction for the current checked Figure 16 source-stack
interface: no two concrete Figure 13 black-layer components have horizontally
matching Figure 16 substitution-block boundaries.

This is a finite fact about the audited Figure 13 table.  It is useful because
it shows that a source-stack compatibility condition phrased directly in terms
of neighboring `phi_L3` blocks cannot be instantiated by adjacent Figure 13
sites.
-/
theorem blackBlockAtSite_no_hBoundary
    (left right : Figure18Site) :
    decide ((blackBlockAtSite left).hBoundaryMatches
      (blackBlockAtSite right)) = false := by
  simpa [blackBlockAtSite] using
    blackBlockAtIndex_no_hBoundary left.index right.index

/--
Vertical form of `blackBlockAtSite_no_hBoundary`.

Together these checks indicate that the Figure 16/Figure 18 scaffold interface
should route recognized macro-square compatibility through the Section 7
free-line geometry, not through adjacent black-layer source-stack block
boundaries.
-/
theorem blackBlockAtSite_no_vBoundary
    (lower upper : Figure18Site) :
    decide ((blackBlockAtSite lower).vBoundaryMatches
      (blackBlockAtSite upper)) = false := by
  simpa [blackBlockAtSite] using
    blackBlockAtIndex_no_vBoundary lower.index upper.index

/--
The current canonical checked Figure 16 recognized-compatible level-data
interface is inconsistent already at Robinson level 0.

The contradiction uses only the source-stack compatibility field: the black
layer compatibility certificate would force a horizontal `phi_L3` block-boundary
match between the two lower-row source sites, but `blackBlockAtSite_no_hBoundary`
rules out every such concrete Figure 13 black-layer boundary.
-/
theorem not_canonicalCheckedFigure16RecognizedCompatibleLevelData_zero :
    CanonicalCheckedFigure16RecognizedCompatibleLevelData 0 → False := by
  intro data
  let R := data.sourceSites.toSiteRectangle
  let S := checkedLayerStackOfSiteRectangle R data.stackCompatible
  let i0 : Fin (RobinsonSquare.freeGridSide 0) := ⟨0, by decide⟩
  let j0 : Fin (RobinsonSquare.freeGridSide 0) := ⟨0, by decide⟩
  have hi0 : i0.val + 1 < RobinsonSquare.freeGridSide 0 := by decide
  have hboundary := S.blackCompatible.hBoundary i0 j0 hi0
  change ((S.blockGrid .black i0 j0).hBoundaryMatches
      (S.blockGrid .black ⟨i0.val + 1, hi0⟩ j0)) at hboundary
  rw [checkedLayerStackOfSiteRectangle_black_blockGrid R data.stackCompatible i0 j0]
    at hboundary
  rw [checkedLayerStackOfSiteRectangle_black_blockGrid R data.stackCompatible
      ⟨i0.val + 1, hi0⟩ j0] at hboundary
  have hfalse : decide ((blackBlockAtSite (R i0 j0)).hBoundaryMatches
      (blackBlockAtSite (R ⟨i0.val + 1, hi0⟩ j0))) = true :=
    decide_eq_true hboundary
  rw [blackBlockAtSite_no_hBoundary] at hfalse
  contradiction

/--
The canonical checked Figure 16 recognized-compatible macro-square interface is
already inconsistent at Robinson level 0.

This is the existential, proof-facing version of
`not_canonicalCheckedFigure16RecognizedCompatibleLevelData_zero`: the
contradiction uses only the checked source-stack compatibility field and does
not depend on row-major checked-list data.
-/
theorem
    not_canonicalCheckedFigure16RecognizedCompatibleRobinsonBoardLevelMacroSquares_zero :
    (∃ source : SiteRectangle
      (RobinsonSquare.freeGridSide 0) (RobinsonSquare.freeGridSide 0),
      ∃ hcompatible :
        (checkedLayerStackRectangleOfSiteRectangle source).compatibleBool
          layerData (checkedLayerStackRectangleOfSiteRectangle_lookupBool source) =
            true,
        ∃ target : SiteRectangle
          (2 * RobinsonSquare.freeGridSide 0)
          (2 * RobinsonSquare.freeGridSide 0),
          Figure16ExpandedSiteRectangle.matchesBool
            (checkedLayerStackOfSiteRectangle source hcompatible) target =
              true ∧
            figure18SiteCompatibleRectangleBool target = true) → False := by
  rintro ⟨R, hcompatible, _target, _hrecognized, _htarget⟩
  let S := checkedLayerStackOfSiteRectangle R hcompatible
  let i0 : Fin (RobinsonSquare.freeGridSide 0) := ⟨0, by decide⟩
  let j0 : Fin (RobinsonSquare.freeGridSide 0) := ⟨0, by decide⟩
  have hi0 : i0.val + 1 < RobinsonSquare.freeGridSide 0 := by decide
  have hboundary := S.blackCompatible.hBoundary i0 j0 hi0
  change ((S.blockGrid .black i0 j0).hBoundaryMatches
      (S.blockGrid .black ⟨i0.val + 1, hi0⟩ j0)) at hboundary
  rw [checkedLayerStackOfSiteRectangle_black_blockGrid R hcompatible i0 j0]
    at hboundary
  rw [checkedLayerStackOfSiteRectangle_black_blockGrid R hcompatible
      ⟨i0.val + 1, hi0⟩ j0] at hboundary
  have hfalse : decide ((blackBlockAtSite (R i0 j0)).hBoundaryMatches
      (blackBlockAtSite (R ⟨i0.val + 1, hi0⟩ j0))) = true :=
    decide_eq_true hboundary
  rw [blackBlockAtSite_no_hBoundary] at hfalse
  contradiction

/--
All-level form of `not_canonicalCheckedFigure16RecognizedCompatibleLevelData_zero`.

This confirms that theorem surfaces requiring
`HasCanonicalCheckedFigure16RecognizedCompatibleLevelData` cannot be used as the
final scaffold route without changing the interface.
-/
theorem not_hasCanonicalCheckedFigure16RecognizedCompatibleLevelData :
    ¬ HasCanonicalCheckedFigure16RecognizedCompatibleLevelData := by
  intro hlevel
  rcases hlevel 0 with ⟨data⟩
  exact not_canonicalCheckedFigure16RecognizedCompatibleLevelData_zero data

/--
All-level form of
`not_canonicalCheckedFigure16RecognizedCompatibleRobinsonBoardLevelMacroSquares_zero`.

This rules out the canonical compatible Figure 16 level-check interface too;
the live scaffold route must avoid checked source-stack adjacency and use the
Section 7 geometry/layer-patch route instead.
-/
theorem
    not_hasCanonicalCheckedFigure16RecognizedCompatibleRobinsonBoardLevelMacroSquares :
    ¬ HasCanonicalCheckedFigure16RecognizedCompatibleRobinsonBoardLevelMacroSquares := by
  intro hlevel
  exact
    not_canonicalCheckedFigure16RecognizedCompatibleRobinsonBoardLevelMacroSquares_zero
      (hlevel 0)

end ConcreteData
end LayeredFigure18ScaffoldData
end Figure13Layers
end OllingerRobinson
end LeanWang
