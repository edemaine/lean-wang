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

end ConcreteData
end LayeredFigure18ScaffoldData
end Figure13Layers
end OllingerRobinson
end LeanWang
