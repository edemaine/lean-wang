/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinsonFigure13Layers

/-!
Concrete audited data extracted from the indexed Figure 13 rendering.

This file is intentionally incremental.  The first committed slice records the
thin `L1` components visible in the top row of
[figures/figure13-indexed.png](../figures/figure13-indexed.png), using the
component labels from
[figures/figure16-layer-components.png](../figures/figure16-layer-components.png).
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace LayeredFigure18ScaffoldData
namespace ConcreteData

/--
Thin-layer entries for Figure 13 tile indices `0` through `7`.

These are the eight tiles in the shortened top row of the indexed Figure 13
rendering, read left-to-right.
-/
def topRowThinEntries : List (Nat × Figure16.Thin) := [
  (0, Figure16.Thin.a),
  (1, Figure16.Thin.c),
  (2, Figure16.Thin.d),
  (3, Figure16.Thin.b),
  (4, Figure16.Thin.a),
  (5, Figure16.Thin.c),
  (6, Figure16.Thin.d),
  (7, Figure16.Thin.b)
]

theorem topRowThinEntries_valid :
    sparseEntriesValidBool topRowThinEntries = true := by
  decide

theorem topRowThinEntries_indices :
    topRowThinEntries.map Prod.fst = [0, 1, 2, 3, 4, 5, 6, 7] := by
  rfl

def topRowThinCheckedEntries : CheckedSparseEntries Figure16.Thin :=
  CheckedSparseEntries.ofEntries topRowThinEntries topRowThinEntries_valid

theorem topRowThinCheckedEntries_entries :
    topRowThinCheckedEntries.entries = topRowThinEntries :=
  rfl

def topRowThinSparseRows : CheckedSparseSeparateLayerRows :=
  CheckedSparseSeparateLayerRows.ofCheckedEntries
    topRowThinCheckedEntries
    (CheckedSparseEntries.empty Figure16.Thick)
    (CheckedSparseEntries.empty Figure16.Black)

theorem topRowThinSparseRows_thinEntries :
    topRowThinSparseRows.thinEntries = topRowThinEntries :=
  rfl

theorem topRowThinSparseRows_thickEntries :
    topRowThinSparseRows.thickEntries = ([] : List (Nat × Figure16.Thick)) :=
  rfl

theorem topRowThinSparseRows_blackEntries :
    topRowThinSparseRows.blackEntries = ([] : List (Nat × Figure16.Black)) :=
  rfl

theorem topRowThinSparseRows_lookup_zero :
    (CheckedSeparateLayerRows.ofSparse topRowThinSparseRows).thinAt
      ⟨0, by decide⟩ = some Figure16.Thin.a :=
  CheckedSeparateLayerRows.ofSparse_thinAt_of_mem
    topRowThinSparseRows (by decide)

theorem topRowThinSparseRows_lookup_one :
    (CheckedSeparateLayerRows.ofSparse topRowThinSparseRows).thinAt
      ⟨1, by decide⟩ = some Figure16.Thin.c :=
  CheckedSeparateLayerRows.ofSparse_thinAt_of_mem
    topRowThinSparseRows (by decide)

theorem topRowThinSparseRows_lookup_two :
    (CheckedSeparateLayerRows.ofSparse topRowThinSparseRows).thinAt
      ⟨2, by decide⟩ = some Figure16.Thin.d :=
  CheckedSeparateLayerRows.ofSparse_thinAt_of_mem
    topRowThinSparseRows (by decide)

theorem topRowThinSparseRows_lookup_three :
    (CheckedSeparateLayerRows.ofSparse topRowThinSparseRows).thinAt
      ⟨3, by decide⟩ = some Figure16.Thin.b :=
  CheckedSeparateLayerRows.ofSparse_thinAt_of_mem
    topRowThinSparseRows (by decide)

theorem topRowThinSparseRows_lookup_four :
    (CheckedSeparateLayerRows.ofSparse topRowThinSparseRows).thinAt
      ⟨4, by decide⟩ = some Figure16.Thin.a :=
  CheckedSeparateLayerRows.ofSparse_thinAt_of_mem
    topRowThinSparseRows (by decide)

theorem topRowThinSparseRows_lookup_five :
    (CheckedSeparateLayerRows.ofSparse topRowThinSparseRows).thinAt
      ⟨5, by decide⟩ = some Figure16.Thin.c :=
  CheckedSeparateLayerRows.ofSparse_thinAt_of_mem
    topRowThinSparseRows (by decide)

theorem topRowThinSparseRows_lookup_six :
    (CheckedSeparateLayerRows.ofSparse topRowThinSparseRows).thinAt
      ⟨6, by decide⟩ = some Figure16.Thin.d :=
  CheckedSeparateLayerRows.ofSparse_thinAt_of_mem
    topRowThinSparseRows (by decide)

theorem topRowThinSparseRows_lookup_seven :
    (CheckedSeparateLayerRows.ofSparse topRowThinSparseRows).thinAt
      ⟨7, by decide⟩ = some Figure16.Thin.b :=
  CheckedSeparateLayerRows.ofSparse_thinAt_of_mem
    topRowThinSparseRows (by decide)

end ConcreteData
end LayeredFigure18ScaffoldData
end Figure13Layers
end OllingerRobinson
end LeanWang
