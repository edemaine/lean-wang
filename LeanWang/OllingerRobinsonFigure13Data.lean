/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinsonFigure13Layers

/-!
Concrete audited data extracted from the indexed Figure 13 rendering.

The row order is the raw Figure 13 tile order from `fig13Tiles`, also shown in
[figures/figure13-indexed.png](../figures/figure13-indexed.png).  The layer
labels are the human transcription committed in
[figures/fig13-human.tsv](../figures/fig13-human.tsv), using the component
names from [figures/figure16-layer-components.png](../figures/figure16-layer-components.png).
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace LayeredFigure18ScaffoldData
namespace ConcreteData

/-- Human-audited thin-layer entries from `figures/fig13-human.tsv`. -/
def thinEntries : List (Nat × Figure16.Thin) := [
  (0, Figure16.Thin.a),
  (1, Figure16.Thin.a),
  (2, Figure16.Thin.a),
  (3, Figure16.Thin.a),
  (4, Figure16.Thin.b),
  (5, Figure16.Thin.b),
  (6, Figure16.Thin.b),
  (7, Figure16.Thin.b),
  (8, Figure16.Thin.c),
  (9, Figure16.Thin.c),
  (10, Figure16.Thin.c),
  (11, Figure16.Thin.c),
  (12, Figure16.Thin.c),
  (13, Figure16.Thin.c),
  (14, Figure16.Thin.c),
  (15, Figure16.Thin.c),
  (16, Figure16.Thin.c),
  (17, Figure16.Thin.c),
  (18, Figure16.Thin.c),
  (19, Figure16.Thin.c),
  (20, Figure16.Thin.c),
  (21, Figure16.Thin.c),
  (22, Figure16.Thin.c),
  (23, Figure16.Thin.c),
  (24, Figure16.Thin.c),
  (25, Figure16.Thin.c),
  (26, Figure16.Thin.c),
  (27, Figure16.Thin.c),
  (28, Figure16.Thin.c),
  (29, Figure16.Thin.c),
  (30, Figure16.Thin.c),
  (31, Figure16.Thin.c),
  (32, Figure16.Thin.a),
  (33, Figure16.Thin.a),
  (34, Figure16.Thin.a),
  (35, Figure16.Thin.a),
  (36, Figure16.Thin.a),
  (37, Figure16.Thin.a),
  (38, Figure16.Thin.a),
  (39, Figure16.Thin.a),
  (40, Figure16.Thin.a),
  (41, Figure16.Thin.a),
  (42, Figure16.Thin.a),
  (43, Figure16.Thin.a),
  (44, Figure16.Thin.a),
  (45, Figure16.Thin.a),
  (46, Figure16.Thin.a),
  (47, Figure16.Thin.a),
  (48, Figure16.Thin.a),
  (49, Figure16.Thin.a),
  (50, Figure16.Thin.a),
  (51, Figure16.Thin.a),
  (52, Figure16.Thin.a),
  (53, Figure16.Thin.a),
  (54, Figure16.Thin.a),
  (55, Figure16.Thin.a),
  (56, Figure16.Thin.d),
  (57, Figure16.Thin.d),
  (58, Figure16.Thin.d),
  (59, Figure16.Thin.d),
  (60, Figure16.Thin.d),
  (61, Figure16.Thin.d),
  (62, Figure16.Thin.d),
  (63, Figure16.Thin.d),
  (64, Figure16.Thin.d),
  (65, Figure16.Thin.d),
  (66, Figure16.Thin.d),
  (67, Figure16.Thin.d),
  (68, Figure16.Thin.d),
  (69, Figure16.Thin.d),
  (70, Figure16.Thin.d),
  (71, Figure16.Thin.d),
  (72, Figure16.Thin.d),
  (73, Figure16.Thin.d),
  (74, Figure16.Thin.d),
  (75, Figure16.Thin.d),
  (76, Figure16.Thin.d),
  (77, Figure16.Thin.d),
  (78, Figure16.Thin.d),
  (79, Figure16.Thin.d),
  (80, Figure16.Thin.a),
  (81, Figure16.Thin.a),
  (82, Figure16.Thin.a),
  (83, Figure16.Thin.a),
  (84, Figure16.Thin.a),
  (85, Figure16.Thin.a),
  (86, Figure16.Thin.a),
  (87, Figure16.Thin.a),
  (88, Figure16.Thin.a),
  (89, Figure16.Thin.a),
  (90, Figure16.Thin.a),
  (91, Figure16.Thin.a)
]

theorem thinEntries_length : thinEntries.length = 92 := by
  rfl

theorem thinEntries_valid : sparseEntriesValidBool thinEntries = true := by
  decide

theorem thinEntries_indices :
    thinEntries.map Prod.fst = List.range 92 := by
  decide

/-- Human-audited thick-layer entries from `figures/fig13-human.tsv`. -/
def thickEntries : List (Nat × Figure16.Thick) := [
  (0, Figure16.Thick.b),
  (1, Figure16.Thick.c),
  (2, Figure16.Thick.a),
  (3, Figure16.Thick.d),
  (4, Figure16.Thick.b),
  (5, Figure16.Thick.c),
  (6, Figure16.Thick.a),
  (7, Figure16.Thick.d),
  (8, Figure16.Thick.m),
  (9, Figure16.Thick.m),
  (10, Figure16.Thick.i),
  (11, Figure16.Thick.i),
  (12, Figure16.Thick.t),
  (13, Figure16.Thick.e),
  (14, Figure16.Thick.j),
  (15, Figure16.Thick.h),
  (16, Figure16.Thick.l),
  (17, Figure16.Thick.f),
  (18, Figure16.Thick.r),
  (19, Figure16.Thick.g),
  (20, Figure16.Thick.o),
  (21, Figure16.Thick.o),
  (22, Figure16.Thick.k),
  (23, Figure16.Thick.k),
  (24, Figure16.Thick.n),
  (25, Figure16.Thick.n),
  (26, Figure16.Thick.q),
  (27, Figure16.Thick.q),
  (28, Figure16.Thick.p),
  (29, Figure16.Thick.p),
  (30, Figure16.Thick.s),
  (31, Figure16.Thick.s),
  (32, Figure16.Thick.m),
  (33, Figure16.Thick.m),
  (34, Figure16.Thick.i),
  (35, Figure16.Thick.i),
  (36, Figure16.Thick.t),
  (37, Figure16.Thick.e),
  (38, Figure16.Thick.j),
  (39, Figure16.Thick.h),
  (40, Figure16.Thick.l),
  (41, Figure16.Thick.f),
  (42, Figure16.Thick.r),
  (43, Figure16.Thick.g),
  (44, Figure16.Thick.o),
  (45, Figure16.Thick.o),
  (46, Figure16.Thick.k),
  (47, Figure16.Thick.k),
  (48, Figure16.Thick.n),
  (49, Figure16.Thick.n),
  (50, Figure16.Thick.q),
  (51, Figure16.Thick.q),
  (52, Figure16.Thick.p),
  (53, Figure16.Thick.p),
  (54, Figure16.Thick.s),
  (55, Figure16.Thick.s),
  (56, Figure16.Thick.t),
  (57, Figure16.Thick.t),
  (58, Figure16.Thick.e),
  (59, Figure16.Thick.j),
  (60, Figure16.Thick.j),
  (61, Figure16.Thick.h),
  (62, Figure16.Thick.l),
  (63, Figure16.Thick.l),
  (64, Figure16.Thick.f),
  (65, Figure16.Thick.r),
  (66, Figure16.Thick.r),
  (67, Figure16.Thick.g),
  (68, Figure16.Thick.o),
  (69, Figure16.Thick.o),
  (70, Figure16.Thick.k),
  (71, Figure16.Thick.n),
  (72, Figure16.Thick.n),
  (73, Figure16.Thick.q),
  (74, Figure16.Thick.p),
  (75, Figure16.Thick.p),
  (76, Figure16.Thick.s),
  (77, Figure16.Thick.m),
  (78, Figure16.Thick.m),
  (79, Figure16.Thick.i),
  (80, Figure16.Thick.t),
  (81, Figure16.Thick.t),
  (82, Figure16.Thick.e),
  (83, Figure16.Thick.j),
  (84, Figure16.Thick.j),
  (85, Figure16.Thick.h),
  (86, Figure16.Thick.l),
  (87, Figure16.Thick.l),
  (88, Figure16.Thick.f),
  (89, Figure16.Thick.r),
  (90, Figure16.Thick.r),
  (91, Figure16.Thick.g)
]

theorem thickEntries_length : thickEntries.length = 92 := by
  rfl

theorem thickEntries_valid : sparseEntriesValidBool thickEntries = true := by
  decide

theorem thickEntries_indices :
    thickEntries.map Prod.fst = List.range 92 := by
  decide

/-- Human-audited black-layer entries from `figures/fig13-human.tsv`. -/
def blackEntries : List (Nat × Figure16.Black) := [
  (0, Figure16.Black.a),
  (1, Figure16.Black.a),
  (2, Figure16.Black.a),
  (3, Figure16.Black.a),
  (4, Figure16.Black.a),
  (5, Figure16.Black.a),
  (6, Figure16.Black.a),
  (7, Figure16.Black.a),
  (8, Figure16.Black.b),
  (9, Figure16.Black.c),
  (10, Figure16.Black.b),
  (11, Figure16.Black.c),
  (12, Figure16.Black.c),
  (13, Figure16.Black.c),
  (14, Figure16.Black.c),
  (15, Figure16.Black.c),
  (16, Figure16.Black.b),
  (17, Figure16.Black.b),
  (18, Figure16.Black.b),
  (19, Figure16.Black.b),
  (20, Figure16.Black.b),
  (21, Figure16.Black.c),
  (22, Figure16.Black.b),
  (23, Figure16.Black.c),
  (24, Figure16.Black.b),
  (25, Figure16.Black.c),
  (26, Figure16.Black.b),
  (27, Figure16.Black.c),
  (28, Figure16.Black.b),
  (29, Figure16.Black.c),
  (30, Figure16.Black.b),
  (31, Figure16.Black.c),
  (32, Figure16.Black.b),
  (33, Figure16.Black.c),
  (34, Figure16.Black.b),
  (35, Figure16.Black.c),
  (36, Figure16.Black.c),
  (37, Figure16.Black.c),
  (38, Figure16.Black.c),
  (39, Figure16.Black.c),
  (40, Figure16.Black.b),
  (41, Figure16.Black.b),
  (42, Figure16.Black.b),
  (43, Figure16.Black.b),
  (44, Figure16.Black.b),
  (45, Figure16.Black.c),
  (46, Figure16.Black.b),
  (47, Figure16.Black.c),
  (48, Figure16.Black.b),
  (49, Figure16.Black.c),
  (50, Figure16.Black.b),
  (51, Figure16.Black.c),
  (52, Figure16.Black.b),
  (53, Figure16.Black.c),
  (54, Figure16.Black.b),
  (55, Figure16.Black.c),
  (56, Figure16.Black.d),
  (57, Figure16.Black.e),
  (58, Figure16.Black.d),
  (59, Figure16.Black.d),
  (60, Figure16.Black.e),
  (61, Figure16.Black.e),
  (62, Figure16.Black.d),
  (63, Figure16.Black.e),
  (64, Figure16.Black.d),
  (65, Figure16.Black.d),
  (66, Figure16.Black.e),
  (67, Figure16.Black.e),
  (68, Figure16.Black.d),
  (69, Figure16.Black.e),
  (70, Figure16.Black.d),
  (71, Figure16.Black.d),
  (72, Figure16.Black.e),
  (73, Figure16.Black.e),
  (74, Figure16.Black.d),
  (75, Figure16.Black.e),
  (76, Figure16.Black.d),
  (77, Figure16.Black.d),
  (78, Figure16.Black.e),
  (79, Figure16.Black.e),
  (80, Figure16.Black.d),
  (81, Figure16.Black.e),
  (82, Figure16.Black.d),
  (83, Figure16.Black.d),
  (84, Figure16.Black.e),
  (85, Figure16.Black.e),
  (86, Figure16.Black.d),
  (87, Figure16.Black.e),
  (88, Figure16.Black.d),
  (89, Figure16.Black.d),
  (90, Figure16.Black.e),
  (91, Figure16.Black.e)
]

theorem blackEntries_length : blackEntries.length = 92 := by
  rfl

theorem blackEntries_valid : sparseEntriesValidBool blackEntries = true := by
  decide

theorem blackEntries_indices :
    blackEntries.map Prod.fst = List.range 92 := by
  decide

def checkedThinEntries : CheckedSparseEntries Figure16.Thin :=
  CheckedSparseEntries.ofEntries thinEntries thinEntries_valid

def checkedThickEntries : CheckedSparseEntries Figure16.Thick :=
  CheckedSparseEntries.ofEntries thickEntries thickEntries_valid

def checkedBlackEntries : CheckedSparseEntries Figure16.Black :=
  CheckedSparseEntries.ofEntries blackEntries blackEntries_valid

/-- Dense sparse-row view of the human Figure 13 layer transcription. -/
def sparseLayerRows : CheckedSparseSeparateLayerRows :=
  CheckedSparseSeparateLayerRows.ofCheckedEntries
    checkedThinEntries checkedThickEntries checkedBlackEntries

/-- The thin layer as a checked 92-entry option row. -/
def thinRows : List (Option Figure16.Thin) := [
  some Figure16.Thin.a,
  some Figure16.Thin.a,
  some Figure16.Thin.a,
  some Figure16.Thin.a,
  some Figure16.Thin.b,
  some Figure16.Thin.b,
  some Figure16.Thin.b,
  some Figure16.Thin.b,
  some Figure16.Thin.c,
  some Figure16.Thin.c,
  some Figure16.Thin.c,
  some Figure16.Thin.c,
  some Figure16.Thin.c,
  some Figure16.Thin.c,
  some Figure16.Thin.c,
  some Figure16.Thin.c,
  some Figure16.Thin.c,
  some Figure16.Thin.c,
  some Figure16.Thin.c,
  some Figure16.Thin.c,
  some Figure16.Thin.c,
  some Figure16.Thin.c,
  some Figure16.Thin.c,
  some Figure16.Thin.c,
  some Figure16.Thin.c,
  some Figure16.Thin.c,
  some Figure16.Thin.c,
  some Figure16.Thin.c,
  some Figure16.Thin.c,
  some Figure16.Thin.c,
  some Figure16.Thin.c,
  some Figure16.Thin.c,
  some Figure16.Thin.a,
  some Figure16.Thin.a,
  some Figure16.Thin.a,
  some Figure16.Thin.a,
  some Figure16.Thin.a,
  some Figure16.Thin.a,
  some Figure16.Thin.a,
  some Figure16.Thin.a,
  some Figure16.Thin.a,
  some Figure16.Thin.a,
  some Figure16.Thin.a,
  some Figure16.Thin.a,
  some Figure16.Thin.a,
  some Figure16.Thin.a,
  some Figure16.Thin.a,
  some Figure16.Thin.a,
  some Figure16.Thin.a,
  some Figure16.Thin.a,
  some Figure16.Thin.a,
  some Figure16.Thin.a,
  some Figure16.Thin.a,
  some Figure16.Thin.a,
  some Figure16.Thin.a,
  some Figure16.Thin.a,
  some Figure16.Thin.d,
  some Figure16.Thin.d,
  some Figure16.Thin.d,
  some Figure16.Thin.d,
  some Figure16.Thin.d,
  some Figure16.Thin.d,
  some Figure16.Thin.d,
  some Figure16.Thin.d,
  some Figure16.Thin.d,
  some Figure16.Thin.d,
  some Figure16.Thin.d,
  some Figure16.Thin.d,
  some Figure16.Thin.d,
  some Figure16.Thin.d,
  some Figure16.Thin.d,
  some Figure16.Thin.d,
  some Figure16.Thin.d,
  some Figure16.Thin.d,
  some Figure16.Thin.d,
  some Figure16.Thin.d,
  some Figure16.Thin.d,
  some Figure16.Thin.d,
  some Figure16.Thin.d,
  some Figure16.Thin.d,
  some Figure16.Thin.a,
  some Figure16.Thin.a,
  some Figure16.Thin.a,
  some Figure16.Thin.a,
  some Figure16.Thin.a,
  some Figure16.Thin.a,
  some Figure16.Thin.a,
  some Figure16.Thin.a,
  some Figure16.Thin.a,
  some Figure16.Thin.a,
  some Figure16.Thin.a,
  some Figure16.Thin.a
]

theorem thinRows_length : thinRows.length = 92 := by
  rfl

/-- The thick layer as a checked 92-entry option row. -/
def thickRows : List (Option Figure16.Thick) := [
  some Figure16.Thick.b,
  some Figure16.Thick.c,
  some Figure16.Thick.a,
  some Figure16.Thick.d,
  some Figure16.Thick.b,
  some Figure16.Thick.c,
  some Figure16.Thick.a,
  some Figure16.Thick.d,
  some Figure16.Thick.m,
  some Figure16.Thick.m,
  some Figure16.Thick.i,
  some Figure16.Thick.i,
  some Figure16.Thick.t,
  some Figure16.Thick.e,
  some Figure16.Thick.j,
  some Figure16.Thick.h,
  some Figure16.Thick.l,
  some Figure16.Thick.f,
  some Figure16.Thick.r,
  some Figure16.Thick.g,
  some Figure16.Thick.o,
  some Figure16.Thick.o,
  some Figure16.Thick.k,
  some Figure16.Thick.k,
  some Figure16.Thick.n,
  some Figure16.Thick.n,
  some Figure16.Thick.q,
  some Figure16.Thick.q,
  some Figure16.Thick.p,
  some Figure16.Thick.p,
  some Figure16.Thick.s,
  some Figure16.Thick.s,
  some Figure16.Thick.m,
  some Figure16.Thick.m,
  some Figure16.Thick.i,
  some Figure16.Thick.i,
  some Figure16.Thick.t,
  some Figure16.Thick.e,
  some Figure16.Thick.j,
  some Figure16.Thick.h,
  some Figure16.Thick.l,
  some Figure16.Thick.f,
  some Figure16.Thick.r,
  some Figure16.Thick.g,
  some Figure16.Thick.o,
  some Figure16.Thick.o,
  some Figure16.Thick.k,
  some Figure16.Thick.k,
  some Figure16.Thick.n,
  some Figure16.Thick.n,
  some Figure16.Thick.q,
  some Figure16.Thick.q,
  some Figure16.Thick.p,
  some Figure16.Thick.p,
  some Figure16.Thick.s,
  some Figure16.Thick.s,
  some Figure16.Thick.t,
  some Figure16.Thick.t,
  some Figure16.Thick.e,
  some Figure16.Thick.j,
  some Figure16.Thick.j,
  some Figure16.Thick.h,
  some Figure16.Thick.l,
  some Figure16.Thick.l,
  some Figure16.Thick.f,
  some Figure16.Thick.r,
  some Figure16.Thick.r,
  some Figure16.Thick.g,
  some Figure16.Thick.o,
  some Figure16.Thick.o,
  some Figure16.Thick.k,
  some Figure16.Thick.n,
  some Figure16.Thick.n,
  some Figure16.Thick.q,
  some Figure16.Thick.p,
  some Figure16.Thick.p,
  some Figure16.Thick.s,
  some Figure16.Thick.m,
  some Figure16.Thick.m,
  some Figure16.Thick.i,
  some Figure16.Thick.t,
  some Figure16.Thick.t,
  some Figure16.Thick.e,
  some Figure16.Thick.j,
  some Figure16.Thick.j,
  some Figure16.Thick.h,
  some Figure16.Thick.l,
  some Figure16.Thick.l,
  some Figure16.Thick.f,
  some Figure16.Thick.r,
  some Figure16.Thick.r,
  some Figure16.Thick.g
]

theorem thickRows_length : thickRows.length = 92 := by
  rfl

/-- The black layer as a checked 92-entry option row. -/
def blackRows : List (Option Figure16.Black) := [
  some Figure16.Black.a,
  some Figure16.Black.a,
  some Figure16.Black.a,
  some Figure16.Black.a,
  some Figure16.Black.a,
  some Figure16.Black.a,
  some Figure16.Black.a,
  some Figure16.Black.a,
  some Figure16.Black.b,
  some Figure16.Black.c,
  some Figure16.Black.b,
  some Figure16.Black.c,
  some Figure16.Black.c,
  some Figure16.Black.c,
  some Figure16.Black.c,
  some Figure16.Black.c,
  some Figure16.Black.b,
  some Figure16.Black.b,
  some Figure16.Black.b,
  some Figure16.Black.b,
  some Figure16.Black.b,
  some Figure16.Black.c,
  some Figure16.Black.b,
  some Figure16.Black.c,
  some Figure16.Black.b,
  some Figure16.Black.c,
  some Figure16.Black.b,
  some Figure16.Black.c,
  some Figure16.Black.b,
  some Figure16.Black.c,
  some Figure16.Black.b,
  some Figure16.Black.c,
  some Figure16.Black.b,
  some Figure16.Black.c,
  some Figure16.Black.b,
  some Figure16.Black.c,
  some Figure16.Black.c,
  some Figure16.Black.c,
  some Figure16.Black.c,
  some Figure16.Black.c,
  some Figure16.Black.b,
  some Figure16.Black.b,
  some Figure16.Black.b,
  some Figure16.Black.b,
  some Figure16.Black.b,
  some Figure16.Black.c,
  some Figure16.Black.b,
  some Figure16.Black.c,
  some Figure16.Black.b,
  some Figure16.Black.c,
  some Figure16.Black.b,
  some Figure16.Black.c,
  some Figure16.Black.b,
  some Figure16.Black.c,
  some Figure16.Black.b,
  some Figure16.Black.c,
  some Figure16.Black.d,
  some Figure16.Black.e,
  some Figure16.Black.d,
  some Figure16.Black.d,
  some Figure16.Black.e,
  some Figure16.Black.e,
  some Figure16.Black.d,
  some Figure16.Black.e,
  some Figure16.Black.d,
  some Figure16.Black.d,
  some Figure16.Black.e,
  some Figure16.Black.e,
  some Figure16.Black.d,
  some Figure16.Black.e,
  some Figure16.Black.d,
  some Figure16.Black.d,
  some Figure16.Black.e,
  some Figure16.Black.e,
  some Figure16.Black.d,
  some Figure16.Black.e,
  some Figure16.Black.d,
  some Figure16.Black.d,
  some Figure16.Black.e,
  some Figure16.Black.e,
  some Figure16.Black.d,
  some Figure16.Black.e,
  some Figure16.Black.d,
  some Figure16.Black.d,
  some Figure16.Black.e,
  some Figure16.Black.e,
  some Figure16.Black.d,
  some Figure16.Black.e,
  some Figure16.Black.d,
  some Figure16.Black.d,
  some Figure16.Black.e,
  some Figure16.Black.e
]

theorem blackRows_length : blackRows.length = 92 := by
  rfl

/-- Separate 92-entry layer rows from the human Figure 13 transcription. -/
def separateLayerRows : CheckedSeparateLayerRows where
  thins := thinRows
  thins_length := thinRows_length
  thicks := thickRows
  thicks_length := thickRows_length
  blacks := blackRows
  blacks_length := blackRows_length

/-- The Figure 13 layer decomposition as a 92-row component table. -/
def componentRows : List Components := [
  Components.ofAll Figure16.Thin.a Figure16.Thick.b Figure16.Black.a,
  Components.ofAll Figure16.Thin.a Figure16.Thick.c Figure16.Black.a,
  Components.ofAll Figure16.Thin.a Figure16.Thick.a Figure16.Black.a,
  Components.ofAll Figure16.Thin.a Figure16.Thick.d Figure16.Black.a,
  Components.ofAll Figure16.Thin.b Figure16.Thick.b Figure16.Black.a,
  Components.ofAll Figure16.Thin.b Figure16.Thick.c Figure16.Black.a,
  Components.ofAll Figure16.Thin.b Figure16.Thick.a Figure16.Black.a,
  Components.ofAll Figure16.Thin.b Figure16.Thick.d Figure16.Black.a,
  Components.ofAll Figure16.Thin.c Figure16.Thick.m Figure16.Black.b,
  Components.ofAll Figure16.Thin.c Figure16.Thick.m Figure16.Black.c,
  Components.ofAll Figure16.Thin.c Figure16.Thick.i Figure16.Black.b,
  Components.ofAll Figure16.Thin.c Figure16.Thick.i Figure16.Black.c,
  Components.ofAll Figure16.Thin.c Figure16.Thick.t Figure16.Black.c,
  Components.ofAll Figure16.Thin.c Figure16.Thick.e Figure16.Black.c,
  Components.ofAll Figure16.Thin.c Figure16.Thick.j Figure16.Black.c,
  Components.ofAll Figure16.Thin.c Figure16.Thick.h Figure16.Black.c,
  Components.ofAll Figure16.Thin.c Figure16.Thick.l Figure16.Black.b,
  Components.ofAll Figure16.Thin.c Figure16.Thick.f Figure16.Black.b,
  Components.ofAll Figure16.Thin.c Figure16.Thick.r Figure16.Black.b,
  Components.ofAll Figure16.Thin.c Figure16.Thick.g Figure16.Black.b,
  Components.ofAll Figure16.Thin.c Figure16.Thick.o Figure16.Black.b,
  Components.ofAll Figure16.Thin.c Figure16.Thick.o Figure16.Black.c,
  Components.ofAll Figure16.Thin.c Figure16.Thick.k Figure16.Black.b,
  Components.ofAll Figure16.Thin.c Figure16.Thick.k Figure16.Black.c,
  Components.ofAll Figure16.Thin.c Figure16.Thick.n Figure16.Black.b,
  Components.ofAll Figure16.Thin.c Figure16.Thick.n Figure16.Black.c,
  Components.ofAll Figure16.Thin.c Figure16.Thick.q Figure16.Black.b,
  Components.ofAll Figure16.Thin.c Figure16.Thick.q Figure16.Black.c,
  Components.ofAll Figure16.Thin.c Figure16.Thick.p Figure16.Black.b,
  Components.ofAll Figure16.Thin.c Figure16.Thick.p Figure16.Black.c,
  Components.ofAll Figure16.Thin.c Figure16.Thick.s Figure16.Black.b,
  Components.ofAll Figure16.Thin.c Figure16.Thick.s Figure16.Black.c,
  Components.ofAll Figure16.Thin.a Figure16.Thick.m Figure16.Black.b,
  Components.ofAll Figure16.Thin.a Figure16.Thick.m Figure16.Black.c,
  Components.ofAll Figure16.Thin.a Figure16.Thick.i Figure16.Black.b,
  Components.ofAll Figure16.Thin.a Figure16.Thick.i Figure16.Black.c,
  Components.ofAll Figure16.Thin.a Figure16.Thick.t Figure16.Black.c,
  Components.ofAll Figure16.Thin.a Figure16.Thick.e Figure16.Black.c,
  Components.ofAll Figure16.Thin.a Figure16.Thick.j Figure16.Black.c,
  Components.ofAll Figure16.Thin.a Figure16.Thick.h Figure16.Black.c,
  Components.ofAll Figure16.Thin.a Figure16.Thick.l Figure16.Black.b,
  Components.ofAll Figure16.Thin.a Figure16.Thick.f Figure16.Black.b,
  Components.ofAll Figure16.Thin.a Figure16.Thick.r Figure16.Black.b,
  Components.ofAll Figure16.Thin.a Figure16.Thick.g Figure16.Black.b,
  Components.ofAll Figure16.Thin.a Figure16.Thick.o Figure16.Black.b,
  Components.ofAll Figure16.Thin.a Figure16.Thick.o Figure16.Black.c,
  Components.ofAll Figure16.Thin.a Figure16.Thick.k Figure16.Black.b,
  Components.ofAll Figure16.Thin.a Figure16.Thick.k Figure16.Black.c,
  Components.ofAll Figure16.Thin.a Figure16.Thick.n Figure16.Black.b,
  Components.ofAll Figure16.Thin.a Figure16.Thick.n Figure16.Black.c,
  Components.ofAll Figure16.Thin.a Figure16.Thick.q Figure16.Black.b,
  Components.ofAll Figure16.Thin.a Figure16.Thick.q Figure16.Black.c,
  Components.ofAll Figure16.Thin.a Figure16.Thick.p Figure16.Black.b,
  Components.ofAll Figure16.Thin.a Figure16.Thick.p Figure16.Black.c,
  Components.ofAll Figure16.Thin.a Figure16.Thick.s Figure16.Black.b,
  Components.ofAll Figure16.Thin.a Figure16.Thick.s Figure16.Black.c,
  Components.ofAll Figure16.Thin.d Figure16.Thick.t Figure16.Black.d,
  Components.ofAll Figure16.Thin.d Figure16.Thick.t Figure16.Black.e,
  Components.ofAll Figure16.Thin.d Figure16.Thick.e Figure16.Black.d,
  Components.ofAll Figure16.Thin.d Figure16.Thick.j Figure16.Black.d,
  Components.ofAll Figure16.Thin.d Figure16.Thick.j Figure16.Black.e,
  Components.ofAll Figure16.Thin.d Figure16.Thick.h Figure16.Black.e,
  Components.ofAll Figure16.Thin.d Figure16.Thick.l Figure16.Black.d,
  Components.ofAll Figure16.Thin.d Figure16.Thick.l Figure16.Black.e,
  Components.ofAll Figure16.Thin.d Figure16.Thick.f Figure16.Black.d,
  Components.ofAll Figure16.Thin.d Figure16.Thick.r Figure16.Black.d,
  Components.ofAll Figure16.Thin.d Figure16.Thick.r Figure16.Black.e,
  Components.ofAll Figure16.Thin.d Figure16.Thick.g Figure16.Black.e,
  Components.ofAll Figure16.Thin.d Figure16.Thick.o Figure16.Black.d,
  Components.ofAll Figure16.Thin.d Figure16.Thick.o Figure16.Black.e,
  Components.ofAll Figure16.Thin.d Figure16.Thick.k Figure16.Black.d,
  Components.ofAll Figure16.Thin.d Figure16.Thick.n Figure16.Black.d,
  Components.ofAll Figure16.Thin.d Figure16.Thick.n Figure16.Black.e,
  Components.ofAll Figure16.Thin.d Figure16.Thick.q Figure16.Black.e,
  Components.ofAll Figure16.Thin.d Figure16.Thick.p Figure16.Black.d,
  Components.ofAll Figure16.Thin.d Figure16.Thick.p Figure16.Black.e,
  Components.ofAll Figure16.Thin.d Figure16.Thick.s Figure16.Black.d,
  Components.ofAll Figure16.Thin.d Figure16.Thick.m Figure16.Black.d,
  Components.ofAll Figure16.Thin.d Figure16.Thick.m Figure16.Black.e,
  Components.ofAll Figure16.Thin.d Figure16.Thick.i Figure16.Black.e,
  Components.ofAll Figure16.Thin.a Figure16.Thick.t Figure16.Black.d,
  Components.ofAll Figure16.Thin.a Figure16.Thick.t Figure16.Black.e,
  Components.ofAll Figure16.Thin.a Figure16.Thick.e Figure16.Black.d,
  Components.ofAll Figure16.Thin.a Figure16.Thick.j Figure16.Black.d,
  Components.ofAll Figure16.Thin.a Figure16.Thick.j Figure16.Black.e,
  Components.ofAll Figure16.Thin.a Figure16.Thick.h Figure16.Black.e,
  Components.ofAll Figure16.Thin.a Figure16.Thick.l Figure16.Black.d,
  Components.ofAll Figure16.Thin.a Figure16.Thick.l Figure16.Black.e,
  Components.ofAll Figure16.Thin.a Figure16.Thick.f Figure16.Black.d,
  Components.ofAll Figure16.Thin.a Figure16.Thick.r Figure16.Black.d,
  Components.ofAll Figure16.Thin.a Figure16.Thick.r Figure16.Black.e,
  Components.ofAll Figure16.Thin.a Figure16.Thick.g Figure16.Black.e
]

theorem componentRows_length : componentRows.length = 92 := by
  rfl

/-- Concrete Figure 13 layer transcription, indexed like `fig13Tiles`. -/
def layerData : Transcription where
  rows := componentRows
  length_eq := componentRows_length

theorem layerData_rows : layerData.rows = componentRows :=
  rfl

theorem separateLayerRows_layerData_rows :
    separateLayerRows.layerData.rows = componentRows := by
  decide

theorem sparseLayerRows_layerData_rows :
    sparseLayerRows.layerData.rows = componentRows := by
  decide

/-- The concrete transcription keeps the raw Figure 13 tile at each index. -/
theorem layerData_layeredTileAt_rawTile (index : Fin 92) :
    (layerData.layeredTileAt index).rawTile = fig13Tile index :=
  layerData.layeredTileAt_rawTile index

theorem layerData_componentsAt_0 :
    layerData.componentsAt ⟨0, by decide⟩ =
      Components.ofAll Figure16.Thin.a Figure16.Thick.b Figure16.Black.a := by
  decide

theorem layerData_componentsAt_1 :
    layerData.componentsAt ⟨1, by decide⟩ =
      Components.ofAll Figure16.Thin.a Figure16.Thick.c Figure16.Black.a := by
  decide

theorem layerData_componentsAt_2 :
    layerData.componentsAt ⟨2, by decide⟩ =
      Components.ofAll Figure16.Thin.a Figure16.Thick.a Figure16.Black.a := by
  decide

theorem layerData_componentsAt_3 :
    layerData.componentsAt ⟨3, by decide⟩ =
      Components.ofAll Figure16.Thin.a Figure16.Thick.d Figure16.Black.a := by
  decide

theorem layerData_componentsAt_4 :
    layerData.componentsAt ⟨4, by decide⟩ =
      Components.ofAll Figure16.Thin.b Figure16.Thick.b Figure16.Black.a := by
  decide

theorem layerData_componentsAt_5 :
    layerData.componentsAt ⟨5, by decide⟩ =
      Components.ofAll Figure16.Thin.b Figure16.Thick.c Figure16.Black.a := by
  decide

theorem layerData_componentsAt_6 :
    layerData.componentsAt ⟨6, by decide⟩ =
      Components.ofAll Figure16.Thin.b Figure16.Thick.a Figure16.Black.a := by
  decide

theorem layerData_componentsAt_7 :
    layerData.componentsAt ⟨7, by decide⟩ =
      Components.ofAll Figure16.Thin.b Figure16.Thick.d Figure16.Black.a := by
  decide

theorem layerData_componentsAt_8 :
    layerData.componentsAt ⟨8, by decide⟩ =
      Components.ofAll Figure16.Thin.c Figure16.Thick.m Figure16.Black.b := by
  decide

theorem layerData_componentsAt_9 :
    layerData.componentsAt ⟨9, by decide⟩ =
      Components.ofAll Figure16.Thin.c Figure16.Thick.m Figure16.Black.c := by
  decide

theorem layerData_componentsAt_10 :
    layerData.componentsAt ⟨10, by decide⟩ =
      Components.ofAll Figure16.Thin.c Figure16.Thick.i Figure16.Black.b := by
  decide

theorem layerData_componentsAt_11 :
    layerData.componentsAt ⟨11, by decide⟩ =
      Components.ofAll Figure16.Thin.c Figure16.Thick.i Figure16.Black.c := by
  decide

theorem layerData_componentsAt_12 :
    layerData.componentsAt ⟨12, by decide⟩ =
      Components.ofAll Figure16.Thin.c Figure16.Thick.t Figure16.Black.c := by
  decide

theorem layerData_componentsAt_13 :
    layerData.componentsAt ⟨13, by decide⟩ =
      Components.ofAll Figure16.Thin.c Figure16.Thick.e Figure16.Black.c := by
  decide

theorem layerData_componentsAt_14 :
    layerData.componentsAt ⟨14, by decide⟩ =
      Components.ofAll Figure16.Thin.c Figure16.Thick.j Figure16.Black.c := by
  decide

theorem layerData_componentsAt_15 :
    layerData.componentsAt ⟨15, by decide⟩ =
      Components.ofAll Figure16.Thin.c Figure16.Thick.h Figure16.Black.c := by
  decide

theorem layerData_componentsAt_16 :
    layerData.componentsAt ⟨16, by decide⟩ =
      Components.ofAll Figure16.Thin.c Figure16.Thick.l Figure16.Black.b := by
  decide

theorem layerData_componentsAt_17 :
    layerData.componentsAt ⟨17, by decide⟩ =
      Components.ofAll Figure16.Thin.c Figure16.Thick.f Figure16.Black.b := by
  decide

theorem layerData_componentsAt_18 :
    layerData.componentsAt ⟨18, by decide⟩ =
      Components.ofAll Figure16.Thin.c Figure16.Thick.r Figure16.Black.b := by
  decide

theorem layerData_componentsAt_19 :
    layerData.componentsAt ⟨19, by decide⟩ =
      Components.ofAll Figure16.Thin.c Figure16.Thick.g Figure16.Black.b := by
  decide

theorem layerData_componentsAt_20 :
    layerData.componentsAt ⟨20, by decide⟩ =
      Components.ofAll Figure16.Thin.c Figure16.Thick.o Figure16.Black.b := by
  decide

theorem layerData_componentsAt_21 :
    layerData.componentsAt ⟨21, by decide⟩ =
      Components.ofAll Figure16.Thin.c Figure16.Thick.o Figure16.Black.c := by
  decide

theorem layerData_componentsAt_22 :
    layerData.componentsAt ⟨22, by decide⟩ =
      Components.ofAll Figure16.Thin.c Figure16.Thick.k Figure16.Black.b := by
  decide

theorem layerData_componentsAt_23 :
    layerData.componentsAt ⟨23, by decide⟩ =
      Components.ofAll Figure16.Thin.c Figure16.Thick.k Figure16.Black.c := by
  decide

theorem layerData_componentsAt_24 :
    layerData.componentsAt ⟨24, by decide⟩ =
      Components.ofAll Figure16.Thin.c Figure16.Thick.n Figure16.Black.b := by
  decide

theorem layerData_componentsAt_25 :
    layerData.componentsAt ⟨25, by decide⟩ =
      Components.ofAll Figure16.Thin.c Figure16.Thick.n Figure16.Black.c := by
  decide

theorem layerData_componentsAt_26 :
    layerData.componentsAt ⟨26, by decide⟩ =
      Components.ofAll Figure16.Thin.c Figure16.Thick.q Figure16.Black.b := by
  decide

theorem layerData_componentsAt_27 :
    layerData.componentsAt ⟨27, by decide⟩ =
      Components.ofAll Figure16.Thin.c Figure16.Thick.q Figure16.Black.c := by
  decide

theorem layerData_componentsAt_28 :
    layerData.componentsAt ⟨28, by decide⟩ =
      Components.ofAll Figure16.Thin.c Figure16.Thick.p Figure16.Black.b := by
  decide

theorem layerData_componentsAt_29 :
    layerData.componentsAt ⟨29, by decide⟩ =
      Components.ofAll Figure16.Thin.c Figure16.Thick.p Figure16.Black.c := by
  decide

theorem layerData_componentsAt_30 :
    layerData.componentsAt ⟨30, by decide⟩ =
      Components.ofAll Figure16.Thin.c Figure16.Thick.s Figure16.Black.b := by
  decide

theorem layerData_componentsAt_31 :
    layerData.componentsAt ⟨31, by decide⟩ =
      Components.ofAll Figure16.Thin.c Figure16.Thick.s Figure16.Black.c := by
  decide

theorem layerData_componentsAt_32 :
    layerData.componentsAt ⟨32, by decide⟩ =
      Components.ofAll Figure16.Thin.a Figure16.Thick.m Figure16.Black.b := by
  decide

theorem layerData_componentsAt_33 :
    layerData.componentsAt ⟨33, by decide⟩ =
      Components.ofAll Figure16.Thin.a Figure16.Thick.m Figure16.Black.c := by
  decide

theorem layerData_componentsAt_34 :
    layerData.componentsAt ⟨34, by decide⟩ =
      Components.ofAll Figure16.Thin.a Figure16.Thick.i Figure16.Black.b := by
  decide

theorem layerData_componentsAt_35 :
    layerData.componentsAt ⟨35, by decide⟩ =
      Components.ofAll Figure16.Thin.a Figure16.Thick.i Figure16.Black.c := by
  decide

theorem layerData_componentsAt_36 :
    layerData.componentsAt ⟨36, by decide⟩ =
      Components.ofAll Figure16.Thin.a Figure16.Thick.t Figure16.Black.c := by
  decide

theorem layerData_componentsAt_37 :
    layerData.componentsAt ⟨37, by decide⟩ =
      Components.ofAll Figure16.Thin.a Figure16.Thick.e Figure16.Black.c := by
  decide

theorem layerData_componentsAt_38 :
    layerData.componentsAt ⟨38, by decide⟩ =
      Components.ofAll Figure16.Thin.a Figure16.Thick.j Figure16.Black.c := by
  decide

theorem layerData_componentsAt_39 :
    layerData.componentsAt ⟨39, by decide⟩ =
      Components.ofAll Figure16.Thin.a Figure16.Thick.h Figure16.Black.c := by
  decide

theorem layerData_componentsAt_40 :
    layerData.componentsAt ⟨40, by decide⟩ =
      Components.ofAll Figure16.Thin.a Figure16.Thick.l Figure16.Black.b := by
  decide

theorem layerData_componentsAt_41 :
    layerData.componentsAt ⟨41, by decide⟩ =
      Components.ofAll Figure16.Thin.a Figure16.Thick.f Figure16.Black.b := by
  decide

theorem layerData_componentsAt_42 :
    layerData.componentsAt ⟨42, by decide⟩ =
      Components.ofAll Figure16.Thin.a Figure16.Thick.r Figure16.Black.b := by
  decide

theorem layerData_componentsAt_43 :
    layerData.componentsAt ⟨43, by decide⟩ =
      Components.ofAll Figure16.Thin.a Figure16.Thick.g Figure16.Black.b := by
  decide

theorem layerData_componentsAt_44 :
    layerData.componentsAt ⟨44, by decide⟩ =
      Components.ofAll Figure16.Thin.a Figure16.Thick.o Figure16.Black.b := by
  decide

theorem layerData_componentsAt_45 :
    layerData.componentsAt ⟨45, by decide⟩ =
      Components.ofAll Figure16.Thin.a Figure16.Thick.o Figure16.Black.c := by
  decide

theorem layerData_componentsAt_46 :
    layerData.componentsAt ⟨46, by decide⟩ =
      Components.ofAll Figure16.Thin.a Figure16.Thick.k Figure16.Black.b := by
  decide

theorem layerData_componentsAt_47 :
    layerData.componentsAt ⟨47, by decide⟩ =
      Components.ofAll Figure16.Thin.a Figure16.Thick.k Figure16.Black.c := by
  decide

theorem layerData_componentsAt_48 :
    layerData.componentsAt ⟨48, by decide⟩ =
      Components.ofAll Figure16.Thin.a Figure16.Thick.n Figure16.Black.b := by
  decide

theorem layerData_componentsAt_49 :
    layerData.componentsAt ⟨49, by decide⟩ =
      Components.ofAll Figure16.Thin.a Figure16.Thick.n Figure16.Black.c := by
  decide

theorem layerData_componentsAt_50 :
    layerData.componentsAt ⟨50, by decide⟩ =
      Components.ofAll Figure16.Thin.a Figure16.Thick.q Figure16.Black.b := by
  decide

theorem layerData_componentsAt_51 :
    layerData.componentsAt ⟨51, by decide⟩ =
      Components.ofAll Figure16.Thin.a Figure16.Thick.q Figure16.Black.c := by
  decide

theorem layerData_componentsAt_52 :
    layerData.componentsAt ⟨52, by decide⟩ =
      Components.ofAll Figure16.Thin.a Figure16.Thick.p Figure16.Black.b := by
  decide

theorem layerData_componentsAt_53 :
    layerData.componentsAt ⟨53, by decide⟩ =
      Components.ofAll Figure16.Thin.a Figure16.Thick.p Figure16.Black.c := by
  decide

theorem layerData_componentsAt_54 :
    layerData.componentsAt ⟨54, by decide⟩ =
      Components.ofAll Figure16.Thin.a Figure16.Thick.s Figure16.Black.b := by
  decide

theorem layerData_componentsAt_55 :
    layerData.componentsAt ⟨55, by decide⟩ =
      Components.ofAll Figure16.Thin.a Figure16.Thick.s Figure16.Black.c := by
  decide

theorem layerData_componentsAt_56 :
    layerData.componentsAt ⟨56, by decide⟩ =
      Components.ofAll Figure16.Thin.d Figure16.Thick.t Figure16.Black.d := by
  decide

theorem layerData_componentsAt_57 :
    layerData.componentsAt ⟨57, by decide⟩ =
      Components.ofAll Figure16.Thin.d Figure16.Thick.t Figure16.Black.e := by
  decide

theorem layerData_componentsAt_58 :
    layerData.componentsAt ⟨58, by decide⟩ =
      Components.ofAll Figure16.Thin.d Figure16.Thick.e Figure16.Black.d := by
  decide

theorem layerData_componentsAt_59 :
    layerData.componentsAt ⟨59, by decide⟩ =
      Components.ofAll Figure16.Thin.d Figure16.Thick.j Figure16.Black.d := by
  decide

theorem layerData_componentsAt_60 :
    layerData.componentsAt ⟨60, by decide⟩ =
      Components.ofAll Figure16.Thin.d Figure16.Thick.j Figure16.Black.e := by
  decide

theorem layerData_componentsAt_61 :
    layerData.componentsAt ⟨61, by decide⟩ =
      Components.ofAll Figure16.Thin.d Figure16.Thick.h Figure16.Black.e := by
  decide

theorem layerData_componentsAt_62 :
    layerData.componentsAt ⟨62, by decide⟩ =
      Components.ofAll Figure16.Thin.d Figure16.Thick.l Figure16.Black.d := by
  decide

theorem layerData_componentsAt_63 :
    layerData.componentsAt ⟨63, by decide⟩ =
      Components.ofAll Figure16.Thin.d Figure16.Thick.l Figure16.Black.e := by
  decide

theorem layerData_componentsAt_64 :
    layerData.componentsAt ⟨64, by decide⟩ =
      Components.ofAll Figure16.Thin.d Figure16.Thick.f Figure16.Black.d := by
  decide

theorem layerData_componentsAt_65 :
    layerData.componentsAt ⟨65, by decide⟩ =
      Components.ofAll Figure16.Thin.d Figure16.Thick.r Figure16.Black.d := by
  decide

theorem layerData_componentsAt_66 :
    layerData.componentsAt ⟨66, by decide⟩ =
      Components.ofAll Figure16.Thin.d Figure16.Thick.r Figure16.Black.e := by
  decide

theorem layerData_componentsAt_67 :
    layerData.componentsAt ⟨67, by decide⟩ =
      Components.ofAll Figure16.Thin.d Figure16.Thick.g Figure16.Black.e := by
  decide

theorem layerData_componentsAt_68 :
    layerData.componentsAt ⟨68, by decide⟩ =
      Components.ofAll Figure16.Thin.d Figure16.Thick.o Figure16.Black.d := by
  decide

theorem layerData_componentsAt_69 :
    layerData.componentsAt ⟨69, by decide⟩ =
      Components.ofAll Figure16.Thin.d Figure16.Thick.o Figure16.Black.e := by
  decide

theorem layerData_componentsAt_70 :
    layerData.componentsAt ⟨70, by decide⟩ =
      Components.ofAll Figure16.Thin.d Figure16.Thick.k Figure16.Black.d := by
  decide

theorem layerData_componentsAt_71 :
    layerData.componentsAt ⟨71, by decide⟩ =
      Components.ofAll Figure16.Thin.d Figure16.Thick.n Figure16.Black.d := by
  decide

theorem layerData_componentsAt_72 :
    layerData.componentsAt ⟨72, by decide⟩ =
      Components.ofAll Figure16.Thin.d Figure16.Thick.n Figure16.Black.e := by
  decide

theorem layerData_componentsAt_73 :
    layerData.componentsAt ⟨73, by decide⟩ =
      Components.ofAll Figure16.Thin.d Figure16.Thick.q Figure16.Black.e := by
  decide

theorem layerData_componentsAt_74 :
    layerData.componentsAt ⟨74, by decide⟩ =
      Components.ofAll Figure16.Thin.d Figure16.Thick.p Figure16.Black.d := by
  decide

theorem layerData_componentsAt_75 :
    layerData.componentsAt ⟨75, by decide⟩ =
      Components.ofAll Figure16.Thin.d Figure16.Thick.p Figure16.Black.e := by
  decide

theorem layerData_componentsAt_76 :
    layerData.componentsAt ⟨76, by decide⟩ =
      Components.ofAll Figure16.Thin.d Figure16.Thick.s Figure16.Black.d := by
  decide

theorem layerData_componentsAt_77 :
    layerData.componentsAt ⟨77, by decide⟩ =
      Components.ofAll Figure16.Thin.d Figure16.Thick.m Figure16.Black.d := by
  decide

theorem layerData_componentsAt_78 :
    layerData.componentsAt ⟨78, by decide⟩ =
      Components.ofAll Figure16.Thin.d Figure16.Thick.m Figure16.Black.e := by
  decide

theorem layerData_componentsAt_79 :
    layerData.componentsAt ⟨79, by decide⟩ =
      Components.ofAll Figure16.Thin.d Figure16.Thick.i Figure16.Black.e := by
  decide

theorem layerData_componentsAt_80 :
    layerData.componentsAt ⟨80, by decide⟩ =
      Components.ofAll Figure16.Thin.a Figure16.Thick.t Figure16.Black.d := by
  decide

theorem layerData_componentsAt_81 :
    layerData.componentsAt ⟨81, by decide⟩ =
      Components.ofAll Figure16.Thin.a Figure16.Thick.t Figure16.Black.e := by
  decide

theorem layerData_componentsAt_82 :
    layerData.componentsAt ⟨82, by decide⟩ =
      Components.ofAll Figure16.Thin.a Figure16.Thick.e Figure16.Black.d := by
  decide

theorem layerData_componentsAt_83 :
    layerData.componentsAt ⟨83, by decide⟩ =
      Components.ofAll Figure16.Thin.a Figure16.Thick.j Figure16.Black.d := by
  decide

theorem layerData_componentsAt_84 :
    layerData.componentsAt ⟨84, by decide⟩ =
      Components.ofAll Figure16.Thin.a Figure16.Thick.j Figure16.Black.e := by
  decide

theorem layerData_componentsAt_85 :
    layerData.componentsAt ⟨85, by decide⟩ =
      Components.ofAll Figure16.Thin.a Figure16.Thick.h Figure16.Black.e := by
  decide

theorem layerData_componentsAt_86 :
    layerData.componentsAt ⟨86, by decide⟩ =
      Components.ofAll Figure16.Thin.a Figure16.Thick.l Figure16.Black.d := by
  decide

theorem layerData_componentsAt_87 :
    layerData.componentsAt ⟨87, by decide⟩ =
      Components.ofAll Figure16.Thin.a Figure16.Thick.l Figure16.Black.e := by
  decide

theorem layerData_componentsAt_88 :
    layerData.componentsAt ⟨88, by decide⟩ =
      Components.ofAll Figure16.Thin.a Figure16.Thick.f Figure16.Black.d := by
  decide

theorem layerData_componentsAt_89 :
    layerData.componentsAt ⟨89, by decide⟩ =
      Components.ofAll Figure16.Thin.a Figure16.Thick.r Figure16.Black.d := by
  decide

theorem layerData_componentsAt_90 :
    layerData.componentsAt ⟨90, by decide⟩ =
      Components.ofAll Figure16.Thin.a Figure16.Thick.r Figure16.Black.e := by
  decide

theorem layerData_componentsAt_91 :
    layerData.componentsAt ⟨91, by decide⟩ =
      Components.ofAll Figure16.Thin.a Figure16.Thick.g Figure16.Black.e := by
  decide

def thinComponentAt (index : Fin 92) : Figure16.Thin :=
  (thinEntries.get ⟨index.val, by simp [thinEntries_length, index.isLt]⟩).2

def thickComponentAt (index : Fin 92) : Figure16.Thick :=
  (thickEntries.get ⟨index.val, by simp [thickEntries_length, index.isLt]⟩).2

def blackComponentAt (index : Fin 92) : Figure16.Black :=
  (blackEntries.get ⟨index.val, by simp [blackEntries_length, index.isLt]⟩).2

theorem sparseLayerRows_thinAt (index : Fin 92) :
    sparseLayerRows.separateLayerRows.thinAt index =
      some (thinComponentAt index) := by
  decide +revert

theorem sparseLayerRows_thickAt (index : Fin 92) :
    sparseLayerRows.separateLayerRows.thickAt index =
      some (thickComponentAt index) := by
  decide +revert

theorem sparseLayerRows_blackAt (index : Fin 92) :
    sparseLayerRows.separateLayerRows.blackAt index =
      some (blackComponentAt index) := by
  decide +revert

def checkedLayerStackRectangleOfSiteRectangle {w h : Nat}
    (R : SiteRectangle w h) : CheckedLayerStackRectangle w h where
  sites := R.toCheckedNatSiteRectangle
  thin := CheckedLayerComponentRectangle.ofRect fun i j =>
    thinComponentAt (R i j).index
  thick := CheckedLayerComponentRectangle.ofRect fun i j =>
    thickComponentAt (R i j).index
  black := CheckedLayerComponentRectangle.ofRect fun i j =>
    blackComponentAt (R i j).index

theorem checkedLayerStackRectangleOfSiteRectangle_matchesSite {w h : Nat}
    (R : SiteRectangle w h) :
    (checkedLayerStackRectangleOfSiteRectangle R).sites.matchesSiteRectangleBool
      R = true :=
  R.toCheckedNatSiteRectangle_matchesSiteRectangleBool

theorem checkedLayerStackRectangleOfSiteRectangle_site_index {w h : Nat}
    (R : SiteRectangle w h) (i : Fin w) (j : Fin h) :
    ((checkedLayerStackRectangleOfSiteRectangle R).sites.toSiteRectangle i j).index =
      (R i j).index := by
  apply Fin.ext
  change (R.toCheckedNatSiteRectangle.specAt i j).1 = (R i j).index.val
  rw [SiteRectangle.toCheckedNatSiteRectangle_specAt]

theorem checkedLayerStackRectangleOfSiteRectangle_thin_componentAt
    {w h : Nat} (R : SiteRectangle w h) (i : Fin w) (j : Fin h) :
    (checkedLayerStackRectangleOfSiteRectangle R).thin.componentAt i j =
      thinComponentAt (R i j).index :=
  CheckedLayerComponentRectangle.ofRect_componentAt _ i j

theorem checkedLayerStackRectangleOfSiteRectangle_thick_componentAt
    {w h : Nat} (R : SiteRectangle w h) (i : Fin w) (j : Fin h) :
    (checkedLayerStackRectangleOfSiteRectangle R).thick.componentAt i j =
      thickComponentAt (R i j).index :=
  CheckedLayerComponentRectangle.ofRect_componentAt _ i j

theorem checkedLayerStackRectangleOfSiteRectangle_black_componentAt
    {w h : Nat} (R : SiteRectangle w h) (i : Fin w) (j : Fin h) :
    (checkedLayerStackRectangleOfSiteRectangle R).black.componentAt i j =
      blackComponentAt (R i j).index :=
  CheckedLayerComponentRectangle.ofRect_componentAt _ i j

theorem sparseLayerRows_layerStackRectangleMatchesBool {w h : Nat}
    (R : SiteRectangle w h) :
    sparseLayerRows.layerStackRectangleMatchesBool
      (checkedLayerStackRectangleOfSiteRectangle R) = true := by
  unfold CheckedSparseSeparateLayerRows.layerStackRectangleMatchesBool
  unfold CheckedSeparateLayerRows.layerStackRectangleMatchesBool
  rw [Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · unfold CheckedSeparateLayerRows.componentRectangleMatchesBool
    apply List.all_eq_true.2
    intro i _hi
    apply List.all_eq_true.2
    intro j _hj
    apply decide_eq_true
    rw [checkedLayerStackRectangleOfSiteRectangle_site_index,
      checkedLayerStackRectangleOfSiteRectangle_thin_componentAt]
    exact sparseLayerRows_thinAt (R i j).index
  · unfold CheckedSeparateLayerRows.componentRectangleMatchesBool
    apply List.all_eq_true.2
    intro i _hi
    apply List.all_eq_true.2
    intro j _hj
    apply decide_eq_true
    rw [checkedLayerStackRectangleOfSiteRectangle_site_index,
      checkedLayerStackRectangleOfSiteRectangle_thick_componentAt]
    exact sparseLayerRows_thickAt (R i j).index
  · unfold CheckedSeparateLayerRows.componentRectangleMatchesBool
    apply List.all_eq_true.2
    intro i _hi
    apply List.all_eq_true.2
    intro j _hj
    apply decide_eq_true
    rw [checkedLayerStackRectangleOfSiteRectangle_site_index,
      checkedLayerStackRectangleOfSiteRectangle_black_componentAt]
    exact sparseLayerRows_blackAt (R i j).index

/--
Dense raw-data adapter for the concrete Figure 13 layer transcription.

The active Figure 18 sites and distinguished corner are still supplied
separately; this definition fixes the 92-row layer table to the human-audited
Figure 13 data above.
-/
def rawDataOfSites
    (activeSiteData : Figure18Site.CheckedNatSpecs)
    (cornerSite : Figure18Site) : CheckedRawData :=
  CheckedRawData.ofCheckedSites componentRows componentRows_length
    activeSiteData cornerSite

theorem rawDataOfSites_layerData
    (activeSiteData : Figure18Site.CheckedNatSpecs)
    (cornerSite : Figure18Site) :
    (rawDataOfSites activeSiteData cornerSite).layerData = layerData :=
  rfl

theorem rawDataOfSites_layerRows
    (activeSiteData : Figure18Site.CheckedNatSpecs)
    (cornerSite : Figure18Site) :
    (rawDataOfSites activeSiteData cornerSite).layerRows = componentRows :=
  rfl

theorem rawDataOfSites_activeSiteData
    (activeSiteData : Figure18Site.CheckedNatSpecs)
    (cornerSite : Figure18Site) :
    (rawDataOfSites activeSiteData cornerSite).activeSiteData =
      activeSiteData :=
  rfl

theorem rawDataOfSites_cornerSite
    (activeSiteData : Figure18Site.CheckedNatSpecs)
    (cornerSite : Figure18Site) :
    (rawDataOfSites activeSiteData cornerSite).cornerSite = cornerSite := by
  cases cornerSite
  rfl

/--
Sparse raw-data adapter for the concrete Figure 13 layer transcription.

This is the preferred constructor for future scaffold data entry because it
keeps the audited layer rows in the `CheckedSparseSeparateLayerRows` form used
by the finite Figure 18 lookup checks.
-/
def sparseRawDataOfSites
    (activeSiteData : Figure18Site.CheckedNatSpecs)
    (cornerSite : Figure18Site) : CheckedSparseRawData :=
  CheckedSparseRawData.ofCheckedSites sparseLayerRows activeSiteData cornerSite

theorem sparseRawDataOfSites_separateLayerRows
    (activeSiteData : Figure18Site.CheckedNatSpecs)
    (cornerSite : Figure18Site) :
    (sparseRawDataOfSites activeSiteData cornerSite).separateLayerRows =
      separateLayerRows :=
  rfl

theorem sparseRawDataOfSites_layerData_rows
    (activeSiteData : Figure18Site.CheckedNatSpecs)
    (cornerSite : Figure18Site) :
    (sparseRawDataOfSites activeSiteData cornerSite).layerData.rows =
      componentRows := by
  exact sparseLayerRows_layerData_rows

private theorem transcription_eq_of_rows_eq
    {D E : Transcription} (hrows : D.rows = E.rows) : D = E := by
  cases D with
  | mk rows length_eq =>
      cases E with
      | mk rows' length_eq' =>
          simp only at hrows
          subst rows'
          rfl

theorem sparseRawDataOfSites_layerData
    (activeSiteData : Figure18Site.CheckedNatSpecs)
    (cornerSite : Figure18Site) :
    (sparseRawDataOfSites activeSiteData cornerSite).layerData = layerData := by
  exact transcription_eq_of_rows_eq
    (sparseRawDataOfSites_layerData_rows activeSiteData cornerSite)

theorem sparseRawDataOfSites_activeSiteData
    (activeSiteData : Figure18Site.CheckedNatSpecs)
    (cornerSite : Figure18Site) :
    (sparseRawDataOfSites activeSiteData cornerSite).activeSiteData =
      activeSiteData :=
  rfl

theorem sparseRawDataOfSites_cornerSite
    (activeSiteData : Figure18Site.CheckedNatSpecs)
    (cornerSite : Figure18Site) :
    (sparseRawDataOfSites activeSiteData cornerSite).cornerSite =
      cornerSite := by
  cases cornerSite
  rfl

theorem sparseRawDataOfSites_layerStackRectangleMatchesBool
    (activeSiteData : Figure18Site.CheckedNatSpecs)
    (cornerSite : Figure18Site) {w h : Nat} (R : SiteRectangle w h) :
    (sparseRawDataOfSites activeSiteData cornerSite).layerStackRectangleMatchesBool
      (checkedLayerStackRectangleOfSiteRectangle R) = true := by
  simpa [sparseRawDataOfSites, CheckedSparseRawData.layerStackRectangleMatchesBool]
    using sparseLayerRows_layerStackRectangleMatchesBool R

theorem sparseRawDataOfSites_exists_checkedLayerStackRectangle
    (activeSiteData : Figure18Site.CheckedNatSpecs)
    (cornerSite : Figure18Site) {w h : Nat} (R : SiteRectangle w h) :
    ∃ (stackData : CheckedLayerStackRectangle w h),
      stackData.sites.matchesSiteRectangleBool R = true ∧
        (sparseRawDataOfSites activeSiteData cornerSite).layerStackRectangleMatchesBool
          stackData = true := by
  exact ⟨checkedLayerStackRectangleOfSiteRectangle R,
    checkedLayerStackRectangleOfSiteRectangle_matchesSite R,
    sparseRawDataOfSites_layerStackRectangleMatchesBool
      activeSiteData cornerSite R⟩

/--
Bundled audit certificate for the human Figure 13 layer transcription.

The first fields say that each sparse layer transcription is a complete
`0..91` indexed table.  The row fields connect those sparse tables to the
dense `componentRows` table, and the final fields expose the stack-rectangle
lookup facts consumed by the scaffold checking layer.
-/
structure Figure13LayerTranscriptionCertificate : Prop where
  thinValid : sparseEntriesValidBool thinEntries = true
  thickValid : sparseEntriesValidBool thickEntries = true
  blackValid : sparseEntriesValidBool blackEntries = true
  thinCoversIndices : thinEntries.map Prod.fst = List.range 92
  thickCoversIndices : thickEntries.map Prod.fst = List.range 92
  blackCoversIndices : blackEntries.map Prod.fst = List.range 92
  componentRowsLength : componentRows.length = 92
  separateRowsLayerData : separateLayerRows.layerData.rows = componentRows
  sparseRowsLayerData : sparseLayerRows.layerData.rows = componentRows
  sparseLayerData : sparseLayerRows.layerData = layerData
  sparseRowsMatchStackRectangles :
    ∀ {w h : Nat} (R : SiteRectangle w h),
      sparseLayerRows.layerStackRectangleMatchesBool
        (checkedLayerStackRectangleOfSiteRectangle R) = true
  sparseRawDataMatchStackRectangles :
    ∀ (activeSiteData : Figure18Site.CheckedNatSpecs)
      (cornerSite : Figure18Site) {w h : Nat} (R : SiteRectangle w h),
      (sparseRawDataOfSites activeSiteData cornerSite).layerStackRectangleMatchesBool
        (checkedLayerStackRectangleOfSiteRectangle R) = true

/--
The concrete Figure 13 layer transcription satisfies the finite audit
certificate derived from `figures/fig13-human.tsv`.
-/
theorem figure13LayerTranscriptionCertificate :
    Figure13LayerTranscriptionCertificate where
  thinValid := thinEntries_valid
  thickValid := thickEntries_valid
  blackValid := blackEntries_valid
  thinCoversIndices := thinEntries_indices
  thickCoversIndices := thickEntries_indices
  blackCoversIndices := blackEntries_indices
  componentRowsLength := componentRows_length
  separateRowsLayerData := separateLayerRows_layerData_rows
  sparseRowsLayerData := sparseLayerRows_layerData_rows
  sparseLayerData := transcription_eq_of_rows_eq sparseLayerRows_layerData_rows
  sparseRowsMatchStackRectangles := sparseLayerRows_layerStackRectangleMatchesBool
  sparseRawDataMatchStackRectangles :=
    sparseRawDataOfSites_layerStackRectangleMatchesBool

def thinBlockAtSite (site : Figure18Site) : Figure16.Block :=
  (LayerComponent.thin (thinComponentAt site.index)).block

def thickBlockAtSite (site : Figure18Site) : Figure16.Block :=
  (LayerComponent.thick (thickComponentAt site.index)).block

def blackBlockAtSite (site : Figure18Site) : Figure16.Block :=
  (LayerComponent.black (blackComponentAt site.index)).block

/-- West/east coordinate of a Figure 18 quadrant inside a Figure 16 block. -/
def quadrantColumn : Quadrant → Fin 2
  | .southwest => ⟨0, by decide⟩
  | .southeast => ⟨1, by decide⟩
  | .northwest => ⟨0, by decide⟩
  | .northeast => ⟨1, by decide⟩

/-- South/north coordinate of a Figure 18 quadrant inside a Figure 16 block. -/
def quadrantRow : Quadrant → Fin 2
  | .southwest => ⟨0, by decide⟩
  | .southeast => ⟨0, by decide⟩
  | .northwest => ⟨1, by decide⟩
  | .northeast => ⟨1, by decide⟩

/-- Entry of a Figure 16 substitution block at a Figure 18 quadrant. -/
def blockEntryAtQuadrant (block : Figure16.Block) (quadrant : Quadrant) :
    Figure16.Symbol :=
  block.entry (quadrantColumn quadrant) (quadrantRow quadrant)

/-- The first L2 summand symbol, coming from the Figure 13 thin/L1 component. -/
def l2Component1SymbolAtSite (site : Figure18Site) : Figure16.Symbol :=
  blockEntryAtQuadrant (thinBlockAtSite site) site.quadrant

/-- The second L2 summand symbol, coming from the Figure 13 thick/L2 component. -/
def l2Component2SymbolAtSite (site : Figure18Site) : Figure16.Symbol :=
  blockEntryAtQuadrant (thickBlockAtSite site) site.quadrant

/-- The L3 symbol at a Figure 18 quadrant. -/
def l3SymbolAtSite (site : Figure18Site) : Figure16.Symbol :=
  blockEntryAtQuadrant (blackBlockAtSite site) site.quadrant

def l2Component1BlankSiteBool (site : Figure18Site) : Bool :=
  decide (l2Component1SymbolAtSite site = Figure16.Symbol.blank)

def l2Component2BlankSiteBool (site : Figure18Site) : Bool :=
  decide (l2Component2SymbolAtSite site = Figure16.Symbol.blank)

/--
Diagnostic predicate for a quarter-site blank in both L2 summands.

This is not the final active-site predicate; the finite facts below show that
the two Figure 16 L2 summands put their local blanks in opposite quadrants, so
the free-square data cannot be recovered by a naive per-tile intersection of
the two local blanks.
-/
def l2BothComponentsBlankSiteBool (site : Figure18Site) : Bool :=
  l2Component1BlankSiteBool site && l2Component2BlankSiteBool site

def natSpecsAtQuadrant (quadrant : Quadrant) : List (Nat × Quadrant) :=
  (List.range 92).map fun index => (index, quadrant)

theorem natSpecsAtQuadrant_length (quadrant : Quadrant) :
    (natSpecsAtQuadrant quadrant).length = 92 := by
  simp [natSpecsAtQuadrant]

theorem natSpecsAtQuadrant_nodup (quadrant : Quadrant) :
    (natSpecsAtQuadrant quadrant).Nodup := by
  unfold natSpecsAtQuadrant
  apply List.Nodup.map
  · intro i j hij
    exact congrArg Prod.fst hij
  · decide

theorem mem_natSpecsAtQuadrant_iff
    {index : Nat} {q quadrant : Quadrant} :
    (index, q) ∈ natSpecsAtQuadrant quadrant ↔
      index < 92 ∧ q = quadrant := by
  constructor
  · intro hmem
    rcases List.mem_map.1 hmem with ⟨index', hindex', hpair⟩
    have hindex_lt : index' < 92 := by
      simpa using List.mem_range.1 hindex'
    cases hpair
    exact ⟨hindex_lt, rfl⟩
  · rintro ⟨hindex, rfl⟩
    exact List.mem_map.2 ⟨index, List.mem_range.2 hindex, rfl⟩

theorem natSpecsAtQuadrant_disjoint_of_ne
    {quadrant₁ quadrant₂ : Quadrant}
    (hne : quadrant₁ ≠ quadrant₂) :
    (natSpecsAtQuadrant quadrant₁).Disjoint
      (natSpecsAtQuadrant quadrant₂) := by
  intro spec hleft hright
  rcases spec with ⟨index, quadrant⟩
  have hq₁ := (mem_natSpecsAtQuadrant_iff.mp hleft).2
  have hq₂ := (mem_natSpecsAtQuadrant_iff.mp hright).2
  exact hne (hq₁.symm.trans hq₂)

def l2Component1BlankSiteSpecs : List (Nat × Quadrant) :=
  Figure18Site.natSpecsOfSites <|
    Figure18Site.all.filter l2Component1BlankSiteBool

def l2Component2BlankSiteSpecs : List (Nat × Quadrant) :=
  Figure18Site.natSpecsOfSites <|
    Figure18Site.all.filter l2Component2BlankSiteBool

def l2BothComponentsBlankSiteSpecs : List (Nat × Quadrant) :=
  Figure18Site.natSpecsOfSites <|
    Figure18Site.all.filter l2BothComponentsBlankSiteBool

theorem l2Component1BlankSiteSpecs_eq :
    l2Component1BlankSiteSpecs = natSpecsAtQuadrant Quadrant.southwest := by
  decide

theorem l2Component1BlankSiteSpecs_length :
    l2Component1BlankSiteSpecs.length = 92 := by
  rw [l2Component1BlankSiteSpecs_eq]
  exact natSpecsAtQuadrant_length Quadrant.southwest

theorem l2Component1BlankSiteSpecs_nodup :
    l2Component1BlankSiteSpecs.Nodup := by
  rw [l2Component1BlankSiteSpecs_eq]
  exact natSpecsAtQuadrant_nodup Quadrant.southwest

theorem l2Component2BlankSiteSpecs_eq :
    l2Component2BlankSiteSpecs = natSpecsAtQuadrant Quadrant.northeast := by
  decide

theorem l2Component2BlankSiteSpecs_length :
    l2Component2BlankSiteSpecs.length = 92 := by
  rw [l2Component2BlankSiteSpecs_eq]
  exact natSpecsAtQuadrant_length Quadrant.northeast

theorem l2Component2BlankSiteSpecs_nodup :
    l2Component2BlankSiteSpecs.Nodup := by
  rw [l2Component2BlankSiteSpecs_eq]
  exact natSpecsAtQuadrant_nodup Quadrant.northeast

theorem l2BlankSiteSpecs_disjoint :
    l2Component1BlankSiteSpecs.Disjoint l2Component2BlankSiteSpecs := by
  rw [l2Component1BlankSiteSpecs_eq, l2Component2BlankSiteSpecs_eq]
  exact natSpecsAtQuadrant_disjoint_of_ne (by decide)

theorem l2BothComponentsBlankSiteSpecs_eq_nil :
    l2BothComponentsBlankSiteSpecs = [] := by
  decide

def generatedStackHCompatiblePairBool
    (left right : Figure18Site) : Bool :=
  if Figure18Site.hCompatible left right then
    decide <|
      (thinBlockAtSite left).hBoundaryMatches (thinBlockAtSite right) ∧
      (thickBlockAtSite left).hBoundaryMatches (thickBlockAtSite right) ∧
      (blackBlockAtSite left).hBoundaryMatches (blackBlockAtSite right)
  else
    true

def generatedStackVCompatiblePairBool
    (lower upper : Figure18Site) : Bool :=
  if Figure18Site.vCompatible lower upper then
    decide <|
      (thinBlockAtSite lower).vBoundaryMatches (thinBlockAtSite upper) ∧
      (thickBlockAtSite lower).vBoundaryMatches (thickBlockAtSite upper) ∧
      (blackBlockAtSite lower).vBoundaryMatches (blackBlockAtSite upper)
  else
    true

def generatedStackSitePairCompatibilityBool
    (sites : List Figure18Site) : Bool :=
  sites.all fun left =>
    sites.all fun right =>
      generatedStackHCompatiblePairBool left right &&
        generatedStackVCompatiblePairBool left right

/-- Horizontal generated-stack compatibility failures among a finite site list. -/
def generatedStackBadHPairs
    (sites : List Figure18Site) : List (Figure18Site × Figure18Site) :=
  sites.flatMap fun left =>
    (sites.filter fun right =>
      !generatedStackHCompatiblePairBool left right).map fun right =>
        (left, right)

/-- Vertical generated-stack compatibility failures among a finite site list. -/
def generatedStackBadVPairs
    (sites : List Figure18Site) : List (Figure18Site × Figure18Site) :=
  sites.flatMap fun lower =>
    (sites.filter fun upper =>
      !generatedStackVCompatiblePairBool lower upper).map fun upper =>
        (lower, upper)

/--
Diagnostic list for the finite generated-stack pair check.

For a future concrete Figure 18 active-site transcription this can be evaluated
to inspect exactly which active/corner site pairs violate the stack check.
-/
def generatedStackPairFailures
    (sites : List Figure18Site) :
    List (String × Figure18Site × Figure18Site) :=
  ((generatedStackBadHPairs sites).map fun pair => ("H", pair.1, pair.2)) ++
  ((generatedStackBadVPairs sites).map fun pair => ("V", pair.1, pair.2))

theorem generatedStackBadHPairs_eq_nil_iff
    {sites : List Figure18Site} :
    generatedStackBadHPairs sites = [] ↔
      ∀ left : Figure18Site, left ∈ sites →
        ∀ right : Figure18Site, right ∈ sites →
          generatedStackHCompatiblePairBool left right = true := by
  simp [generatedStackBadHPairs]

theorem generatedStackBadVPairs_eq_nil_iff
    {sites : List Figure18Site} :
    generatedStackBadVPairs sites = [] ↔
      ∀ lower : Figure18Site, lower ∈ sites →
        ∀ upper : Figure18Site, upper ∈ sites →
          generatedStackVCompatiblePairBool lower upper = true := by
  simp [generatedStackBadVPairs]

theorem generatedStackSitePairCompatibilityBool_eq_true_iff
    {sites : List Figure18Site} :
    generatedStackSitePairCompatibilityBool sites = true ↔
      ∀ left : Figure18Site, left ∈ sites →
        ∀ right : Figure18Site, right ∈ sites →
          generatedStackHCompatiblePairBool left right = true ∧
            generatedStackVCompatiblePairBool left right = true := by
  constructor
  · intro hcheck left hleft right hright
    unfold generatedStackSitePairCompatibilityBool at hcheck
    have hleftCheck := List.all_eq_true.1 hcheck left hleft
    have hrightCheck := List.all_eq_true.1 hleftCheck right hright
    rw [Bool.and_eq_true] at hrightCheck
    exact hrightCheck
  · intro hpairs
    unfold generatedStackSitePairCompatibilityBool
    apply List.all_eq_true.2
    intro left hleft
    apply List.all_eq_true.2
    intro right hright
    rw [Bool.and_eq_true]
    exact hpairs left hleft right hright

theorem generatedStackSitePairCompatibilityBool_eq_true_iff_failures_eq_nil
    {sites : List Figure18Site} :
    generatedStackSitePairCompatibilityBool sites = true ↔
      generatedStackPairFailures sites = [] := by
  rw [generatedStackSitePairCompatibilityBool_eq_true_iff]
  change (∀ left : Figure18Site, left ∈ sites →
        ∀ right : Figure18Site, right ∈ sites →
          generatedStackHCompatiblePairBool left right = true ∧
            generatedStackVCompatiblePairBool left right = true) ↔
      (((generatedStackBadHPairs sites).map fun pair =>
          ("H", pair.1, pair.2)) ++
        ((generatedStackBadVPairs sites).map fun pair =>
          ("V", pair.1, pair.2))) = []
  rw [List.append_eq_nil_iff, List.map_eq_nil_iff, List.map_eq_nil_iff,
    generatedStackBadHPairs_eq_nil_iff, generatedStackBadVPairs_eq_nil_iff]
  constructor
  · intro hpairs
    constructor
    · intro left hleft right hright
      exact (hpairs left hleft right hright).1
    · intro lower hlower upper hupper
      exact (hpairs lower hlower upper hupper).2
  · intro hpairs left hleft right hright
    exact ⟨hpairs.1 left hleft right hright,
      hpairs.2 left hleft right hright⟩

def generatedStackAllowedSites
    (activeSiteData : Figure18Site.CheckedNatSpecs)
    (cornerSite : Figure18Site) : List Figure18Site :=
  cornerSite :: activeSiteData.sites

def generatedStackAllowedSitePairFailures
    (activeSiteData : Figure18Site.CheckedNatSpecs)
    (cornerSite : Figure18Site) :
    List (String × Figure18Site × Figure18Site) :=
  generatedStackPairFailures
    (generatedStackAllowedSites activeSiteData cornerSite)

def generatedStackAllowedSitePairCompatibilityBool
    (activeSiteData : Figure18Site.CheckedNatSpecs)
    (cornerSite : Figure18Site) : Bool :=
  generatedStackSitePairCompatibilityBool
    (generatedStackAllowedSites activeSiteData cornerSite)

theorem
    generatedStackAllowedSitePairCompatibilityBool_eq_true_iff_failures_eq_nil
    {activeSiteData : Figure18Site.CheckedNatSpecs}
    {cornerSite : Figure18Site} :
    generatedStackAllowedSitePairCompatibilityBool activeSiteData cornerSite =
      true ↔
      generatedStackAllowedSitePairFailures activeSiteData cornerSite = [] :=
  generatedStackSitePairCompatibilityBool_eq_true_iff_failures_eq_nil

theorem generatedStackAllowedSitePairCompatibilityBool_of_failures_eq_nil
    {activeSiteData : Figure18Site.CheckedNatSpecs}
    {cornerSite : Figure18Site}
    (hfailures :
      generatedStackAllowedSitePairFailures activeSiteData cornerSite = []) :
    generatedStackAllowedSitePairCompatibilityBool activeSiteData cornerSite =
      true :=
  generatedStackAllowedSitePairCompatibilityBool_eq_true_iff_failures_eq_nil.2
    hfailures

theorem generatedStackAllowedSitePairFailures_eq_nil_of_pairCompatibilityBool
    {activeSiteData : Figure18Site.CheckedNatSpecs}
    {cornerSite : Figure18Site}
    (hpair :
      generatedStackAllowedSitePairCompatibilityBool activeSiteData cornerSite =
        true) :
    generatedStackAllowedSitePairFailures activeSiteData cornerSite = [] :=
  generatedStackAllowedSitePairCompatibilityBool_eq_true_iff_failures_eq_nil.1
    hpair

theorem generatedStackSitePairCompatibilityBool_of_subset
    {sites sites' : List Figure18Site}
    (hcheck : generatedStackSitePairCompatibilityBool sites = true)
    (hsubset : ∀ site : Figure18Site, site ∈ sites' → site ∈ sites) :
    generatedStackSitePairCompatibilityBool sites' = true := by
  unfold generatedStackSitePairCompatibilityBool at hcheck ⊢
  apply List.all_eq_true.2
  intro left hleft
  apply List.all_eq_true.2
  intro right hright
  exact List.all_eq_true.1
    (List.all_eq_true.1 hcheck left (hsubset left hleft))
    right (hsubset right hright)

theorem generatedStackAllowedSitePairCompatibilityBool_of_sites_subset
    {activeSiteData activeSiteData' : Figure18Site.CheckedNatSpecs}
    {cornerSite : Figure18Site}
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool activeSiteData cornerSite =
        true)
    (hsubset :
      ∀ site : Figure18Site,
        site ∈ activeSiteData'.sites →
          site = cornerSite ∨ site ∈ activeSiteData.sites) :
    generatedStackAllowedSitePairCompatibilityBool activeSiteData' cornerSite =
      true := by
  apply generatedStackSitePairCompatibilityBool_of_subset hcheck
  intro site hsite
  have hsite' : site = cornerSite ∨ site ∈ activeSiteData'.sites := by
    simpa [generatedStackAllowedSites] using hsite
  rcases hsite' with rfl | hsite'
  · simp [generatedStackAllowedSites]
  · rcases hsubset site hsite' with rfl | hsite
    · simp [generatedStackAllowedSites]
    · simp [generatedStackAllowedSites, hsite]

theorem generatedStackAllowedSitePairCompatibilityBool_ofActiveSites
    {activeSiteData : Figure18Site.CheckedNatSpecs}
    {cornerSite : Figure18Site}
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool activeSiteData cornerSite =
        true) :
    generatedStackAllowedSitePairCompatibilityBool
      (Figure18RoleTable.FlatRoleTable.ofActiveSites
        activeSiteData.sites cornerSite).activeSiteData
      cornerSite = true := by
  apply generatedStackAllowedSitePairCompatibilityBool_of_sites_subset hcheck
  intro site hsite
  have hsite' :
      site ∈ (Figure18RoleTable.FlatRoleTable.ofActiveSites
        activeSiteData.sites cornerSite).activeSites := by
    simpa using hsite
  exact (Figure18RoleTable.FlatRoleTable.mem_ofActiveSites_activeSites_iff
    activeSiteData.sites cornerSite site).1 hsite'

set_option maxRecDepth 20000 in
/--
Finite regression for the flat Figure 18 role-table route.

The smoke table is intentionally not the paper's scaffold.  This theorem only
checks that the generated Figure 13/Figure 16 stack-compatibility checker runs
through the same `FlatRoleTable.activeSiteData`/`cornerSite` interface that a
future Figure 18 transcription will use.
-/
theorem Figure18RoleTable.smokeFlat_pairCompatibility :
    generatedStackAllowedSitePairCompatibilityBool
      Figure18RoleTable.smokeFlat.activeSiteData
      Figure18RoleTable.smokeFlat.cornerSite = true := by
  decide

set_option maxRecDepth 20000 in
theorem Figure18RoleTable.smokeFlat_pairFailures :
    generatedStackAllowedSitePairFailures
      Figure18RoleTable.smokeFlat.activeSiteData
      Figure18RoleTable.smokeFlat.cornerSite = [] := by
  decide

theorem generatedStackHBoundaries_of_pairCompatibilityBool
    {sites : List Figure18Site} {left right : Figure18Site}
    (hcheck : generatedStackSitePairCompatibilityBool sites = true)
    (hleft : left ∈ sites) (hright : right ∈ sites)
    (hh : Figure18Site.hCompatible left right = true) :
    (thinBlockAtSite left).hBoundaryMatches (thinBlockAtSite right) ∧
      (thickBlockAtSite left).hBoundaryMatches (thickBlockAtSite right) ∧
      (blackBlockAtSite left).hBoundaryMatches (blackBlockAtSite right) := by
  unfold generatedStackSitePairCompatibilityBool at hcheck
  have hleftCheck := List.all_eq_true.1 hcheck left hleft
  have hrightCheck := List.all_eq_true.1 hleftCheck right hright
  rw [Bool.and_eq_true] at hrightCheck
  unfold generatedStackHCompatiblePairBool at hrightCheck
  simpa [hh] using hrightCheck.1

theorem generatedStackVBoundaries_of_pairCompatibilityBool
    {sites : List Figure18Site} {lower upper : Figure18Site}
    (hcheck : generatedStackSitePairCompatibilityBool sites = true)
    (hlower : lower ∈ sites) (hupper : upper ∈ sites)
    (hv : Figure18Site.vCompatible lower upper = true) :
    (thinBlockAtSite lower).vBoundaryMatches (thinBlockAtSite upper) ∧
      (thickBlockAtSite lower).vBoundaryMatches (thickBlockAtSite upper) ∧
      (blackBlockAtSite lower).vBoundaryMatches (blackBlockAtSite upper) := by
  unfold generatedStackSitePairCompatibilityBool at hcheck
  have hlowerCheck := List.all_eq_true.1 hcheck lower hlower
  have hupperCheck := List.all_eq_true.1 hlowerCheck upper hupper
  rw [Bool.and_eq_true] at hupperCheck
  unfold generatedStackVCompatiblePairBool at hupperCheck
  simpa [hv] using hupperCheck.2

theorem mem_generatedStackAllowedSites_of_listed
    {activeSiteData : Figure18Site.CheckedNatSpecs}
    {cornerSite site : Figure18Site}
    (hsite : site = cornerSite ∨ site ∈ activeSiteData.sites) :
    site ∈ generatedStackAllowedSites activeSiteData cornerSite := by
  rcases hsite with rfl | hsite
  · simp [generatedStackAllowedSites]
  · simp [generatedStackAllowedSites, hsite]

theorem generatedStackAllowedSitePairCompatibilityBool_eq_true_iff
    {activeSiteData : Figure18Site.CheckedNatSpecs}
    {cornerSite : Figure18Site} :
    generatedStackAllowedSitePairCompatibilityBool activeSiteData cornerSite =
      true ↔
      ∀ left : Figure18Site,
        left = cornerSite ∨ left ∈ activeSiteData.sites →
        ∀ right : Figure18Site,
          right = cornerSite ∨ right ∈ activeSiteData.sites →
          generatedStackHCompatiblePairBool left right = true ∧
            generatedStackVCompatiblePairBool left right = true := by
  constructor
  · intro hcheck left hleft right hright
    exact
      generatedStackSitePairCompatibilityBool_eq_true_iff.1 hcheck
        left (mem_generatedStackAllowedSites_of_listed hleft)
        right (mem_generatedStackAllowedSites_of_listed hright)
  · intro hpairs
    apply generatedStackSitePairCompatibilityBool_eq_true_iff.2
    intro left hleft right hright
    have hleft' :
        left = cornerSite ∨ left ∈ activeSiteData.sites := by
      simpa [generatedStackAllowedSites] using hleft
    have hright' :
        right = cornerSite ∨ right ∈ activeSiteData.sites := by
      simpa [generatedStackAllowedSites] using hright
    exact hpairs left hleft' right hright'

theorem generatedStackHBoundaries_of_allowedPairCompatibilityBool
    {activeSiteData : Figure18Site.CheckedNatSpecs}
    {cornerSite left right : Figure18Site}
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool activeSiteData cornerSite =
        true)
    (hleft : left = cornerSite ∨ left ∈ activeSiteData.sites)
    (hright : right = cornerSite ∨ right ∈ activeSiteData.sites)
    (hh : Figure18Site.hCompatible left right = true) :
    (thinBlockAtSite left).hBoundaryMatches (thinBlockAtSite right) ∧
      (thickBlockAtSite left).hBoundaryMatches (thickBlockAtSite right) ∧
      (blackBlockAtSite left).hBoundaryMatches (blackBlockAtSite right) :=
  generatedStackHBoundaries_of_pairCompatibilityBool hcheck
    (mem_generatedStackAllowedSites_of_listed hleft)
    (mem_generatedStackAllowedSites_of_listed hright) hh

theorem generatedStackVBoundaries_of_allowedPairCompatibilityBool
    {activeSiteData : Figure18Site.CheckedNatSpecs}
    {cornerSite lower upper : Figure18Site}
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool activeSiteData cornerSite =
        true)
    (hlower : lower = cornerSite ∨ lower ∈ activeSiteData.sites)
    (hupper : upper = cornerSite ∨ upper ∈ activeSiteData.sites)
    (hv : Figure18Site.vCompatible lower upper = true) :
    (thinBlockAtSite lower).vBoundaryMatches (thinBlockAtSite upper) ∧
      (thickBlockAtSite lower).vBoundaryMatches (thickBlockAtSite upper) ∧
      (blackBlockAtSite lower).vBoundaryMatches (blackBlockAtSite upper) :=
  generatedStackVBoundaries_of_pairCompatibilityBool hcheck
    (mem_generatedStackAllowedSites_of_listed hlower)
    (mem_generatedStackAllowedSites_of_listed hupper) hv

set_option linter.flexible false in
theorem generatedStackThinHBoundaryBool_of_allowedPairCompatibilityBool
    {activeSiteData : Figure18Site.CheckedNatSpecs}
    {cornerSite : Figure18Site}
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool activeSiteData cornerSite =
        true)
    {n : Nat} (R : SiteRectangle n n)
    (hsites : ∀ i : Fin n, ∀ j : Fin n,
      R i j = cornerSite ∨ R i j ∈ activeSiteData.sites)
    (hh : ∀ i : Fin n, ∀ j : Fin n, ∀ hi : i.val + 1 < n,
      Figure18Site.hCompatible (R i j) (R ⟨i.val + 1, hi⟩ j) = true) :
    CompatibleLayerComponentRectangle.hBoundaryBool
      ((checkedLayerStackRectangleOfSiteRectangle R).thinRectangle
        (sparseRawDataOfSites activeSiteData cornerSite).layerData
        (CheckedLayerStackRectangle.thinLookupBool_of_lookupBool
          (CheckedSparseRawData.lookupBool_layerData_of_layerStackRectangleMatchesBool
            (sparseRawDataOfSites_layerStackRectangleMatchesBool
              activeSiteData cornerSite R)))).toLayerComponentRectangle =
        true := by
  unfold CompatibleLayerComponentRectangle.hBoundaryBool
  apply List.all_eq_true.2
  intro i _hi_mem
  by_cases hi : i.val + 1 < n
  · simp [hi]
    intro j
    have hb := generatedStackHBoundaries_of_allowedPairCompatibilityBool
      hcheck (hsites i j) (hsites ⟨i.val + 1, hi⟩ j) (hh i j hi)
    dsimp [TypedLayerComponentRectangle.toLayerComponentRectangle,
      LayerComponentRectangle.blockGrid]
    simp [CheckedLayerStackRectangle.thinRectangle,
      CheckedLayerComponentRectangle.toTypedLayerComponentRectangle_componentRect,
      checkedLayerStackRectangleOfSiteRectangle_thin_componentAt,
      thinBlockAtSite] at hb ⊢
    exact hb.1
  · simp [hi]

set_option linter.flexible false in
theorem generatedStackThickHBoundaryBool_of_allowedPairCompatibilityBool
    {activeSiteData : Figure18Site.CheckedNatSpecs}
    {cornerSite : Figure18Site}
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool activeSiteData cornerSite =
        true)
    {n : Nat} (R : SiteRectangle n n)
    (hsites : ∀ i : Fin n, ∀ j : Fin n,
      R i j = cornerSite ∨ R i j ∈ activeSiteData.sites)
    (hh : ∀ i : Fin n, ∀ j : Fin n, ∀ hi : i.val + 1 < n,
      Figure18Site.hCompatible (R i j) (R ⟨i.val + 1, hi⟩ j) = true) :
    CompatibleLayerComponentRectangle.hBoundaryBool
      ((checkedLayerStackRectangleOfSiteRectangle R).thickRectangle
        (sparseRawDataOfSites activeSiteData cornerSite).layerData
        (CheckedLayerStackRectangle.thickLookupBool_of_lookupBool
          (CheckedSparseRawData.lookupBool_layerData_of_layerStackRectangleMatchesBool
            (sparseRawDataOfSites_layerStackRectangleMatchesBool
              activeSiteData cornerSite R)))).toLayerComponentRectangle =
        true := by
  unfold CompatibleLayerComponentRectangle.hBoundaryBool
  apply List.all_eq_true.2
  intro i _hi_mem
  by_cases hi : i.val + 1 < n
  · simp [hi]
    intro j
    have hb := generatedStackHBoundaries_of_allowedPairCompatibilityBool
      hcheck (hsites i j) (hsites ⟨i.val + 1, hi⟩ j) (hh i j hi)
    dsimp [TypedLayerComponentRectangle.toLayerComponentRectangle,
      LayerComponentRectangle.blockGrid]
    simp [CheckedLayerStackRectangle.thickRectangle,
      CheckedLayerComponentRectangle.toTypedLayerComponentRectangle_componentRect,
      checkedLayerStackRectangleOfSiteRectangle_thick_componentAt,
      thickBlockAtSite] at hb ⊢
    exact hb.2.1
  · simp [hi]

set_option linter.flexible false in
theorem generatedStackBlackHBoundaryBool_of_allowedPairCompatibilityBool
    {activeSiteData : Figure18Site.CheckedNatSpecs}
    {cornerSite : Figure18Site}
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool activeSiteData cornerSite =
        true)
    {n : Nat} (R : SiteRectangle n n)
    (hsites : ∀ i : Fin n, ∀ j : Fin n,
      R i j = cornerSite ∨ R i j ∈ activeSiteData.sites)
    (hh : ∀ i : Fin n, ∀ j : Fin n, ∀ hi : i.val + 1 < n,
      Figure18Site.hCompatible (R i j) (R ⟨i.val + 1, hi⟩ j) = true) :
    CompatibleLayerComponentRectangle.hBoundaryBool
      ((checkedLayerStackRectangleOfSiteRectangle R).blackRectangle
        (sparseRawDataOfSites activeSiteData cornerSite).layerData
        (CheckedLayerStackRectangle.blackLookupBool_of_lookupBool
          (CheckedSparseRawData.lookupBool_layerData_of_layerStackRectangleMatchesBool
            (sparseRawDataOfSites_layerStackRectangleMatchesBool
              activeSiteData cornerSite R)))).toLayerComponentRectangle =
        true := by
  unfold CompatibleLayerComponentRectangle.hBoundaryBool
  apply List.all_eq_true.2
  intro i _hi_mem
  by_cases hi : i.val + 1 < n
  · simp [hi]
    intro j
    have hb := generatedStackHBoundaries_of_allowedPairCompatibilityBool
      hcheck (hsites i j) (hsites ⟨i.val + 1, hi⟩ j) (hh i j hi)
    dsimp [TypedLayerComponentRectangle.toLayerComponentRectangle,
      LayerComponentRectangle.blockGrid]
    simp [CheckedLayerStackRectangle.blackRectangle,
      CheckedLayerComponentRectangle.toTypedLayerComponentRectangle_componentRect,
      checkedLayerStackRectangleOfSiteRectangle_black_componentAt,
      blackBlockAtSite] at hb ⊢
    exact hb.2.2
  · simp [hi]

set_option linter.flexible false in
theorem generatedStackThinVBoundaryBool_of_allowedPairCompatibilityBool
    {activeSiteData : Figure18Site.CheckedNatSpecs}
    {cornerSite : Figure18Site}
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool activeSiteData cornerSite =
        true)
    {n : Nat} (R : SiteRectangle n n)
    (hsites : ∀ i : Fin n, ∀ j : Fin n,
      R i j = cornerSite ∨ R i j ∈ activeSiteData.sites)
    (hv : ∀ i : Fin n, ∀ j : Fin n, ∀ hj : j.val + 1 < n,
      Figure18Site.vCompatible (R i j) (R i ⟨j.val + 1, hj⟩) = true) :
    CompatibleLayerComponentRectangle.vBoundaryBool
      ((checkedLayerStackRectangleOfSiteRectangle R).thinRectangle
        (sparseRawDataOfSites activeSiteData cornerSite).layerData
        (CheckedLayerStackRectangle.thinLookupBool_of_lookupBool
          (CheckedSparseRawData.lookupBool_layerData_of_layerStackRectangleMatchesBool
            (sparseRawDataOfSites_layerStackRectangleMatchesBool
              activeSiteData cornerSite R)))).toLayerComponentRectangle =
        true := by
  unfold CompatibleLayerComponentRectangle.vBoundaryBool
  apply List.all_eq_true.2
  intro j _hj_mem
  by_cases hj : j.val + 1 < n
  · simp [hj]
    intro i
    have hb := generatedStackVBoundaries_of_allowedPairCompatibilityBool
      hcheck (hsites i j) (hsites i ⟨j.val + 1, hj⟩) (hv i j hj)
    dsimp [TypedLayerComponentRectangle.toLayerComponentRectangle,
      LayerComponentRectangle.blockGrid]
    simp [CheckedLayerStackRectangle.thinRectangle,
      CheckedLayerComponentRectangle.toTypedLayerComponentRectangle_componentRect,
      checkedLayerStackRectangleOfSiteRectangle_thin_componentAt,
      thinBlockAtSite] at hb ⊢
    exact hb.1
  · simp [hj]

set_option linter.flexible false in
theorem generatedStackThickVBoundaryBool_of_allowedPairCompatibilityBool
    {activeSiteData : Figure18Site.CheckedNatSpecs}
    {cornerSite : Figure18Site}
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool activeSiteData cornerSite =
        true)
    {n : Nat} (R : SiteRectangle n n)
    (hsites : ∀ i : Fin n, ∀ j : Fin n,
      R i j = cornerSite ∨ R i j ∈ activeSiteData.sites)
    (hv : ∀ i : Fin n, ∀ j : Fin n, ∀ hj : j.val + 1 < n,
      Figure18Site.vCompatible (R i j) (R i ⟨j.val + 1, hj⟩) = true) :
    CompatibleLayerComponentRectangle.vBoundaryBool
      ((checkedLayerStackRectangleOfSiteRectangle R).thickRectangle
        (sparseRawDataOfSites activeSiteData cornerSite).layerData
        (CheckedLayerStackRectangle.thickLookupBool_of_lookupBool
          (CheckedSparseRawData.lookupBool_layerData_of_layerStackRectangleMatchesBool
            (sparseRawDataOfSites_layerStackRectangleMatchesBool
              activeSiteData cornerSite R)))).toLayerComponentRectangle =
        true := by
  unfold CompatibleLayerComponentRectangle.vBoundaryBool
  apply List.all_eq_true.2
  intro j _hj_mem
  by_cases hj : j.val + 1 < n
  · simp [hj]
    intro i
    have hb := generatedStackVBoundaries_of_allowedPairCompatibilityBool
      hcheck (hsites i j) (hsites i ⟨j.val + 1, hj⟩) (hv i j hj)
    dsimp [TypedLayerComponentRectangle.toLayerComponentRectangle,
      LayerComponentRectangle.blockGrid]
    simp [CheckedLayerStackRectangle.thickRectangle,
      CheckedLayerComponentRectangle.toTypedLayerComponentRectangle_componentRect,
      checkedLayerStackRectangleOfSiteRectangle_thick_componentAt,
      thickBlockAtSite] at hb ⊢
    exact hb.2.1
  · simp [hj]

set_option linter.flexible false in
theorem generatedStackBlackVBoundaryBool_of_allowedPairCompatibilityBool
    {activeSiteData : Figure18Site.CheckedNatSpecs}
    {cornerSite : Figure18Site}
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool activeSiteData cornerSite =
        true)
    {n : Nat} (R : SiteRectangle n n)
    (hsites : ∀ i : Fin n, ∀ j : Fin n,
      R i j = cornerSite ∨ R i j ∈ activeSiteData.sites)
    (hv : ∀ i : Fin n, ∀ j : Fin n, ∀ hj : j.val + 1 < n,
      Figure18Site.vCompatible (R i j) (R i ⟨j.val + 1, hj⟩) = true) :
    CompatibleLayerComponentRectangle.vBoundaryBool
      ((checkedLayerStackRectangleOfSiteRectangle R).blackRectangle
        (sparseRawDataOfSites activeSiteData cornerSite).layerData
        (CheckedLayerStackRectangle.blackLookupBool_of_lookupBool
          (CheckedSparseRawData.lookupBool_layerData_of_layerStackRectangleMatchesBool
            (sparseRawDataOfSites_layerStackRectangleMatchesBool
              activeSiteData cornerSite R)))).toLayerComponentRectangle =
        true := by
  unfold CompatibleLayerComponentRectangle.vBoundaryBool
  apply List.all_eq_true.2
  intro j _hj_mem
  by_cases hj : j.val + 1 < n
  · simp [hj]
    intro i
    have hb := generatedStackVBoundaries_of_allowedPairCompatibilityBool
      hcheck (hsites i j) (hsites i ⟨j.val + 1, hj⟩) (hv i j hj)
    dsimp [TypedLayerComponentRectangle.toLayerComponentRectangle,
      LayerComponentRectangle.blockGrid]
    simp [CheckedLayerStackRectangle.blackRectangle,
      CheckedLayerComponentRectangle.toTypedLayerComponentRectangle_componentRect,
      checkedLayerStackRectangleOfSiteRectangle_black_componentAt,
      blackBlockAtSite] at hb ⊢
    exact hb.2.2
  · simp [hj]

def HasGeneratedStackCompatibilityForListedActiveSiteRectangles
    (activeSiteData : Figure18Site.CheckedNatSpecs)
    (cornerSite : Figure18Site) : Prop :=
  ∀ {n : Nat} {hn : 0 < n} (R : SiteRectangle n n),
    (∀ i : Fin n, ∀ j : Fin n,
      R i j = cornerSite ∨ R i j ∈ activeSiteData.sites) →
    R ⟨0, hn⟩ ⟨0, hn⟩ = cornerSite →
    (∀ i : Fin n, ∀ j : Fin n, ∀ hi : i.val + 1 < n,
      Figure18Site.hCompatible (R i j) (R ⟨i.val + 1, hi⟩ j) = true) →
    (∀ i : Fin n, ∀ j : Fin n, ∀ hj : j.val + 1 < n,
      Figure18Site.vCompatible (R i j) (R i ⟨j.val + 1, hj⟩) = true) →
      let stackData := checkedLayerStackRectangleOfSiteRectangle R
      stackData.compatibleBool (sparseRawDataOfSites activeSiteData cornerSite).layerData
        (CheckedSparseRawData.lookupBool_layerData_of_layerStackRectangleMatchesBool
          (sparseRawDataOfSites_layerStackRectangleMatchesBool
            activeSiteData cornerSite R)) = true

/--
Local compatibility target for generated Figure 13 layer stacks over arbitrary
Figure 18 site rectangles.

Only the selected sites and local horizontal/vertical compatibility matter for
the Figure 16 layer stack check.  The lower-left corner condition used by
listed-active windows is handled separately by those window structures.
-/
def HasGeneratedStackCompatibilityForAllowedSiteRectangles
    (activeSiteData : Figure18Site.CheckedNatSpecs)
    (cornerSite : Figure18Site) : Prop :=
  ∀ {n : Nat} (R : SiteRectangle n n),
    (∀ i : Fin n, ∀ j : Fin n,
      R i j = cornerSite ∨ R i j ∈ activeSiteData.sites) →
    (∀ i : Fin n, ∀ j : Fin n, ∀ hi : i.val + 1 < n,
      Figure18Site.hCompatible (R i j) (R ⟨i.val + 1, hi⟩ j) = true) →
    (∀ i : Fin n, ∀ j : Fin n, ∀ hj : j.val + 1 < n,
      Figure18Site.vCompatible (R i j) (R i ⟨j.val + 1, hj⟩) = true) →
      let stackData := checkedLayerStackRectangleOfSiteRectangle R
      stackData.compatibleBool (sparseRawDataOfSites activeSiteData cornerSite).layerData
        (CheckedSparseRawData.lookupBool_layerData_of_layerStackRectangleMatchesBool
          (sparseRawDataOfSites_layerStackRectangleMatchesBool
            activeSiteData cornerSite R)) = true

theorem hasGeneratedStackCompatibilityForAllowedSiteRectangles_of_allowedPairCompatibilityBool
    (activeSiteData : Figure18Site.CheckedNatSpecs)
    (cornerSite : Figure18Site)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool activeSiteData cornerSite =
        true) :
    HasGeneratedStackCompatibilityForAllowedSiteRectangles
      activeSiteData cornerSite := by
  intro n R hsites hh hv
  dsimp
  unfold CheckedLayerStackRectangle.compatibleBool
  rw [Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · unfold TypedLayerComponentRectangle.compatibleBool
    unfold CompatibleLayerComponentRectangle.compatibleBool
    rw [Bool.and_eq_true]
    exact ⟨
      generatedStackThinHBoundaryBool_of_allowedPairCompatibilityBool
        hcheck R hsites hh,
      generatedStackThinVBoundaryBool_of_allowedPairCompatibilityBool
        hcheck R hsites hv⟩
  · unfold TypedLayerComponentRectangle.compatibleBool
    unfold CompatibleLayerComponentRectangle.compatibleBool
    rw [Bool.and_eq_true]
    exact ⟨
      generatedStackThickHBoundaryBool_of_allowedPairCompatibilityBool
        hcheck R hsites hh,
      generatedStackThickVBoundaryBool_of_allowedPairCompatibilityBool
        hcheck R hsites hv⟩
  · unfold TypedLayerComponentRectangle.compatibleBool
    unfold CompatibleLayerComponentRectangle.compatibleBool
    rw [Bool.and_eq_true]
    exact ⟨
      generatedStackBlackHBoundaryBool_of_allowedPairCompatibilityBool
        hcheck R hsites hh,
      generatedStackBlackVBoundaryBool_of_allowedPairCompatibilityBool
        hcheck R hsites hv⟩

theorem hasGeneratedStackCompatibilityForListedActiveSiteRectangles_of_allowedPairCompatibilityBool
    (activeSiteData : Figure18Site.CheckedNatSpecs)
    (cornerSite : Figure18Site)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool activeSiteData cornerSite =
        true) :
    HasGeneratedStackCompatibilityForListedActiveSiteRectangles
      activeSiteData cornerSite := by
  intro n _hn R hsites _hcorner hh hv
  exact
    hasGeneratedStackCompatibilityForAllowedSiteRectangles_of_allowedPairCompatibilityBool
      activeSiteData cornerSite hcheck R hsites hh hv

theorem sparseRawDataOfSites_exists_compatible_checkedLayerStackRectangle
    (activeSiteData : Figure18Site.CheckedNatSpecs)
    (cornerSite : Figure18Site)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool activeSiteData cornerSite =
        true)
    {n : Nat} (R : SiteRectangle n n)
    (hsites : ∀ i : Fin n, ∀ j : Fin n,
      R i j = cornerSite ∨ R i j ∈ activeSiteData.sites)
    (hh : ∀ i : Fin n, ∀ j : Fin n, ∀ hi : i.val + 1 < n,
      Figure18Site.hCompatible (R i j) (R ⟨i.val + 1, hi⟩ j) = true)
    (hv : ∀ i : Fin n, ∀ j : Fin n, ∀ hj : j.val + 1 < n,
      Figure18Site.vCompatible (R i j) (R i ⟨j.val + 1, hj⟩) = true) :
    ∃ (stackData : CheckedLayerStackRectangle n n),
      ∃ (_hsite : stackData.sites.matchesSiteRectangleBool R = true),
        ∃ (hmatch :
          (sparseRawDataOfSites activeSiteData cornerSite).layerStackRectangleMatchesBool
            stackData = true),
          stackData.compatibleBool
            (sparseRawDataOfSites activeSiteData cornerSite).layerData
            (CheckedSparseRawData.lookupBool_layerData_of_layerStackRectangleMatchesBool
              hmatch) = true := by
  refine ⟨checkedLayerStackRectangleOfSiteRectangle R,
    checkedLayerStackRectangleOfSiteRectangle_matchesSite R,
    sparseRawDataOfSites_layerStackRectangleMatchesBool
      activeSiteData cornerSite R,
    ?_⟩
  exact
    hasGeneratedStackCompatibilityForAllowedSiteRectangles_of_allowedPairCompatibilityBool
      activeSiteData cornerSite hcheck R hsites hh hv

/--
Attach the concrete Figure 13/16 layer stack to an indexed-routed Figure 18
fixed-corner square, assuming its selected site rectangle uses only allowed
sites and has locally compatible neighboring sites.
-/
def sparseRawDataOfSites_toIndexedRoutedFixedCornerSquareWithLayerStack
    (activeSiteData : Figure18Site.CheckedNatSpecs)
    (cornerSite : Figure18Site)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool activeSiteData cornerSite =
        true)
    {table : Figure18RoleTable} {T : TileSet} {seed : WangTile}
    {x : Int × Int →
      TileIn (combineWithScaffold table.presentation.toScaffold T seed)}
    {n : Nat} {hn : 0 < n}
    (window : Figure18IndexedRoutedFixedCornerSquare table x n hn)
    (hsites : ∀ i : Fin n, ∀ j : Fin n,
      siteRectangleOfIndexedRoutedFixedCornerSquare window i j = cornerSite ∨
        siteRectangleOfIndexedRoutedFixedCornerSquare window i j ∈
          activeSiteData.sites)
    (hh : ∀ i : Fin n, ∀ j : Fin n, ∀ hi : i.val + 1 < n,
      Figure18Site.hCompatible
        (siteRectangleOfIndexedRoutedFixedCornerSquare window i j)
        (siteRectangleOfIndexedRoutedFixedCornerSquare window
          ⟨i.val + 1, hi⟩ j) = true)
    (hv : ∀ i : Fin n, ∀ j : Fin n, ∀ hj : j.val + 1 < n,
      Figure18Site.vCompatible
        (siteRectangleOfIndexedRoutedFixedCornerSquare window i j)
        (siteRectangleOfIndexedRoutedFixedCornerSquare window
          i ⟨j.val + 1, hj⟩) = true) :
    Figure18IndexedRoutedFixedCornerSquareWithLayerStack
      (sparseRawDataOfSites activeSiteData cornerSite).layerData table x n hn := by
  let R := siteRectangleOfIndexedRoutedFixedCornerSquare window
  let stackData := checkedLayerStackRectangleOfSiteRectangle R
  let data := sparseRawDataOfSites activeSiteData cornerSite
  have hmatch : data.layerStackRectangleMatchesBool stackData = true :=
    sparseRawDataOfSites_layerStackRectangleMatchesBool activeSiteData cornerSite R
  have hcompatible :
      stackData.compatibleBool data.layerData
        (CheckedSparseRawData.lookupBool_layerData_of_layerStackRectangleMatchesBool
          hmatch) = true :=
    hasGeneratedStackCompatibilityForAllowedSiteRectangles_of_allowedPairCompatibilityBool
      activeSiteData cornerSite hcheck R hsites hh hv
  exact data.toIndexedRoutedFixedCornerSquareWithLayerStack window stackData
    (checkedLayerStackRectangleOfSiteRectangle_matchesSite R) hmatch hcompatible

/--
Geometric routed-window target whose selected site rectangle is directly
checkable against the concrete Figure 13/16 layer stack data.

This is the scaffold-facing obligation we want from the Figure 18 proof: for
each combined tiling and size, produce an indexed-routed fixed-corner square
whose selected Figure 13 sites are all either the distinguished corner or
listed active sites, and whose neighboring selected sites are locally
compatible.
-/
def HasAllowedIndexedRoutedFixedCornerSquares
    (activeSiteData : Figure18Site.CheckedNatSpecs)
    (cornerSite : Figure18Site) (table : Figure18RoleTable) : Prop :=
  ∀ {T : TileSet} {seed : WangTile}
    (x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed)),
    ValidPlaneTiling (combineWithScaffold table.presentation.toScaffold T seed) x →
      ∀ n : Nat, ∀ hn : 0 < n,
        ∃ (window : Figure18IndexedRoutedFixedCornerSquare table x n hn),
          (∀ i : Fin n, ∀ j : Fin n,
            siteRectangleOfIndexedRoutedFixedCornerSquare window i j =
              cornerSite ∨
            siteRectangleOfIndexedRoutedFixedCornerSquare window i j ∈
              activeSiteData.sites) ∧
          (∀ i : Fin n, ∀ j : Fin n, ∀ hi : i.val + 1 < n,
            Figure18Site.hCompatible
              (siteRectangleOfIndexedRoutedFixedCornerSquare window i j)
              (siteRectangleOfIndexedRoutedFixedCornerSquare window
                ⟨i.val + 1, hi⟩ j) = true) ∧
          (∀ i : Fin n, ∀ j : Fin n, ∀ hj : j.val + 1 < n,
            Figure18Site.vCompatible
              (siteRectangleOfIndexedRoutedFixedCornerSquare window i j)
              (siteRectangleOfIndexedRoutedFixedCornerSquare window
                i ⟨j.val + 1, hj⟩) = true)

/--
Local compatibility of the virtual neighboring sites selected by Robinson's
routed board/free-grid geometry.

This is a geometric condition only: it does not assert that the selected sites
belong to the active-site list.  For generated flat role tables, that membership
follows from the `active` field of `Figure18RobinsonBoardRoutedFreeGrid`.
-/
def HasLocallyCompatibleRobinsonBoardRoutedFreeGrids
    (table : Figure18RoleTable) : Prop :=
  ∀ {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed)}
    {n : Nat} {hn : 0 < n}
    (grid : Figure18RobinsonBoardRoutedFreeGrid table x n hn),
      (∀ i : Fin n, ∀ j : Fin n, ∀ hi : i.val + 1 < n,
        Figure18Site.hCompatible
          (siteRectangleOfIndexedRoutedFixedCornerSquare
            grid.toIndexedRoutedFixedCornerSquare i j)
          (siteRectangleOfIndexedRoutedFixedCornerSquare
            grid.toIndexedRoutedFixedCornerSquare ⟨i.val + 1, hi⟩ j) =
            true) ∧
      (∀ i : Fin n, ∀ j : Fin n, ∀ hj : j.val + 1 < n,
        Figure18Site.vCompatible
          (siteRectangleOfIndexedRoutedFixedCornerSquare
            grid.toIndexedRoutedFixedCornerSquare i j)
          (siteRectangleOfIndexedRoutedFixedCornerSquare
            grid.toIndexedRoutedFixedCornerSquare i ⟨j.val + 1, hj⟩) =
            true)

/--
Level-indexed local compatibility of Robinson's virtual neighboring sites.

This matches Section 7 more directly than
`HasLocallyCompatibleRobinsonBoardRoutedFreeGrids`: only the canonical free
grid at each red-board level has to be checked.  Smaller requested payload
windows are obtained by restriction.
-/
def HasLocallyCompatibleRobinsonBoardLevelRoutedFreeGrids
    (table : Figure18RoleTable) : Prop :=
  ∀ {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed)}
    (level : Nat)
    (grid : Figure18RobinsonBoardRoutedFreeGrid table x
      (RobinsonSquare.freeGridSide level)
      (RobinsonSquare.freeGridSide_pos level)),
      (∀ i : Fin (RobinsonSquare.freeGridSide level),
        ∀ j : Fin (RobinsonSquare.freeGridSide level),
        ∀ hi : i.val + 1 < RobinsonSquare.freeGridSide level,
          Figure18Site.hCompatible
            (siteRectangleOfIndexedRoutedFixedCornerSquare
              grid.toIndexedRoutedFixedCornerSquare i j)
            (siteRectangleOfIndexedRoutedFixedCornerSquare
              grid.toIndexedRoutedFixedCornerSquare ⟨i.val + 1, hi⟩ j) =
              true) ∧
      (∀ i : Fin (RobinsonSquare.freeGridSide level),
        ∀ j : Fin (RobinsonSquare.freeGridSide level),
        ∀ hj : j.val + 1 < RobinsonSquare.freeGridSide level,
          Figure18Site.vCompatible
            (siteRectangleOfIndexedRoutedFixedCornerSquare
              grid.toIndexedRoutedFixedCornerSquare i j)
            (siteRectangleOfIndexedRoutedFixedCornerSquare
              grid.toIndexedRoutedFixedCornerSquare i ⟨j.val + 1, hj⟩) =
              true)

/--
Robinson routed free-grid witnesses whose selected site rectangles are allowed
by the active/corner data and locally compatible for the generated layer-stack
checker.
-/
def HasAllowedRobinsonBoardRoutedFreeGrids
    (activeSiteData : Figure18Site.CheckedNatSpecs)
    (cornerSite : Figure18Site) (table : Figure18RoleTable) : Prop :=
  ∀ {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed)}
    {n : Nat} {hn : 0 < n}
    (grid : Figure18RobinsonBoardRoutedFreeGrid table x n hn),
      (∀ i : Fin n, ∀ j : Fin n,
        siteRectangleOfIndexedRoutedFixedCornerSquare
            grid.toIndexedRoutedFixedCornerSquare i j =
          cornerSite ∨
        siteRectangleOfIndexedRoutedFixedCornerSquare
            grid.toIndexedRoutedFixedCornerSquare i j ∈
          activeSiteData.sites) ∧
      (∀ i : Fin n, ∀ j : Fin n, ∀ hi : i.val + 1 < n,
        Figure18Site.hCompatible
          (siteRectangleOfIndexedRoutedFixedCornerSquare
            grid.toIndexedRoutedFixedCornerSquare i j)
          (siteRectangleOfIndexedRoutedFixedCornerSquare
            grid.toIndexedRoutedFixedCornerSquare ⟨i.val + 1, hi⟩ j) =
            true) ∧
      (∀ i : Fin n, ∀ j : Fin n, ∀ hj : j.val + 1 < n,
        Figure18Site.vCompatible
          (siteRectangleOfIndexedRoutedFixedCornerSquare
            grid.toIndexedRoutedFixedCornerSquare i j)
          (siteRectangleOfIndexedRoutedFixedCornerSquare
            grid.toIndexedRoutedFixedCornerSquare i ⟨j.val + 1, hj⟩) =
            true)

/--
Level-indexed version of `HasAllowedRobinsonBoardRoutedFreeGrids`.

Robinson's board proof naturally produces a full free-grid at each board level.
This predicate asks only those canonical level grids to have allowed and locally
compatible Figure 18 sites.  Arbitrary requested finite windows are then handled
by restricting the level grid.
-/
def HasAllowedRobinsonBoardLevelRoutedFreeGrids
    (activeSiteData : Figure18Site.CheckedNatSpecs)
    (cornerSite : Figure18Site) (table : Figure18RoleTable) : Prop :=
  ∀ {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed)}
    (level : Nat)
    (grid : Figure18RobinsonBoardRoutedFreeGrid table x
      (RobinsonSquare.freeGridSide level)
      (RobinsonSquare.freeGridSide_pos level)),
      (∀ i : Fin (RobinsonSquare.freeGridSide level),
        ∀ j : Fin (RobinsonSquare.freeGridSide level),
          siteRectangleOfIndexedRoutedFixedCornerSquare
              grid.toIndexedRoutedFixedCornerSquare i j =
            cornerSite ∨
          siteRectangleOfIndexedRoutedFixedCornerSquare
              grid.toIndexedRoutedFixedCornerSquare i j ∈
            activeSiteData.sites) ∧
      (∀ i : Fin (RobinsonSquare.freeGridSide level),
        ∀ j : Fin (RobinsonSquare.freeGridSide level),
        ∀ hi : i.val + 1 < RobinsonSquare.freeGridSide level,
          Figure18Site.hCompatible
            (siteRectangleOfIndexedRoutedFixedCornerSquare
              grid.toIndexedRoutedFixedCornerSquare i j)
            (siteRectangleOfIndexedRoutedFixedCornerSquare
              grid.toIndexedRoutedFixedCornerSquare ⟨i.val + 1, hi⟩ j) =
              true) ∧
      (∀ i : Fin (RobinsonSquare.freeGridSide level),
        ∀ j : Fin (RobinsonSquare.freeGridSide level),
        ∀ hj : j.val + 1 < RobinsonSquare.freeGridSide level,
          Figure18Site.vCompatible
            (siteRectangleOfIndexedRoutedFixedCornerSquare
              grid.toIndexedRoutedFixedCornerSquare i j)
            (siteRectangleOfIndexedRoutedFixedCornerSquare
              grid.toIndexedRoutedFixedCornerSquare i ⟨j.val + 1, hj⟩) =
              true)

theorem hasAllowedRobinsonBoardRoutedFreeGrids_of_flatRoleTable
    (activeSiteData : Figure18Site.CheckedNatSpecs)
    (cornerSite : Figure18Site)
    (hcompatible :
      HasLocallyCompatibleRobinsonBoardRoutedFreeGrids
        (Figure18RoleTable.FlatRoleTable.ofActiveSites
          activeSiteData.sites cornerSite).toRoleTable) :
    HasAllowedRobinsonBoardRoutedFreeGrids activeSiteData cornerSite
      (Figure18RoleTable.FlatRoleTable.ofActiveSites
        activeSiteData.sites cornerSite).toRoleTable := by
  intro T seed x n hn grid
  rcases hcompatible grid with ⟨hh, hv⟩
  refine ⟨?_, hh, hv⟩
  intro i j
  have hactiveRole :
      CellRole.isActive
        ((Figure18RoleTable.FlatRoleTable.ofActiveSites
          activeSiteData.sites cornerSite).toRoleTable.roleAtSite
            (siteRectangleOfIndexedRoutedFixedCornerSquare
              grid.toIndexedRoutedFixedCornerSquare i j)) = true := by
    simpa [Figure18RobinsonBoardRoutedFreeGrid.toIndexedRoutedFixedCornerSquare,
      Figure18IndexedRoutedFixedCornerSquare.ofSiteMatches,
      siteRectangleOfIndexedRoutedFixedCornerSquare] using grid.active i j
  exact (Figure18RoleTable.isActive_roleOfActiveSites_iff
    activeSiteData.sites cornerSite
    (siteRectangleOfIndexedRoutedFixedCornerSquare
      grid.toIndexedRoutedFixedCornerSquare i j)).1
    (by
      simpa [Figure18RoleTable.FlatRoleTable.ofActiveSites_roleAtSite]
        using hactiveRole)

theorem hasAllowedRobinsonBoardLevelRoutedFreeGrids_of_flatRoleTable
    (activeSiteData : Figure18Site.CheckedNatSpecs)
    (cornerSite : Figure18Site)
    (hcompatible :
      HasLocallyCompatibleRobinsonBoardLevelRoutedFreeGrids
        (Figure18RoleTable.FlatRoleTable.ofActiveSites
          activeSiteData.sites cornerSite).toRoleTable) :
    HasAllowedRobinsonBoardLevelRoutedFreeGrids activeSiteData cornerSite
      (Figure18RoleTable.FlatRoleTable.ofActiveSites
        activeSiteData.sites cornerSite).toRoleTable := by
  intro T seed x level grid
  rcases hcompatible level grid with ⟨hh, hv⟩
  refine ⟨?_, hh, hv⟩
  intro i j
  have hactiveRole :
      CellRole.isActive
        ((Figure18RoleTable.FlatRoleTable.ofActiveSites
          activeSiteData.sites cornerSite).toRoleTable.roleAtSite
            (siteRectangleOfIndexedRoutedFixedCornerSquare
              grid.toIndexedRoutedFixedCornerSquare i j)) = true := by
    simpa [Figure18RobinsonBoardRoutedFreeGrid.toIndexedRoutedFixedCornerSquare,
      Figure18IndexedRoutedFixedCornerSquare.ofSiteMatches,
      siteRectangleOfIndexedRoutedFixedCornerSquare] using grid.active i j
  exact (Figure18RoleTable.isActive_roleOfActiveSites_iff
    activeSiteData.sites cornerSite
    (siteRectangleOfIndexedRoutedFixedCornerSquare
      grid.toIndexedRoutedFixedCornerSquare i j)).1
    (by
      simpa [Figure18RoleTable.FlatRoleTable.ofActiveSites_roleAtSite]
        using hactiveRole)

theorem sparseRawDataOfSites_hasIndexedRoutedCheckedStacks_of_allowedRouted
    (activeSiteData : Figure18Site.CheckedNatSpecs)
    (cornerSite : Figure18Site)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool activeSiteData cornerSite =
        true)
    {table : Figure18RoleTable}
    (hallowed :
      HasAllowedIndexedRoutedFixedCornerSquares activeSiteData cornerSite table) :
    (sparseRawDataOfSites activeSiteData cornerSite).HasIndexedRoutedFixedCornerSquareCheckedStacks
      table := by
  intro T seed x hx n hn
  rcases hallowed x hx n hn with ⟨window, hsites, hh, hv⟩
  let R := siteRectangleOfIndexedRoutedFixedCornerSquare window
  rcases sparseRawDataOfSites_exists_compatible_checkedLayerStackRectangle
      activeSiteData cornerSite hcheck R hsites hh hv with
    ⟨stackData, hsite, hmatch, hcompatible⟩
  exact ⟨window, stackData, hsite, hmatch, hcompatible⟩

theorem sparseRawDataOfSites_hasCheckedStacksForRobinsonBoardRoutedFreeGrids_of_allowed
    (activeSiteData : Figure18Site.CheckedNatSpecs)
    (cornerSite : Figure18Site)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool activeSiteData cornerSite =
        true)
    {table : Figure18RoleTable}
    (hallowed :
      HasAllowedRobinsonBoardRoutedFreeGrids activeSiteData cornerSite table) :
    (sparseRawDataOfSites
      activeSiteData cornerSite).HasCheckedStacksForRobinsonBoardRoutedFreeGrids
      table := by
  intro T seed x n hn grid
  rcases hallowed grid with ⟨hsites, hh, hv⟩
  let window := grid.toIndexedRoutedFixedCornerSquare
  let R := siteRectangleOfIndexedRoutedFixedCornerSquare window
  rcases sparseRawDataOfSites_exists_compatible_checkedLayerStackRectangle
      activeSiteData cornerSite hcheck R hsites hh hv with
    ⟨stackData, hsite, hmatch, hcompatible⟩
  exact ⟨stackData, hsite, hmatch, hcompatible⟩

theorem sparseRawDataOfSites_hasRobinsonBoardRoutedFreeGridCheckedStacks_of_level
    (activeSiteData : Figure18Site.CheckedNatSpecs)
    (cornerSite : Figure18Site)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool activeSiteData cornerSite =
        true)
    {table : Figure18RoleTable}
    (hgrids : HasFigure18RobinsonBoardLevelRoutedFreeGridsForTable table)
    (hallowed :
      HasAllowedRobinsonBoardLevelRoutedFreeGrids activeSiteData cornerSite
        table) :
    (sparseRawDataOfSites
      activeSiteData cornerSite).HasRobinsonBoardRoutedFreeGridCheckedStacks
      table := by
  intro T seed x hx n hn
  rcases RobinsonSquare.exists_level_with_payload_capacity n with
    ⟨level, hcap⟩
  rcases hgrids x hx level with ⟨bigGrid⟩
  let grid := bigGrid.restrict hn hcap
  rcases hallowed level bigGrid with ⟨hsitesBig, hhBig, hvBig⟩
  have hsites : ∀ i : Fin n, ∀ j : Fin n,
      siteRectangleOfIndexedRoutedFixedCornerSquare
          grid.toIndexedRoutedFixedCornerSquare i j =
        cornerSite ∨
      siteRectangleOfIndexedRoutedFixedCornerSquare
          grid.toIndexedRoutedFixedCornerSquare i j ∈
        activeSiteData.sites := by
    intro i j
    simpa [grid, Figure18RobinsonBoardRoutedFreeGrid.restrict,
      Figure18RobinsonBoardRoutedFreeGrid.toIndexedRoutedFixedCornerSquare,
      Figure18IndexedRoutedFixedCornerSquare.ofSiteMatches,
      siteRectangleOfIndexedRoutedFixedCornerSquare] using
      hsitesBig (Fin.castLE hcap i) (Fin.castLE hcap j)
  have hh : ∀ i : Fin n, ∀ j : Fin n, ∀ hi : i.val + 1 < n,
      Figure18Site.hCompatible
        (siteRectangleOfIndexedRoutedFixedCornerSquare
          grid.toIndexedRoutedFixedCornerSquare i j)
        (siteRectangleOfIndexedRoutedFixedCornerSquare
          grid.toIndexedRoutedFixedCornerSquare ⟨i.val + 1, hi⟩ j) =
          true := by
    intro i j hi
    have hiBig : (Fin.castLE hcap i).val + 1 <
        RobinsonSquare.freeGridSide level :=
      Nat.lt_of_lt_of_le hi hcap
    simpa [grid, Figure18RobinsonBoardRoutedFreeGrid.restrict,
      Figure18RobinsonBoardRoutedFreeGrid.toIndexedRoutedFixedCornerSquare,
      Figure18IndexedRoutedFixedCornerSquare.ofSiteMatches,
      siteRectangleOfIndexedRoutedFixedCornerSquare, Fin.castLE] using
      hhBig (Fin.castLE hcap i) (Fin.castLE hcap j) hiBig
  have hv : ∀ i : Fin n, ∀ j : Fin n, ∀ hj : j.val + 1 < n,
      Figure18Site.vCompatible
        (siteRectangleOfIndexedRoutedFixedCornerSquare
          grid.toIndexedRoutedFixedCornerSquare i j)
        (siteRectangleOfIndexedRoutedFixedCornerSquare
          grid.toIndexedRoutedFixedCornerSquare i ⟨j.val + 1, hj⟩) =
          true := by
    intro i j hj
    have hjBig : (Fin.castLE hcap j).val + 1 <
        RobinsonSquare.freeGridSide level :=
      Nat.lt_of_lt_of_le hj hcap
    simpa [grid, Figure18RobinsonBoardRoutedFreeGrid.restrict,
      Figure18RobinsonBoardRoutedFreeGrid.toIndexedRoutedFixedCornerSquare,
      Figure18IndexedRoutedFixedCornerSquare.ofSiteMatches,
      siteRectangleOfIndexedRoutedFixedCornerSquare, Fin.castLE] using
      hvBig (Fin.castLE hcap i) (Fin.castLE hcap j) hjBig
  let window := grid.toIndexedRoutedFixedCornerSquare
  let R := siteRectangleOfIndexedRoutedFixedCornerSquare window
  rcases sparseRawDataOfSites_exists_compatible_checkedLayerStackRectangle
      activeSiteData cornerSite hcheck R hsites hh hv with
    ⟨stackData, hsite, hmatch, hcompatible⟩
  exact ⟨grid, stackData, hsite, hmatch, hcompatible⟩

theorem hasAllowedIndexedRoutedFixedCornerSquares_of_flatActiveSite
    (activeSiteData : Figure18Site.CheckedNatSpecs)
    (cornerSite : Figure18Site)
    (hflat :
      HasFigure18FlatActiveSiteFixedCornerSquares
        (Figure18RoleTable.FlatRoleTable.ofActiveSites
          activeSiteData.sites cornerSite)) :
    HasAllowedIndexedRoutedFixedCornerSquares activeSiteData cornerSite
      (Figure18RoleTable.FlatRoleTable.ofActiveSites
        activeSiteData.sites cornerSite).toRoleTable := by
  intro T seed x hx n hn
  rcases hflat x hx n hn with
    ⟨horizontalCoord, verticalCoord, horizontalCoord_succ,
      verticalCoord_succ, activeSites, corner⟩
  let table := Figure18RoleTable.FlatRoleTable.ofActiveSites
    activeSiteData.sites cornerSite
  let window : Figure18FlatActiveSiteFixedCornerSquare table x n hn := {
    horizontalCoord := horizontalCoord
    verticalCoord := verticalCoord
    horizontalCoord_succ := horizontalCoord_succ
    verticalCoord_succ := verticalCoord_succ
    activeSites := activeSites
    cornerSite := corner
  }
  refine ⟨window.toIndexedRoutedFixedCornerSquare hx, ?_, ?_, ?_⟩
  · intro i j
    change
      table.toRoleTable.combinedSite
          (x (horizontalCoord i, verticalCoord j)) =
        cornerSite ∨
      table.toRoleTable.combinedSite
          (x (horizontalCoord i, verticalCoord j)) ∈
        activeSiteData.sites
    exact (Figure18RoleTable.FlatRoleTable.mem_ofActiveSites_activeSites_iff
      activeSiteData.sites cornerSite
      (table.toRoleTable.combinedSite
        (x (horizontalCoord i, verticalCoord j)))).1
      (activeSites i j)
  · intro i j hi
    change
      Figure18Site.hCompatible
        (table.toRoleTable.combinedSite
          (x (horizontalCoord i, verticalCoord j)))
        (table.toRoleTable.combinedSite
          (x (horizontalCoord ⟨i.val + 1, hi⟩, verticalCoord j))) =
        true
    exact table.toRoleTable.combinedSite_hCompatible_of_selectedCoords
      hx horizontalCoord verticalCoord horizontalCoord_succ i j hi
  · intro i j hj
    change
      Figure18Site.vCompatible
        (table.toRoleTable.combinedSite
          (x (horizontalCoord i, verticalCoord j)))
        (table.toRoleTable.combinedSite
          (x (horizontalCoord i, verticalCoord ⟨j.val + 1, hj⟩))) =
        true
    exact table.toRoleTable.combinedSite_vCompatible_of_selectedCoords
      hx horizontalCoord verticalCoord verticalCoord_succ i j hj

theorem hasAllowedIndexedRoutedFixedCornerSquares_of_listedActiveSite
    (activeSiteData : Figure18Site.CheckedNatSpecs)
    (cornerSite : Figure18Site)
    (hlisted :
      HasFigure18ListedActiveSiteFixedCornerSquares
        activeSiteData.sites cornerSite) :
    HasAllowedIndexedRoutedFixedCornerSquares activeSiteData cornerSite
      (Figure18RoleTable.FlatRoleTable.ofActiveSites
        activeSiteData.sites cornerSite).toRoleTable :=
  hasAllowedIndexedRoutedFixedCornerSquares_of_flatActiveSite
    activeSiteData cornerSite
    (hasFigure18FlatActiveSiteFixedCornerSquares_of_listedActiveSite hlisted)

theorem sparseRawDataOfSites_hasCheckedStacksForListedActiveSiteRectangles_of_generatedCompatibility
    (activeSiteData : Figure18Site.CheckedNatSpecs)
    (cornerSite : Figure18Site)
    (hcompat :
      HasGeneratedStackCompatibilityForListedActiveSiteRectangles
        activeSiteData cornerSite) :
    (sparseRawDataOfSites activeSiteData cornerSite).HasCheckedStacksForListedActiveSiteRectangles
        activeSiteData.sites cornerSite := by
  intro n hn R hsites hcorner hh hv
  refine ⟨checkedLayerStackRectangleOfSiteRectangle R,
    checkedLayerStackRectangleOfSiteRectangle_matchesSite R,
    sparseRawDataOfSites_layerStackRectangleMatchesBool
      activeSiteData cornerSite R,
    ?_⟩
  exact hcompat R hsites hcorner hh hv

theorem
    sparseRawDataOfSites_hasCheckedStacks_of_allowedPairCompatibilityBool
    (activeSiteData : Figure18Site.CheckedNatSpecs)
    (cornerSite : Figure18Site)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool activeSiteData cornerSite =
        true) :
    (sparseRawDataOfSites activeSiteData cornerSite).HasCheckedStacksForListedActiveSiteRectangles
        activeSiteData.sites cornerSite :=
  sparseRawDataOfSites_hasCheckedStacksForListedActiveSiteRectangles_of_generatedCompatibility
    activeSiteData cornerSite
    (hasGeneratedStackCompatibilityForListedActiveSiteRectangles_of_allowedPairCompatibilityBool
      activeSiteData cornerSite hcheck)

/--
Concrete layered scaffold data with the Figure 13 layer transcription fixed and
the finite Figure 18 active-site/corner data supplied as parameters.
-/
def scaffoldDataOfSites
    (activeSiteData : Figure18Site.CheckedNatSpecs)
    (cornerSite : Figure18Site) : LayeredFigure18ScaffoldData :=
  (sparseRawDataOfSites activeSiteData cornerSite).toLayeredFigure18ScaffoldData

theorem scaffoldDataOfSites_layerData
    (activeSiteData : Figure18Site.CheckedNatSpecs)
    (cornerSite : Figure18Site) :
    (scaffoldDataOfSites activeSiteData cornerSite).layerData = layerData :=
  sparseRawDataOfSites_layerData activeSiteData cornerSite

theorem scaffoldDataOfSites_activeSiteData
    (activeSiteData : Figure18Site.CheckedNatSpecs)
    (cornerSite : Figure18Site) :
    (scaffoldDataOfSites activeSiteData cornerSite).activeSiteData =
      activeSiteData :=
  rfl

theorem scaffoldDataOfSites_cornerSite
    (activeSiteData : Figure18Site.CheckedNatSpecs)
    (cornerSite : Figure18Site) :
    (scaffoldDataOfSites activeSiteData cornerSite).cornerSite =
      cornerSite :=
  sparseRawDataOfSites_cornerSite activeSiteData cornerSite

theorem scaffoldDataOfSites_tiles
    (activeSiteData : Figure18Site.CheckedNatSpecs)
    (cornerSite : Figure18Site) :
    (scaffoldDataOfSites activeSiteData cornerSite).scaffold.tiles =
      TileSubdivision.subdivideTileSet fig13Tiles :=
  (scaffoldDataOfSites activeSiteData cornerSite).scaffold_tiles

def scaffoldDataOfSitesCertificateOfCheckedStacks
    (activeSiteData : Figure18Site.CheckedNatSpecs)
    (cornerSite : Figure18Site)
    (hchecked :
      (sparseRawDataOfSites
        activeSiteData cornerSite).HasIndexedActiveWindowCheckedStacks
          (scaffoldDataOfSites activeSiteData cornerSite).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfSites activeSiteData cornerSite).table.presentation.toScaffold) :
    (scaffoldDataOfSites activeSiteData cornerSite).Certificate :=
  CheckedSparseRawData.certificateOfCheckedIndexedActiveStacks
    (sparseRawDataOfSites activeSiteData cornerSite) hchecked realizes

def scaffoldDataOfSitesIndexedRoutedCertificateOfCheckedStacks
    (activeSiteData : Figure18Site.CheckedNatSpecs)
    (cornerSite : Figure18Site)
    (hchecked :
      (sparseRawDataOfSites
        activeSiteData cornerSite).HasIndexedRoutedFixedCornerSquareCheckedStacks
          (scaffoldDataOfSites activeSiteData cornerSite).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfSites activeSiteData cornerSite).table.presentation.toScaffold) :
    (scaffoldDataOfSites activeSiteData cornerSite).IndexedRoutedCertificate :=
  CheckedSparseRawData.indexedRoutedCertificateOfCheckedStacks
    (sparseRawDataOfSites activeSiteData cornerSite) hchecked realizes

def scaffoldDataOfSitesIndexedRoutedCertificateOfRobinsonBoardRoutedFreeGridCheckedStacks
    (activeSiteData : Figure18Site.CheckedNatSpecs)
    (cornerSite : Figure18Site)
    (hchecked :
      (sparseRawDataOfSites
        activeSiteData cornerSite).HasRobinsonBoardRoutedFreeGridCheckedStacks
          (scaffoldDataOfSites activeSiteData cornerSite).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfSites activeSiteData cornerSite).table.presentation.toScaffold) :
    (scaffoldDataOfSites activeSiteData cornerSite).IndexedRoutedCertificate :=
  CheckedSparseRawData.indexedRoutedCertificateOfRobinsonBoardRoutedFreeGridCheckedStacks
    (sparseRawDataOfSites activeSiteData cornerSite) hchecked realizes

def scaffoldDataOfSitesIndexedRoutedCertificateOfAllowedRouted
    (activeSiteData : Figure18Site.CheckedNatSpecs)
    (cornerSite : Figure18Site)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool activeSiteData cornerSite =
        true)
    (hallowed :
      HasAllowedIndexedRoutedFixedCornerSquares activeSiteData cornerSite
        (scaffoldDataOfSites activeSiteData cornerSite).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfSites activeSiteData cornerSite).table.presentation.toScaffold) :
    (scaffoldDataOfSites activeSiteData cornerSite).IndexedRoutedCertificate :=
  scaffoldDataOfSitesIndexedRoutedCertificateOfCheckedStacks
    activeSiteData cornerSite
    (sparseRawDataOfSites_hasIndexedRoutedCheckedStacks_of_allowedRouted
      activeSiteData cornerSite hcheck hallowed)
    realizes

def scaffoldDataOfSitesIndexedRoutedCertificateOfFlatActiveSite
    (activeSiteData : Figure18Site.CheckedNatSpecs)
    (cornerSite : Figure18Site)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool activeSiteData cornerSite =
        true)
    (hflat :
      HasFigure18FlatActiveSiteFixedCornerSquares
        (Figure18RoleTable.FlatRoleTable.ofActiveSites
          activeSiteData.sites cornerSite))
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfSites activeSiteData cornerSite).table.presentation.toScaffold) :
    (scaffoldDataOfSites activeSiteData cornerSite).IndexedRoutedCertificate :=
  scaffoldDataOfSitesIndexedRoutedCertificateOfAllowedRouted
    activeSiteData cornerSite hcheck
    (hasAllowedIndexedRoutedFixedCornerSquares_of_flatActiveSite
      activeSiteData cornerSite hflat)
    realizes

def scaffoldDataOfSitesIndexedRoutedCertificateOfListedActiveSite
    (activeSiteData : Figure18Site.CheckedNatSpecs)
    (cornerSite : Figure18Site)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool activeSiteData cornerSite =
        true)
    (hlisted :
      HasFigure18ListedActiveSiteFixedCornerSquares
        activeSiteData.sites cornerSite)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfSites activeSiteData cornerSite).table.presentation.toScaffold) :
    (scaffoldDataOfSites activeSiteData cornerSite).IndexedRoutedCertificate :=
  scaffoldDataOfSitesIndexedRoutedCertificateOfAllowedRouted
    activeSiteData cornerSite hcheck
    (hasAllowedIndexedRoutedFixedCornerSquares_of_listedActiveSite
      activeSiteData cornerSite hlisted)
    realizes

def scaffoldDataOfSitesIndexedRoutedCertificateOfAdjacentProductWitnessCheckedStacks
    (activeSiteData : Figure18Site.CheckedNatSpecs)
    (cornerSite : Figure18Site)
    (hchecked :
      (sparseRawDataOfSites
        activeSiteData cornerSite).HasAdjacentProductWitnessCheckedStacks
          (scaffoldDataOfSites activeSiteData cornerSite).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfSites activeSiteData cornerSite).table.presentation.toScaffold) :
    (scaffoldDataOfSites activeSiteData cornerSite).IndexedRoutedCertificate :=
  CheckedSparseRawData.indexedRoutedCertificateOfAdjacentProductWitnessCheckedStacks
    (sparseRawDataOfSites activeSiteData cornerSite) hchecked realizes

def scaffoldDataOfSitesIndexedRoutedCertificateOfDecodedSiteCheckedStacks
    (activeSiteData : Figure18Site.CheckedNatSpecs)
    (cornerSite : Figure18Site)
    (hchecked :
      (sparseRawDataOfSites
        activeSiteData cornerSite).HasDecodedSiteCheckedStacks
          (scaffoldDataOfSites activeSiteData cornerSite).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfSites activeSiteData cornerSite).table.presentation.toScaffold) :
    (scaffoldDataOfSites activeSiteData cornerSite).IndexedRoutedCertificate :=
  CheckedSparseRawData.indexedRoutedCertificateOfDecodedSiteCheckedStacks
    (sparseRawDataOfSites activeSiteData cornerSite) hchecked realizes

def scaffoldDataOfSitesIndexedRoutedCertificateOfFlatDecodedSiteCheckedStacks
    (activeSiteData : Figure18Site.CheckedNatSpecs)
    (cornerSite : Figure18Site)
    (hchecked :
      (sparseRawDataOfSites
        activeSiteData cornerSite).HasFlatDecodedSiteCheckedStacks
          (scaffoldDataOfSites activeSiteData cornerSite).flatTable)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfSites activeSiteData cornerSite).table.presentation.toScaffold) :
    (scaffoldDataOfSites activeSiteData cornerSite).IndexedRoutedCertificate :=
  CheckedSparseRawData.indexedRoutedCertificateOfFlatDecodedSiteCheckedStacks
    (sparseRawDataOfSites activeSiteData cornerSite) hchecked realizes

def scaffoldDataOfSitesIndexedRoutedCertificateOfFlatActiveSiteCheckedStacks
    (activeSiteData : Figure18Site.CheckedNatSpecs)
    (cornerSite : Figure18Site)
    (hchecked :
      (sparseRawDataOfSites
        activeSiteData cornerSite).HasFlatActiveSiteCheckedStacks
          (scaffoldDataOfSites activeSiteData cornerSite).flatTable)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfSites activeSiteData cornerSite).table.presentation.toScaffold) :
    (scaffoldDataOfSites activeSiteData cornerSite).IndexedRoutedCertificate :=
  CheckedSparseRawData.indexedRoutedCertificateOfFlatActiveSiteCheckedStacks
    (sparseRawDataOfSites activeSiteData cornerSite) hchecked realizes

def scaffoldDataOfSitesIndexedRoutedCertificateOfListedActiveSiteCheckedStacks
    (activeSiteData : Figure18Site.CheckedNatSpecs)
    (cornerSite : Figure18Site)
    (hchecked :
      (sparseRawDataOfSites
        activeSiteData cornerSite).HasListedActiveSiteCheckedStacks
          activeSiteData.sites cornerSite)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfSites activeSiteData cornerSite).table.presentation.toScaffold) :
    (scaffoldDataOfSites activeSiteData cornerSite).IndexedRoutedCertificate :=
  CheckedSparseRawData.indexedRoutedCertificateOfListedActiveSiteCheckedStacks
    (sparseRawDataOfSites activeSiteData cornerSite) hchecked realizes

def scaffoldDataOfSitesIndexedRoutedCertificateOfListedActiveSiteWindows
    (activeSiteData : Figure18Site.CheckedNatSpecs)
    (cornerSite : Figure18Site)
    (hwindows :
      HasFigure18ListedActiveSiteFixedCornerSquareWindows
        activeSiteData.sites cornerSite)
    (hstacks :
      (sparseRawDataOfSites
        activeSiteData cornerSite).HasCheckedStacksForListedActiveSiteWindows
          activeSiteData.sites cornerSite)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfSites activeSiteData cornerSite).table.presentation.toScaffold) :
    (scaffoldDataOfSites activeSiteData cornerSite).IndexedRoutedCertificate :=
  scaffoldDataOfSitesIndexedRoutedCertificateOfListedActiveSiteCheckedStacks
    activeSiteData cornerSite
    (CheckedSparseRawData.hasListedActiveSiteCheckedStacks_of_windows
      hwindows hstacks)
    realizes

def scaffoldDataOfSitesIndexedRoutedCertificateOfListedActiveSiteRectangles
    (activeSiteData : Figure18Site.CheckedNatSpecs)
    (cornerSite : Figure18Site)
    (hwindows :
      HasFigure18ListedActiveSiteFixedCornerSquareWindows
        activeSiteData.sites cornerSite)
    (hrectangles :
      (sparseRawDataOfSites
        activeSiteData cornerSite).HasCheckedStacksForListedActiveSiteRectangles
          activeSiteData.sites cornerSite)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfSites activeSiteData cornerSite).table.presentation.toScaffold) :
    (scaffoldDataOfSites activeSiteData cornerSite).IndexedRoutedCertificate :=
  scaffoldDataOfSitesIndexedRoutedCertificateOfListedActiveSiteWindows
    activeSiteData cornerSite hwindows
    (CheckedSparseRawData.hasCheckedStacksForListedActiveSiteWindows_of_rectangles
      hrectangles)
    realizes

def scaffoldDataOfSitesIndexedRoutedCertificateOfListedActiveSitePairCompatibility
    (activeSiteData : Figure18Site.CheckedNatSpecs)
    (cornerSite : Figure18Site)
    (hwindows :
      HasFigure18ListedActiveSiteFixedCornerSquareWindows
        activeSiteData.sites cornerSite)
    (hpair :
      generatedStackAllowedSitePairCompatibilityBool activeSiteData cornerSite =
        true)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfSites activeSiteData cornerSite).table.presentation.toScaffold) :
    (scaffoldDataOfSites activeSiteData cornerSite).IndexedRoutedCertificate :=
  scaffoldDataOfSitesIndexedRoutedCertificateOfListedActiveSiteRectangles
    activeSiteData cornerSite hwindows
    (sparseRawDataOfSites_hasCheckedStacks_of_allowedPairCompatibilityBool
      activeSiteData cornerSite hpair)
    realizes

/--
Concrete layered scaffold data from a flat Figure 18 role table.

This is the entry point for a future paper-derived Figure 18 role
transcription: the table determines the active sites and corner site, while the
Figure 13 layer decomposition remains the audited data in this module.
-/
def scaffoldDataOfFlatRoleTable
    (table : Figure18RoleTable.FlatRoleTable) :
    LayeredFigure18ScaffoldData :=
  scaffoldDataOfSites table.activeSiteData table.cornerSite

@[simp]
theorem scaffoldDataOfFlatRoleTable_activeSiteData
    (table : Figure18RoleTable.FlatRoleTable) :
    (scaffoldDataOfFlatRoleTable table).activeSiteData =
      table.activeSiteData :=
  rfl

@[simp]
theorem scaffoldDataOfFlatRoleTable_activeSites
    (table : Figure18RoleTable.FlatRoleTable) :
    (scaffoldDataOfFlatRoleTable table).activeSites =
      table.activeSites := by
  rw [LayeredFigure18ScaffoldData.activeSites_eq]
  simp

@[simp]
theorem scaffoldDataOfFlatRoleTable_cornerSite
    (table : Figure18RoleTable.FlatRoleTable) :
    (scaffoldDataOfFlatRoleTable table).cornerSite =
      table.cornerSite :=
  scaffoldDataOfSites_cornerSite table.activeSiteData table.cornerSite

theorem scaffoldDataOfFlatRoleTable_tiles
    (table : Figure18RoleTable.FlatRoleTable) :
    (scaffoldDataOfFlatRoleTable table).scaffold.tiles =
      TileSubdivision.subdivideTileSet fig13Tiles :=
  scaffoldDataOfSites_tiles table.activeSiteData table.cornerSite

/-- Plain Figure 18 scaffold data from a flat Figure 18 role table. -/
def figure18ScaffoldDataOfFlatRoleTable
    (table : Figure18RoleTable.FlatRoleTable) :
    Figure18ScaffoldData where
  activeSiteData := table.activeSiteData
  cornerSite := table.cornerSite

@[simp]
theorem figure18ScaffoldDataOfFlatRoleTable_activeSiteData
    (table : Figure18RoleTable.FlatRoleTable) :
    (figure18ScaffoldDataOfFlatRoleTable table).activeSiteData =
      table.activeSiteData :=
  rfl

@[simp]
theorem figure18ScaffoldDataOfFlatRoleTable_activeSites
    (table : Figure18RoleTable.FlatRoleTable) :
    (figure18ScaffoldDataOfFlatRoleTable table).activeSites =
      table.activeSites := by
  rw [Figure18ScaffoldData.activeSites]
  simp

@[simp]
theorem figure18ScaffoldDataOfFlatRoleTable_cornerSite
    (table : Figure18RoleTable.FlatRoleTable) :
    (figure18ScaffoldDataOfFlatRoleTable table).cornerSite =
      table.cornerSite :=
  rfl

/--
Remaining obligations for a concrete flat Figure 18 role table.

After the paper's Figure 18 role transcription is entered as a
`FlatRoleTable`, these are the three scaffold-specific facts still needed by
the Wang-tiling reduction: the geometric listed-window invariant, the finite
Figure 13/Figure 16 generated-stack compatibility check, and realization of
active/corner squares by the scaffold.
-/
structure FlatRoleTableObligations
    (table : Figure18RoleTable.FlatRoleTable) : Prop where
  listedWindows :
    (figure18ScaffoldDataOfFlatRoleTable
      table).HasLocalFreeSquareWindowInvariant
  pairCompatibility :
    generatedStackAllowedSitePairCompatibilityBool
      table.activeSiteData table.cornerSite = true
  realizes :
    (figure18ScaffoldDataOfFlatRoleTable table).HasRealizationInvariant

namespace FlatRoleTableObligations

def ofCertificate
    (table : Figure18RoleTable.FlatRoleTable)
    (certificate : (figure18ScaffoldDataOfFlatRoleTable table).Certificate)
    (hpair :
      generatedStackAllowedSitePairCompatibilityBool
        table.activeSiteData table.cornerSite = true) :
    FlatRoleTableObligations table where
  listedWindows :=
    hasFigure18ListedActiveSiteFixedCornerSquareWindows_of_exists
      certificate.localFreeSquares
  pairCompatibility := hpair
  realizes := certificate.realizes

def ofCertificateFailures
    (table : Figure18RoleTable.FlatRoleTable)
    (certificate : (figure18ScaffoldDataOfFlatRoleTable table).Certificate)
    (hfailures :
      generatedStackAllowedSitePairFailures
        table.activeSiteData table.cornerSite = []) :
    FlatRoleTableObligations table :=
  ofCertificate table certificate
    (generatedStackAllowedSitePairCompatibilityBool_of_failures_eq_nil
      hfailures)

end FlatRoleTableObligations

def figure18ScaffoldDataOfFlatRoleTableCertificateOfObligations
    (table : Figure18RoleTable.FlatRoleTable)
    (obligations : FlatRoleTableObligations table) :
    (figure18ScaffoldDataOfFlatRoleTable table).Certificate :=
  Figure18ScaffoldData.Certificate.ofWindows
    (figure18ScaffoldDataOfFlatRoleTable table)
    obligations.listedWindows
    obligations.realizes

def scaffoldDataOfFlatRoleTableIndexedRoutedCertificateOfListedPairCompatibility
    (table : Figure18RoleTable.FlatRoleTable)
    (hwindows :
      HasFigure18ListedActiveSiteFixedCornerSquareWindows
        table.activeSiteData.sites table.cornerSite)
    (hpair :
      generatedStackAllowedSitePairCompatibilityBool
        table.activeSiteData table.cornerSite = true)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfFlatRoleTable table).table.presentation.toScaffold) :
    (scaffoldDataOfFlatRoleTable table).IndexedRoutedCertificate := by
  exact
    scaffoldDataOfSitesIndexedRoutedCertificateOfListedActiveSitePairCompatibility
      table.activeSiteData table.cornerSite
      hwindows
      hpair
      realizes

def scaffoldDataOfFlatRoleTableIndexedRoutedCertificateOfCertificatePairCompatibility
    (table : Figure18RoleTable.FlatRoleTable)
    (certificate : (figure18ScaffoldDataOfFlatRoleTable table).Certificate)
    (hpair :
      generatedStackAllowedSitePairCompatibilityBool
        table.activeSiteData table.cornerSite = true) :
    (scaffoldDataOfFlatRoleTable table).IndexedRoutedCertificate :=
  scaffoldDataOfFlatRoleTableIndexedRoutedCertificateOfListedPairCompatibility
    table
    (hasFigure18ListedActiveSiteFixedCornerSquareWindows_of_exists
      certificate.localFreeSquares)
    hpair
    certificate.realizes

def scaffoldDataOfFlatRoleTableIndexedRoutedCertificateOfCertificateFailures
    (table : Figure18RoleTable.FlatRoleTable)
    (certificate : (figure18ScaffoldDataOfFlatRoleTable table).Certificate)
    (hfailures :
      generatedStackAllowedSitePairFailures
        table.activeSiteData table.cornerSite = []) :
    (scaffoldDataOfFlatRoleTable table).IndexedRoutedCertificate :=
  scaffoldDataOfFlatRoleTableIndexedRoutedCertificateOfCertificatePairCompatibility
    table certificate
    (generatedStackAllowedSitePairCompatibilityBool_of_failures_eq_nil
      hfailures)

def scaffoldDataOfFlatRoleTableIndexedRoutedCertificateOfObligations
    (table : Figure18RoleTable.FlatRoleTable)
    (obligations : FlatRoleTableObligations table) :
    (scaffoldDataOfFlatRoleTable table).IndexedRoutedCertificate :=
  scaffoldDataOfFlatRoleTableIndexedRoutedCertificateOfListedPairCompatibility
    table obligations.listedWindows obligations.pairCompatibility
    obligations.realizes

/--
Plain Figure 18 scaffold data with the Figure 13 layer transcription fixed.

This is the non-layered certificate target: proving its `Certificate` only
requires the listed-active-site local free-square invariant and realization
invariant, while the surrounding concrete data still records that the scaffold
tiles are the human-audited Figure 13 transcription.
-/
def figure18ScaffoldDataOfSites
    (activeSiteData : Figure18Site.CheckedNatSpecs)
    (cornerSite : Figure18Site) : Figure18ScaffoldData :=
  (scaffoldDataOfSites activeSiteData cornerSite).scaffoldData

theorem figure18ScaffoldDataOfSites_activeSiteData
    (activeSiteData : Figure18Site.CheckedNatSpecs)
    (cornerSite : Figure18Site) :
    (figure18ScaffoldDataOfSites activeSiteData cornerSite).activeSiteData =
      activeSiteData :=
  rfl

theorem figure18ScaffoldDataOfSites_cornerSite
    (activeSiteData : Figure18Site.CheckedNatSpecs)
    (cornerSite : Figure18Site) :
    (figure18ScaffoldDataOfSites activeSiteData cornerSite).cornerSite =
      cornerSite :=
  scaffoldDataOfSites_cornerSite activeSiteData cornerSite

theorem figure18ScaffoldDataOfSites_tiles
    (activeSiteData : Figure18Site.CheckedNatSpecs)
    (cornerSite : Figure18Site) :
    (figure18ScaffoldDataOfSites activeSiteData cornerSite).tiles =
      figure18ScaffoldTiles :=
  (figure18ScaffoldDataOfSites activeSiteData cornerSite).tiles_eq

def figure18ScaffoldDataOfSitesCertificateOfWindows
    (activeSiteData : Figure18Site.CheckedNatSpecs)
    (cornerSite : Figure18Site)
    (localFreeSquareWindows :
      (figure18ScaffoldDataOfSites
        activeSiteData cornerSite).HasLocalFreeSquareWindowInvariant)
    (realizes :
      (figure18ScaffoldDataOfSites
        activeSiteData cornerSite).HasRealizationInvariant) :
    (figure18ScaffoldDataOfSites activeSiteData cornerSite).Certificate :=
  Figure18ScaffoldData.Certificate.ofWindows
    (figure18ScaffoldDataOfSites activeSiteData cornerSite)
    localFreeSquareWindows realizes

def figure18ScaffoldDataOfSitesCertificateOfIndexedActiveWindows
    (activeSiteData : Figure18Site.CheckedNatSpecs)
    (cornerSite : Figure18Site)
    (indexedActiveWindows :
      HasFigure18IndexedActiveCornerWindows
        (figure18ScaffoldDataOfSites
          activeSiteData cornerSite).table.toRoleTable)
    (realizes :
      (figure18ScaffoldDataOfSites
        activeSiteData cornerSite).HasRealizationInvariant) :
    (figure18ScaffoldDataOfSites activeSiteData cornerSite).Certificate :=
  Figure18ScaffoldData.Certificate.ofIndexedActiveWindows
    (figure18ScaffoldDataOfSites activeSiteData cornerSite)
    indexedActiveWindows realizes

/-- Checked active-site data from raw Figure 18 site specs. -/
def activeSiteDataOfSpecs
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true) :
    Figure18Site.CheckedNatSpecs where
  specs := activeSiteSpecs
  valid := activeSiteSpecs_valid

/-- Checked corner site from a raw Figure 13 tile index and quadrant. -/
def cornerSiteOfNat
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true) :
    Figure18Site where
  index := ⟨cornerIndex, of_decide_eq_true cornerIndex_valid⟩
  quadrant := cornerQuadrant

@[simp]
theorem activeSiteDataOfSpecs_specs
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true) :
    (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid).specs =
      activeSiteSpecs :=
  rfl

@[simp]
theorem cornerSiteOfNat_index_val
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true) :
    (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid).index.val =
      cornerIndex :=
  rfl

@[simp]
theorem cornerSiteOfNat_quadrant
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true) :
    (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid).quadrant =
      cornerQuadrant :=
  rfl

/-- Raw Nat-indexed form of the distinguished Figure 18 corner site. -/
def cornerNatSpec (cornerIndex : Nat) (cornerQuadrant : Quadrant) :
    Nat × Quadrant :=
  (cornerIndex, cornerQuadrant)

/--
Finite data sanity check for the final Figure 18 Nat-site transcription.

This is intentionally separate from the scaffold obligations: it catches
entry-level mistakes in the raw active-site list before proving any geometric
or generated-stack facts.
-/
def natSiteSpecSanityBool
    (activeSiteSpecs : List (Nat × Quadrant))
    (cornerIndex : Nat) (cornerQuadrant : Quadrant) : Bool :=
  (((Figure18Site.natSpecsValidBool activeSiteSpecs &&
    decide (cornerIndex < 92)) &&
    decide activeSiteSpecs.Nodup) &&
    decide (cornerNatSpec cornerIndex cornerQuadrant ∉ activeSiteSpecs))

/-- Proposition-level form of `natSiteSpecSanityBool`. -/
structure NatSiteSpecSanity
    (activeSiteSpecs : List (Nat × Quadrant))
    (cornerIndex : Nat) (cornerQuadrant : Quadrant) : Prop where
  activeSiteSpecs_valid :
    Figure18Site.natSpecsValidBool activeSiteSpecs = true
  cornerIndex_valid : decide (cornerIndex < 92) = true
  activeSiteSpecs_nodup : activeSiteSpecs.Nodup
  corner_not_active : cornerNatSpec cornerIndex cornerQuadrant ∉ activeSiteSpecs

theorem natSiteSpecSanity_of_bool
    {activeSiteSpecs : List (Nat × Quadrant)}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    (hcheck :
      natSiteSpecSanityBool activeSiteSpecs cornerIndex cornerQuadrant =
        true) :
    NatSiteSpecSanity activeSiteSpecs cornerIndex cornerQuadrant := by
  unfold natSiteSpecSanityBool at hcheck
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hcheck
  exact {
    activeSiteSpecs_valid := hcheck.1.1.1
    cornerIndex_valid := hcheck.1.1.2
    activeSiteSpecs_nodup := of_decide_eq_true hcheck.1.2
    corner_not_active := of_decide_eq_true hcheck.2
  }

namespace NatSiteSpecSanity

def activeSiteData
    {activeSiteSpecs : List (Nat × Quadrant)}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    (sanity : NatSiteSpecSanity activeSiteSpecs cornerIndex cornerQuadrant) :
    Figure18Site.CheckedNatSpecs :=
  activeSiteDataOfSpecs activeSiteSpecs sanity.activeSiteSpecs_valid

def cornerSite
    {activeSiteSpecs : List (Nat × Quadrant)}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    (sanity : NatSiteSpecSanity activeSiteSpecs cornerIndex cornerQuadrant) :
    Figure18Site :=
  cornerSiteOfNat cornerIndex cornerQuadrant sanity.cornerIndex_valid

theorem cornerSite_not_mem_activeSiteData_sites
    {activeSiteSpecs : List (Nat × Quadrant)}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    (sanity : NatSiteSpecSanity activeSiteSpecs cornerIndex cornerQuadrant) :
    sanity.cornerSite ∉ sanity.activeSiteData.sites := by
  intro hmem
  have hspec := sanity.activeSiteData.mem_specs_of_mem_sites hmem
  exact sanity.corner_not_active (by
    simpa [activeSiteData, cornerSite, cornerNatSpec] using hspec)

end NatSiteSpecSanity

/--
Diagnostic active-site candidate from the first L2 summand's local blank
quadrants, with the distinguished corner removed from the raw active list.

This is not asserted to be the final Figure 18 active-site set. It is a named
finite candidate so that the local data-entry and generated-stack audits can be
run in Lean.
-/
def l2Component1BlankCandidateActiveSiteSpecs : List (Nat × Quadrant) :=
  l2Component1BlankSiteSpecs.erase (cornerNatSpec 0 Quadrant.southwest)

theorem l2Component1BlankCandidateActiveSiteSpecs_length :
    l2Component1BlankCandidateActiveSiteSpecs.length = 91 := by
  decide

theorem l2Component1BlankCandidateActiveSiteSpecs_nodup :
    l2Component1BlankCandidateActiveSiteSpecs.Nodup := by
  decide

theorem l2Component1BlankCandidateSanityBool :
    natSiteSpecSanityBool l2Component1BlankCandidateActiveSiteSpecs
      0 Quadrant.southwest = true := by
  decide

def l2Component1BlankCandidateSanity :
    NatSiteSpecSanity l2Component1BlankCandidateActiveSiteSpecs
      0 Quadrant.southwest :=
  natSiteSpecSanity_of_bool l2Component1BlankCandidateSanityBool

def l2Component1BlankCandidateActiveSiteData :
    Figure18Site.CheckedNatSpecs :=
  l2Component1BlankCandidateSanity.activeSiteData

def l2Component1BlankCandidateCornerSite : Figure18Site :=
  l2Component1BlankCandidateSanity.cornerSite

set_option maxRecDepth 20000 in
theorem l2Component1BlankCandidatePairFailures :
    generatedStackAllowedSitePairFailures
      l2Component1BlankCandidateActiveSiteData
      l2Component1BlankCandidateCornerSite = [] := by
  decide

theorem l2Component1BlankCandidatePairCompatibilityBool :
    generatedStackAllowedSitePairCompatibilityBool
      l2Component1BlankCandidateActiveSiteData
      l2Component1BlankCandidateCornerSite = true :=
  generatedStackAllowedSitePairCompatibilityBool_of_failures_eq_nil
    l2Component1BlankCandidatePairFailures

/--
Diagnostic active-site candidate from the second L2 summand's local blank
quadrants, with the distinguished corner removed from the raw active list.
-/
def l2Component2BlankCandidateActiveSiteSpecs : List (Nat × Quadrant) :=
  l2Component2BlankSiteSpecs.erase (cornerNatSpec 0 Quadrant.northeast)

theorem l2Component2BlankCandidateActiveSiteSpecs_length :
    l2Component2BlankCandidateActiveSiteSpecs.length = 91 := by
  decide

theorem l2Component2BlankCandidateActiveSiteSpecs_nodup :
    l2Component2BlankCandidateActiveSiteSpecs.Nodup := by
  decide

theorem l2BlankCandidateActiveSiteSpecs_disjoint :
    l2Component1BlankCandidateActiveSiteSpecs.Disjoint
      l2Component2BlankCandidateActiveSiteSpecs := by
  rw [← List.inter_eq_nil_iff_disjoint]
  decide

theorem l2Component2BlankCandidateSanityBool :
    natSiteSpecSanityBool l2Component2BlankCandidateActiveSiteSpecs
      0 Quadrant.northeast = true := by
  decide

def l2Component2BlankCandidateSanity :
    NatSiteSpecSanity l2Component2BlankCandidateActiveSiteSpecs
      0 Quadrant.northeast :=
  natSiteSpecSanity_of_bool l2Component2BlankCandidateSanityBool

def l2Component2BlankCandidateActiveSiteData :
    Figure18Site.CheckedNatSpecs :=
  l2Component2BlankCandidateSanity.activeSiteData

def l2Component2BlankCandidateCornerSite : Figure18Site :=
  l2Component2BlankCandidateSanity.cornerSite

set_option maxRecDepth 20000 in
theorem l2Component2BlankCandidatePairFailures :
    generatedStackAllowedSitePairFailures
      l2Component2BlankCandidateActiveSiteData
      l2Component2BlankCandidateCornerSite = [] := by
  decide

theorem l2Component2BlankCandidatePairCompatibilityBool :
    generatedStackAllowedSitePairCompatibilityBool
      l2Component2BlankCandidateActiveSiteData
      l2Component2BlankCandidateCornerSite = true :=
  generatedStackAllowedSitePairCompatibilityBool_of_failures_eq_nil
    l2Component2BlankCandidatePairFailures

/--
Generated flat Figure 18 role table from raw Nat-indexed active sites.

This names the `ofActiveSites` route used by the scaffold theorem surface, so
the finite Figure 18 transcription can be stated in terms of Nat-indexed paper
data without re-spelling the generated flat-table construction.
-/
def flatRoleTableOfNatSites
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true) :
    Figure18RoleTable.FlatRoleTable :=
  Figure18RoleTable.FlatRoleTable.ofActiveSites
    (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid).sites
    (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid)

@[simp]
theorem flatRoleTableOfNatSites_cornerSite
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true) :
    (flatRoleTableOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid).cornerSite =
        cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid :=
  rfl

theorem mem_flatRoleTableOfNatSites_activeSites_iff
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (site : Figure18Site) :
    site ∈ (flatRoleTableOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid).activeSites ↔
      site =
        cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid ∨
      site ∈
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid).sites := by
  exact Figure18RoleTable.FlatRoleTable.mem_ofActiveSites_activeSites_iff
    (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid).sites
    (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid)
    site

theorem generatedStackAllowedSitePairCompatibilityBool_flatRoleTableOfNatSites
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (hpair :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true) :
    generatedStackAllowedSitePairCompatibilityBool
      (flatRoleTableOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).activeSiteData
      (flatRoleTableOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).cornerSite = true := by
  rw [flatRoleTableOfNatSites_cornerSite]
  simpa [flatRoleTableOfNatSites] using
    generatedStackAllowedSitePairCompatibilityBool_ofActiveSites
      (activeSiteData :=
        activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
      (cornerSite :=
        cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid)
      hpair

/--
Concrete sparse raw data from raw active-site specs and a raw checked corner.

This is the finite data-entry target for the scaffold transcription: the
Figure 13 layer rows are fixed to `figures/fig13-human.tsv`; only the active
Figure 18 sites and corner remain as paper-derived finite data.
-/
def sparseRawDataOfNatSites
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true) :
    CheckedSparseRawData where
  layerRows := sparseLayerRows
  activeSiteSpecs := activeSiteSpecs
  activeSiteSpecs_valid := activeSiteSpecs_valid
  cornerIndex := cornerIndex
  cornerQuadrant := cornerQuadrant
  cornerIndex_valid := cornerIndex_valid

theorem sparseRawDataOfNatSites_eq_sparseRawDataOfSites
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true) :
    sparseRawDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid =
      sparseRawDataOfSites
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) :=
  rfl

theorem sparseRawDataOfNatSites_layerData
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true) :
    (sparseRawDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid).layerData = layerData := by
  rw [sparseRawDataOfNatSites_eq_sparseRawDataOfSites]
  exact sparseRawDataOfSites_layerData _ _

theorem sparseRawDataOfNatSites_activeSiteSpecs
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true) :
    (sparseRawDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid).activeSiteSpecs =
        activeSiteSpecs :=
  rfl

theorem sparseRawDataOfNatSites_cornerIndex
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true) :
    (sparseRawDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid).cornerIndex =
        cornerIndex :=
  rfl

theorem sparseRawDataOfNatSites_cornerQuadrant
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true) :
    (sparseRawDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid).cornerQuadrant =
        cornerQuadrant :=
  rfl

/-- Concrete layered scaffold data from raw active-site specs and corner. -/
def scaffoldDataOfNatSites
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true) :
    LayeredFigure18ScaffoldData :=
  (sparseRawDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
    cornerIndex cornerQuadrant cornerIndex_valid).toLayeredFigure18ScaffoldData

theorem scaffoldDataOfNatSites_layerData
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true) :
    (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid).layerData = layerData :=
  sparseRawDataOfNatSites_layerData activeSiteSpecs activeSiteSpecs_valid
    cornerIndex cornerQuadrant cornerIndex_valid

theorem scaffoldDataOfNatSites_tiles
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true) :
    (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid).scaffold.tiles =
        TileSubdivision.subdivideTileSet fig13Tiles :=
  (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
    cornerIndex cornerQuadrant cornerIndex_valid).scaffold_tiles

def scaffoldDataOfNatSitesCertificateOfCheckedStacks
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hchecked :
      (sparseRawDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant
        cornerIndex_valid).HasIndexedActiveWindowCheckedStacks
          (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
            cornerIndex cornerQuadrant cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold) :
    (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid).Certificate :=
  CheckedSparseRawData.certificateOfCheckedIndexedActiveStacks
    (sparseRawDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid)
    hchecked realizes

def scaffoldDataOfNatSitesIndexedRoutedCertificateOfCheckedStacks
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hchecked :
      (sparseRawDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant
        cornerIndex_valid).HasIndexedRoutedFixedCornerSquareCheckedStacks
          (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
            cornerIndex cornerQuadrant cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold) :
    (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid).IndexedRoutedCertificate :=
  CheckedSparseRawData.indexedRoutedCertificateOfCheckedStacks
    (sparseRawDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid)
    hchecked realizes

def scaffoldDataOfNatSitesIndexedRoutedCertificateOfRobinsonBoardRoutedFreeGridCheckedStacks
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hchecked :
      (sparseRawDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant
        cornerIndex_valid).HasRobinsonBoardRoutedFreeGridCheckedStacks
          (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
            cornerIndex cornerQuadrant cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold) :
    (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid).IndexedRoutedCertificate :=
  CheckedSparseRawData.indexedRoutedCertificateOfRobinsonBoardRoutedFreeGridCheckedStacks
    (sparseRawDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid)
    hchecked realizes

def scaffoldDataOfNatSitesIndexedRoutedCertificateOfRobinsonBoardRoutedFreeGrids
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hgrids :
      HasFigure18RobinsonBoardRoutedFreeGridsForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hstacks :
      (sparseRawDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant
        cornerIndex_valid).HasCheckedStacksForRobinsonBoardRoutedFreeGrids
          (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
            cornerIndex cornerQuadrant cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold) :
    (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid).IndexedRoutedCertificate :=
  CheckedSparseRawData.indexedRoutedCertificateOfRobinsonBoardRoutedFreeGrids
    (sparseRawDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid)
    hgrids hstacks realizes

def scaffoldDataOfNatSitesIndexedRoutedCertificateOfAllowedRobinsonBoardRoutedFreeGrids
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hgrids :
      HasFigure18RobinsonBoardRoutedFreeGridsForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (hallowed :
      HasAllowedRobinsonBoardRoutedFreeGrids
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid)
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold) :
    (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid).IndexedRoutedCertificate :=
  scaffoldDataOfNatSitesIndexedRoutedCertificateOfRobinsonBoardRoutedFreeGrids
    activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
    cornerIndex_valid hgrids
    (sparseRawDataOfSites_hasCheckedStacksForRobinsonBoardRoutedFreeGrids_of_allowed
      (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
      (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid)
      hcheck hallowed)
    realizes

def scaffoldDataOfNatSitesIndexedRoutedCertificateOfLocallyCompatibleRobinsonBoardRoutedFreeGrids
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hgrids :
      HasFigure18RobinsonBoardRoutedFreeGridsForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (hcompatible :
      HasLocallyCompatibleRobinsonBoardRoutedFreeGrids
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold) :
    (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid).IndexedRoutedCertificate :=
  scaffoldDataOfNatSitesIndexedRoutedCertificateOfAllowedRobinsonBoardRoutedFreeGrids
    activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
    cornerIndex_valid hgrids hcheck
    (hasAllowedRobinsonBoardRoutedFreeGrids_of_flatRoleTable
      (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
      (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid)
      hcompatible)
    realizes

def scaffoldDataOfNatSitesIndexedRoutedCertificateOfAllowedRouted
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (hallowed :
      HasAllowedIndexedRoutedFixedCornerSquares
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid)
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold) :
    (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid).IndexedRoutedCertificate :=
  scaffoldDataOfNatSitesIndexedRoutedCertificateOfCheckedStacks
    activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
    cornerIndex_valid
    (sparseRawDataOfSites_hasIndexedRoutedCheckedStacks_of_allowedRouted
      (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
      (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid)
      hcheck hallowed)
    realizes

def scaffoldDataOfNatSitesIndexedRoutedCertificateOfFlatActiveSite
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (hflat :
      HasFigure18FlatActiveSiteFixedCornerSquares
        (Figure18RoleTable.FlatRoleTable.ofActiveSites
          (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid).sites
          (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid)))
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold) :
    (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid).IndexedRoutedCertificate :=
  scaffoldDataOfNatSitesIndexedRoutedCertificateOfAllowedRouted
    activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
    cornerIndex_valid hcheck
    (hasAllowedIndexedRoutedFixedCornerSquares_of_flatActiveSite
      (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
      (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid)
      hflat)
    realizes

def scaffoldDataOfNatSitesIndexedRoutedCertificateOfListedActiveSite
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (hlisted :
      HasFigure18ListedActiveSiteFixedCornerSquares
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid).sites
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid))
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold) :
    (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid).IndexedRoutedCertificate :=
  scaffoldDataOfNatSitesIndexedRoutedCertificateOfAllowedRouted
    activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
    cornerIndex_valid hcheck
    (hasAllowedIndexedRoutedFixedCornerSquares_of_listedActiveSite
      (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
      (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid)
      hlisted)
    realizes

def scaffoldDataOfNatSitesIndexedRoutedCertificateOfAdjacentProductWitnessCheckedStacks
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hchecked :
      (sparseRawDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant
        cornerIndex_valid).HasAdjacentProductWitnessCheckedStacks
          (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
            cornerIndex cornerQuadrant cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold) :
    (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid).IndexedRoutedCertificate :=
  CheckedSparseRawData.indexedRoutedCertificateOfAdjacentProductWitnessCheckedStacks
    (sparseRawDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid)
    hchecked realizes

def scaffoldDataOfNatSitesIndexedRoutedCertificateOfDecodedSiteCheckedStacks
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hchecked :
      (sparseRawDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant
        cornerIndex_valid).HasDecodedSiteCheckedStacks
          (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
            cornerIndex cornerQuadrant cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold) :
    (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid).IndexedRoutedCertificate :=
  CheckedSparseRawData.indexedRoutedCertificateOfDecodedSiteCheckedStacks
    (sparseRawDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid)
    hchecked realizes

def scaffoldDataOfNatSitesIndexedRoutedCertificateOfFlatDecodedSiteCheckedStacks
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hchecked :
      (sparseRawDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant
        cornerIndex_valid).HasFlatDecodedSiteCheckedStacks
          (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
            cornerIndex cornerQuadrant cornerIndex_valid).flatTable)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold) :
    (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid).IndexedRoutedCertificate :=
  CheckedSparseRawData.indexedRoutedCertificateOfFlatDecodedSiteCheckedStacks
    (sparseRawDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid)
    hchecked realizes

def scaffoldDataOfNatSitesIndexedRoutedCertificateOfFlatActiveSiteCheckedStacks
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hchecked :
      (sparseRawDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant
        cornerIndex_valid).HasFlatActiveSiteCheckedStacks
          (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
            cornerIndex cornerQuadrant cornerIndex_valid).flatTable)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold) :
    (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid).IndexedRoutedCertificate :=
  CheckedSparseRawData.indexedRoutedCertificateOfFlatActiveSiteCheckedStacks
    (sparseRawDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid)
    hchecked realizes

def scaffoldDataOfNatSitesIndexedRoutedCertificateOfListedActiveSiteCheckedStacks
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hchecked :
      (sparseRawDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant
        cornerIndex_valid).HasListedActiveSiteCheckedStacks
          (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid).sites
          (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid))
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold) :
    (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid).IndexedRoutedCertificate :=
  CheckedSparseRawData.indexedRoutedCertificateOfListedActiveSiteCheckedStacks
    (sparseRawDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid)
    hchecked realizes

def scaffoldDataOfNatSitesIndexedRoutedCertificateOfListedActiveSiteWindows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hwindows :
      HasFigure18ListedActiveSiteFixedCornerSquareWindows
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid).sites
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid))
    (hstacks :
      (sparseRawDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant
        cornerIndex_valid).HasCheckedStacksForListedActiveSiteWindows
          (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid).sites
          (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid))
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold) :
    (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid).IndexedRoutedCertificate :=
  scaffoldDataOfNatSitesIndexedRoutedCertificateOfListedActiveSiteCheckedStacks
    activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
    cornerIndex_valid
    (CheckedSparseRawData.hasListedActiveSiteCheckedStacks_of_windows
      hwindows hstacks)
    realizes

def scaffoldDataOfNatSitesIndexedRoutedCertificateOfListedActiveSiteRectangles
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hwindows :
      HasFigure18ListedActiveSiteFixedCornerSquareWindows
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid).sites
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid))
    (hrectangles :
      (sparseRawDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant
        cornerIndex_valid).HasCheckedStacksForListedActiveSiteRectangles
          (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid).sites
          (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid))
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold) :
    (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid).IndexedRoutedCertificate :=
  scaffoldDataOfNatSitesIndexedRoutedCertificateOfListedActiveSiteWindows
    activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
    cornerIndex_valid hwindows
    (CheckedSparseRawData.hasCheckedStacksForListedActiveSiteWindows_of_rectangles
      hrectangles)
    realizes

def scaffoldDataOfNatSitesIndexedRoutedCertificateOfListedActiveSitePairCompatibility
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hwindows :
      HasFigure18ListedActiveSiteFixedCornerSquareWindows
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid).sites
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid))
    (hpair :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) = true)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold) :
    (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid).IndexedRoutedCertificate :=
  scaffoldDataOfNatSitesIndexedRoutedCertificateOfListedActiveSiteRectangles
    activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
    cornerIndex_valid hwindows
    (sparseRawDataOfSites_hasCheckedStacks_of_allowedPairCompatibilityBool
      (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
      (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid)
      hpair)
    realizes

theorem sparseRawDataOfNatSites_hasCheckedStacksForFlatRoleTable
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hpair :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true) :
    (sparseRawDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant
      cornerIndex_valid).HasCheckedStacksForListedActiveSiteWindowsForFlatTable
        (flatRoleTableOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid) := by
  apply CheckedSparseRawData.hasCheckedStacksForListedActiveSiteWindowsForFlatTable_of_rectangles
  intro n hn R hsites hcorner hh hv
  let table :=
    flatRoleTableOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid
  let stackData := checkedLayerStackRectangleOfSiteRectangle R
  refine ⟨stackData, checkedLayerStackRectangleOfSiteRectangle_matchesSite R,
    ?_, ?_⟩
  · simpa [sparseRawDataOfNatSites_eq_sparseRawDataOfSites] using
      sparseRawDataOfSites_layerStackRectangleMatchesBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid)
        R
  · have hpair' :
        generatedStackAllowedSitePairCompatibilityBool
          table.activeSiteData table.cornerSite = true := by
      exact generatedStackAllowedSitePairCompatibilityBool_flatRoleTableOfNatSites
        hpair
    have hsites' : ∀ i : Fin n, ∀ j : Fin n,
        R i j = table.cornerSite ∨ R i j ∈ table.activeSiteData.sites := by
      intro i j
      simpa [table] using hsites i j
    have hcompat :=
      hasGeneratedStackCompatibilityForAllowedSiteRectangles_of_allowedPairCompatibilityBool
        table.activeSiteData table.cornerSite hpair' R hsites' hh hv
    simpa [table, sparseRawDataOfNatSites_layerData,
      sparseRawDataOfSites_layerData] using hcompat

def scaffoldDataOfNatSitesIndexedRoutedCertificateOfFlatRoleTablePairCompatibility
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hwindows :
      HasFigure18ListedActiveSiteFixedCornerSquareWindowsForTable
        (flatRoleTableOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).toRoleTable
        (flatRoleTableOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).activeSites
        (flatRoleTableOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).cornerSite)
    (hpair :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold) :
    (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid).IndexedRoutedCertificate := by
  apply CheckedSparseRawData.indexedRoutedCertificateOfListedActiveSiteCheckedStacksForFlatTable
  · exact CheckedSparseRawData.hasListedActiveSiteCheckedStacksForFlatTable_of_windows
      hwindows
      (sparseRawDataOfNatSites_hasCheckedStacksForFlatRoleTable
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hpair)
  · exact realizes

/-- Plain Figure 18 scaffold data from raw active-site specs and corner. -/
def figure18ScaffoldDataOfNatSites
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true) :
    Figure18ScaffoldData :=
  (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
    cornerIndex cornerQuadrant cornerIndex_valid).scaffoldData

theorem figure18ScaffoldDataOfNatSites_activeSiteSpecs
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true) :
    (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid).activeSiteData.specs =
        activeSiteSpecs :=
  rfl

theorem figure18ScaffoldDataOfNatSites_cornerIndex
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true) :
    (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid).cornerSite.index.val =
        cornerIndex :=
  rfl

theorem figure18ScaffoldDataOfNatSites_cornerQuadrant
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true) :
    (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid).cornerSite.quadrant =
        cornerQuadrant :=
  rfl

theorem figure18ScaffoldDataOfNatSites_tiles
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true) :
    (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid).tiles =
        figure18ScaffoldTiles :=
  (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
    cornerIndex cornerQuadrant cornerIndex_valid).tiles_eq

theorem figure18ScaffoldDataOfNatSites_table
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true) :
    (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid).table =
        flatRoleTableOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid := by
  rfl

def figure18ScaffoldDataOfNatSitesCertificateOfWindows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (localFreeSquareWindows :
      (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).HasLocalFreeSquareWindowInvariant)
    (realizes :
      (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).HasRealizationInvariant) :
    (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid).Certificate :=
  Figure18ScaffoldData.Certificate.ofWindows
    (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid)
    localFreeSquareWindows realizes

def figure18ScaffoldDataOfNatSitesCertificateOfIndexedActiveWindows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (indexedActiveWindows :
      HasFigure18IndexedActiveCornerWindows
        (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.toRoleTable)
    (realizes :
      (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).HasRealizationInvariant) :
    (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid).Certificate :=
  Figure18ScaffoldData.Certificate.ofIndexedActiveWindows
    (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid)
    indexedActiveWindows realizes

/--
Bundled scaffold-side obligations for raw Nat-indexed Figure 18 site data.

This is the theorem-facing package intended for the final concrete Figure 18
instantiation: the listed-window geometric invariant, the finite generated
Figure 13/Figure 16 stack compatibility check, and the active/corner
realization invariant.
-/
structure NatSiteObligations
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true) : Prop where
  listedWindows :
    (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid).HasLocalFreeSquareWindowInvariant
  pairCompatibility :
    generatedStackAllowedSitePairCompatibilityBool
      (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
      (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
        true
  realizes :
    (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid).HasRealizationInvariant

namespace NatSiteObligations

def ofCertificate
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (certificate :
      (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).Certificate)
    (hpair :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true) :
    NatSiteObligations activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid where
  listedWindows :=
    hasFigure18ListedActiveSiteFixedCornerSquareWindows_of_exists
      certificate.localFreeSquares
  pairCompatibility := hpair
  realizes := certificate.realizes

def ofCertificateFailures
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (certificate :
      (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).Certificate)
    (hfailures :
      generatedStackAllowedSitePairFailures
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          []) :
    NatSiteObligations activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid :=
  ofCertificate activeSiteSpecs activeSiteSpecs_valid
    cornerIndex cornerQuadrant cornerIndex_valid certificate
    (generatedStackAllowedSitePairCompatibilityBool_of_failures_eq_nil
      hfailures)

theorem flatRoleTable_pairCompatibility
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (obligations :
      NatSiteObligations activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid) :
    generatedStackAllowedSitePairCompatibilityBool
      (flatRoleTableOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).activeSiteData
      (flatRoleTableOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).cornerSite = true :=
  generatedStackAllowedSitePairCompatibilityBool_flatRoleTableOfNatSites
    obligations.pairCompatibility

theorem flatRoleTable_listedWindowsForTable
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (obligations :
      NatSiteObligations activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid) :
    HasFigure18ListedActiveSiteFixedCornerSquareWindowsForTable
      (flatRoleTableOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).toRoleTable
      (flatRoleTableOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).activeSites
      (flatRoleTableOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).cornerSite := by
  rw [flatRoleTableOfNatSites_cornerSite]
  exact
    hasFigure18ListedActiveSiteFixedCornerSquareWindowsForTable_toGeneratedActiveSites
      obligations.listedWindows

end NatSiteObligations

def figure18ScaffoldDataOfNatSitesCertificateOfObligations
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (obligations :
      NatSiteObligations activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid) :
    (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid).Certificate :=
  Figure18ScaffoldData.Certificate.ofWindows
    (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid)
    obligations.listedWindows obligations.realizes

def scaffoldDataOfNatSitesIndexedRoutedCertificateOfCertificatePairCompatibility
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (certificate :
      (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).Certificate)
    (hpair :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true) :
    (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid).IndexedRoutedCertificate :=
  scaffoldDataOfNatSitesIndexedRoutedCertificateOfListedActiveSitePairCompatibility
    activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
    cornerIndex_valid
    (hasFigure18ListedActiveSiteFixedCornerSquareWindows_of_exists
      certificate.localFreeSquares)
    hpair
    certificate.realizes

def scaffoldDataOfNatSitesIndexedRoutedCertificateOfCertificateFailures
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (certificate :
      (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).Certificate)
    (hfailures :
      generatedStackAllowedSitePairFailures
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          []) :
    (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid).IndexedRoutedCertificate :=
  scaffoldDataOfNatSitesIndexedRoutedCertificateOfCertificatePairCompatibility
    activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
    cornerIndex_valid certificate
    (generatedStackAllowedSitePairCompatibilityBool_of_failures_eq_nil
      hfailures)

def scaffoldDataOfNatSitesIndexedRoutedCertificateOfObligations
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (obligations :
      NatSiteObligations activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid) :
    (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid).IndexedRoutedCertificate :=
  scaffoldDataOfNatSitesIndexedRoutedCertificateOfListedActiveSitePairCompatibility
    activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
    cornerIndex_valid
    obligations.listedWindows
    obligations.pairCompatibility
    obligations.realizes

def scaffoldDataOfNatSitesIndexedRoutedCertificateOfFlatRoleTableObligations
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (obligations :
      NatSiteObligations activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid) :
    (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid).IndexedRoutedCertificate :=
  scaffoldDataOfNatSitesIndexedRoutedCertificateOfFlatRoleTablePairCompatibility
    activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
    cornerIndex_valid
    obligations.flatRoleTable_listedWindowsForTable
    obligations.pairCompatibility
    obligations.realizes

def scaffoldDataOfNatSitesIndexedRoutedCertificateOfFlatRoleTableCertificatePairCompatibility
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (certificate :
      (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).Certificate)
    (hpair :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true) :
    (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid).IndexedRoutedCertificate :=
  scaffoldDataOfNatSitesIndexedRoutedCertificateOfFlatRoleTableObligations
    activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
    cornerIndex_valid
    (NatSiteObligations.ofCertificate
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid certificate hpair)

def scaffoldDataOfNatSitesIndexedRoutedCertificateOfFlatRoleTableCertificateFailures
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (certificate :
      (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).Certificate)
    (hfailures :
      generatedStackAllowedSitePairFailures
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          []) :
    (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid).IndexedRoutedCertificate :=
  scaffoldDataOfNatSitesIndexedRoutedCertificateOfFlatRoleTableObligations
    activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
    cornerIndex_valid
    (NatSiteObligations.ofCertificateFailures
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid certificate hfailures)

namespace NatSiteObligations

def toCertificate
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (obligations :
      NatSiteObligations activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid) :
    (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid).Certificate :=
  figure18ScaffoldDataOfNatSitesCertificateOfObligations
    activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
    cornerIndex_valid obligations

/-- Convert bundled Nat-site obligations through the generated flat-table route. -/
def toIndexedRoutedCertificate
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (obligations :
      NatSiteObligations activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid) :
    (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid).IndexedRoutedCertificate :=
  scaffoldDataOfNatSitesIndexedRoutedCertificateOfFlatRoleTableObligations
    activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
    cornerIndex_valid obligations

/--
Convert bundled Nat-site obligations through the original listed-active route.

The default `toIndexedRoutedCertificate` uses the generated flat-table active
site list, which is closer to the final Figure 18 theorem surface.
-/
def toListedActiveIndexedRoutedCertificate
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (obligations :
      NatSiteObligations activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid) :
    (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid).IndexedRoutedCertificate :=
  scaffoldDataOfNatSitesIndexedRoutedCertificateOfObligations
    activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
    cornerIndex_valid obligations

end NatSiteObligations

/--
Concrete theorem-facing scaffold package for the Figure 13/Figure 18 Nat-site
route.

The fields split the remaining concrete work in the intended way: finite
paper-derived active-site/corner data, the geometric scaffold certificate, and
the generated finite stack-pair audit.
-/
structure NatSiteScaffoldCertificate where
  activeSiteSpecs : List (Nat × Quadrant)
  activeSiteSpecs_valid :
    Figure18Site.natSpecsValidBool activeSiteSpecs = true
  cornerIndex : Nat
  cornerQuadrant : Quadrant
  cornerIndex_valid : decide (cornerIndex < 92) = true
  certificate :
    (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid).Certificate
  pairFailures :
    generatedStackAllowedSitePairFailures
      (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
      (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) = []

namespace NatSiteScaffoldCertificate

def ofWindows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (localFreeSquareWindows :
      (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).HasLocalFreeSquareWindowInvariant)
    (realizes :
      (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).HasRealizationInvariant)
    (pairFailures :
      generatedStackAllowedSitePairFailures
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          []) :
    NatSiteScaffoldCertificate where
  activeSiteSpecs := activeSiteSpecs
  activeSiteSpecs_valid := activeSiteSpecs_valid
  cornerIndex := cornerIndex
  cornerQuadrant := cornerQuadrant
  cornerIndex_valid := cornerIndex_valid
  certificate :=
    figure18ScaffoldDataOfNatSitesCertificateOfWindows
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid localFreeSquareWindows realizes
  pairFailures := pairFailures

def ofIndexedActiveWindows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (indexedActiveWindows :
      HasFigure18IndexedActiveCornerWindows
        (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.toRoleTable)
    (realizes :
      (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).HasRealizationInvariant)
    (pairFailures :
      generatedStackAllowedSitePairFailures
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          []) :
    NatSiteScaffoldCertificate where
  activeSiteSpecs := activeSiteSpecs
  activeSiteSpecs_valid := activeSiteSpecs_valid
  cornerIndex := cornerIndex
  cornerQuadrant := cornerQuadrant
  cornerIndex_valid := cornerIndex_valid
  certificate :=
    figure18ScaffoldDataOfNatSitesCertificateOfIndexedActiveWindows
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid indexedActiveWindows realizes
  pairFailures := pairFailures

def ofObligations
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (obligations :
      NatSiteObligations activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid) :
    NatSiteScaffoldCertificate where
  activeSiteSpecs := activeSiteSpecs
  activeSiteSpecs_valid := activeSiteSpecs_valid
  cornerIndex := cornerIndex
  cornerQuadrant := cornerQuadrant
  cornerIndex_valid := cornerIndex_valid
  certificate := obligations.toCertificate
  pairFailures :=
    generatedStackAllowedSitePairFailures_eq_nil_of_pairCompatibilityBool
      obligations.pairCompatibility

def ofSaneObligations
    (activeSiteSpecs : List (Nat × Quadrant))
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (sanity :
      NatSiteSpecSanity activeSiteSpecs cornerIndex cornerQuadrant)
    (obligations :
      NatSiteObligations activeSiteSpecs sanity.activeSiteSpecs_valid
        cornerIndex cornerQuadrant sanity.cornerIndex_valid) :
    NatSiteScaffoldCertificate :=
  ofObligations activeSiteSpecs sanity.activeSiteSpecs_valid
    cornerIndex cornerQuadrant sanity.cornerIndex_valid obligations

def activeSiteData (C : NatSiteScaffoldCertificate) :
    Figure18Site.CheckedNatSpecs :=
  activeSiteDataOfSpecs C.activeSiteSpecs C.activeSiteSpecs_valid

def cornerSite (C : NatSiteScaffoldCertificate) : Figure18Site :=
  cornerSiteOfNat C.cornerIndex C.cornerQuadrant C.cornerIndex_valid

def scaffoldData (C : NatSiteScaffoldCertificate) :
    LayeredFigure18ScaffoldData :=
  scaffoldDataOfNatSites C.activeSiteSpecs C.activeSiteSpecs_valid
    C.cornerIndex C.cornerQuadrant C.cornerIndex_valid

def figure18ScaffoldData (C : NatSiteScaffoldCertificate) :
    Figure18ScaffoldData :=
  figure18ScaffoldDataOfNatSites C.activeSiteSpecs C.activeSiteSpecs_valid
    C.cornerIndex C.cornerQuadrant C.cornerIndex_valid

def checkedListedActiveSiteInstance (C : NatSiteScaffoldCertificate) :
    Figure18CheckedListedActiveSiteInstance :=
  C.figure18ScaffoldData.toCheckedListedActiveSiteInstance C.certificate

def flexibleInstance (C : NatSiteScaffoldCertificate) :
    Figure18FlexibleInstance :=
  C.checkedListedActiveSiteInstance.toFlexibleInstance

def obligations (C : NatSiteScaffoldCertificate) :
    NatSiteObligations C.activeSiteSpecs C.activeSiteSpecs_valid
      C.cornerIndex C.cornerQuadrant C.cornerIndex_valid :=
  NatSiteObligations.ofCertificateFailures
    C.activeSiteSpecs C.activeSiteSpecs_valid
    C.cornerIndex C.cornerQuadrant C.cornerIndex_valid
    C.certificate C.pairFailures

def indexedRoutedCertificate (C : NatSiteScaffoldCertificate) :
    C.scaffoldData.IndexedRoutedCertificate :=
  scaffoldDataOfNatSitesIndexedRoutedCertificateOfFlatRoleTableCertificateFailures
    C.activeSiteSpecs C.activeSiteSpecs_valid
    C.cornerIndex C.cornerQuadrant C.cornerIndex_valid
    C.certificate C.pairFailures

def listedActiveIndexedRoutedCertificate (C : NatSiteScaffoldCertificate) :
    C.scaffoldData.IndexedRoutedCertificate :=
  scaffoldDataOfNatSitesIndexedRoutedCertificateOfCertificateFailures
    C.activeSiteSpecs C.activeSiteSpecs_valid
    C.cornerIndex C.cornerQuadrant C.cornerIndex_valid
    C.certificate C.pairFailures

theorem pairCompatibility (C : NatSiteScaffoldCertificate) :
    generatedStackAllowedSitePairCompatibilityBool
      C.activeSiteData C.cornerSite = true :=
  generatedStackAllowedSitePairCompatibilityBool_of_failures_eq_nil
    C.pairFailures

theorem scaffoldData_tiles (C : NatSiteScaffoldCertificate) :
    C.scaffoldData.scaffold.tiles = TileSubdivision.subdivideTileSet fig13Tiles :=
  scaffoldDataOfNatSites_tiles C.activeSiteSpecs C.activeSiteSpecs_valid
    C.cornerIndex C.cornerQuadrant C.cornerIndex_valid

theorem figure18ScaffoldData_tiles (C : NatSiteScaffoldCertificate) :
    C.figure18ScaffoldData.tiles = figure18ScaffoldTiles :=
  figure18ScaffoldDataOfNatSites_tiles C.activeSiteSpecs C.activeSiteSpecs_valid
    C.cornerIndex C.cornerQuadrant C.cornerIndex_valid

@[simp]
theorem checkedListedActiveSiteInstance_activeSiteData
    (C : NatSiteScaffoldCertificate) :
    C.checkedListedActiveSiteInstance.activeSiteData = C.activeSiteData :=
  rfl

@[simp]
theorem checkedListedActiveSiteInstance_cornerSite
    (C : NatSiteScaffoldCertificate) :
    C.checkedListedActiveSiteInstance.cornerSite = C.cornerSite :=
  rfl

theorem checkedListedActiveSiteInstance_presentation_tiles
    (C : NatSiteScaffoldCertificate) :
    C.checkedListedActiveSiteInstance.presentation.tiles =
      TileSubdivision.subdivideTileSet fig13Tiles :=
  C.checkedListedActiveSiteInstance.presentation_tiles

theorem isScaffold (C : NatSiteScaffoldCertificate) :
    IsScaffold C.figure18ScaffoldData.scaffold :=
  C.certificate.isScaffold

theorem checkedListedActiveSiteInstance_isScaffold
    (C : NatSiteScaffoldCertificate) :
    IsScaffold C.checkedListedActiveSiteInstance.presentation.toScaffold :=
  C.checkedListedActiveSiteInstance.isScaffold

end NatSiteScaffoldCertificate

/--
Concrete theorem-facing scaffold package for Robinson's routed board/free-grid
route.

This is the clean scaffold-side target after switching to Robinson Section 7:
finite Nat-indexed Figure 18 site data, checked Figure 13/Figure 16 layer
stacks attached to each routed board free-grid witness, and the realization
invariant.  It avoids the older listed-window plus pair-compatibility route.
-/
structure NatSiteRobinsonScaffoldCertificate where
  activeSiteSpecs : List (Nat × Quadrant)
  activeSiteSpecs_valid :
    Figure18Site.natSpecsValidBool activeSiteSpecs = true
  cornerIndex : Nat
  cornerQuadrant : Quadrant
  cornerIndex_valid : decide (cornerIndex < 92) = true
  robinsonStacks :
    (sparseRawDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant
      cornerIndex_valid).HasRobinsonBoardRoutedFreeGridCheckedStacks
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table
  realizes :
    RealizesActiveCornerSquares
      (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold

/--
Bundled Robinson-board/free-grid obligations for raw Nat-indexed Figure 18 site
data.

This is the intended Section 7 target after the generated Figure 13/Figure 16
stack check has been separated out: Robinson geometry supplies arbitrarily large
routed free grids, proves local compatibility of their selected Figure 18 sites,
and realizes payload square tilings on the scaffold.
-/
structure NatSiteRobinsonObligations
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true) : Prop where
  routedFreeGrids :
    HasFigure18RobinsonBoardRoutedFreeGridsForTable
      (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).table
  pairCompatibility :
    generatedStackAllowedSitePairCompatibilityBool
      (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
      (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
        true
  localCompatibility :
    HasLocallyCompatibleRobinsonBoardRoutedFreeGrids
      (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).table
  realizes :
    RealizesActiveCornerSquares
      (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold

/--
Level-indexed Robinson-board/free-grid obligations.

This is the preferred Section 7 surface: Robinson geometry supplies the full
free grid at each board level, and finite checking is required only for those
level grids.  Arbitrary finite payload squares are obtained by restricting a
large enough level grid.
-/
structure NatSiteRobinsonLevelObligations
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true) : Prop where
  levelRoutedFreeGrids :
    HasFigure18RobinsonBoardLevelRoutedFreeGridsForTable
      (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).table
  pairCompatibility :
    generatedStackAllowedSitePairCompatibilityBool
      (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
      (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
        true
  levelAllowed :
    HasAllowedRobinsonBoardLevelRoutedFreeGrids
      (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
      (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid)
      (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).table
  realizes :
    RealizesActiveCornerSquares
      (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold

namespace NatSiteRobinsonObligations

def ofPairFailures
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (routedFreeGrids :
      HasFigure18RobinsonBoardRoutedFreeGridsForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (localCompatibility :
      HasLocallyCompatibleRobinsonBoardRoutedFreeGrids
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold)
    (pairFailures :
      generatedStackAllowedSitePairFailures
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          []) :
    NatSiteRobinsonObligations activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid where
  routedFreeGrids := routedFreeGrids
  pairCompatibility :=
    generatedStackAllowedSitePairCompatibilityBool_of_failures_eq_nil
      pairFailures
  localCompatibility := localCompatibility
  realizes := realizes

def ofL2Component1BlankCandidate
    (routedFreeGrids :
      HasFigure18RobinsonBoardRoutedFreeGridsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (localCompatibility :
      HasLocallyCompatibleRobinsonBoardRoutedFreeGrids
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold) :
    NatSiteRobinsonObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid where
  routedFreeGrids := routedFreeGrids
  pairCompatibility := by
    simpa [l2Component1BlankCandidateActiveSiteData,
      l2Component1BlankCandidateCornerSite, NatSiteSpecSanity.activeSiteData,
      NatSiteSpecSanity.cornerSite] using
      l2Component1BlankCandidatePairCompatibilityBool
  localCompatibility := localCompatibility
  realizes := realizes

def ofL2Component2BlankCandidate
    (routedFreeGrids :
      HasFigure18RobinsonBoardRoutedFreeGridsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (localCompatibility :
      HasLocallyCompatibleRobinsonBoardRoutedFreeGrids
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold) :
    NatSiteRobinsonObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid where
  routedFreeGrids := routedFreeGrids
  pairCompatibility := by
    simpa [l2Component2BlankCandidateActiveSiteData,
      l2Component2BlankCandidateCornerSite, NatSiteSpecSanity.activeSiteData,
      NatSiteSpecSanity.cornerSite] using
      l2Component2BlankCandidatePairCompatibilityBool
  localCompatibility := localCompatibility
  realizes := realizes

end NatSiteRobinsonObligations

namespace NatSiteRobinsonLevelObligations

def ofLocalCompatibility
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (levelRoutedFreeGrids :
      HasFigure18RobinsonBoardLevelRoutedFreeGridsForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (levelLocalCompatibility :
      HasLocallyCompatibleRobinsonBoardLevelRoutedFreeGrids
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true) :
    NatSiteRobinsonLevelObligations activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid where
  levelRoutedFreeGrids := levelRoutedFreeGrids
  pairCompatibility := hcheck
  levelAllowed :=
    hasAllowedRobinsonBoardLevelRoutedFreeGrids_of_flatRoleTable
      (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
      (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid)
      levelLocalCompatibility
  realizes := realizes

def ofPairFailures
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (levelRoutedFreeGrids :
      HasFigure18RobinsonBoardLevelRoutedFreeGridsForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (levelAllowed :
      HasAllowedRobinsonBoardLevelRoutedFreeGrids
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid)
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold)
    (pairFailures :
      generatedStackAllowedSitePairFailures
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          []) :
    NatSiteRobinsonLevelObligations activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid where
  levelRoutedFreeGrids := levelRoutedFreeGrids
  pairCompatibility :=
    generatedStackAllowedSitePairCompatibilityBool_of_failures_eq_nil
      pairFailures
  levelAllowed := levelAllowed
  realizes := realizes

def ofL2Component1BlankCandidate
    (levelRoutedFreeGrids :
      HasFigure18RobinsonBoardLevelRoutedFreeGridsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (levelAllowed :
      HasAllowedRobinsonBoardLevelRoutedFreeGrids
        l2Component1BlankCandidateActiveSiteData
        l2Component1BlankCandidateCornerSite
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold) :
    NatSiteRobinsonLevelObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid where
  levelRoutedFreeGrids := levelRoutedFreeGrids
  pairCompatibility := by
    simpa [l2Component1BlankCandidateActiveSiteData,
      l2Component1BlankCandidateCornerSite, NatSiteSpecSanity.activeSiteData,
      NatSiteSpecSanity.cornerSite] using
      l2Component1BlankCandidatePairCompatibilityBool
  levelAllowed := by
    intro T seed x level grid
    simpa [l2Component1BlankCandidateActiveSiteData,
      l2Component1BlankCandidateCornerSite, NatSiteSpecSanity.activeSiteData,
      NatSiteSpecSanity.cornerSite] using
      (levelAllowed (level := level) (grid := grid))
  realizes := realizes

def ofL2Component1BlankCandidateLocal
    (levelRoutedFreeGrids :
      HasFigure18RobinsonBoardLevelRoutedFreeGridsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (levelLocalCompatibility :
      HasLocallyCompatibleRobinsonBoardLevelRoutedFreeGrids
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold) :
    NatSiteRobinsonLevelObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofLocalCompatibility
    l2Component1BlankCandidateActiveSiteSpecs
    l2Component1BlankCandidateSanity.activeSiteSpecs_valid
    0 Quadrant.southwest
    l2Component1BlankCandidateSanity.cornerIndex_valid
    levelRoutedFreeGrids levelLocalCompatibility realizes
    (by
      simpa [l2Component1BlankCandidateActiveSiteData,
        l2Component1BlankCandidateCornerSite, NatSiteSpecSanity.activeSiteData,
        NatSiteSpecSanity.cornerSite] using
        l2Component1BlankCandidatePairCompatibilityBool)

def ofL2Component2BlankCandidate
    (levelRoutedFreeGrids :
      HasFigure18RobinsonBoardLevelRoutedFreeGridsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (levelAllowed :
      HasAllowedRobinsonBoardLevelRoutedFreeGrids
        l2Component2BlankCandidateActiveSiteData
        l2Component2BlankCandidateCornerSite
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold) :
    NatSiteRobinsonLevelObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid where
  levelRoutedFreeGrids := levelRoutedFreeGrids
  pairCompatibility := by
    simpa [l2Component2BlankCandidateActiveSiteData,
      l2Component2BlankCandidateCornerSite, NatSiteSpecSanity.activeSiteData,
      NatSiteSpecSanity.cornerSite] using
      l2Component2BlankCandidatePairCompatibilityBool
  levelAllowed := by
    intro T seed x level grid
    simpa [l2Component2BlankCandidateActiveSiteData,
      l2Component2BlankCandidateCornerSite, NatSiteSpecSanity.activeSiteData,
      NatSiteSpecSanity.cornerSite] using
      (levelAllowed (level := level) (grid := grid))
  realizes := realizes

def ofL2Component2BlankCandidateLocal
    (levelRoutedFreeGrids :
      HasFigure18RobinsonBoardLevelRoutedFreeGridsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (levelLocalCompatibility :
      HasLocallyCompatibleRobinsonBoardLevelRoutedFreeGrids
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold) :
    NatSiteRobinsonLevelObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofLocalCompatibility
    l2Component2BlankCandidateActiveSiteSpecs
    l2Component2BlankCandidateSanity.activeSiteSpecs_valid
    0 Quadrant.northeast
    l2Component2BlankCandidateSanity.cornerIndex_valid
    levelRoutedFreeGrids levelLocalCompatibility realizes
    (by
      simpa [l2Component2BlankCandidateActiveSiteData,
        l2Component2BlankCandidateCornerSite, NatSiteSpecSanity.activeSiteData,
        NatSiteSpecSanity.cornerSite] using
        l2Component2BlankCandidatePairCompatibilityBool)

end NatSiteRobinsonLevelObligations

namespace NatSiteRobinsonScaffoldCertificate

def ofFreeGrids
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hgrids :
      HasFigure18RobinsonBoardRoutedFreeGridsForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hstacks :
      (sparseRawDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant
        cornerIndex_valid).HasCheckedStacksForRobinsonBoardRoutedFreeGrids
          (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
            cornerIndex cornerQuadrant cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold) :
    NatSiteRobinsonScaffoldCertificate where
  activeSiteSpecs := activeSiteSpecs
  activeSiteSpecs_valid := activeSiteSpecs_valid
  cornerIndex := cornerIndex
  cornerQuadrant := cornerQuadrant
  cornerIndex_valid := cornerIndex_valid
  robinsonStacks :=
    CheckedSparseRawData.hasRobinsonBoardRoutedFreeGridCheckedStacks_of_freeGrids
      hgrids hstacks
  realizes := realizes

def ofAllowedFreeGrids
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hgrids :
      HasFigure18RobinsonBoardRoutedFreeGridsForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (hallowed :
      HasAllowedRobinsonBoardRoutedFreeGrids
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid)
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold) :
    NatSiteRobinsonScaffoldCertificate :=
  ofFreeGrids activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
    cornerIndex_valid hgrids
    (sparseRawDataOfSites_hasCheckedStacksForRobinsonBoardRoutedFreeGrids_of_allowed
      (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
      (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid)
      hcheck hallowed)
    realizes

def ofLocallyCompatibleFreeGrids
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hgrids :
      HasFigure18RobinsonBoardRoutedFreeGridsForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (hcompatible :
      HasLocallyCompatibleRobinsonBoardRoutedFreeGrids
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold) :
    NatSiteRobinsonScaffoldCertificate :=
  ofAllowedFreeGrids activeSiteSpecs activeSiteSpecs_valid cornerIndex
    cornerQuadrant cornerIndex_valid hgrids hcheck
    (hasAllowedRobinsonBoardRoutedFreeGrids_of_flatRoleTable
      (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
      (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid)
      hcompatible)
    realizes

def ofLevelAllowedFreeGrids
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hgrids :
      HasFigure18RobinsonBoardLevelRoutedFreeGridsForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (hallowed :
      HasAllowedRobinsonBoardLevelRoutedFreeGrids
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid)
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold) :
    NatSiteRobinsonScaffoldCertificate where
  activeSiteSpecs := activeSiteSpecs
  activeSiteSpecs_valid := activeSiteSpecs_valid
  cornerIndex := cornerIndex
  cornerQuadrant := cornerQuadrant
  cornerIndex_valid := cornerIndex_valid
  robinsonStacks :=
    sparseRawDataOfSites_hasRobinsonBoardRoutedFreeGridCheckedStacks_of_level
      (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
      (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid)
      hcheck hgrids hallowed
  realizes := realizes

def ofLevelLocallyCompatibleFreeGrids
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hgrids :
      HasFigure18RobinsonBoardLevelRoutedFreeGridsForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (hcompatible :
      HasLocallyCompatibleRobinsonBoardLevelRoutedFreeGrids
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold) :
    NatSiteRobinsonScaffoldCertificate :=
  ofLevelAllowedFreeGrids activeSiteSpecs activeSiteSpecs_valid
    cornerIndex cornerQuadrant cornerIndex_valid hgrids hcheck
    (hasAllowedRobinsonBoardLevelRoutedFreeGrids_of_flatRoleTable
      (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
      (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid)
      hcompatible)
    realizes

def ofObligations
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (obligations :
      NatSiteRobinsonObligations activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid) :
    NatSiteRobinsonScaffoldCertificate :=
  ofLocallyCompatibleFreeGrids activeSiteSpecs activeSiteSpecs_valid
    cornerIndex cornerQuadrant cornerIndex_valid
    obligations.routedFreeGrids obligations.pairCompatibility
    obligations.localCompatibility obligations.realizes

def ofLevelObligations
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (obligations :
      NatSiteRobinsonLevelObligations activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid) :
    NatSiteRobinsonScaffoldCertificate :=
  ofLevelAllowedFreeGrids activeSiteSpecs activeSiteSpecs_valid
    cornerIndex cornerQuadrant cornerIndex_valid
    obligations.levelRoutedFreeGrids obligations.pairCompatibility
    obligations.levelAllowed obligations.realizes

def ofPairFailures
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (routedFreeGrids :
      HasFigure18RobinsonBoardRoutedFreeGridsForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (localCompatibility :
      HasLocallyCompatibleRobinsonBoardRoutedFreeGrids
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold)
    (pairFailures :
      generatedStackAllowedSitePairFailures
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          []) :
    NatSiteRobinsonScaffoldCertificate :=
  ofObligations activeSiteSpecs activeSiteSpecs_valid cornerIndex
    cornerQuadrant cornerIndex_valid
    (NatSiteRobinsonObligations.ofPairFailures activeSiteSpecs
      activeSiteSpecs_valid cornerIndex cornerQuadrant cornerIndex_valid
      routedFreeGrids localCompatibility realizes pairFailures)

def ofL2Component1BlankCandidate
    (routedFreeGrids :
      HasFigure18RobinsonBoardRoutedFreeGridsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (localCompatibility :
      HasLocallyCompatibleRobinsonBoardRoutedFreeGrids
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold) :
    NatSiteRobinsonScaffoldCertificate :=
  ofObligations
    l2Component1BlankCandidateActiveSiteSpecs
    l2Component1BlankCandidateSanity.activeSiteSpecs_valid
    0 Quadrant.southwest
    l2Component1BlankCandidateSanity.cornerIndex_valid
    (NatSiteRobinsonObligations.ofL2Component1BlankCandidate
      routedFreeGrids localCompatibility realizes)

def ofL2Component1BlankCandidateLevel
    (levelRoutedFreeGrids :
      HasFigure18RobinsonBoardLevelRoutedFreeGridsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (levelAllowed :
      HasAllowedRobinsonBoardLevelRoutedFreeGrids
        l2Component1BlankCandidateActiveSiteData
        l2Component1BlankCandidateCornerSite
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold) :
    NatSiteRobinsonScaffoldCertificate :=
  ofLevelObligations
    l2Component1BlankCandidateActiveSiteSpecs
    l2Component1BlankCandidateSanity.activeSiteSpecs_valid
    0 Quadrant.southwest
    l2Component1BlankCandidateSanity.cornerIndex_valid
    (NatSiteRobinsonLevelObligations.ofL2Component1BlankCandidate
      levelRoutedFreeGrids levelAllowed realizes)

def ofL2Component1BlankCandidateLevelLocal
    (levelRoutedFreeGrids :
      HasFigure18RobinsonBoardLevelRoutedFreeGridsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (levelLocalCompatibility :
      HasLocallyCompatibleRobinsonBoardLevelRoutedFreeGrids
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold) :
    NatSiteRobinsonScaffoldCertificate :=
  ofLevelObligations
    l2Component1BlankCandidateActiveSiteSpecs
    l2Component1BlankCandidateSanity.activeSiteSpecs_valid
    0 Quadrant.southwest
    l2Component1BlankCandidateSanity.cornerIndex_valid
    (NatSiteRobinsonLevelObligations.ofL2Component1BlankCandidateLocal
      levelRoutedFreeGrids levelLocalCompatibility realizes)

def ofL2Component2BlankCandidate
    (routedFreeGrids :
      HasFigure18RobinsonBoardRoutedFreeGridsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (localCompatibility :
      HasLocallyCompatibleRobinsonBoardRoutedFreeGrids
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold) :
    NatSiteRobinsonScaffoldCertificate :=
  ofObligations
    l2Component2BlankCandidateActiveSiteSpecs
    l2Component2BlankCandidateSanity.activeSiteSpecs_valid
    0 Quadrant.northeast
    l2Component2BlankCandidateSanity.cornerIndex_valid
    (NatSiteRobinsonObligations.ofL2Component2BlankCandidate
      routedFreeGrids localCompatibility realizes)

def ofL2Component2BlankCandidateLevel
    (levelRoutedFreeGrids :
      HasFigure18RobinsonBoardLevelRoutedFreeGridsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (levelAllowed :
      HasAllowedRobinsonBoardLevelRoutedFreeGrids
        l2Component2BlankCandidateActiveSiteData
        l2Component2BlankCandidateCornerSite
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold) :
    NatSiteRobinsonScaffoldCertificate :=
  ofLevelObligations
    l2Component2BlankCandidateActiveSiteSpecs
    l2Component2BlankCandidateSanity.activeSiteSpecs_valid
    0 Quadrant.northeast
    l2Component2BlankCandidateSanity.cornerIndex_valid
    (NatSiteRobinsonLevelObligations.ofL2Component2BlankCandidate
      levelRoutedFreeGrids levelAllowed realizes)

def ofL2Component2BlankCandidateLevelLocal
    (levelRoutedFreeGrids :
      HasFigure18RobinsonBoardLevelRoutedFreeGridsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (levelLocalCompatibility :
      HasLocallyCompatibleRobinsonBoardLevelRoutedFreeGrids
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold) :
    NatSiteRobinsonScaffoldCertificate :=
  ofLevelObligations
    l2Component2BlankCandidateActiveSiteSpecs
    l2Component2BlankCandidateSanity.activeSiteSpecs_valid
    0 Quadrant.northeast
    l2Component2BlankCandidateSanity.cornerIndex_valid
    (NatSiteRobinsonLevelObligations.ofL2Component2BlankCandidateLocal
      levelRoutedFreeGrids levelLocalCompatibility realizes)

def activeSiteData (C : NatSiteRobinsonScaffoldCertificate) :
    Figure18Site.CheckedNatSpecs :=
  activeSiteDataOfSpecs C.activeSiteSpecs C.activeSiteSpecs_valid

def cornerSite (C : NatSiteRobinsonScaffoldCertificate) : Figure18Site :=
  cornerSiteOfNat C.cornerIndex C.cornerQuadrant C.cornerIndex_valid

def scaffoldData (C : NatSiteRobinsonScaffoldCertificate) :
    LayeredFigure18ScaffoldData :=
  scaffoldDataOfNatSites C.activeSiteSpecs C.activeSiteSpecs_valid
    C.cornerIndex C.cornerQuadrant C.cornerIndex_valid

def figure18ScaffoldData (C : NatSiteRobinsonScaffoldCertificate) :
    Figure18ScaffoldData :=
  figure18ScaffoldDataOfNatSites C.activeSiteSpecs C.activeSiteSpecs_valid
    C.cornerIndex C.cornerQuadrant C.cornerIndex_valid

def indexedRoutedCertificate (C : NatSiteRobinsonScaffoldCertificate) :
    C.scaffoldData.IndexedRoutedCertificate :=
  scaffoldDataOfNatSitesIndexedRoutedCertificateOfRobinsonBoardRoutedFreeGridCheckedStacks
    C.activeSiteSpecs C.activeSiteSpecs_valid
    C.cornerIndex C.cornerQuadrant C.cornerIndex_valid
    C.robinsonStacks C.realizes

def indexedRoutedInstance (C : NatSiteRobinsonScaffoldCertificate) :
    Figure18IndexedRoutedInstance :=
  C.indexedRoutedCertificate.toFigure18IndexedRoutedInstance

def flexibleInstance (C : NatSiteRobinsonScaffoldCertificate) :
    Figure18FlexibleInstance :=
  C.indexedRoutedCertificate.toFigure18FlexibleInstance

theorem scaffoldData_tiles (C : NatSiteRobinsonScaffoldCertificate) :
    C.scaffoldData.scaffold.tiles = TileSubdivision.subdivideTileSet fig13Tiles :=
  scaffoldDataOfNatSites_tiles C.activeSiteSpecs C.activeSiteSpecs_valid
    C.cornerIndex C.cornerQuadrant C.cornerIndex_valid

theorem figure18ScaffoldData_tiles (C : NatSiteRobinsonScaffoldCertificate) :
    C.figure18ScaffoldData.tiles = figure18ScaffoldTiles :=
  figure18ScaffoldDataOfNatSites_tiles C.activeSiteSpecs C.activeSiteSpecs_valid
    C.cornerIndex C.cornerQuadrant C.cornerIndex_valid

theorem indexedRoutedInstance_presentation_tiles
    (C : NatSiteRobinsonScaffoldCertificate) :
    C.indexedRoutedInstance.presentation.tiles =
      TileSubdivision.subdivideTileSet fig13Tiles :=
  C.indexedRoutedInstance.presentation_tiles

theorem isScaffold (C : NatSiteRobinsonScaffoldCertificate) :
    IsScaffold C.scaffoldData.scaffold :=
  C.indexedRoutedCertificate.isScaffold

theorem indexedRoutedInstance_isScaffold
    (C : NatSiteRobinsonScaffoldCertificate) :
    IsScaffold C.indexedRoutedInstance.presentation.toScaffold :=
  C.indexedRoutedInstance.isScaffold

end NatSiteRobinsonScaffoldCertificate

end ConcreteData
end LayeredFigure18ScaffoldData
end Figure13Layers
end OllingerRobinson
end LeanWang
