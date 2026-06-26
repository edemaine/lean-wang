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

def thinBlockAtSite (site : Figure18Site) : Figure16.Block :=
  (LayerComponent.thin (thinComponentAt site.index)).block

def thickBlockAtSite (site : Figure18Site) : Figure16.Block :=
  (LayerComponent.thick (thickComponentAt site.index)).block

def blackBlockAtSite (site : Figure18Site) : Figure16.Block :=
  (LayerComponent.black (blackComponentAt site.index)).block

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

def generatedStackAllowedSites
    (activeSiteData : Figure18Site.CheckedNatSpecs)
    (cornerSite : Figure18Site) : List Figure18Site :=
  cornerSite :: activeSiteData.sites

def generatedStackAllowedSitePairCompatibilityBool
    (activeSiteData : Figure18Site.CheckedNatSpecs)
    (cornerSite : Figure18Site) : Bool :=
  generatedStackSitePairCompatibilityBool
    (generatedStackAllowedSites activeSiteData cornerSite)

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

theorem hasGeneratedStackCompatibilityForListedActiveSiteRectangles_of_allowedPairCompatibilityBool
    (activeSiteData : Figure18Site.CheckedNatSpecs)
    (cornerSite : Figure18Site)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool activeSiteData cornerSite =
        true) :
    HasGeneratedStackCompatibilityForListedActiveSiteRectangles
      activeSiteData cornerSite := by
  intro n hn R hsites _hcorner hh hv
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

end ConcreteData
end LayeredFigure18ScaffoldData
end Figure13Layers
end OllingerRobinson
end LeanWang
