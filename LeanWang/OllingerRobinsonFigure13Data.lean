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

private theorem transcription_eq_of_rows_eq
    {D E : Transcription} (hrows : D.rows = E.rows) : D = E := by
  cases D with
  | mk rows length_eq =>
      cases E with
      | mk rows' length_eq' =>
          simp only at hrows
          subst rows'
          rfl

theorem separateLayerRows_layerData_rows :
    separateLayerRows.layerData.rows = componentRows := by
  decide

theorem separateLayerRows_layerData :
    separateLayerRows.layerData = layerData :=
  transcription_eq_of_rows_eq separateLayerRows_layerData_rows

theorem sparseLayerRows_layerData_rows :
    sparseLayerRows.layerData.rows = componentRows := by
  decide

theorem sparseLayerRows_layerData :
    sparseLayerRows.layerData = layerData :=
  transcription_eq_of_rows_eq sparseLayerRows_layerData_rows

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
  separateLayerData : separateLayerRows.layerData = layerData
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
  separateLayerData := separateLayerRows_layerData
  sparseRowsLayerData := sparseLayerRows_layerData_rows
  sparseLayerData := sparseLayerRows_layerData
  sparseRowsMatchStackRectangles := sparseLayerRows_layerStackRectangleMatchesBool
  sparseRawDataMatchStackRectangles :=
    sparseRawDataOfSites_layerStackRectangleMatchesBool

def thinBlockAtSite (site : Figure18Site) : Figure16.Block :=
  (LayerComponent.thin (thinComponentAt site.index)).block

def thickBlockAtSite (site : Figure18Site) : Figure16.Block :=
  (LayerComponent.thick (thickComponentAt site.index)).block

def blackBlockAtSite (site : Figure18Site) : Figure16.Block :=
  (LayerComponent.black (blackComponentAt site.index)).block

theorem checkedLayerStackRectangleOfSiteRectangle_lookupBool {w h : Nat}
    (R : SiteRectangle w h) :
    (checkedLayerStackRectangleOfSiteRectangle R).lookupBool layerData = true := by
  have hlookup :=
    CheckedSparseSeparateLayerRows.lookupBool_layerData_of_layerStackRectangleMatchesBool
      (rows := sparseLayerRows)
      (sparseLayerRows_layerStackRectangleMatchesBool R)
  simpa [sparseLayerRows_layerData] using hlookup

/--
Canonical compatible Figure 16 layer stack attached to a concrete Figure 13
site rectangle.

The rectangle supplies the layer components via the audited Figure 13 rows.
The explicit compatibility proof is the finite Figure 16 neighbor check for
the induced block grids.
-/
def checkedLayerStackOfSiteRectangle {w h : Nat}
    (R : SiteRectangle w h)
    (hcompatible :
      (checkedLayerStackRectangleOfSiteRectangle R).compatibleBool layerData
        (checkedLayerStackRectangleOfSiteRectangle_lookupBool R) = true) :
    LayerStackRectangle layerData
      (checkedLayerStackRectangleOfSiteRectangle R).siteRectangle :=
  ((checkedLayerStackRectangleOfSiteRectangle R).toTypedLayerStackRectangleOfChecks
    layerData (checkedLayerStackRectangleOfSiteRectangle_lookupBool R)
    hcompatible).toLayerStackRectangle

def layerStackRectangleOfSiteRectangle {w h : Nat}
    (R : SiteRectangle w h)
    (hcompatible :
      (checkedLayerStackRectangleOfSiteRectangle R).compatibleBool layerData
        (checkedLayerStackRectangleOfSiteRectangle_lookupBool R) = true) :
    LayerStackRectangle layerData R := by
  let data := checkedLayerStackRectangleOfSiteRectangle R
  have hsite : data.siteRectangle = R :=
    CheckedNatSiteRectangle.toSiteRectangle_eq_of_matchesSiteRectangleBool
      (checkedLayerStackRectangleOfSiteRectangle_matchesSite R)
  rw [← hsite]
  exact checkedLayerStackOfSiteRectangle R hcompatible

theorem checkedLayerStackOfSiteRectangle_thin_blockGrid {w h : Nat}
    (R : SiteRectangle w h)
    (hcompatible :
      (checkedLayerStackRectangleOfSiteRectangle R).compatibleBool layerData
        (checkedLayerStackRectangleOfSiteRectangle_lookupBool R) = true)
    (i : Fin w) (j : Fin h) :
    (checkedLayerStackOfSiteRectangle R hcompatible).blockGrid .thin i j =
      thinBlockAtSite (R i j) := by
  simp [checkedLayerStackOfSiteRectangle,
    CheckedLayerStackRectangle.toTypedLayerStackRectangleOfChecks,
    CheckedLayerStackRectangle.toTypedLayerStackRectangle,
    TypedLayerStackRectangle.toLayerStackRectangle, LayerStackRectangle.blockGrid,
    TypedLayerComponentRectangle.toLayerComponentRectangle,
    LayerComponentRectangle.blockGrid, CheckedLayerStackRectangle.thinRectangle,
    checkedLayerStackRectangleOfSiteRectangle_thin_componentAt, thinBlockAtSite]

theorem checkedLayerStackOfSiteRectangle_thick_blockGrid {w h : Nat}
    (R : SiteRectangle w h)
    (hcompatible :
      (checkedLayerStackRectangleOfSiteRectangle R).compatibleBool layerData
        (checkedLayerStackRectangleOfSiteRectangle_lookupBool R) = true)
    (i : Fin w) (j : Fin h) :
    (checkedLayerStackOfSiteRectangle R hcompatible).blockGrid .thick i j =
      thickBlockAtSite (R i j) := by
  simp [checkedLayerStackOfSiteRectangle,
    CheckedLayerStackRectangle.toTypedLayerStackRectangleOfChecks,
    CheckedLayerStackRectangle.toTypedLayerStackRectangle,
    TypedLayerStackRectangle.toLayerStackRectangle, LayerStackRectangle.blockGrid,
    TypedLayerComponentRectangle.toLayerComponentRectangle,
    LayerComponentRectangle.blockGrid, CheckedLayerStackRectangle.thickRectangle,
    checkedLayerStackRectangleOfSiteRectangle_thick_componentAt, thickBlockAtSite]

theorem checkedLayerStackOfSiteRectangle_black_blockGrid {w h : Nat}
    (R : SiteRectangle w h)
    (hcompatible :
      (checkedLayerStackRectangleOfSiteRectangle R).compatibleBool layerData
        (checkedLayerStackRectangleOfSiteRectangle_lookupBool R) = true)
    (i : Fin w) (j : Fin h) :
    (checkedLayerStackOfSiteRectangle R hcompatible).blockGrid .black i j =
      blackBlockAtSite (R i j) := by
  simp [checkedLayerStackOfSiteRectangle,
    CheckedLayerStackRectangle.toTypedLayerStackRectangleOfChecks,
    CheckedLayerStackRectangle.toTypedLayerStackRectangle,
    TypedLayerStackRectangle.toLayerStackRectangle, LayerStackRectangle.blockGrid,
    TypedLayerComponentRectangle.toLayerComponentRectangle,
    LayerComponentRectangle.blockGrid, CheckedLayerStackRectangle.blackRectangle,
    checkedLayerStackRectangleOfSiteRectangle_black_componentAt, blackBlockAtSite]

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

/-- Figure 18 quadrant selected by a west/east and south/north offset. -/
def quadrantOfOffset (di dj : Fin 2) : Quadrant :=
  if dj.val = 0 then
    if di.val = 0 then Quadrant.southwest else Quadrant.southeast
  else
    if di.val = 0 then Quadrant.northwest else Quadrant.northeast

/--
Whether a Figure 18 site exposes a requested Figure 16 symbol triple in the
requested quadrant.
-/
def siteMatchesSymbolsBool
    (l2c1 l2c2 l3 : Figure16.Symbol) (quadrant : Quadrant)
    (site : Figure18Site) : Bool :=
  decide (site.quadrant = quadrant) &&
    decide (l2Component1SymbolAtSite site = l2c1) &&
    decide (l2Component2SymbolAtSite site = l2c2) &&
    decide (l3SymbolAtSite site = l3)

/--
First audited Figure 18 site exposing a requested Figure 16 symbol triple in a
requested quadrant, if one exists.
-/
def siteOfSymbols?
    (l2c1 l2c2 l3 : Figure16.Symbol) (quadrant : Quadrant) :
    Option Figure18Site :=
  Figure18Site.all.find? (siteMatchesSymbolsBool l2c1 l2c2 l3 quadrant)

theorem siteMatchesSymbolsBool_eq_true
    {l2c1 l2c2 l3 : Figure16.Symbol} {quadrant : Quadrant}
    {site : Figure18Site}
    (hmatch : siteMatchesSymbolsBool l2c1 l2c2 l3 quadrant site = true) :
    site.quadrant = quadrant ∧
      l2Component1SymbolAtSite site = l2c1 ∧
      l2Component2SymbolAtSite site = l2c2 ∧
      l3SymbolAtSite site = l3 := by
  unfold siteMatchesSymbolsBool at hmatch
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hmatch
  exact ⟨of_decide_eq_true hmatch.1.1.1,
    of_decide_eq_true hmatch.1.1.2,
    of_decide_eq_true hmatch.1.2,
    of_decide_eq_true hmatch.2⟩

theorem siteOfSymbols?_eq_some_quadrant
    {l2c1 l2c2 l3 : Figure16.Symbol} {quadrant : Quadrant}
    {site : Figure18Site}
    (hsite : siteOfSymbols? l2c1 l2c2 l3 quadrant = some site) :
    site.quadrant = quadrant := by
  exact (siteMatchesSymbolsBool_eq_true (List.find?_some hsite)).1

theorem siteOfSymbols?_eq_some_l2Component1
    {l2c1 l2c2 l3 : Figure16.Symbol} {quadrant : Quadrant}
    {site : Figure18Site}
    (hsite : siteOfSymbols? l2c1 l2c2 l3 quadrant = some site) :
    l2Component1SymbolAtSite site = l2c1 := by
  exact (siteMatchesSymbolsBool_eq_true (List.find?_some hsite)).2.1

theorem siteOfSymbols?_eq_some_l2Component2
    {l2c1 l2c2 l3 : Figure16.Symbol} {quadrant : Quadrant}
    {site : Figure18Site}
    (hsite : siteOfSymbols? l2c1 l2c2 l3 quadrant = some site) :
    l2Component2SymbolAtSite site = l2c2 := by
  exact (siteMatchesSymbolsBool_eq_true (List.find?_some hsite)).2.2.1

theorem siteOfSymbols?_eq_some_l3
    {l2c1 l2c2 l3 : Figure16.Symbol} {quadrant : Quadrant}
    {site : Figure18Site}
    (hsite : siteOfSymbols? l2c1 l2c2 l3 quadrant = some site) :
    l3SymbolAtSite site = l3 := by
  exact (siteMatchesSymbolsBool_eq_true (List.find?_some hsite)).2.2.2

/--
Lookup for one Figure 18 site in the doubled Figure 16 expansion of a source
Figure 18 site.
-/
def expandedSourceSite?
    (source : Figure18Site) (di dj : Fin 2) : Option Figure18Site :=
  siteOfSymbols?
    ((thinBlockAtSite source).entry di dj)
    ((thickBlockAtSite source).entry di dj)
    ((blackBlockAtSite source).entry di dj)
    (quadrantOfOffset di dj)

theorem expandedSourceSite?_eq_some_quadrant
    {source target : Figure18Site} {di dj : Fin 2}
    (hsite : expandedSourceSite? source di dj = some target) :
    target.quadrant = quadrantOfOffset di dj := by
  exact siteOfSymbols?_eq_some_quadrant hsite

theorem expandedSourceSite?_eq_some_l2Component1
    {source target : Figure18Site} {di dj : Fin 2}
    (hsite : expandedSourceSite? source di dj = some target) :
    l2Component1SymbolAtSite target =
      (thinBlockAtSite source).entry di dj := by
  exact siteOfSymbols?_eq_some_l2Component1 hsite

theorem expandedSourceSite?_eq_some_l2Component2
    {source target : Figure18Site} {di dj : Fin 2}
    (hsite : expandedSourceSite? source di dj = some target) :
    l2Component2SymbolAtSite target =
      (thickBlockAtSite source).entry di dj := by
  exact siteOfSymbols?_eq_some_l2Component2 hsite

theorem expandedSourceSite?_eq_some_l3
    {source target : Figure18Site} {di dj : Fin 2}
    (hsite : expandedSourceSite? source di dj = some target) :
    l3SymbolAtSite target =
      (blackBlockAtSite source).entry di dj := by
  exact siteOfSymbols?_eq_some_l3 hsite

private theorem expandedSourceSite?_isSome_index_0
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨0, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_1
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨1, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_2
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨2, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_3
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨3, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_4
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨4, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_5
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨5, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_6
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨6, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_7
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨7, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_8
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨8, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_9
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨9, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_10
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨10, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_11
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨11, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_12
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨12, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_13
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨13, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_14
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨14, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_15
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨15, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_16
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨16, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_17
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨17, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_18
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨18, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_19
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨19, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_20
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨20, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_21
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨21, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_22
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨22, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_23
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨23, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_24
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨24, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_25
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨25, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_26
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨26, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_27
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨27, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_28
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨28, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_29
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨29, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_30
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨30, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_31
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨31, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_32
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨32, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_33
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨33, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_34
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨34, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_35
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨35, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_36
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨36, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_37
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨37, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_38
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨38, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_39
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨39, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_40
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨40, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_41
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨41, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_42
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨42, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_43
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨43, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_44
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨44, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_45
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨45, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_46
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨46, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_47
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨47, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_48
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨48, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_49
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨49, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_50
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨50, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_51
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨51, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_52
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨52, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_53
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨53, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_54
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨54, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_55
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨55, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_56
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨56, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_57
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨57, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_58
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨58, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_59
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨59, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_60
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨60, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_61
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨61, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_62
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨62, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_63
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨63, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_64
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨64, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_65
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨65, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_66
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨66, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_67
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨67, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_68
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨68, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_69
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨69, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_70
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨70, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_71
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨71, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_72
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨72, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_73
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨73, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_74
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨74, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_75
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨75, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_76
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨76, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_77
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨77, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_78
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨78, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_79
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨79, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_80
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨80, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_81
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨81, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_82
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨82, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_83
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨83, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_84
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨84, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_85
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨85, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_86
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨86, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_87
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨87, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_88
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨88, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_89
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨89, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_90
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨90, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

private theorem expandedSourceSite?_isSome_index_91
    (quadrant : Quadrant) (di dj : Fin 2) :
    (expandedSourceSite?
      ({ index := ⟨91, by decide⟩, quadrant := quadrant } : Figure18Site)
      di dj).isSome = true := by
  rcases di with ⟨di, hdi⟩
  rcases dj with ⟨dj, hdj⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdi_cases with rfl | rfl <;>
    rcases hdj_cases with rfl | rfl <;>
    cases quadrant <;>
    decide +revert

/--
Every local Figure 16 expansion cell of an audited Figure 13 site has a
matching Figure 18 site in the transcribed table.
-/
theorem expandedSourceSite?_isSome
    (source : Figure18Site) (di dj : Fin 2) :
    (expandedSourceSite? source di dj).isSome = true := by
  rcases source with ⟨index, quadrant⟩
  rcases index with ⟨n, hn⟩
  by_cases h0 : n = 0
  · subst n
    exact expandedSourceSite?_isSome_index_0 quadrant di dj
  by_cases h1 : n = 1
  · subst n
    exact expandedSourceSite?_isSome_index_1 quadrant di dj
  by_cases h2 : n = 2
  · subst n
    exact expandedSourceSite?_isSome_index_2 quadrant di dj
  by_cases h3 : n = 3
  · subst n
    exact expandedSourceSite?_isSome_index_3 quadrant di dj
  by_cases h4 : n = 4
  · subst n
    exact expandedSourceSite?_isSome_index_4 quadrant di dj
  by_cases h5 : n = 5
  · subst n
    exact expandedSourceSite?_isSome_index_5 quadrant di dj
  by_cases h6 : n = 6
  · subst n
    exact expandedSourceSite?_isSome_index_6 quadrant di dj
  by_cases h7 : n = 7
  · subst n
    exact expandedSourceSite?_isSome_index_7 quadrant di dj
  by_cases h8 : n = 8
  · subst n
    exact expandedSourceSite?_isSome_index_8 quadrant di dj
  by_cases h9 : n = 9
  · subst n
    exact expandedSourceSite?_isSome_index_9 quadrant di dj
  by_cases h10 : n = 10
  · subst n
    exact expandedSourceSite?_isSome_index_10 quadrant di dj
  by_cases h11 : n = 11
  · subst n
    exact expandedSourceSite?_isSome_index_11 quadrant di dj
  by_cases h12 : n = 12
  · subst n
    exact expandedSourceSite?_isSome_index_12 quadrant di dj
  by_cases h13 : n = 13
  · subst n
    exact expandedSourceSite?_isSome_index_13 quadrant di dj
  by_cases h14 : n = 14
  · subst n
    exact expandedSourceSite?_isSome_index_14 quadrant di dj
  by_cases h15 : n = 15
  · subst n
    exact expandedSourceSite?_isSome_index_15 quadrant di dj
  by_cases h16 : n = 16
  · subst n
    exact expandedSourceSite?_isSome_index_16 quadrant di dj
  by_cases h17 : n = 17
  · subst n
    exact expandedSourceSite?_isSome_index_17 quadrant di dj
  by_cases h18 : n = 18
  · subst n
    exact expandedSourceSite?_isSome_index_18 quadrant di dj
  by_cases h19 : n = 19
  · subst n
    exact expandedSourceSite?_isSome_index_19 quadrant di dj
  by_cases h20 : n = 20
  · subst n
    exact expandedSourceSite?_isSome_index_20 quadrant di dj
  by_cases h21 : n = 21
  · subst n
    exact expandedSourceSite?_isSome_index_21 quadrant di dj
  by_cases h22 : n = 22
  · subst n
    exact expandedSourceSite?_isSome_index_22 quadrant di dj
  by_cases h23 : n = 23
  · subst n
    exact expandedSourceSite?_isSome_index_23 quadrant di dj
  by_cases h24 : n = 24
  · subst n
    exact expandedSourceSite?_isSome_index_24 quadrant di dj
  by_cases h25 : n = 25
  · subst n
    exact expandedSourceSite?_isSome_index_25 quadrant di dj
  by_cases h26 : n = 26
  · subst n
    exact expandedSourceSite?_isSome_index_26 quadrant di dj
  by_cases h27 : n = 27
  · subst n
    exact expandedSourceSite?_isSome_index_27 quadrant di dj
  by_cases h28 : n = 28
  · subst n
    exact expandedSourceSite?_isSome_index_28 quadrant di dj
  by_cases h29 : n = 29
  · subst n
    exact expandedSourceSite?_isSome_index_29 quadrant di dj
  by_cases h30 : n = 30
  · subst n
    exact expandedSourceSite?_isSome_index_30 quadrant di dj
  by_cases h31 : n = 31
  · subst n
    exact expandedSourceSite?_isSome_index_31 quadrant di dj
  by_cases h32 : n = 32
  · subst n
    exact expandedSourceSite?_isSome_index_32 quadrant di dj
  by_cases h33 : n = 33
  · subst n
    exact expandedSourceSite?_isSome_index_33 quadrant di dj
  by_cases h34 : n = 34
  · subst n
    exact expandedSourceSite?_isSome_index_34 quadrant di dj
  by_cases h35 : n = 35
  · subst n
    exact expandedSourceSite?_isSome_index_35 quadrant di dj
  by_cases h36 : n = 36
  · subst n
    exact expandedSourceSite?_isSome_index_36 quadrant di dj
  by_cases h37 : n = 37
  · subst n
    exact expandedSourceSite?_isSome_index_37 quadrant di dj
  by_cases h38 : n = 38
  · subst n
    exact expandedSourceSite?_isSome_index_38 quadrant di dj
  by_cases h39 : n = 39
  · subst n
    exact expandedSourceSite?_isSome_index_39 quadrant di dj
  by_cases h40 : n = 40
  · subst n
    exact expandedSourceSite?_isSome_index_40 quadrant di dj
  by_cases h41 : n = 41
  · subst n
    exact expandedSourceSite?_isSome_index_41 quadrant di dj
  by_cases h42 : n = 42
  · subst n
    exact expandedSourceSite?_isSome_index_42 quadrant di dj
  by_cases h43 : n = 43
  · subst n
    exact expandedSourceSite?_isSome_index_43 quadrant di dj
  by_cases h44 : n = 44
  · subst n
    exact expandedSourceSite?_isSome_index_44 quadrant di dj
  by_cases h45 : n = 45
  · subst n
    exact expandedSourceSite?_isSome_index_45 quadrant di dj
  by_cases h46 : n = 46
  · subst n
    exact expandedSourceSite?_isSome_index_46 quadrant di dj
  by_cases h47 : n = 47
  · subst n
    exact expandedSourceSite?_isSome_index_47 quadrant di dj
  by_cases h48 : n = 48
  · subst n
    exact expandedSourceSite?_isSome_index_48 quadrant di dj
  by_cases h49 : n = 49
  · subst n
    exact expandedSourceSite?_isSome_index_49 quadrant di dj
  by_cases h50 : n = 50
  · subst n
    exact expandedSourceSite?_isSome_index_50 quadrant di dj
  by_cases h51 : n = 51
  · subst n
    exact expandedSourceSite?_isSome_index_51 quadrant di dj
  by_cases h52 : n = 52
  · subst n
    exact expandedSourceSite?_isSome_index_52 quadrant di dj
  by_cases h53 : n = 53
  · subst n
    exact expandedSourceSite?_isSome_index_53 quadrant di dj
  by_cases h54 : n = 54
  · subst n
    exact expandedSourceSite?_isSome_index_54 quadrant di dj
  by_cases h55 : n = 55
  · subst n
    exact expandedSourceSite?_isSome_index_55 quadrant di dj
  by_cases h56 : n = 56
  · subst n
    exact expandedSourceSite?_isSome_index_56 quadrant di dj
  by_cases h57 : n = 57
  · subst n
    exact expandedSourceSite?_isSome_index_57 quadrant di dj
  by_cases h58 : n = 58
  · subst n
    exact expandedSourceSite?_isSome_index_58 quadrant di dj
  by_cases h59 : n = 59
  · subst n
    exact expandedSourceSite?_isSome_index_59 quadrant di dj
  by_cases h60 : n = 60
  · subst n
    exact expandedSourceSite?_isSome_index_60 quadrant di dj
  by_cases h61 : n = 61
  · subst n
    exact expandedSourceSite?_isSome_index_61 quadrant di dj
  by_cases h62 : n = 62
  · subst n
    exact expandedSourceSite?_isSome_index_62 quadrant di dj
  by_cases h63 : n = 63
  · subst n
    exact expandedSourceSite?_isSome_index_63 quadrant di dj
  by_cases h64 : n = 64
  · subst n
    exact expandedSourceSite?_isSome_index_64 quadrant di dj
  by_cases h65 : n = 65
  · subst n
    exact expandedSourceSite?_isSome_index_65 quadrant di dj
  by_cases h66 : n = 66
  · subst n
    exact expandedSourceSite?_isSome_index_66 quadrant di dj
  by_cases h67 : n = 67
  · subst n
    exact expandedSourceSite?_isSome_index_67 quadrant di dj
  by_cases h68 : n = 68
  · subst n
    exact expandedSourceSite?_isSome_index_68 quadrant di dj
  by_cases h69 : n = 69
  · subst n
    exact expandedSourceSite?_isSome_index_69 quadrant di dj
  by_cases h70 : n = 70
  · subst n
    exact expandedSourceSite?_isSome_index_70 quadrant di dj
  by_cases h71 : n = 71
  · subst n
    exact expandedSourceSite?_isSome_index_71 quadrant di dj
  by_cases h72 : n = 72
  · subst n
    exact expandedSourceSite?_isSome_index_72 quadrant di dj
  by_cases h73 : n = 73
  · subst n
    exact expandedSourceSite?_isSome_index_73 quadrant di dj
  by_cases h74 : n = 74
  · subst n
    exact expandedSourceSite?_isSome_index_74 quadrant di dj
  by_cases h75 : n = 75
  · subst n
    exact expandedSourceSite?_isSome_index_75 quadrant di dj
  by_cases h76 : n = 76
  · subst n
    exact expandedSourceSite?_isSome_index_76 quadrant di dj
  by_cases h77 : n = 77
  · subst n
    exact expandedSourceSite?_isSome_index_77 quadrant di dj
  by_cases h78 : n = 78
  · subst n
    exact expandedSourceSite?_isSome_index_78 quadrant di dj
  by_cases h79 : n = 79
  · subst n
    exact expandedSourceSite?_isSome_index_79 quadrant di dj
  by_cases h80 : n = 80
  · subst n
    exact expandedSourceSite?_isSome_index_80 quadrant di dj
  by_cases h81 : n = 81
  · subst n
    exact expandedSourceSite?_isSome_index_81 quadrant di dj
  by_cases h82 : n = 82
  · subst n
    exact expandedSourceSite?_isSome_index_82 quadrant di dj
  by_cases h83 : n = 83
  · subst n
    exact expandedSourceSite?_isSome_index_83 quadrant di dj
  by_cases h84 : n = 84
  · subst n
    exact expandedSourceSite?_isSome_index_84 quadrant di dj
  by_cases h85 : n = 85
  · subst n
    exact expandedSourceSite?_isSome_index_85 quadrant di dj
  by_cases h86 : n = 86
  · subst n
    exact expandedSourceSite?_isSome_index_86 quadrant di dj
  by_cases h87 : n = 87
  · subst n
    exact expandedSourceSite?_isSome_index_87 quadrant di dj
  by_cases h88 : n = 88
  · subst n
    exact expandedSourceSite?_isSome_index_88 quadrant di dj
  by_cases h89 : n = 89
  · subst n
    exact expandedSourceSite?_isSome_index_89 quadrant di dj
  by_cases h90 : n = 90
  · subst n
    exact expandedSourceSite?_isSome_index_90 quadrant di dj
  · have h91 : n = 91 := by omega
    subst n
    exact expandedSourceSite?_isSome_index_91 quadrant di dj

/--
The Figure 18 site selected for one cell of the doubled Figure 16 expansion of
a source Figure 18 site.
-/
def expandedSourceSite
    (source : Figure18Site) (di dj : Fin 2) : Figure18Site :=
  (expandedSourceSite? source di dj).get
    (expandedSourceSite?_isSome source di dj)

theorem expandedSourceSite?_eq_some
    (source : Figure18Site) (di dj : Fin 2) :
    expandedSourceSite? source di dj =
      some (expandedSourceSite source di dj) := by
  exact (Option.some_get (expandedSourceSite?_isSome source di dj)).symm

theorem expandedSourceSite_quadrant
    (source : Figure18Site) (di dj : Fin 2) :
    (expandedSourceSite source di dj).quadrant =
      quadrantOfOffset di dj :=
  expandedSourceSite?_eq_some_quadrant
    (expandedSourceSite?_eq_some source di dj)

theorem expandedSourceSite_l2Component1
    (source : Figure18Site) (di dj : Fin 2) :
    l2Component1SymbolAtSite (expandedSourceSite source di dj) =
      (thinBlockAtSite source).entry di dj :=
  expandedSourceSite?_eq_some_l2Component1
    (expandedSourceSite?_eq_some source di dj)

theorem expandedSourceSite_l2Component2
    (source : Figure18Site) (di dj : Fin 2) :
    l2Component2SymbolAtSite (expandedSourceSite source di dj) =
      (thickBlockAtSite source).entry di dj :=
  expandedSourceSite?_eq_some_l2Component2
    (expandedSourceSite?_eq_some source di dj)

theorem expandedSourceSite_l3
    (source : Figure18Site) (di dj : Fin 2) :
    l3SymbolAtSite (expandedSourceSite source di dj) =
      (blackBlockAtSite source).entry di dj :=
  expandedSourceSite?_eq_some_l3
    (expandedSourceSite?_eq_some source di dj)

/--
A jointly checked `2 × 2` Figure 18 site block realizing the Figure 16
substitution of one source site.

The independent `expandedSourceSite` decoder above proves that each requested
symbol triple exists, but it chooses each quadrant separately.  This block-level
target is the compatibility-aware form needed for the scaffold proof: the four
chosen sites must both expose the requested Figure 16 symbols and glue along
their internal Figure 18 edges.
-/
structure Figure16ExpandedSourceSiteBlock
    (source : Figure18Site)
    (target : Fin 2 → Fin 2 → Figure18Site) : Prop where
  siteMatch : ∀ di : Fin 2, ∀ dj : Fin 2,
    siteMatchesSymbolsBool
      ((thinBlockAtSite source).entry di dj)
      ((thickBlockAtSite source).entry di dj)
      ((blackBlockAtSite source).entry di dj)
      (quadrantOfOffset di dj)
      (target di dj) = true
  hWithin : ∀ dj : Fin 2,
    Figure18Site.hCompatible
      (target ⟨0, by decide⟩ dj)
      (target ⟨1, by decide⟩ dj) = true
  vWithin : ∀ di : Fin 2,
    Figure18Site.vCompatible
      (target di ⟨0, by decide⟩)
      (target di ⟨1, by decide⟩) = true

namespace Figure16ExpandedSourceSiteBlock

/-- Finite checker for a joint `2 × 2` source-site expansion block. -/
def matchesBool
    (source : Figure18Site)
    (target : Fin 2 → Fin 2 → Figure18Site) : Bool :=
  ((List.finRange 2).all fun di =>
    (List.finRange 2).all fun dj =>
      siteMatchesSymbolsBool
        ((thinBlockAtSite source).entry di dj)
        ((thickBlockAtSite source).entry di dj)
        ((blackBlockAtSite source).entry di dj)
        (quadrantOfOffset di dj)
        (target di dj)) &&
  ((List.finRange 2).all fun dj =>
    Figure18Site.hCompatible
      (target ⟨0, by decide⟩ dj)
      (target ⟨1, by decide⟩ dj)) &&
  ((List.finRange 2).all fun di =>
    Figure18Site.vCompatible
      (target di ⟨0, by decide⟩)
      (target di ⟨1, by decide⟩))

theorem of_matchesBool
    {source : Figure18Site}
    {target : Fin 2 → Fin 2 → Figure18Site}
    (hcheck : matchesBool source target = true) :
    Figure16ExpandedSourceSiteBlock source target := by
  unfold matchesBool at hcheck
  rw [Bool.and_eq_true, Bool.and_eq_true] at hcheck
  refine ⟨?_, ?_, ?_⟩
  · intro di dj
    have hdi := List.all_eq_true.1 hcheck.1.1 di (List.mem_finRange di)
    exact List.all_eq_true.1 hdi dj (List.mem_finRange dj)
  · intro dj
    exact List.all_eq_true.1 hcheck.1.2 dj (List.mem_finRange dj)
  · intro di
    exact List.all_eq_true.1 hcheck.2 di (List.mem_finRange di)

theorem matchesBool_of
    {source : Figure18Site}
    {target : Fin 2 → Fin 2 → Figure18Site}
    (hexpanded : Figure16ExpandedSourceSiteBlock source target) :
    matchesBool source target = true := by
  unfold matchesBool
  rw [Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · apply List.all_eq_true.2
    intro di _hdi
    apply List.all_eq_true.2
    intro dj _hdj
    exact hexpanded.siteMatch di dj
  · apply List.all_eq_true.2
    intro dj _hdj
    exact hexpanded.hWithin dj
  · apply List.all_eq_true.2
    intro di _hdi
    exact hexpanded.vWithin di

theorem quadrant
    {source : Figure18Site}
    {target : Fin 2 → Fin 2 → Figure18Site}
    (hexpanded : Figure16ExpandedSourceSiteBlock source target)
    (di dj : Fin 2) :
    (target di dj).quadrant = quadrantOfOffset di dj :=
  (siteMatchesSymbolsBool_eq_true (hexpanded.siteMatch di dj)).1

theorem l2Component1
    {source : Figure18Site}
    {target : Fin 2 → Fin 2 → Figure18Site}
    (hexpanded : Figure16ExpandedSourceSiteBlock source target)
    (di dj : Fin 2) :
    l2Component1SymbolAtSite (target di dj) =
      (thinBlockAtSite source).entry di dj :=
  (siteMatchesSymbolsBool_eq_true (hexpanded.siteMatch di dj)).2.1

theorem l2Component2
    {source : Figure18Site}
    {target : Fin 2 → Fin 2 → Figure18Site}
    (hexpanded : Figure16ExpandedSourceSiteBlock source target)
    (di dj : Fin 2) :
    l2Component2SymbolAtSite (target di dj) =
      (thickBlockAtSite source).entry di dj :=
  (siteMatchesSymbolsBool_eq_true (hexpanded.siteMatch di dj)).2.2.1

theorem l3
    {source : Figure18Site}
    {target : Fin 2 → Fin 2 → Figure18Site}
    (hexpanded : Figure16ExpandedSourceSiteBlock source target)
    (di dj : Fin 2) :
    l3SymbolAtSite (target di dj) =
      (blackBlockAtSite source).entry di dj :=
  (siteMatchesSymbolsBool_eq_true (hexpanded.siteMatch di dj)).2.2.2

end Figure16ExpandedSourceSiteBlock

/--
Canonical compatible source-site expansion: keep the raw Figure 13 tile index
and select the quadrant requested by the Figure 16 block offset.
-/
def canonicalExpandedSourceSite
    (source : Figure18Site) (di dj : Fin 2) : Figure18Site where
  index := source.index
  quadrant := quadrantOfOffset di dj

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_0
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨0, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨0, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_1
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨1, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨1, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_2
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨2, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨2, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_3
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨3, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨3, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_4
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨4, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨4, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_5
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨5, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨5, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_6
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨6, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨6, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_7
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨7, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨7, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_8
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨8, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨8, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_9
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨9, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨9, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_10
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨10, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨10, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_11
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨11, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨11, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_12
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨12, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨12, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_13
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨13, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨13, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_14
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨14, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨14, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_15
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨15, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨15, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_16
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨16, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨16, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_17
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨17, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨17, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_18
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨18, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨18, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_19
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨19, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨19, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_20
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨20, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨20, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_21
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨21, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨21, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_22
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨22, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨22, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_23
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨23, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨23, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_24
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨24, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨24, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_25
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨25, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨25, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_26
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨26, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨26, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_27
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨27, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨27, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_28
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨28, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨28, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_29
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨29, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨29, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_30
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨30, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨30, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_31
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨31, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨31, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_32
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨32, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨32, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_33
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨33, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨33, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_34
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨34, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨34, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_35
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨35, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨35, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_36
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨36, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨36, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_37
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨37, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨37, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_38
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨38, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨38, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_39
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨39, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨39, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_40
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨40, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨40, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_41
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨41, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨41, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_42
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨42, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨42, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_43
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨43, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨43, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_44
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨44, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨44, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_45
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨45, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨45, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_46
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨46, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨46, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_47
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨47, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨47, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_48
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨48, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨48, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_49
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨49, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨49, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_50
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨50, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨50, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_51
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨51, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨51, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_52
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨52, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨52, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_53
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨53, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨53, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_54
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨54, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨54, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_55
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨55, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨55, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_56
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨56, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨56, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_57
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨57, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨57, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_58
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨58, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨58, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_59
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨59, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨59, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_60
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨60, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨60, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_61
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨61, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨61, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_62
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨62, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨62, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_63
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨63, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨63, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_64
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨64, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨64, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_65
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨65, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨65, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_66
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨66, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨66, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_67
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨67, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨67, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_68
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨68, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨68, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_69
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨69, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨69, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_70
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨70, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨70, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_71
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨71, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨71, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_72
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨72, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨72, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_73
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨73, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨73, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_74
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨74, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨74, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_75
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨75, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨75, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_76
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨76, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨76, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_77
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨77, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨77, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_78
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨78, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨78, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_79
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨79, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨79, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_80
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨80, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨80, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_81
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨81, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨81, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_82
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨82, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨82, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_83
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨83, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨83, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_84
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨84, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨84, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_85
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨85, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨85, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_86
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨86, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨86, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_87
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨87, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨87, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_88
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨88, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨88, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_89
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨89, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨89, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_90
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨90, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨90, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

private theorem canonicalExpandedSourceSiteBlock_matchesBool_index_91
    (quadrant : Quadrant) :
    Figure16ExpandedSourceSiteBlock.matchesBool
      ({ index := ⟨91, by decide⟩, quadrant := quadrant } : Figure18Site)
      (canonicalExpandedSourceSite
        ({ index := ⟨91, by decide⟩, quadrant := quadrant } : Figure18Site)) = true := by
  cases quadrant <;> decide +revert

theorem canonicalExpandedSourceSiteBlock_matchesBool
    (source : Figure18Site) :
    Figure16ExpandedSourceSiteBlock.matchesBool source
      (canonicalExpandedSourceSite source) = true := by
  rcases source with ⟨index, quadrant⟩
  rcases index with ⟨n, hn⟩
  by_cases h0 : n = 0
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_0 quadrant
  by_cases h1 : n = 1
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_1 quadrant
  by_cases h2 : n = 2
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_2 quadrant
  by_cases h3 : n = 3
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_3 quadrant
  by_cases h4 : n = 4
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_4 quadrant
  by_cases h5 : n = 5
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_5 quadrant
  by_cases h6 : n = 6
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_6 quadrant
  by_cases h7 : n = 7
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_7 quadrant
  by_cases h8 : n = 8
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_8 quadrant
  by_cases h9 : n = 9
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_9 quadrant
  by_cases h10 : n = 10
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_10 quadrant
  by_cases h11 : n = 11
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_11 quadrant
  by_cases h12 : n = 12
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_12 quadrant
  by_cases h13 : n = 13
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_13 quadrant
  by_cases h14 : n = 14
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_14 quadrant
  by_cases h15 : n = 15
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_15 quadrant
  by_cases h16 : n = 16
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_16 quadrant
  by_cases h17 : n = 17
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_17 quadrant
  by_cases h18 : n = 18
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_18 quadrant
  by_cases h19 : n = 19
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_19 quadrant
  by_cases h20 : n = 20
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_20 quadrant
  by_cases h21 : n = 21
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_21 quadrant
  by_cases h22 : n = 22
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_22 quadrant
  by_cases h23 : n = 23
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_23 quadrant
  by_cases h24 : n = 24
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_24 quadrant
  by_cases h25 : n = 25
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_25 quadrant
  by_cases h26 : n = 26
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_26 quadrant
  by_cases h27 : n = 27
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_27 quadrant
  by_cases h28 : n = 28
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_28 quadrant
  by_cases h29 : n = 29
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_29 quadrant
  by_cases h30 : n = 30
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_30 quadrant
  by_cases h31 : n = 31
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_31 quadrant
  by_cases h32 : n = 32
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_32 quadrant
  by_cases h33 : n = 33
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_33 quadrant
  by_cases h34 : n = 34
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_34 quadrant
  by_cases h35 : n = 35
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_35 quadrant
  by_cases h36 : n = 36
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_36 quadrant
  by_cases h37 : n = 37
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_37 quadrant
  by_cases h38 : n = 38
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_38 quadrant
  by_cases h39 : n = 39
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_39 quadrant
  by_cases h40 : n = 40
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_40 quadrant
  by_cases h41 : n = 41
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_41 quadrant
  by_cases h42 : n = 42
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_42 quadrant
  by_cases h43 : n = 43
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_43 quadrant
  by_cases h44 : n = 44
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_44 quadrant
  by_cases h45 : n = 45
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_45 quadrant
  by_cases h46 : n = 46
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_46 quadrant
  by_cases h47 : n = 47
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_47 quadrant
  by_cases h48 : n = 48
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_48 quadrant
  by_cases h49 : n = 49
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_49 quadrant
  by_cases h50 : n = 50
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_50 quadrant
  by_cases h51 : n = 51
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_51 quadrant
  by_cases h52 : n = 52
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_52 quadrant
  by_cases h53 : n = 53
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_53 quadrant
  by_cases h54 : n = 54
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_54 quadrant
  by_cases h55 : n = 55
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_55 quadrant
  by_cases h56 : n = 56
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_56 quadrant
  by_cases h57 : n = 57
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_57 quadrant
  by_cases h58 : n = 58
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_58 quadrant
  by_cases h59 : n = 59
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_59 quadrant
  by_cases h60 : n = 60
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_60 quadrant
  by_cases h61 : n = 61
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_61 quadrant
  by_cases h62 : n = 62
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_62 quadrant
  by_cases h63 : n = 63
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_63 quadrant
  by_cases h64 : n = 64
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_64 quadrant
  by_cases h65 : n = 65
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_65 quadrant
  by_cases h66 : n = 66
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_66 quadrant
  by_cases h67 : n = 67
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_67 quadrant
  by_cases h68 : n = 68
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_68 quadrant
  by_cases h69 : n = 69
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_69 quadrant
  by_cases h70 : n = 70
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_70 quadrant
  by_cases h71 : n = 71
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_71 quadrant
  by_cases h72 : n = 72
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_72 quadrant
  by_cases h73 : n = 73
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_73 quadrant
  by_cases h74 : n = 74
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_74 quadrant
  by_cases h75 : n = 75
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_75 quadrant
  by_cases h76 : n = 76
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_76 quadrant
  by_cases h77 : n = 77
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_77 quadrant
  by_cases h78 : n = 78
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_78 quadrant
  by_cases h79 : n = 79
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_79 quadrant
  by_cases h80 : n = 80
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_80 quadrant
  by_cases h81 : n = 81
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_81 quadrant
  by_cases h82 : n = 82
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_82 quadrant
  by_cases h83 : n = 83
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_83 quadrant
  by_cases h84 : n = 84
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_84 quadrant
  by_cases h85 : n = 85
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_85 quadrant
  by_cases h86 : n = 86
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_86 quadrant
  by_cases h87 : n = 87
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_87 quadrant
  by_cases h88 : n = 88
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_88 quadrant
  by_cases h89 : n = 89
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_89 quadrant
  by_cases h90 : n = 90
  · subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_90 quadrant
  · have h91 : n = 91 := by omega
    subst n
    exact canonicalExpandedSourceSiteBlock_matchesBool_index_91 quadrant

theorem canonicalExpandedSourceSiteBlock
    (source : Figure18Site) :
    Figure16ExpandedSourceSiteBlock source
      (canonicalExpandedSourceSite source) :=
  Figure16ExpandedSourceSiteBlock.of_matchesBool
    (canonicalExpandedSourceSiteBlock_matchesBool source)

/--
The doubled Figure 18 site rectangle obtained by the canonical compatible
source-site expansion.
-/
def canonicalExpandedSiteRectangleOfSiteRectangle {w h : Nat}
    (R : SiteRectangle w h) : SiteRectangle (2 * w) (2 * h) :=
  fun i j =>
    canonicalExpandedSourceSite
      (R (Figure16.BlockGrid.doubledBlockCoord i)
        (Figure16.BlockGrid.doubledBlockCoord j))
      (Figure16.BlockGrid.doubledOffset i)
      (Figure16.BlockGrid.doubledOffset j)

theorem canonicalExpandedSiteRectangleOfSiteRectangle_l2Component1
    {w h : Nat} (R : SiteRectangle w h)
    (i : Fin (2 * w)) (j : Fin (2 * h)) :
    l2Component1SymbolAtSite
        (canonicalExpandedSiteRectangleOfSiteRectangle R i j) =
      (thinBlockAtSite
        (R (Figure16.BlockGrid.doubledBlockCoord i)
          (Figure16.BlockGrid.doubledBlockCoord j))).entry
        (Figure16.BlockGrid.doubledOffset i)
        (Figure16.BlockGrid.doubledOffset j) :=
  Figure16ExpandedSourceSiteBlock.l2Component1
    (canonicalExpandedSourceSiteBlock
      (R (Figure16.BlockGrid.doubledBlockCoord i)
        (Figure16.BlockGrid.doubledBlockCoord j)))
    (Figure16.BlockGrid.doubledOffset i)
    (Figure16.BlockGrid.doubledOffset j)

theorem canonicalExpandedSiteRectangleOfSiteRectangle_l2Component2
    {w h : Nat} (R : SiteRectangle w h)
    (i : Fin (2 * w)) (j : Fin (2 * h)) :
    l2Component2SymbolAtSite
        (canonicalExpandedSiteRectangleOfSiteRectangle R i j) =
      (thickBlockAtSite
        (R (Figure16.BlockGrid.doubledBlockCoord i)
          (Figure16.BlockGrid.doubledBlockCoord j))).entry
        (Figure16.BlockGrid.doubledOffset i)
        (Figure16.BlockGrid.doubledOffset j) :=
  Figure16ExpandedSourceSiteBlock.l2Component2
    (canonicalExpandedSourceSiteBlock
      (R (Figure16.BlockGrid.doubledBlockCoord i)
        (Figure16.BlockGrid.doubledBlockCoord j)))
    (Figure16.BlockGrid.doubledOffset i)
    (Figure16.BlockGrid.doubledOffset j)

theorem canonicalExpandedSiteRectangleOfSiteRectangle_l3
    {w h : Nat} (R : SiteRectangle w h)
    (i : Fin (2 * w)) (j : Fin (2 * h)) :
    l3SymbolAtSite
        (canonicalExpandedSiteRectangleOfSiteRectangle R i j) =
      (blackBlockAtSite
        (R (Figure16.BlockGrid.doubledBlockCoord i)
          (Figure16.BlockGrid.doubledBlockCoord j))).entry
        (Figure16.BlockGrid.doubledOffset i)
        (Figure16.BlockGrid.doubledOffset j) :=
  Figure16ExpandedSourceSiteBlock.l3
    (canonicalExpandedSourceSiteBlock
      (R (Figure16.BlockGrid.doubledBlockCoord i)
        (Figure16.BlockGrid.doubledBlockCoord j)))
    (Figure16.BlockGrid.doubledOffset i)
    (Figure16.BlockGrid.doubledOffset j)

/--
The doubled Figure 18 site rectangle obtained by applying the Figure 16
substitution lookup to every source site.
-/
def expandedSiteRectangleOfSiteRectangle {w h : Nat}
    (R : SiteRectangle w h) : SiteRectangle (2 * w) (2 * h) :=
  fun i j =>
    expandedSourceSite
      (R (Figure16.BlockGrid.doubledBlockCoord i)
        (Figure16.BlockGrid.doubledBlockCoord j))
      (Figure16.BlockGrid.doubledOffset i)
      (Figure16.BlockGrid.doubledOffset j)

theorem expandedSiteRectangleOfSiteRectangle_l2Component1 {w h : Nat}
    (R : SiteRectangle w h) (i : Fin (2 * w)) (j : Fin (2 * h)) :
    l2Component1SymbolAtSite (expandedSiteRectangleOfSiteRectangle R i j) =
      (thinBlockAtSite
        (R (Figure16.BlockGrid.doubledBlockCoord i)
          (Figure16.BlockGrid.doubledBlockCoord j))).entry
        (Figure16.BlockGrid.doubledOffset i)
        (Figure16.BlockGrid.doubledOffset j) :=
  expandedSourceSite_l2Component1 _ _ _

theorem expandedSiteRectangleOfSiteRectangle_l2Component2 {w h : Nat}
    (R : SiteRectangle w h) (i : Fin (2 * w)) (j : Fin (2 * h)) :
    l2Component2SymbolAtSite (expandedSiteRectangleOfSiteRectangle R i j) =
      (thickBlockAtSite
        (R (Figure16.BlockGrid.doubledBlockCoord i)
          (Figure16.BlockGrid.doubledBlockCoord j))).entry
        (Figure16.BlockGrid.doubledOffset i)
        (Figure16.BlockGrid.doubledOffset j) :=
  expandedSourceSite_l2Component2 _ _ _

theorem expandedSiteRectangleOfSiteRectangle_l3 {w h : Nat}
    (R : SiteRectangle w h) (i : Fin (2 * w)) (j : Fin (2 * h)) :
    l3SymbolAtSite (expandedSiteRectangleOfSiteRectangle R i j) =
      (blackBlockAtSite
        (R (Figure16.BlockGrid.doubledBlockCoord i)
          (Figure16.BlockGrid.doubledBlockCoord j))).entry
        (Figure16.BlockGrid.doubledOffset i)
        (Figure16.BlockGrid.doubledOffset j) :=
  expandedSourceSite_l3 _ _ _

/--
A doubled Figure 13 site rectangle recognized by a Figure 16 substitution
expansion.

The source rectangle carries the three compatible Figure 16 layer grids.  The
target rectangle is twice as large in each direction.  Its decoded symbols must
agree with the expanded thin/L1 substitution in the first L2 summand, the
expanded thick/L2 substitution in the second L2 summand, and the expanded black
substitution in L3.
-/
structure Figure16ExpandedSiteRectangle
    {w h : Nat} (source : SiteRectangle w h)
    (stack : LayerStackRectangle layerData source)
    (target : SiteRectangle (2 * w) (2 * h)) : Prop where
  l2Component1 :
    ∀ i : Fin (2 * w), ∀ j : Fin (2 * h),
      l2Component1SymbolAtSite (target i j) =
        Figure16.BlockGrid.expandedSymbol (stack.blockGrid .thin)
          (Figure16.BlockGrid.doubledBlockCoord i)
          (Figure16.BlockGrid.doubledBlockCoord j)
          (Figure16.BlockGrid.doubledOffset i)
          (Figure16.BlockGrid.doubledOffset j)
  l2Component2 :
    ∀ i : Fin (2 * w), ∀ j : Fin (2 * h),
      l2Component2SymbolAtSite (target i j) =
        Figure16.BlockGrid.expandedSymbol (stack.blockGrid .thick)
          (Figure16.BlockGrid.doubledBlockCoord i)
          (Figure16.BlockGrid.doubledBlockCoord j)
          (Figure16.BlockGrid.doubledOffset i)
          (Figure16.BlockGrid.doubledOffset j)
  l3 :
    ∀ i : Fin (2 * w), ∀ j : Fin (2 * h),
      l3SymbolAtSite (target i j) =
        Figure16.BlockGrid.expandedSymbol (stack.blockGrid .black)
          (Figure16.BlockGrid.doubledBlockCoord i)
          (Figure16.BlockGrid.doubledBlockCoord j)
          (Figure16.BlockGrid.doubledOffset i)
          (Figure16.BlockGrid.doubledOffset j)

namespace Figure16ExpandedSiteRectangle

/-- Finite checker for `Figure16ExpandedSiteRectangle`. -/
def matchesBool
    {w h : Nat} {source : SiteRectangle w h}
    (stack : LayerStackRectangle layerData source)
    (target : SiteRectangle (2 * w) (2 * h)) : Bool :=
  ((List.finRange (2 * w)).all fun i =>
    (List.finRange (2 * h)).all fun j =>
      decide <| l2Component1SymbolAtSite (target i j) =
        Figure16.BlockGrid.expandedSymbol (stack.blockGrid .thin)
          (Figure16.BlockGrid.doubledBlockCoord i)
          (Figure16.BlockGrid.doubledBlockCoord j)
          (Figure16.BlockGrid.doubledOffset i)
          (Figure16.BlockGrid.doubledOffset j)) &&
  ((List.finRange (2 * w)).all fun i =>
    (List.finRange (2 * h)).all fun j =>
      decide <| l2Component2SymbolAtSite (target i j) =
        Figure16.BlockGrid.expandedSymbol (stack.blockGrid .thick)
          (Figure16.BlockGrid.doubledBlockCoord i)
          (Figure16.BlockGrid.doubledBlockCoord j)
          (Figure16.BlockGrid.doubledOffset i)
          (Figure16.BlockGrid.doubledOffset j)) &&
  ((List.finRange (2 * w)).all fun i =>
    (List.finRange (2 * h)).all fun j =>
      decide <| l3SymbolAtSite (target i j) =
        Figure16.BlockGrid.expandedSymbol (stack.blockGrid .black)
          (Figure16.BlockGrid.doubledBlockCoord i)
          (Figure16.BlockGrid.doubledBlockCoord j)
          (Figure16.BlockGrid.doubledOffset i)
          (Figure16.BlockGrid.doubledOffset j))

theorem of_matchesBool
    {w h : Nat} {source : SiteRectangle w h}
    {stack : LayerStackRectangle layerData source}
    {target : SiteRectangle (2 * w) (2 * h)}
    (hcheck : matchesBool stack target = true) :
    Figure16ExpandedSiteRectangle source stack target := by
  unfold matchesBool at hcheck
  rw [Bool.and_eq_true, Bool.and_eq_true] at hcheck
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    have hi := List.all_eq_true.1 hcheck.1.1 i (List.mem_finRange i)
    have hj := List.all_eq_true.1 hi j (List.mem_finRange j)
    exact of_decide_eq_true hj
  · intro i j
    have hi := List.all_eq_true.1 hcheck.1.2 i (List.mem_finRange i)
    have hj := List.all_eq_true.1 hi j (List.mem_finRange j)
    exact of_decide_eq_true hj
  · intro i j
    have hi := List.all_eq_true.1 hcheck.2 i (List.mem_finRange i)
    have hj := List.all_eq_true.1 hi j (List.mem_finRange j)
    exact of_decide_eq_true hj

theorem matchesBool_of
    {w h : Nat} {source : SiteRectangle w h}
    {stack : LayerStackRectangle layerData source}
    {target : SiteRectangle (2 * w) (2 * h)}
    (hrecognized : Figure16ExpandedSiteRectangle source stack target) :
    matchesBool stack target = true := by
  unfold matchesBool
  rw [Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · apply List.all_eq_true.2
    intro i _hi
    apply List.all_eq_true.2
    intro j _hj
    exact decide_eq_true (hrecognized.l2Component1 i j)
  · apply List.all_eq_true.2
    intro i _hi
    apply List.all_eq_true.2
    intro j _hj
    exact decide_eq_true (hrecognized.l2Component2 i j)
  · apply List.all_eq_true.2
    intro i _hi
    apply List.all_eq_true.2
    intro j _hj
    exact decide_eq_true (hrecognized.l3 i j)

end Figure16ExpandedSiteRectangle

theorem figure16ExpandedSiteRectangle_matchesBool_checkedLayerStack_expanded
    {w h : Nat} (R : SiteRectangle w h)
    (hcompatible :
      (checkedLayerStackRectangleOfSiteRectangle R).compatibleBool layerData
        (checkedLayerStackRectangleOfSiteRectangle_lookupBool R) = true) :
    Figure16ExpandedSiteRectangle.matchesBool
      (checkedLayerStackOfSiteRectangle R hcompatible)
      (expandedSiteRectangleOfSiteRectangle R) = true := by
  unfold Figure16ExpandedSiteRectangle.matchesBool
  rw [Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · apply List.all_eq_true.2
    intro i _hi
    apply List.all_eq_true.2
    intro j _hj
    apply decide_eq_true
    rw [expandedSiteRectangleOfSiteRectangle_l2Component1,
      Figure16.BlockGrid.expandedSymbol,
      checkedLayerStackOfSiteRectangle_thin_blockGrid]
  · apply List.all_eq_true.2
    intro i _hi
    apply List.all_eq_true.2
    intro j _hj
    apply decide_eq_true
    rw [expandedSiteRectangleOfSiteRectangle_l2Component2,
      Figure16.BlockGrid.expandedSymbol,
      checkedLayerStackOfSiteRectangle_thick_blockGrid]
  · apply List.all_eq_true.2
    intro i _hi
    apply List.all_eq_true.2
    intro j _hj
    apply decide_eq_true
    rw [expandedSiteRectangleOfSiteRectangle_l3,
      Figure16.BlockGrid.expandedSymbol,
      checkedLayerStackOfSiteRectangle_black_blockGrid]

theorem figure16ExpandedSiteRectangle_matchesBool_checkedLayerStack_canonicalExpanded
    {w h : Nat} (R : SiteRectangle w h)
    (hcompatible :
      (checkedLayerStackRectangleOfSiteRectangle R).compatibleBool layerData
        (checkedLayerStackRectangleOfSiteRectangle_lookupBool R) = true) :
    Figure16ExpandedSiteRectangle.matchesBool
      (checkedLayerStackOfSiteRectangle R hcompatible)
      (canonicalExpandedSiteRectangleOfSiteRectangle R) = true := by
  unfold Figure16ExpandedSiteRectangle.matchesBool
  rw [Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · apply List.all_eq_true.2
    intro i _hi
    apply List.all_eq_true.2
    intro j _hj
    apply decide_eq_true
    rw [canonicalExpandedSiteRectangleOfSiteRectangle_l2Component1,
      Figure16.BlockGrid.expandedSymbol,
      checkedLayerStackOfSiteRectangle_thin_blockGrid]
  · apply List.all_eq_true.2
    intro i _hi
    apply List.all_eq_true.2
    intro j _hj
    apply decide_eq_true
    rw [canonicalExpandedSiteRectangleOfSiteRectangle_l2Component2,
      Figure16.BlockGrid.expandedSymbol,
      checkedLayerStackOfSiteRectangle_thick_blockGrid]
  · apply List.all_eq_true.2
    intro i _hi
    apply List.all_eq_true.2
    intro j _hj
    apply decide_eq_true
    rw [canonicalExpandedSiteRectangleOfSiteRectangle_l3,
      Figure16.BlockGrid.expandedSymbol,
      checkedLayerStackOfSiteRectangle_black_blockGrid]

/-- Figure 18 site-neighbor compatibility for a site rectangle. -/
def Figure18SiteCompatibleRectangle {w h : Nat}
    (R : SiteRectangle w h) : Prop :=
  (∀ i : Fin w, ∀ j : Fin h, ∀ hi : i.val + 1 < w,
    Figure18Site.hCompatible (R i j) (R ⟨i.val + 1, hi⟩ j) = true) ∧
  (∀ i : Fin w, ∀ j : Fin h, ∀ hj : j.val + 1 < h,
    Figure18Site.vCompatible (R i j) (R i ⟨j.val + 1, hj⟩) = true)

/-- Finite checker for Figure 18 site-neighbor compatibility. -/
def figure18SiteCompatibleRectangleBool {w h : Nat}
    (R : SiteRectangle w h) : Bool :=
  ((List.finRange w).all fun i =>
    if hi : i.val + 1 < w then
      (List.finRange h).all fun j =>
        Figure18Site.hCompatible (R i j) (R ⟨i.val + 1, hi⟩ j)
    else
      true) &&
  ((List.finRange h).all fun j =>
    if hj : j.val + 1 < h then
      (List.finRange w).all fun i =>
        Figure18Site.vCompatible (R i j) (R i ⟨j.val + 1, hj⟩)
    else
      true)

set_option linter.flexible false in
theorem figure18SiteCompatibleRectangle_of_bool
    {w h : Nat} {R : SiteRectangle w h}
    (hcheck : figure18SiteCompatibleRectangleBool R = true) :
    Figure18SiteCompatibleRectangle R := by
  unfold figure18SiteCompatibleRectangleBool at hcheck
  rw [Bool.and_eq_true] at hcheck
  constructor
  · intro i j hi
    have hiCheck := List.all_eq_true.1 hcheck.1 i (List.mem_finRange i)
    simp [hi] at hiCheck
    exact hiCheck j
  · intro i j hj
    have hjCheck := List.all_eq_true.1 hcheck.2 j (List.mem_finRange j)
    simp [hj] at hjCheck
    exact hjCheck i

set_option linter.flexible false in
theorem figure18SiteCompatibleRectangleBool_of
    {w h : Nat} {R : SiteRectangle w h}
    (hcompatible : Figure18SiteCompatibleRectangle R) :
    figure18SiteCompatibleRectangleBool R = true := by
  unfold figure18SiteCompatibleRectangleBool
  rw [Bool.and_eq_true]
  constructor
  · apply List.all_eq_true.2
    intro i _hiMem
    by_cases hi : i.val + 1 < w
    · simp [hi]
      intro j
      exact hcompatible.1 i j hi
    · simp [hi]
  · apply List.all_eq_true.2
    intro j _hjMem
    by_cases hj : j.val + 1 < h
    · simp [hj]
      intro i
      exact hcompatible.2 i j hj
    · simp [hj]

set_option maxHeartbeats 800000 in
-- Splitting doubled-neighbor compatibility unfolds several finite Figure 13 tile definitions.
theorem figure18SiteCompatibleRectangle_canonicalExpanded_of_rawBoundaryCompatible
    {w h : Nat} (R : SiteRectangle w h)
    (hrawCompat : R.RawBoundaryCompatible) :
    Figure18SiteCompatibleRectangle
      (canonicalExpandedSiteRectangleOfSiteRectangle R) := by
  constructor
  · intro i j hi
    rcases Figure16.BlockGrid.doubledOffset_eq_zero_or_one i with hzero | hone
    · rcases Figure16.BlockGrid.doubled_succ_of_offset_zero i hi hzero with
        ⟨hblock, hoff⟩
      have hoff_i : Figure16.BlockGrid.doubledOffset i = ⟨0, by decide⟩ :=
        Fin.ext hzero
      simpa [canonicalExpandedSiteRectangleOfSiteRectangle,
        canonicalExpandedSourceSite, hblock, hoff, hoff_i] using
        (canonicalExpandedSourceSiteBlock
          (R (Figure16.BlockGrid.doubledBlockCoord i)
            (Figure16.BlockGrid.doubledBlockCoord j))).hWithin
          (Figure16.BlockGrid.doubledOffset j)
    · rcases Figure16.BlockGrid.doubled_succ_of_offset_one i hi hone with
        ⟨hb, hblock, hoff⟩
      have hoff_i : Figure16.BlockGrid.doubledOffset i = ⟨1, by decide⟩ :=
        Fin.ext hone
      have hraw : WangTile.HMatches
          (R (Figure16.BlockGrid.doubledBlockCoord i)
            (Figure16.BlockGrid.doubledBlockCoord j)).rawTile
          (R ⟨(Figure16.BlockGrid.doubledBlockCoord i).val + 1, hb⟩
            (Figure16.BlockGrid.doubledBlockCoord j)).rawTile := by
        have hsub := hrawCompat.1
          (Figure16.BlockGrid.doubledBlockCoord i)
          (Figure16.BlockGrid.doubledBlockCoord j) hb
        simpa [SiteRectangle.rawTileRect,
          TileSubdivision.hMatches_subdivideTileAt_iff] using hsub
      rcases Figure16.BlockGrid.doubledOffset_eq_zero_or_one j with
        hzero_j | hone_j
      · have hoff_j : Figure16.BlockGrid.doubledOffset j = ⟨0, by decide⟩ :=
          Fin.ext hzero_j
        simpa [canonicalExpandedSiteRectangleOfSiteRectangle,
          canonicalExpandedSourceSite, hblock, hoff, hoff_i, hoff_j,
          quadrantOfOffset, Figure18Site.hCompatible, Figure18Site.rawTile] using
          (decide_eq_true hraw)
      · have hoff_j : Figure16.BlockGrid.doubledOffset j = ⟨1, by decide⟩ :=
          Fin.ext hone_j
        simpa [canonicalExpandedSiteRectangleOfSiteRectangle,
          canonicalExpandedSourceSite, hblock, hoff, hoff_i, hoff_j,
          quadrantOfOffset, Figure18Site.hCompatible, Figure18Site.rawTile] using
          (decide_eq_true hraw)
  · intro i j hj
    rcases Figure16.BlockGrid.doubledOffset_eq_zero_or_one j with hzero | hone
    · rcases Figure16.BlockGrid.doubled_succ_of_offset_zero j hj hzero with
        ⟨hblock, hoff⟩
      have hoff_j : Figure16.BlockGrid.doubledOffset j = ⟨0, by decide⟩ :=
        Fin.ext hzero
      simpa [canonicalExpandedSiteRectangleOfSiteRectangle,
        canonicalExpandedSourceSite, hblock, hoff, hoff_j] using
        (canonicalExpandedSourceSiteBlock
          (R (Figure16.BlockGrid.doubledBlockCoord i)
            (Figure16.BlockGrid.doubledBlockCoord j))).vWithin
          (Figure16.BlockGrid.doubledOffset i)
    · rcases Figure16.BlockGrid.doubled_succ_of_offset_one j hj hone with
        ⟨hb, hblock, hoff⟩
      have hoff_j : Figure16.BlockGrid.doubledOffset j = ⟨1, by decide⟩ :=
        Fin.ext hone
      have hraw : WangTile.VMatches
          (R (Figure16.BlockGrid.doubledBlockCoord i)
            (Figure16.BlockGrid.doubledBlockCoord j)).rawTile
          (R (Figure16.BlockGrid.doubledBlockCoord i)
            ⟨(Figure16.BlockGrid.doubledBlockCoord j).val + 1, hb⟩).rawTile := by
        have hsub := hrawCompat.2
          (Figure16.BlockGrid.doubledBlockCoord i)
          (Figure16.BlockGrid.doubledBlockCoord j) hb
        simpa [SiteRectangle.rawTileRect,
          TileSubdivision.vMatches_subdivideTileAt_iff] using hsub
      rcases Figure16.BlockGrid.doubledOffset_eq_zero_or_one i with
        hzero_i | hone_i
      · have hoff_i : Figure16.BlockGrid.doubledOffset i = ⟨0, by decide⟩ :=
          Fin.ext hzero_i
        simpa [canonicalExpandedSiteRectangleOfSiteRectangle,
          canonicalExpandedSourceSite, hblock, hoff, hoff_i, hoff_j,
          quadrantOfOffset, Figure18Site.vCompatible, Figure18Site.rawTile] using
          (decide_eq_true hraw)
      · have hoff_i : Figure16.BlockGrid.doubledOffset i = ⟨1, by decide⟩ :=
          Fin.ext hone_i
        simpa [canonicalExpandedSiteRectangleOfSiteRectangle,
          canonicalExpandedSourceSite, hblock, hoff, hoff_i, hoff_j,
          quadrantOfOffset, Figure18Site.vCompatible, Figure18Site.rawTile] using
          (decide_eq_true hraw)

/--
Figure 16-recognized macro-squares at every Robinson board/free-grid level.

This is the finite scaffold-instantiation target immediately before raw
Figure 13 compactness: construct the source layer stack, recognize the doubled
site rectangle obtained from applying the substitutions, and prove that the
recognized target has the raw Figure 13 macro-boundary matches.
-/
def HasFigure16RecognizedRobinsonBoardLevelMacroSquares : Prop :=
  ∀ level : Nat,
    ∃ source : SiteRectangle
      (RobinsonSquare.freeGridSide level) (RobinsonSquare.freeGridSide level),
      ∃ stack : LayerStackRectangle layerData source,
        ∃ target : SiteRectangle
          (2 * RobinsonSquare.freeGridSide level)
          (2 * RobinsonSquare.freeGridSide level),
          Figure16ExpandedSiteRectangle source stack target ∧
            target.RawBoundaryCompatible

/--
Finite-check version of the Figure 16-recognized Robinson board macro-square
target.
-/
def HasCheckedFigure16RecognizedRobinsonBoardLevelMacroSquares : Prop :=
  ∀ level : Nat,
    ∃ source : SiteRectangle
      (RobinsonSquare.freeGridSide level) (RobinsonSquare.freeGridSide level),
      ∃ stack : LayerStackRectangle layerData source,
        ∃ target : SiteRectangle
          (2 * RobinsonSquare.freeGridSide level)
          (2 * RobinsonSquare.freeGridSide level),
          Figure16ExpandedSiteRectangle.matchesBool stack target = true ∧
            target.rawBoundaryCompatibleBool = true

/--
Canonical finite-check version of the Figure 16-recognized Robinson board
macro-square target.

Unlike `HasCheckedFigure16RecognizedRobinsonBoardLevelMacroSquares`, this
target does not quantify over an arbitrary layer stack.  The stack is the
audited concrete Figure 13 layer stack attached to `source`; the first boolean
field is exactly the finite Figure 16 neighbor-compatibility check needed to
build that stack.
-/
def HasCanonicalCheckedFigure16RecognizedRobinsonBoardLevelMacroSquares : Prop :=
  ∀ level : Nat,
    ∃ source : SiteRectangle
      (RobinsonSquare.freeGridSide level) (RobinsonSquare.freeGridSide level),
      ∃ hcompatible :
        (checkedLayerStackRectangleOfSiteRectangle source).compatibleBool
          layerData (checkedLayerStackRectangleOfSiteRectangle_lookupBool source) =
            true,
        ∃ target : SiteRectangle
          (2 * RobinsonSquare.freeGridSide level)
          (2 * RobinsonSquare.freeGridSide level),
          Figure16ExpandedSiteRectangle.matchesBool
            (checkedLayerStackOfSiteRectangle source hcompatible) target =
              true ∧
            target.rawBoundaryCompatibleBool = true

/--
Canonical source-level raw-boundary macro-square target.

This is the source-side form suggested by Robinson's board/free-line argument:
at every board level, choose a square of Figure 13 sites whose audited Figure 16
layer stack is locally compatible and whose raw Figure 13 tile boundaries match
across adjacent source cells.  The canonical Figure 16 expansion of such a
source square is compatible as a Figure 18 site rectangle.
-/
def HasCanonicalCheckedFigure16SourceRawBoundaryMacroSquares : Prop :=
  ∀ level : Nat,
    ∃ source : SiteRectangle
      (RobinsonSquare.freeGridSide level) (RobinsonSquare.freeGridSide level),
      ∃ _hcompatible :
        (checkedLayerStackRectangleOfSiteRectangle source).compatibleBool
          layerData (checkedLayerStackRectangleOfSiteRectangle_lookupBool source) =
            true,
        source.RawBoundaryCompatible

/--
Finite-check version of `HasCanonicalCheckedFigure16SourceRawBoundaryMacroSquares`.
-/
def HasCanonicalCheckedFigure16SourceRawBoundaryMacroSquaresBool : Prop :=
  ∀ level : Nat,
    ∃ source : SiteRectangle
      (RobinsonSquare.freeGridSide level) (RobinsonSquare.freeGridSide level),
      ∃ _hcompatible :
        (checkedLayerStackRectangleOfSiteRectangle source).compatibleBool
          layerData (checkedLayerStackRectangleOfSiteRectangle_lookupBool source) =
            true,
        source.rawBoundaryCompatibleBool = true

/--
One level of the Robinson Section 7 source/free-grid certificate.

The board/free-line argument should eventually construct these certificates:
the selected source rectangle is the virtual grid of free row/column crossings,
`stackCompatible` is the checked Figure 16 layer-stack local compatibility
fact, and `rawBoundary` is the raw Figure 13 edge matching along adjacent
source cells.
-/
structure CanonicalFigure16SourceRawBoundaryLevelCertificate
    (level : Nat) where
  source : SiteRectangle
    (RobinsonSquare.freeGridSide level) (RobinsonSquare.freeGridSide level)
  stackCompatible :
    (checkedLayerStackRectangleOfSiteRectangle source).compatibleBool
      layerData (checkedLayerStackRectangleOfSiteRectangle_lookupBool source) =
        true
  rawBoundary : source.rawBoundaryCompatibleBool = true

/--
Level-certificate form of the finite checked source raw-boundary target.

This is the intended proof obligation for the remaining Robinson board
construction: produce one finite source/free-grid certificate at every board
level.
-/
def HasCanonicalFigure16SourceRawBoundaryLevelCertificates : Prop :=
  ∀ level : Nat,
    Nonempty (CanonicalFigure16SourceRawBoundaryLevelCertificate level)

/--
Explicit finite-check form of the source/free-grid certificate target.

This avoids nested dependent existentials when proving the remaining Robinson
board construction: for each level, choose the source rectangle and prove the
two boolean checks needed to build a level certificate.
-/
def HasCanonicalFigure16SourceRawBoundaryLevelChecks : Prop :=
  ∀ level : Nat,
    ∃ source : SiteRectangle
      (RobinsonSquare.freeGridSide level) (RobinsonSquare.freeGridSide level),
      (checkedLayerStackRectangleOfSiteRectangle source).compatibleBool
        layerData (checkedLayerStackRectangleOfSiteRectangle_lookupBool source) =
          true ∧
        source.rawBoundaryCompatibleBool = true

/--
Concrete row-major checked data for one Robinson source/free-grid level.

This is the finite-data form expected from a generated or human-audited
Robinson board construction: `sites` stores the selected Figure 18 sites as
raw tile indices and quadrants, while the two boolean fields are exactly the
checks needed by `HasCanonicalFigure16SourceRawBoundaryLevelChecks`.
-/
structure CanonicalFigure16SourceRawBoundaryCheckedLevelData
    (level : Nat) where
  sites : CheckedNatSiteRectangle
    (RobinsonSquare.freeGridSide level) (RobinsonSquare.freeGridSide level)
  stackCompatible :
    (checkedLayerStackRectangleOfSiteRectangle sites.toSiteRectangle).compatibleBool
      layerData
      (checkedLayerStackRectangleOfSiteRectangle_lookupBool sites.toSiteRectangle) =
        true
  rawBoundary : sites.toSiteRectangle.rawBoundaryCompatibleBool = true

/--
Checked-list form of the canonical source/free-grid target.

Compared with `HasCanonicalFigure16SourceRawBoundaryLevelChecks`, this exposes
the chosen source rectangles as row-major checked lists of `(tile, quadrant)`
pairs, which is a better target for finite generation and audit.
-/
def HasCanonicalFigure16SourceRawBoundaryCheckedLevelData : Prop :=
  ∀ level : Nat,
    Nonempty (CanonicalFigure16SourceRawBoundaryCheckedLevelData level)

/--
Shifted Robinson board-level source/free-grid checks.

Robinson's first nondegenerate board has side `4^1 - 1` and `2^1 + 1`
free rows/columns.  This target indexes those boards by `level : Nat`, using
`level + 1` for the underlying `RobinsonSquare` scale, and therefore avoids
the degenerate `freeGridSide 0 = 2` case.

This remains an over-strong diagnostic target: it asks the Figure 16 source
components themselves to form a compatible source stack.  The Section 7
construction should instead be proved through the board/free-line invariant and
the expanded Figure 13 board data it induces.
-/
def HasCanonicalFigure16SourceRawBoundaryBoardLevelChecks : Prop :=
  ∀ level : Nat,
    ∃ source : SiteRectangle
      (RobinsonSquare.freeGridSide (level + 1))
      (RobinsonSquare.freeGridSide (level + 1)),
      (checkedLayerStackRectangleOfSiteRectangle source).compatibleBool
        layerData (checkedLayerStackRectangleOfSiteRectangle_lookupBool source) =
          true ∧
        source.rawBoundaryCompatibleBool = true

/-- Row-major checked data for one shifted Robinson board level. -/
structure CanonicalFigure16SourceRawBoundaryCheckedBoardLevelData
    (level : Nat) where
  sites : CheckedNatSiteRectangle
    (RobinsonSquare.freeGridSide (level + 1))
    (RobinsonSquare.freeGridSide (level + 1))
  stackCompatible :
    (checkedLayerStackRectangleOfSiteRectangle sites.toSiteRectangle).compatibleBool
      layerData
      (checkedLayerStackRectangleOfSiteRectangle_lookupBool sites.toSiteRectangle) =
        true
  rawBoundary : sites.toSiteRectangle.rawBoundaryCompatibleBool = true

/-- Checked-list form of the shifted Robinson board-level target. -/
def HasCanonicalFigure16SourceRawBoundaryCheckedBoardLevelData : Prop :=
  ∀ level : Nat,
    Nonempty (CanonicalFigure16SourceRawBoundaryCheckedBoardLevelData level)

/--
Row-major checked data for one positive Robinson board-level raw Figure 13
macro-square.

This is the exact finite-data form of
`HasFigure13RobinsonPositiveBoardLevelAlignedMacroSquares`: it records only the
selected Figure 18 sites and the raw Figure 13 boundary check.  Unlike
`CanonicalFigure16SourceRawBoundaryCheckedBoardLevelData`, it does not require
the selected sites themselves to satisfy the over-strong Figure 16 source-stack
compatibility diagnostic.
-/
structure Figure13PositiveBoardLevelCheckedData (level : Nat) where
  sites : CheckedNatSiteRectangle
    (RobinsonSquare.freeGridSide (level + 1))
    (RobinsonSquare.freeGridSide (level + 1))
  rawBoundary : sites.toSiteRectangle.rawBoundaryCompatibleBool = true

/-- Checked-list form of the exact positive board-level raw Figure 13 target. -/
def HasFigure13PositiveBoardLevelCheckedData : Prop :=
  ∀ level : Nat, Nonempty (Figure13PositiveBoardLevelCheckedData level)

/--
Propositional raw-boundary form of one positive Robinson board-level raw Figure
13 macro-square.

This is convenient for the eventual board/free-line proof, which should derive
the local horizontal and vertical boundary matches as propositions.  The
Boolean checked form above remains the better finite-audit target.
-/
structure Figure13PositiveBoardLevelRawData (level : Nat) where
  sites : CheckedNatSiteRectangle
    (RobinsonSquare.freeGridSide (level + 1))
    (RobinsonSquare.freeGridSide (level + 1))
  rawBoundary : sites.toSiteRectangle.RawBoundaryCompatible

/-- Propositional form of the exact positive board-level raw Figure 13 target. -/
def HasFigure13PositiveBoardLevelRawData : Prop :=
  ∀ level : Nat, Nonempty (Figure13PositiveBoardLevelRawData level)

/--
Ordinary square-tiling form of the exact positive Robinson board-level raw
Figure 13 target.

This is Robinson's Section 7 board/free-grid surface after forgetting the
chosen Figure 18 sites: for each positive board level, tile the virtual
free-row/free-column square of side `freeGridSide (level + 1)`.

This is now kept only as a diagnostic comparison surface.  The raw Figure 13
macro tiles do not tile even a `2 × 2` square; the proof-facing scaffold route
must use subdivided Figure 18 site compatibility instead.
-/
def HasFigure13PositiveBoardLevelTileableSquares : Prop :=
  ∀ level : Nat,
    TileableSquare fig13Tiles (RobinsonSquare.freeGridSide (level + 1))

/--
The raw positive-board square-tiling surface is false for the current Figure 13
macro-tile transcription.
-/
theorem not_hasFigure13PositiveBoardLevelTileableSquares :
    ¬ HasFigure13PositiveBoardLevelTileableSquares := by
  intro hsquares
  have hsquare := hsquares 0
  exact not_tileableSquare_fig13Tiles_two
    (tileableSquare_crop (by decide : 2 ≤ RobinsonSquare.freeGridSide (0 + 1))
      hsquare)

/-- A chosen scanned Figure 13 index for a known raw tile-list member. -/
noncomputable def fig13IndexOfMem {tile : WangTile}
    (hmem : tile ∈ fig13Tiles) : Fin 92 :=
  Classical.choose (exists_fig13Tile_eq_of_mem_fig13Tiles hmem)

theorem fig13Tile_fig13IndexOfMem {tile : WangTile}
    (hmem : tile ∈ fig13Tiles) :
    fig13Tile (fig13IndexOfMem hmem) = tile :=
  Classical.choose_spec (exists_fig13Tile_eq_of_mem_fig13Tiles hmem)

/--
Choose Figure 18 sites over a valid raw Figure 13 rectangle by decoding each
raw tile to its scanned Figure 13 index.

All sites use the southwest quadrant because this object records only the raw
macro-tile identities; the positive-board raw-data target below depends on
`rawTileRect`, not on the chosen quarter.
-/
noncomputable def siteRectangleOfValidFig13Rectangle {w h : Nat}
    (x : Rectangle w h) (hx : ValidRectangle fig13Tiles x) :
    SiteRectangle w h :=
  fun i j => {
    index := fig13IndexOfMem (hx.1 i j)
    quadrant := .southwest
  }

theorem rawTileRect_siteRectangleOfValidFig13Rectangle {w h : Nat}
    (x : Rectangle w h) (hx : ValidRectangle fig13Tiles x) :
    (siteRectangleOfValidFig13Rectangle x hx).rawTileRect = x := by
  funext i j
  exact fig13Tile_fig13IndexOfMem (hx.1 i j)

/--
A valid raw Figure 13 rectangle induces the raw-boundary compatibility predicate
used by the positive-board interface.
-/
theorem rawBoundaryCompatible_siteRectangleOfValidFig13Rectangle {w h : Nat}
    (x : Rectangle w h) (hx : ValidRectangle fig13Tiles x) :
    (siteRectangleOfValidFig13Rectangle x hx).RawBoundaryCompatible := by
  constructor
  · intro i j hi
    have hmatch := TileSubdivision.hMatches_southeast_southwest_of_hMatches
      (hx.2.1 i j hi)
    simpa [rawTileRect_siteRectangleOfValidFig13Rectangle x hx] using hmatch
  · intro i j hj
    have hmatch := TileSubdivision.vMatches_northwest_southwest_of_vMatches
      (hx.2.2 i j hj)
    simpa [rawTileRect_siteRectangleOfValidFig13Rectangle x hx] using hmatch

/-- Package one valid raw Figure 13 board-level square as positive-board raw data. -/
noncomputable def positiveBoardLevelRawDataOfValidFig13Rectangle
    (level : Nat)
    {x : Rectangle
      (RobinsonSquare.freeGridSide (level + 1))
      (RobinsonSquare.freeGridSide (level + 1))}
    (hx : ValidRectangle fig13Tiles x) :
    Figure13PositiveBoardLevelRawData level := by
  let sites :=
    (siteRectangleOfValidFig13Rectangle x hx).toCheckedNatSiteRectangle
  have hsites : sites.toSiteRectangle =
      siteRectangleOfValidFig13Rectangle x hx :=
    CheckedNatSiteRectangle.toSiteRectangle_eq_of_matchesSiteRectangleBool
      (SiteRectangle.toCheckedNatSiteRectangle_matchesSiteRectangleBool
        (siteRectangleOfValidFig13Rectangle x hx))
  exact {
    sites := sites
    rawBoundary := by
      simpa [hsites] using
        rawBoundaryCompatible_siteRectangleOfValidFig13Rectangle x hx
  }

/--
Board-level raw Figure 13 square tilings supply the exact positive-board raw
data interface.
-/
theorem rawPositiveBoardLevelData_of_positiveBoardLevelTileableSquares
    (hsquares : HasFigure13PositiveBoardLevelTileableSquares) :
    HasFigure13PositiveBoardLevelRawData := by
  intro level
  rcases hsquares level with ⟨x, hx⟩
  exact ⟨positiveBoardLevelRawDataOfValidFig13Rectangle level hx⟩

/--
Finite diagnostic for the over-strong source raw-boundary board target: a
horizontal two-cell source edge satisfying both checked layer-stack
compatibility and raw Figure 13 boundary compatibility.
-/
def sourceRawBoundaryHCompatiblePairBool
    (left right : Figure18Site) : Bool :=
  let source : SiteRectangle 2 1 := fun i _ =>
    if i.val = 0 then left else right
  (checkedLayerStackRectangleOfSiteRectangle source).compatibleBool
    layerData (checkedLayerStackRectangleOfSiteRectangle_lookupBool source) &&
    source.rawBoundaryCompatibleBool

/--
Finite diagnostic for the over-strong source raw-boundary board target: a
vertical two-cell source edge satisfying both checked layer-stack compatibility
and raw Figure 13 boundary compatibility.
-/
def sourceRawBoundaryVCompatiblePairBool
    (lower upper : Figure18Site) : Bool :=
  let source : SiteRectangle 1 2 := fun _ j =>
    if j.val = 0 then lower else upper
  (checkedLayerStackRectangleOfSiteRectangle source).compatibleBool
    layerData (checkedLayerStackRectangleOfSiteRectangle_lookupBool source) &&
    source.rawBoundaryCompatibleBool

/--
All horizontal two-cell witnesses for the current source raw-boundary board
diagnostic.
-/
def sourceRawBoundaryHCompatiblePairs : List (Figure18Site × Figure18Site) :=
  Figure18Site.all.flatMap fun left =>
    Figure18Site.all.filterMap fun right =>
      if sourceRawBoundaryHCompatiblePairBool left right then
        some (left, right)
      else
        none

/--
All vertical two-cell witnesses for the current source raw-boundary board
diagnostic.
-/
def sourceRawBoundaryVCompatiblePairs : List (Figure18Site × Figure18Site) :=
  Figure18Site.all.flatMap fun lower =>
    Figure18Site.all.filterMap fun upper =>
      if sourceRawBoundaryVCompatiblePairBool lower upper then
        some (lower, upper)
      else
        none

/--
Boolean no-witness form of `sourceRawBoundaryHCompatiblePairs`.  This avoids
materializing the witness list inside the reflected proof term.
-/
def noSourceRawBoundaryHCompatiblePairsBool : Bool :=
  Figure18Site.all.all fun left =>
    Figure18Site.all.all fun right =>
      !sourceRawBoundaryHCompatiblePairBool left right

/--
Boolean no-witness form of `sourceRawBoundaryVCompatiblePairs`.  This avoids
materializing the witness list inside the reflected proof term.
-/
def noSourceRawBoundaryVCompatiblePairsBool : Bool :=
  Figure18Site.all.all fun lower =>
    Figure18Site.all.all fun upper =>
      !sourceRawBoundaryVCompatiblePairBool lower upper

theorem noSourceRawBoundaryHCompatiblePairsBool_eq_true_iff :
    noSourceRawBoundaryHCompatiblePairsBool = true ↔
      ∀ left right : Figure18Site,
        sourceRawBoundaryHCompatiblePairBool left right = false := by
  constructor
  · intro hcheck left right
    unfold noSourceRawBoundaryHCompatiblePairsBool at hcheck
    have hleftCheck :=
      List.all_eq_true.1 hcheck left (Figure18Site.mem_all left)
    have hrightCheck :=
      List.all_eq_true.1 hleftCheck right (Figure18Site.mem_all right)
    cases hcompat : sourceRawBoundaryHCompatiblePairBool left right <;>
      simp [hcompat] at hrightCheck ⊢
  · intro hpairs
    unfold noSourceRawBoundaryHCompatiblePairsBool
    apply List.all_eq_true.2
    intro left _
    apply List.all_eq_true.2
    intro right _
    simp [hpairs left right]

theorem noSourceRawBoundaryVCompatiblePairsBool_eq_true_iff :
    noSourceRawBoundaryVCompatiblePairsBool = true ↔
      ∀ lower upper : Figure18Site,
        sourceRawBoundaryVCompatiblePairBool lower upper = false := by
  constructor
  · intro hcheck lower upper
    unfold noSourceRawBoundaryVCompatiblePairsBool at hcheck
    have hlowerCheck :=
      List.all_eq_true.1 hcheck lower (Figure18Site.mem_all lower)
    have hupperCheck :=
      List.all_eq_true.1 hlowerCheck upper (Figure18Site.mem_all upper)
    cases hcompat : sourceRawBoundaryVCompatiblePairBool lower upper <;>
      simp [hcompat] at hupperCheck ⊢
  · intro hpairs
    unfold noSourceRawBoundaryVCompatiblePairsBool
    apply List.all_eq_true.2
    intro lower _
    apply List.all_eq_true.2
    intro upper _
    simp [hpairs lower upper]

set_option linter.style.nativeDecide false in
-- Native evaluation keeps this finite diagnostic from expanding a large
-- reflected pair search into a kernel proof term.
/--
The over-strong source/raw-boundary board diagnostic has no horizontal
two-cell witness in the current Figure 13/Figure 16 transcription.
-/
theorem noSourceRawBoundaryHCompatiblePairsBool_eq_true :
    noSourceRawBoundaryHCompatiblePairsBool = true := by
  native_decide

set_option linter.style.nativeDecide false in
-- Native evaluation keeps this finite diagnostic from expanding a large
-- reflected pair search into a kernel proof term.
/--
The over-strong source/raw-boundary board diagnostic has no vertical two-cell
witness in the current Figure 13/Figure 16 transcription.
-/
theorem noSourceRawBoundaryVCompatiblePairsBool_eq_true :
    noSourceRawBoundaryVCompatiblePairsBool = true := by
  native_decide

/--
Pointwise horizontal form of the reflected no-witness check.
-/
theorem sourceRawBoundaryHCompatiblePairBool_eq_false
    (left right : Figure18Site) :
    sourceRawBoundaryHCompatiblePairBool left right = false :=
  noSourceRawBoundaryHCompatiblePairsBool_eq_true_iff.1
    noSourceRawBoundaryHCompatiblePairsBool_eq_true left right

/--
Pointwise vertical form of the reflected no-witness check.
-/
theorem sourceRawBoundaryVCompatiblePairBool_eq_false
    (lower upper : Figure18Site) :
    sourceRawBoundaryVCompatiblePairBool lower upper = false :=
  noSourceRawBoundaryVCompatiblePairsBool_eq_true_iff.1
    noSourceRawBoundaryVCompatiblePairsBool_eq_true lower upper

theorem canonicalFigure16SourceRawBoundaryLevelChecks_of_levelCertificates
    (hlevel : HasCanonicalFigure16SourceRawBoundaryLevelCertificates) :
    HasCanonicalFigure16SourceRawBoundaryLevelChecks := by
  intro level
  rcases hlevel level with ⟨cert⟩
  exact ⟨cert.source, cert.stackCompatible, cert.rawBoundary⟩

theorem canonicalFigure16SourceRawBoundaryLevelChecks_of_checkedLevelData
    (hlevel : HasCanonicalFigure16SourceRawBoundaryCheckedLevelData) :
    HasCanonicalFigure16SourceRawBoundaryLevelChecks := by
  intro level
  rcases hlevel level with ⟨data⟩
  exact ⟨data.sites.toSiteRectangle, data.stackCompatible,
    data.rawBoundary⟩

theorem canonicalFigure16SourceRawBoundaryCheckedLevelData_of_levelChecks
    (hlevel : HasCanonicalFigure16SourceRawBoundaryLevelChecks) :
    HasCanonicalFigure16SourceRawBoundaryCheckedLevelData := by
  intro level
  rcases hlevel level with ⟨source, hstack, hraw⟩
  let sites := source.toCheckedNatSiteRectangle
  have hsites : sites.toSiteRectangle = source :=
    CheckedNatSiteRectangle.toSiteRectangle_eq_of_matchesSiteRectangleBool
      (SiteRectangle.toCheckedNatSiteRectangle_matchesSiteRectangleBool source)
  exact ⟨{
    sites := sites
    stackCompatible := by
      simpa [hsites] using hstack
    rawBoundary := by
      simpa [hsites] using hraw
  }⟩

theorem canonicalFigure16SourceRawBoundaryLevelChecks_iff_checkedLevelData :
    HasCanonicalFigure16SourceRawBoundaryLevelChecks ↔
      HasCanonicalFigure16SourceRawBoundaryCheckedLevelData :=
  ⟨canonicalFigure16SourceRawBoundaryCheckedLevelData_of_levelChecks,
    canonicalFigure16SourceRawBoundaryLevelChecks_of_checkedLevelData⟩

theorem canonicalFigure16SourceRawBoundaryBoardLevelChecks_of_checkedBoardLevelData
    (hlevel : HasCanonicalFigure16SourceRawBoundaryCheckedBoardLevelData) :
    HasCanonicalFigure16SourceRawBoundaryBoardLevelChecks := by
  intro level
  rcases hlevel level with ⟨data⟩
  exact ⟨data.sites.toSiteRectangle, data.stackCompatible,
    data.rawBoundary⟩

theorem canonicalFigure16SourceRawBoundaryCheckedBoardLevelData_of_boardLevelChecks
    (hlevel : HasCanonicalFigure16SourceRawBoundaryBoardLevelChecks) :
    HasCanonicalFigure16SourceRawBoundaryCheckedBoardLevelData := by
  intro level
  rcases hlevel level with ⟨source, hstack, hraw⟩
  let sites := source.toCheckedNatSiteRectangle
  have hsites : sites.toSiteRectangle = source :=
    CheckedNatSiteRectangle.toSiteRectangle_eq_of_matchesSiteRectangleBool
      (SiteRectangle.toCheckedNatSiteRectangle_matchesSiteRectangleBool source)
  exact ⟨{
    sites := sites
    stackCompatible := by
      simpa [hsites] using hstack
    rawBoundary := by
      simpa [hsites] using hraw
  }⟩

theorem canonicalFigure16SourceRawBoundaryBoardLevelChecks_iff_checkedBoardLevelData :
    HasCanonicalFigure16SourceRawBoundaryBoardLevelChecks ↔
      HasCanonicalFigure16SourceRawBoundaryCheckedBoardLevelData :=
  ⟨canonicalFigure16SourceRawBoundaryCheckedBoardLevelData_of_boardLevelChecks,
    canonicalFigure16SourceRawBoundaryBoardLevelChecks_of_checkedBoardLevelData⟩

/--
Exact positive board-level raw Figure 13 checked data supplies the Section 7
positive-board aligned macro-square interface.
-/
theorem robinsonPositiveBoardLevelAlignedMacroSquares_of_checkedPositiveBoardLevelData
    (hlevel : HasFigure13PositiveBoardLevelCheckedData) :
    HasFigure13RobinsonPositiveBoardLevelAlignedMacroSquares := by
  intro level
  rcases hlevel level with ⟨data⟩
  exact ⟨data.sites.toSiteRectangle,
    SiteRectangle.rawBoundaryCompatible_of_rawBoundaryCompatibleBool
      data.rawBoundary⟩

/--
The positive-board aligned macro-square interface can be re-expressed as exact
row-major checked data.
-/
theorem checkedPositiveBoardLevelData_of_robinsonPositiveBoardLevelAlignedMacroSquares
    (hlevel : HasFigure13RobinsonPositiveBoardLevelAlignedMacroSquares) :
    HasFigure13PositiveBoardLevelCheckedData := by
  intro level
  rcases hlevel level with ⟨source, hraw⟩
  let sites := source.toCheckedNatSiteRectangle
  have hsites : sites.toSiteRectangle = source :=
    CheckedNatSiteRectangle.toSiteRectangle_eq_of_matchesSiteRectangleBool
      (SiteRectangle.toCheckedNatSiteRectangle_matchesSiteRectangleBool source)
  refine ⟨{ sites := sites, rawBoundary := ?_ }⟩
  rw [hsites]
  exact SiteRectangle.rawBoundaryCompatibleBool_of_rawBoundaryCompatible hraw

/--
Exact checked data is equivalent to the positive-board aligned macro-square
interface.
-/
theorem checkedPositiveBoardLevelData_iff_robinsonPositiveBoardLevelAlignedMacroSquares :
    HasFigure13PositiveBoardLevelCheckedData ↔
      HasFigure13RobinsonPositiveBoardLevelAlignedMacroSquares :=
  ⟨robinsonPositiveBoardLevelAlignedMacroSquares_of_checkedPositiveBoardLevelData,
    checkedPositiveBoardLevelData_of_robinsonPositiveBoardLevelAlignedMacroSquares⟩

/--
Propositional positive-board raw data supplies the Boolean checked positive
board-level data.
-/
theorem checkedPositiveBoardLevelData_of_rawPositiveBoardLevelData
    (hlevel : HasFigure13PositiveBoardLevelRawData) :
    HasFigure13PositiveBoardLevelCheckedData := by
  intro level
  rcases hlevel level with ⟨data⟩
  exact ⟨{
    sites := data.sites
    rawBoundary :=
      SiteRectangle.rawBoundaryCompatibleBool_of_rawBoundaryCompatible
        data.rawBoundary
  }⟩

/--
Boolean checked positive-board data supplies the propositional raw-boundary
form.
-/
theorem rawPositiveBoardLevelData_of_checkedPositiveBoardLevelData
    (hlevel : HasFigure13PositiveBoardLevelCheckedData) :
    HasFigure13PositiveBoardLevelRawData := by
  intro level
  rcases hlevel level with ⟨data⟩
  exact ⟨{
    sites := data.sites
    rawBoundary :=
      SiteRectangle.rawBoundaryCompatible_of_rawBoundaryCompatibleBool
        data.rawBoundary
  }⟩

/--
The propositional and Boolean checked forms of exact positive-board raw Figure
13 data are equivalent.
-/
theorem rawPositiveBoardLevelData_iff_checkedPositiveBoardLevelData :
    HasFigure13PositiveBoardLevelRawData ↔
      HasFigure13PositiveBoardLevelCheckedData :=
  ⟨checkedPositiveBoardLevelData_of_rawPositiveBoardLevelData,
    rawPositiveBoardLevelData_of_checkedPositiveBoardLevelData⟩

/--
Unshifted canonical Figure 16 source/raw-boundary checked level data is already
too strong for the current transcription: shifting level `n` to `n + 1`
forgets to exact positive board-level raw Figure 13 checked data.
-/
theorem checkedPositiveBoardLevelData_of_canonicalRawBoundaryCheckedLevelData
    (hlevel : HasCanonicalFigure16SourceRawBoundaryCheckedLevelData) :
    HasFigure13PositiveBoardLevelCheckedData := by
  intro level
  rcases hlevel (level + 1) with ⟨data⟩
  exact ⟨{
    sites := data.sites
    rawBoundary := data.rawBoundary
  }⟩

/--
Canonical Figure 16 source/raw-boundary level checks are too strong: they
forget to exact positive board-level raw Figure 13 checked data.
-/
theorem checkedPositiveBoardLevelData_of_canonicalRawBoundaryLevelChecks
    (hlevel : HasCanonicalFigure16SourceRawBoundaryLevelChecks) :
    HasFigure13PositiveBoardLevelCheckedData :=
  checkedPositiveBoardLevelData_of_canonicalRawBoundaryCheckedLevelData
    (canonicalFigure16SourceRawBoundaryCheckedLevelData_of_levelChecks hlevel)

/--
Canonical Figure 16 source/raw-boundary level certificates are too strong:
they forget to exact positive board-level raw Figure 13 checked data.
-/
theorem checkedPositiveBoardLevelData_of_canonicalRawBoundaryLevelCertificates
    (hlevel : HasCanonicalFigure16SourceRawBoundaryLevelCertificates) :
    HasFigure13PositiveBoardLevelCheckedData :=
  checkedPositiveBoardLevelData_of_canonicalRawBoundaryLevelChecks
    (canonicalFigure16SourceRawBoundaryLevelChecks_of_levelCertificates hlevel)

/--
Canonical Figure 16 source/raw-boundary macro-square witnesses are too strong:
they forget to exact positive board-level raw Figure 13 checked data after the
same level shift.
-/
theorem checkedPositiveBoardLevelData_of_canonicalRawBoundaryMacroSquares
    (hlevel : HasCanonicalCheckedFigure16SourceRawBoundaryMacroSquares) :
    HasFigure13PositiveBoardLevelCheckedData := by
  intro level
  rcases hlevel (level + 1) with ⟨source, _hstack, hraw⟩
  let sites := source.toCheckedNatSiteRectangle
  have hsites : sites.toSiteRectangle = source :=
    CheckedNatSiteRectangle.toSiteRectangle_eq_of_matchesSiteRectangleBool
      (SiteRectangle.toCheckedNatSiteRectangle_matchesSiteRectangleBool source)
  exact ⟨{
    sites := sites
    rawBoundary := by
      rw [hsites]
      exact SiteRectangle.rawBoundaryCompatibleBool_of_rawBoundaryCompatible hraw
  }⟩

/--
Propositional positive-board raw data gives the exact board-level raw Figure 13
square tilings at Robinson's shifted Section 7 free-grid sizes.
-/
theorem positiveBoardLevelTileableSquares_of_rawPositiveBoardLevelData
    (hlevel : HasFigure13PositiveBoardLevelRawData) :
    HasFigure13PositiveBoardLevelTileableSquares := by
  intro level
  rcases hlevel level with ⟨data⟩
  exact data.sites.toSiteRectangle.tileableRawSquare_of_rawBoundaryCompatible
    data.rawBoundary

/--
Boolean checked positive-board data gives the exact board-level raw Figure 13
square tilings at Robinson's shifted Section 7 free-grid sizes.
-/
theorem positiveBoardLevelTileableSquares_of_checkedPositiveBoardLevelData
    (hlevel : HasFigure13PositiveBoardLevelCheckedData) :
    HasFigure13PositiveBoardLevelTileableSquares :=
  positiveBoardLevelTileableSquares_of_rawPositiveBoardLevelData
    (rawPositiveBoardLevelData_of_checkedPositiveBoardLevelData hlevel)

/--
Positive Robinson-board aligned macro-squares are exactly ordinary raw Figure
13 square tilings at the shifted Section 7 free-grid sizes.
-/
theorem positiveBoardLevelTileableSquares_of_robinsonPositiveBoardLevelAlignedMacroSquares
    (hlevel : HasFigure13RobinsonPositiveBoardLevelAlignedMacroSquares) :
    HasFigure13PositiveBoardLevelTileableSquares := by
  intro level
  rcases hlevel level with ⟨R, hcompat⟩
  exact R.tileableRawSquare_of_rawBoundaryCompatible hcompat

/--
Exact positive board-level raw Figure 13 square tilings are equivalent to the
propositional raw-boundary data surface.
-/
theorem positiveBoardLevelTileableSquares_iff_rawPositiveBoardLevelData :
    HasFigure13PositiveBoardLevelTileableSquares ↔
      HasFigure13PositiveBoardLevelRawData :=
  ⟨rawPositiveBoardLevelData_of_positiveBoardLevelTileableSquares,
    positiveBoardLevelTileableSquares_of_rawPositiveBoardLevelData⟩

/--
Exact positive board-level raw Figure 13 square tilings are equivalent to the
checked positive-board data surface.
-/
theorem positiveBoardLevelTileableSquares_iff_checkedPositiveBoardLevelData :
    HasFigure13PositiveBoardLevelTileableSquares ↔
      HasFigure13PositiveBoardLevelCheckedData := by
  exact
    positiveBoardLevelTileableSquares_iff_rawPositiveBoardLevelData.trans
      rawPositiveBoardLevelData_iff_checkedPositiveBoardLevelData

/--
Exact positive board-level raw Figure 13 square tilings are equivalent to the
positive Robinson-board aligned macro-square surface.
-/
theorem
    positiveBoardLevelTileableSquares_iff_robinsonPositiveBoardLevelAlignedMacroSquares :
    HasFigure13PositiveBoardLevelTileableSquares ↔
      HasFigure13RobinsonPositiveBoardLevelAlignedMacroSquares := by
  exact
    positiveBoardLevelTileableSquares_iff_checkedPositiveBoardLevelData.trans
      checkedPositiveBoardLevelData_iff_robinsonPositiveBoardLevelAlignedMacroSquares

/--
The over-strong row-major checked Figure 16 source raw-boundary board target
forgets to the exact positive board-level raw Figure 13 checked data.
-/
theorem checkedPositiveBoardLevelData_of_canonicalRawBoundaryCheckedBoardLevelData
    (hlevel : HasCanonicalFigure16SourceRawBoundaryCheckedBoardLevelData) :
    HasFigure13PositiveBoardLevelCheckedData := by
  intro level
  rcases hlevel level with ⟨data⟩
  exact ⟨{ sites := data.sites, rawBoundary := data.rawBoundary }⟩

/--
The over-strong Figure 16 source raw-boundary board checks imply the exact
positive board-level raw Figure 13 checked data.
-/
theorem checkedPositiveBoardLevelData_of_canonicalRawBoundaryBoardLevelChecks
    (hlevel : HasCanonicalFigure16SourceRawBoundaryBoardLevelChecks) :
    HasFigure13PositiveBoardLevelCheckedData :=
  checkedPositiveBoardLevelData_of_canonicalRawBoundaryCheckedBoardLevelData
    (canonicalFigure16SourceRawBoundaryCheckedBoardLevelData_of_boardLevelChecks
      hlevel)

/--
The over-strong row-major Figure 16 source raw-boundary board data gives the
exact board-level raw Figure 13 square tilings.
-/
theorem positiveBoardLevelTileableSquares_of_canonicalRawBoundaryCheckedBoardLevelData
    (hlevel : HasCanonicalFigure16SourceRawBoundaryCheckedBoardLevelData) :
    HasFigure13PositiveBoardLevelTileableSquares :=
  positiveBoardLevelTileableSquares_of_checkedPositiveBoardLevelData
    (checkedPositiveBoardLevelData_of_canonicalRawBoundaryCheckedBoardLevelData
      hlevel)

/--
The over-strong Figure 16 source raw-boundary board checks give the exact
board-level raw Figure 13 square tilings.
-/
theorem positiveBoardLevelTileableSquares_of_canonicalRawBoundaryBoardLevelChecks
    (hlevel : HasCanonicalFigure16SourceRawBoundaryBoardLevelChecks) :
    HasFigure13PositiveBoardLevelTileableSquares :=
  positiveBoardLevelTileableSquares_of_checkedPositiveBoardLevelData
    (checkedPositiveBoardLevelData_of_canonicalRawBoundaryBoardLevelChecks
      hlevel)

theorem canonicalFigure16SourceRawBoundaryLevelCertificates_of_levelChecks
    (hlevel : HasCanonicalFigure16SourceRawBoundaryLevelChecks) :
    HasCanonicalFigure16SourceRawBoundaryLevelCertificates := by
  intro level
  rcases hlevel level with ⟨source, hstack, hraw⟩
  exact ⟨{
    source := source
    stackCompatible := hstack
    rawBoundary := hraw
  }⟩

theorem canonicalFigure16SourceRawBoundaryLevelChecks_iff_levelCertificates :
    HasCanonicalFigure16SourceRawBoundaryLevelChecks ↔
      HasCanonicalFigure16SourceRawBoundaryLevelCertificates :=
  ⟨canonicalFigure16SourceRawBoundaryLevelCertificates_of_levelChecks,
    canonicalFigure16SourceRawBoundaryLevelChecks_of_levelCertificates⟩

theorem canonicalCheckedFigure16SourceRawBoundaryBool_of_levelCertificates
    (hlevel : HasCanonicalFigure16SourceRawBoundaryLevelCertificates) :
    HasCanonicalCheckedFigure16SourceRawBoundaryMacroSquaresBool := by
  intro level
  rcases hlevel level with ⟨cert⟩
  exact ⟨cert.source, cert.stackCompatible, cert.rawBoundary⟩

theorem canonicalCheckedFigure16SourceRawBoundaryBool_of_levelChecks
    (hlevel : HasCanonicalFigure16SourceRawBoundaryLevelChecks) :
    HasCanonicalCheckedFigure16SourceRawBoundaryMacroSquaresBool :=
  canonicalCheckedFigure16SourceRawBoundaryBool_of_levelCertificates
    (canonicalFigure16SourceRawBoundaryLevelCertificates_of_levelChecks hlevel)

theorem canonicalFigure16SourceRawBoundaryLevelCertificates_of_bool
    (hlevel : HasCanonicalCheckedFigure16SourceRawBoundaryMacroSquaresBool) :
    HasCanonicalFigure16SourceRawBoundaryLevelCertificates := by
  intro level
  rcases hlevel level with ⟨source, hstack, hraw⟩
  exact ⟨{
    source := source
    stackCompatible := hstack
    rawBoundary := hraw
  }⟩

theorem canonicalFigure16SourceRawBoundaryLevelChecks_of_bool
    (hlevel : HasCanonicalCheckedFigure16SourceRawBoundaryMacroSquaresBool) :
    HasCanonicalFigure16SourceRawBoundaryLevelChecks :=
  canonicalFigure16SourceRawBoundaryLevelChecks_of_levelCertificates
    (canonicalFigure16SourceRawBoundaryLevelCertificates_of_bool hlevel)

theorem canonicalCheckedFigure16SourceRawBoundaryBool_iff_levelCertificates :
    HasCanonicalCheckedFigure16SourceRawBoundaryMacroSquaresBool ↔
      HasCanonicalFigure16SourceRawBoundaryLevelCertificates :=
  ⟨canonicalFigure16SourceRawBoundaryLevelCertificates_of_bool,
    canonicalCheckedFigure16SourceRawBoundaryBool_of_levelCertificates⟩

theorem canonicalCheckedFigure16SourceRawBoundaryBool_iff_levelChecks :
    HasCanonicalCheckedFigure16SourceRawBoundaryMacroSquaresBool ↔
      HasCanonicalFigure16SourceRawBoundaryLevelChecks :=
  ⟨canonicalFigure16SourceRawBoundaryLevelChecks_of_bool,
    canonicalCheckedFigure16SourceRawBoundaryBool_of_levelChecks⟩

theorem canonicalCheckedFigure16SourceRawBoundary_of_bool
    (hlevel : HasCanonicalCheckedFigure16SourceRawBoundaryMacroSquaresBool) :
    HasCanonicalCheckedFigure16SourceRawBoundaryMacroSquares := by
  intro level
  rcases hlevel level with ⟨source, hcompatible, hraw⟩
  exact ⟨source, hcompatible,
    SiteRectangle.rawBoundaryCompatible_of_rawBoundaryCompatibleBool hraw⟩

theorem canonicalCheckedFigure16SourceRawBoundary_of_levelCertificates
    (hlevel : HasCanonicalFigure16SourceRawBoundaryLevelCertificates) :
    HasCanonicalCheckedFigure16SourceRawBoundaryMacroSquares :=
  canonicalCheckedFigure16SourceRawBoundary_of_bool
    (canonicalCheckedFigure16SourceRawBoundaryBool_of_levelCertificates hlevel)

/--
Boolean canonical Figure 16 source/raw-boundary macro-square witnesses are too
strong for the same reason as their propositional form.
-/
theorem checkedPositiveBoardLevelData_of_canonicalRawBoundaryMacroSquaresBool
    (hlevel : HasCanonicalCheckedFigure16SourceRawBoundaryMacroSquaresBool) :
    HasFigure13PositiveBoardLevelCheckedData :=
  checkedPositiveBoardLevelData_of_canonicalRawBoundaryMacroSquares
    (canonicalCheckedFigure16SourceRawBoundary_of_bool hlevel)

/--
The unshifted canonical Figure 16 source/raw-boundary checked level-data
surface is impossible for the current Figure 13 transcription.
-/
theorem not_hasCanonicalFigure16SourceRawBoundaryCheckedLevelData :
    ¬ HasCanonicalFigure16SourceRawBoundaryCheckedLevelData := by
  intro hlevel
  exact not_hasFigure13PositiveBoardLevelTileableSquares
    (positiveBoardLevelTileableSquares_of_checkedPositiveBoardLevelData
      (checkedPositiveBoardLevelData_of_canonicalRawBoundaryCheckedLevelData
        hlevel))

/--
The unshifted canonical Figure 16 source/raw-boundary level-check surface is
impossible for the current Figure 13 transcription.
-/
theorem not_hasCanonicalFigure16SourceRawBoundaryLevelChecks :
    ¬ HasCanonicalFigure16SourceRawBoundaryLevelChecks := by
  intro hlevel
  exact not_hasCanonicalFigure16SourceRawBoundaryCheckedLevelData
    (canonicalFigure16SourceRawBoundaryCheckedLevelData_of_levelChecks hlevel)

/--
The unshifted canonical Figure 16 source/raw-boundary level-certificate surface
is impossible for the current Figure 13 transcription.
-/
theorem not_hasCanonicalFigure16SourceRawBoundaryLevelCertificates :
    ¬ HasCanonicalFigure16SourceRawBoundaryLevelCertificates := by
  intro hlevel
  exact not_hasCanonicalFigure16SourceRawBoundaryLevelChecks
    (canonicalFigure16SourceRawBoundaryLevelChecks_of_levelCertificates hlevel)

/--
The canonical Figure 16 source/raw-boundary macro-square surface is impossible
for the current Figure 13 transcription.
-/
theorem not_hasCanonicalCheckedFigure16SourceRawBoundaryMacroSquares :
    ¬ HasCanonicalCheckedFigure16SourceRawBoundaryMacroSquares := by
  intro hlevel
  exact not_hasFigure13PositiveBoardLevelTileableSquares
    (positiveBoardLevelTileableSquares_of_checkedPositiveBoardLevelData
      (checkedPositiveBoardLevelData_of_canonicalRawBoundaryMacroSquares
        hlevel))

/--
The Boolean canonical Figure 16 source/raw-boundary macro-square surface is
impossible for the current Figure 13 transcription.
-/
theorem not_hasCanonicalCheckedFigure16SourceRawBoundaryMacroSquaresBool :
    ¬ HasCanonicalCheckedFigure16SourceRawBoundaryMacroSquaresBool := by
  intro hlevel
  exact not_hasCanonicalCheckedFigure16SourceRawBoundaryMacroSquares
    (canonicalCheckedFigure16SourceRawBoundary_of_bool hlevel)

/--
The shifted board-level source/raw-boundary checked data is also impossible:
it is exactly a checked positive board-level raw Figure 13 target.
-/
theorem not_hasCanonicalFigure16SourceRawBoundaryCheckedBoardLevelData :
    ¬ HasCanonicalFigure16SourceRawBoundaryCheckedBoardLevelData := by
  intro hlevel
  exact not_hasFigure13PositiveBoardLevelTileableSquares
    (positiveBoardLevelTileableSquares_of_checkedPositiveBoardLevelData
      (checkedPositiveBoardLevelData_of_canonicalRawBoundaryCheckedBoardLevelData
        hlevel))

/--
The shifted board-level source/raw-boundary level-check surface is impossible
for the current Figure 13 transcription.
-/
theorem not_hasCanonicalFigure16SourceRawBoundaryBoardLevelChecks :
    ¬ HasCanonicalFigure16SourceRawBoundaryBoardLevelChecks := by
  intro hlevel
  exact not_hasCanonicalFigure16SourceRawBoundaryCheckedBoardLevelData
    (canonicalFigure16SourceRawBoundaryCheckedBoardLevelData_of_boardLevelChecks
      hlevel)

theorem robinsonBoardLevelAlignedMacroSquares_of_canonicalCheckedFigure16SourceRawBoundary
    (hlevel : HasCanonicalCheckedFigure16SourceRawBoundaryMacroSquares) :
    HasFigure13RobinsonBoardLevelAlignedMacroSquares := by
  intro level
  rcases hlevel level with ⟨source, _hcompatible, hraw⟩
  exact ⟨source, hraw⟩

theorem robinsonBoardLevelAlignedMacroSquares_of_canonicalCheckedFigure16SourceRawBoundaryBool
    (hlevel : HasCanonicalCheckedFigure16SourceRawBoundaryMacroSquaresBool) :
    HasFigure13RobinsonBoardLevelAlignedMacroSquares :=
  robinsonBoardLevelAlignedMacroSquares_of_canonicalCheckedFigure16SourceRawBoundary
    (canonicalCheckedFigure16SourceRawBoundary_of_bool hlevel)

theorem figure16RecognizedRobinsonBoardLevelMacroSquares_of_checked
    (hlevel : HasCheckedFigure16RecognizedRobinsonBoardLevelMacroSquares) :
    HasFigure16RecognizedRobinsonBoardLevelMacroSquares := by
  intro level
  rcases hlevel level with ⟨source, stack, target, hrecognized, hraw⟩
  exact ⟨source, stack, target,
    Figure16ExpandedSiteRectangle.of_matchesBool hrecognized,
    SiteRectangle.rawBoundaryCompatible_of_rawBoundaryCompatibleBool hraw⟩

theorem checkedFigure16RecognizedRobinsonBoardLevelMacroSquares_of_canonical
    (hlevel :
      HasCanonicalCheckedFigure16RecognizedRobinsonBoardLevelMacroSquares) :
    HasCheckedFigure16RecognizedRobinsonBoardLevelMacroSquares := by
  intro level
  rcases hlevel level with ⟨source, hcompatible, target, hrecognized, hraw⟩
  exact ⟨(checkedLayerStackRectangleOfSiteRectangle source).siteRectangle,
    checkedLayerStackOfSiteRectangle source hcompatible, target,
      hrecognized, hraw⟩

theorem figure16RecognizedRobinsonBoardLevelMacroSquares_of_canonicalChecked
    (hlevel :
      HasCanonicalCheckedFigure16RecognizedRobinsonBoardLevelMacroSquares) :
    HasFigure16RecognizedRobinsonBoardLevelMacroSquares :=
  figure16RecognizedRobinsonBoardLevelMacroSquares_of_checked
    (checkedFigure16RecognizedRobinsonBoardLevelMacroSquares_of_canonical
      hlevel)

/--
Figure 16-recognized Robinson board macro-squares supply the cofinal aligned
raw Figure 13 macro-square target.
-/
theorem alignedMacroSquares_of_figure16RecognizedRobinsonBoardLevelMacroSquares
    (hlevel : HasFigure16RecognizedRobinsonBoardLevelMacroSquares) :
    HasAlignedFigure13MacroSquares := by
  intro n
  rcases RobinsonSquare.exists_level_with_payload_capacity n with
    ⟨level, hcap⟩
  rcases hlevel level with ⟨source, stack, target, _hrecognized, hraw⟩
  refine ⟨2 * RobinsonSquare.freeGridSide level, ?_, target, hraw⟩
  exact hcap.trans
    (Nat.le_mul_of_pos_left _ (by decide : 0 < 2))

/--
Figure 16-recognized Robinson board macro-squares compactly determine a raw
Figure 13 plane tiling.
-/
theorem tilesPlane_fig13Tiles_of_figure16RecognizedRobinsonBoardLevelMacroSquares
    (hlevel : HasFigure16RecognizedRobinsonBoardLevelMacroSquares) :
    TilesPlane fig13Tiles :=
  tilesPlane_fig13Tiles_of_alignedMacroSquares
    (alignedMacroSquares_of_figure16RecognizedRobinsonBoardLevelMacroSquares
      hlevel)

/--
Figure 16-recognized Robinson board macro-squares supply every centered raw
Figure 13 box.
-/
theorem tileableBoxes_fig13Tiles_of_figure16RecognizedRobinsonBoardLevelMacroSquares
    (hlevel : HasFigure16RecognizedRobinsonBoardLevelMacroSquares) :
    ∀ r : Nat, TileableBox fig13Tiles r :=
  tileableBoxes_fig13Tiles_of_alignedMacroSquares
    (alignedMacroSquares_of_figure16RecognizedRobinsonBoardLevelMacroSquares
      hlevel)

/--
Finite-checked Figure 16-recognized Robinson board macro-squares compactly
determine a raw Figure 13 plane tiling.
-/
theorem tilesPlane_fig13Tiles_of_checkedFigure16RecognizedRobinsonBoardLevelMacroSquares
    (hlevel : HasCheckedFigure16RecognizedRobinsonBoardLevelMacroSquares) :
    TilesPlane fig13Tiles :=
  tilesPlane_fig13Tiles_of_figure16RecognizedRobinsonBoardLevelMacroSquares
    (figure16RecognizedRobinsonBoardLevelMacroSquares_of_checked hlevel)

/--
Finite-checked Figure 16-recognized Robinson board macro-squares supply every
centered raw Figure 13 box.
-/
theorem tileableBoxes_fig13Tiles_of_checkedFigure16RecognizedRobinsonBoardLevelMacroSquares
    (hlevel : HasCheckedFigure16RecognizedRobinsonBoardLevelMacroSquares) :
    ∀ r : Nat, TileableBox fig13Tiles r :=
  tileableBoxes_fig13Tiles_of_figure16RecognizedRobinsonBoardLevelMacroSquares
    (figure16RecognizedRobinsonBoardLevelMacroSquares_of_checked hlevel)

/--
Canonical finite-checked Figure 16-recognized Robinson board macro-squares
compactly determine a raw Figure 13 plane tiling.
-/
theorem tilesPlane_fig13Tiles_of_canonicalCheckedFigure16RecognizedRobinsonBoardLevelMacroSquares
    (hlevel :
      HasCanonicalCheckedFigure16RecognizedRobinsonBoardLevelMacroSquares) :
    TilesPlane fig13Tiles :=
  tilesPlane_fig13Tiles_of_checkedFigure16RecognizedRobinsonBoardLevelMacroSquares
    (checkedFigure16RecognizedRobinsonBoardLevelMacroSquares_of_canonical
      hlevel)

/--
Canonical finite-checked Figure 16-recognized Robinson board macro-squares
supply every centered raw Figure 13 box.
-/
theorem tileableBoxes_fig13Tiles_of_canonicalCheckedFigure16RecognizedRobinsonBoardLevelMacroSquares
    (hlevel :
      HasCanonicalCheckedFigure16RecognizedRobinsonBoardLevelMacroSquares) :
    ∀ r : Nat, TileableBox fig13Tiles r :=
  tileableBoxes_fig13Tiles_of_checkedFigure16RecognizedRobinsonBoardLevelMacroSquares
    (checkedFigure16RecognizedRobinsonBoardLevelMacroSquares_of_canonical
      hlevel)

/--
Canonical source raw-boundary macro-squares supply cofinal aligned raw Figure
13 macro-squares.
-/
theorem alignedMacroSquares_of_canonicalCheckedFigure16SourceRawBoundary
    (hlevel : HasCanonicalCheckedFigure16SourceRawBoundaryMacroSquares) :
    HasAlignedFigure13MacroSquares := by
  intro n
  rcases RobinsonSquare.exists_level_with_payload_capacity n with
    ⟨level, hcap⟩
  rcases hlevel level with ⟨source, _hcompatible, hraw⟩
  exact ⟨RobinsonSquare.freeGridSide level, hcap, source, hraw⟩

/--
Canonical source raw-boundary macro-squares compactly determine a raw Figure 13
plane tiling.
-/
theorem tilesPlane_fig13Tiles_of_canonicalCheckedFigure16SourceRawBoundary
    (hlevel : HasCanonicalCheckedFigure16SourceRawBoundaryMacroSquares) :
    TilesPlane fig13Tiles :=
  tilesPlane_fig13Tiles_of_alignedMacroSquares
    (alignedMacroSquares_of_canonicalCheckedFigure16SourceRawBoundary hlevel)

/--
Canonical source raw-boundary macro-squares supply every centered raw Figure 13
box.
-/
theorem tileableBoxes_fig13Tiles_of_canonicalCheckedFigure16SourceRawBoundary
    (hlevel : HasCanonicalCheckedFigure16SourceRawBoundaryMacroSquares) :
    ∀ r : Nat, TileableBox fig13Tiles r :=
  tileableBoxes_fig13Tiles_of_alignedMacroSquares
    (alignedMacroSquares_of_canonicalCheckedFigure16SourceRawBoundary hlevel)

/--
Shifted Robinson board-level source raw-boundary checks supply cofinal aligned
raw Figure 13 macro-squares.

The shift by one level matches Robinson's Section 7 count, whose first board
has `2^1 + 1 = 3` free rows/columns.  For a requested square of side `n`, the
board indexed by `n` has side `freeGridSide (n + 1)`, which is large enough.
-/
theorem alignedMacroSquares_of_canonicalFigure16SourceRawBoundaryBoardLevelChecks
    (hlevel : HasCanonicalFigure16SourceRawBoundaryBoardLevelChecks) :
    HasAlignedFigure13MacroSquares := by
  intro n
  rcases hlevel n with ⟨source, _hcompatible, hraw⟩
  refine ⟨RobinsonSquare.freeGridSide (n + 1), ?_, source,
    SiteRectangle.rawBoundaryCompatible_of_rawBoundaryCompatibleBool hraw⟩
  exact Nat.le_trans (Nat.le_succ n)
    (RobinsonSquare.self_le_freeGridSide (n + 1))

/--
Shifted Robinson board-level source raw-boundary checks supply the positive
board-level aligned raw Figure 13 macro-square interface.
-/
theorem robinsonPositiveBoardLevelAlignedMacroSquares_of_canonicalBoardLevelChecks
    (hlevel : HasCanonicalFigure16SourceRawBoundaryBoardLevelChecks) :
    HasFigure13RobinsonPositiveBoardLevelAlignedMacroSquares := by
  intro level
  rcases hlevel level with ⟨source, _hcompatible, hraw⟩
  exact ⟨source,
    SiteRectangle.rawBoundaryCompatible_of_rawBoundaryCompatibleBool hraw⟩

/--
Shifted Robinson board-level source raw-boundary checks compactly determine a
raw Figure 13 plane tiling.
-/
theorem tilesPlane_fig13Tiles_of_canonicalFigure16SourceRawBoundaryBoardLevelChecks
    (hlevel : HasCanonicalFigure16SourceRawBoundaryBoardLevelChecks) :
    TilesPlane fig13Tiles :=
  tilesPlane_fig13Tiles_of_alignedMacroSquares
    (alignedMacroSquares_of_canonicalFigure16SourceRawBoundaryBoardLevelChecks
      hlevel)

/--
Shifted Robinson board-level source raw-boundary checks supply every centered
raw Figure 13 box.
-/
theorem tileableBoxes_fig13Tiles_of_canonicalFigure16SourceRawBoundaryBoardLevelChecks
    (hlevel : HasCanonicalFigure16SourceRawBoundaryBoardLevelChecks) :
    ∀ r : Nat, TileableBox fig13Tiles r :=
  tileableBoxes_fig13Tiles_of_alignedMacroSquares
    (alignedMacroSquares_of_canonicalFigure16SourceRawBoundaryBoardLevelChecks
      hlevel)

/--
Row-major checked shifted board-level data compactly determines a raw Figure 13
plane tiling.
-/
theorem tilesPlane_fig13Tiles_of_canonicalFigure16SourceRawBoundaryCheckedBoardLevelData
    (hlevel : HasCanonicalFigure16SourceRawBoundaryCheckedBoardLevelData) :
    TilesPlane fig13Tiles :=
  tilesPlane_fig13Tiles_of_canonicalFigure16SourceRawBoundaryBoardLevelChecks
    (canonicalFigure16SourceRawBoundaryBoardLevelChecks_of_checkedBoardLevelData
      hlevel)

/--
Row-major checked shifted board-level data supplies every centered raw Figure
13 box.
-/
theorem tileableBoxes_fig13Tiles_of_canonicalFigure16SourceRawBoundaryCheckedBoardLevelData
    (hlevel : HasCanonicalFigure16SourceRawBoundaryCheckedBoardLevelData) :
    ∀ r : Nat, TileableBox fig13Tiles r :=
  tileableBoxes_fig13Tiles_of_canonicalFigure16SourceRawBoundaryBoardLevelChecks
    (canonicalFigure16SourceRawBoundaryBoardLevelChecks_of_checkedBoardLevelData
      hlevel)

/--
Figure 16-recognized macro-squares whose targets are compatible Figure 18
site rectangles.

This is the compatibility-aware form of the Figure 16 scaffold target.  It does
not claim that the doubled target is already aligned as raw Figure 13 macro
tiles; it only requires the actual Figure 18 quarter-site adjacency needed for
tiling `figure18ScaffoldTiles`.
-/
def HasFigure16RecognizedCompatibleRobinsonBoardLevelMacroSquares : Prop :=
  ∀ level : Nat,
    ∃ source : SiteRectangle
      (RobinsonSquare.freeGridSide level) (RobinsonSquare.freeGridSide level),
      ∃ stack : LayerStackRectangle layerData source,
        ∃ target : SiteRectangle
          (2 * RobinsonSquare.freeGridSide level)
          (2 * RobinsonSquare.freeGridSide level),
          Figure16ExpandedSiteRectangle source stack target ∧
            Figure18SiteCompatibleRectangle target

/--
Finite-check version of the Figure 16-recognized compatible Figure 18
macro-square target.
-/
def HasCheckedFigure16RecognizedCompatibleRobinsonBoardLevelMacroSquares :
    Prop :=
  ∀ level : Nat,
    ∃ source : SiteRectangle
      (RobinsonSquare.freeGridSide level) (RobinsonSquare.freeGridSide level),
      ∃ stack : LayerStackRectangle layerData source,
        ∃ target : SiteRectangle
          (2 * RobinsonSquare.freeGridSide level)
          (2 * RobinsonSquare.freeGridSide level),
          Figure16ExpandedSiteRectangle.matchesBool stack target = true ∧
            figure18SiteCompatibleRectangleBool target = true

/--
Canonical finite-check version of the compatible Figure 18 macro-square target.
-/
def HasCanonicalCheckedFigure16RecognizedCompatibleRobinsonBoardLevelMacroSquares :
    Prop :=
  ∀ level : Nat,
    ∃ source : SiteRectangle
      (RobinsonSquare.freeGridSide level) (RobinsonSquare.freeGridSide level),
      ∃ hcompatible :
        (checkedLayerStackRectangleOfSiteRectangle source).compatibleBool
          layerData (checkedLayerStackRectangleOfSiteRectangle_lookupBool source) =
            true,
        ∃ target : SiteRectangle
          (2 * RobinsonSquare.freeGridSide level)
          (2 * RobinsonSquare.freeGridSide level),
          Figure16ExpandedSiteRectangle.matchesBool
            (checkedLayerStackOfSiteRectangle source hcompatible) target =
              true ∧
            figure18SiteCompatibleRectangleBool target = true

/--
Concrete row-major checked data for one compatible Figure 16 recognized
Robinson board/free-grid level.

This is the finite-data form of
`HasCanonicalCheckedFigure16RecognizedCompatibleRobinsonBoardLevelMacroSquares`:
`sourceSites` stores the selected source Figure 18 sites, `targetSites` stores
the doubled Figure 16 expansion target, and the three boolean fields are the
checked layer-stack compatibility, Figure 16 recognition, and target Figure 18
site compatibility checks.
-/
structure CanonicalCheckedFigure16RecognizedCompatibleLevelData
    (level : Nat) where
  sourceSites : CheckedNatSiteRectangle
    (RobinsonSquare.freeGridSide level) (RobinsonSquare.freeGridSide level)
  stackCompatible :
    (checkedLayerStackRectangleOfSiteRectangle sourceSites.toSiteRectangle).compatibleBool
      layerData
      (checkedLayerStackRectangleOfSiteRectangle_lookupBool sourceSites.toSiteRectangle) =
        true
  targetSites : CheckedNatSiteRectangle
    (2 * RobinsonSquare.freeGridSide level)
    (2 * RobinsonSquare.freeGridSide level)
  recognized :
    Figure16ExpandedSiteRectangle.matchesBool
      (checkedLayerStackOfSiteRectangle sourceSites.toSiteRectangle stackCompatible)
      targetSites.toSiteRectangle = true
  targetCompatible :
    figure18SiteCompatibleRectangleBool targetSites.toSiteRectangle = true

/--
Checked-list form of the compatible Figure 16 recognized Robinson board/free-grid
target.

Compared with the canonical existential target, this exposes both source and
target rectangles as row-major checked lists of `(tile, quadrant)` pairs, which
is the expected shape for generated finite certificates.
-/
def HasCanonicalCheckedFigure16RecognizedCompatibleLevelData : Prop :=
  ∀ level : Nat,
    Nonempty (CanonicalCheckedFigure16RecognizedCompatibleLevelData level)

theorem canonicalCheckedFigure16RecognizedCompatibleLevel_of_data
    {level : Nat}
    (data : CanonicalCheckedFigure16RecognizedCompatibleLevelData level) :
    ∃ source : SiteRectangle
      (RobinsonSquare.freeGridSide level) (RobinsonSquare.freeGridSide level),
      ∃ hcompatible :
        (checkedLayerStackRectangleOfSiteRectangle source).compatibleBool
          layerData (checkedLayerStackRectangleOfSiteRectangle_lookupBool source) =
            true,
        ∃ target : SiteRectangle
          (2 * RobinsonSquare.freeGridSide level)
          (2 * RobinsonSquare.freeGridSide level),
          Figure16ExpandedSiteRectangle.matchesBool
            (checkedLayerStackOfSiteRectangle source hcompatible) target =
              true ∧
            figure18SiteCompatibleRectangleBool target = true :=
  ⟨data.sourceSites.toSiteRectangle, data.stackCompatible,
    data.targetSites.toSiteRectangle, data.recognized, data.targetCompatible⟩

theorem canonicalCheckedFigure16RecognizedCompatible_of_checkedLevelData
    (hlevel : HasCanonicalCheckedFigure16RecognizedCompatibleLevelData) :
    HasCanonicalCheckedFigure16RecognizedCompatibleRobinsonBoardLevelMacroSquares := by
  intro level
  rcases hlevel level with ⟨data⟩
  exact canonicalCheckedFigure16RecognizedCompatibleLevel_of_data data

set_option linter.style.longLine false in
/--
Canonical source raw-boundary checked level data canonically generates checked
compatible Figure 16 level data by using the doubled canonical Figure 16
expansion as the target rectangle.
-/
theorem canonicalCheckedFigure16RecognizedCompatibleLevelData_of_rawBoundaryCheckedLevelData
    (hlevel : HasCanonicalFigure16SourceRawBoundaryCheckedLevelData) :
    HasCanonicalCheckedFigure16RecognizedCompatibleLevelData := by
  intro level
  rcases hlevel level with ⟨data⟩
  let source := data.sites.toSiteRectangle
  let target := canonicalExpandedSiteRectangleOfSiteRectangle source
  let targetSites := target.toCheckedNatSiteRectangle
  have htarget : targetSites.toSiteRectangle = target :=
    CheckedNatSiteRectangle.toSiteRectangle_eq_of_matchesSiteRectangleBool
      (SiteRectangle.toCheckedNatSiteRectangle_matchesSiteRectangleBool target)
  exact ⟨{
    sourceSites := data.sites
    stackCompatible := data.stackCompatible
    targetSites := targetSites
    recognized := by
      simpa [source, target, targetSites, htarget] using
        figure16ExpandedSiteRectangle_matchesBool_checkedLayerStack_canonicalExpanded
          source data.stackCompatible
    targetCompatible := by
      have hraw : source.RawBoundaryCompatible :=
        SiteRectangle.rawBoundaryCompatible_of_rawBoundaryCompatibleBool
          data.rawBoundary
      simpa [source, target, targetSites, htarget] using
        figure18SiteCompatibleRectangleBool_of
          (figure18SiteCompatibleRectangle_canonicalExpanded_of_rawBoundaryCompatible
            source hraw)
  }⟩

theorem canonicalCheckedFigure16RecognizedCompatible_of_rawBoundaryCompatible
    (hlevel : ∀ level : Nat,
      ∃ source : SiteRectangle
        (RobinsonSquare.freeGridSide level) (RobinsonSquare.freeGridSide level),
        ∃ _hcompatible :
          (checkedLayerStackRectangleOfSiteRectangle source).compatibleBool
            layerData (checkedLayerStackRectangleOfSiteRectangle_lookupBool source) =
              true,
          source.RawBoundaryCompatible) :
    HasCanonicalCheckedFigure16RecognizedCompatibleRobinsonBoardLevelMacroSquares := by
  intro level
  rcases hlevel level with ⟨source, hcompatible, hraw⟩
  refine ⟨source, hcompatible,
    canonicalExpandedSiteRectangleOfSiteRectangle source, ?_, ?_⟩
  · exact
      figure16ExpandedSiteRectangle_matchesBool_checkedLayerStack_canonicalExpanded
        source hcompatible
  · exact figure18SiteCompatibleRectangleBool_of
      (figure18SiteCompatibleRectangle_canonicalExpanded_of_rawBoundaryCompatible
        source hraw)

theorem canonicalCheckedFigure16RecognizedCompatible_of_sourceRawBoundary
    (hlevel : HasCanonicalCheckedFigure16SourceRawBoundaryMacroSquares) :
    HasCanonicalCheckedFigure16RecognizedCompatibleRobinsonBoardLevelMacroSquares :=
  canonicalCheckedFigure16RecognizedCompatible_of_rawBoundaryCompatible hlevel

theorem figure16RecognizedCompatibleRobinsonBoardLevelMacroSquares_of_checked
    (hlevel :
      HasCheckedFigure16RecognizedCompatibleRobinsonBoardLevelMacroSquares) :
    HasFigure16RecognizedCompatibleRobinsonBoardLevelMacroSquares := by
  intro level
  rcases hlevel level with ⟨source, stack, target, hrecognized, hcompatible⟩
  exact ⟨source, stack, target,
    Figure16ExpandedSiteRectangle.of_matchesBool hrecognized,
    figure18SiteCompatibleRectangle_of_bool hcompatible⟩

theorem checkedFigure16RecognizedCompatibleRobinsonBoardLevelMacroSquares_of_canonical
    (hlevel :
      HasCanonicalCheckedFigure16RecognizedCompatibleRobinsonBoardLevelMacroSquares) :
    HasCheckedFigure16RecognizedCompatibleRobinsonBoardLevelMacroSquares := by
  intro level
  rcases hlevel level with ⟨source, hcompatible, target, hrecognized, htarget⟩
  exact ⟨(checkedLayerStackRectangleOfSiteRectangle source).siteRectangle,
    checkedLayerStackOfSiteRectangle source hcompatible, target,
    hrecognized, htarget⟩

theorem figure16RecognizedCompatibleRobinsonBoardLevelMacroSquares_of_canonicalChecked
    (hlevel :
      HasCanonicalCheckedFigure16RecognizedCompatibleRobinsonBoardLevelMacroSquares) :
    HasFigure16RecognizedCompatibleRobinsonBoardLevelMacroSquares :=
  figure16RecognizedCompatibleRobinsonBoardLevelMacroSquares_of_checked
    (checkedFigure16RecognizedCompatibleRobinsonBoardLevelMacroSquares_of_canonical
      hlevel)

theorem cofinal_tileableSquares_figure18ScaffoldTiles_of_figure16RecognizedCompatible
    (hlevel : HasFigure16RecognizedCompatibleRobinsonBoardLevelMacroSquares) :
    ∀ n : Nat, ∃ m : Nat, n ≤ m ∧
      TileableSquare figure18ScaffoldTiles m := by
  intro n
  rcases RobinsonSquare.exists_level_with_payload_capacity n with
    ⟨level, hcap⟩
  rcases hlevel level with ⟨_source, _stack, target, _hrecognized,
    hcompatible⟩
  refine ⟨2 * RobinsonSquare.freeGridSide level, ?_, ?_⟩
  · exact hcap.trans
      (Nat.le_mul_of_pos_left _ (by decide : 0 < 2))
  · exact SiteRectangle.tileableSquare_of_compatible target
      hcompatible.1 hcompatible.2

theorem tilesPlane_figure18ScaffoldTiles_of_figure16RecognizedCompatible
    (hlevel : HasFigure16RecognizedCompatibleRobinsonBoardLevelMacroSquares) :
    TilesPlane figure18ScaffoldTiles :=
  tilesPlane_of_cofinal_tileableSquares
    (cofinal_tileableSquares_figure18ScaffoldTiles_of_figure16RecognizedCompatible
      hlevel)

theorem tilesPlane_figure18ScaffoldTiles_of_checkedFigure16RecognizedCompatible
    (hlevel :
      HasCheckedFigure16RecognizedCompatibleRobinsonBoardLevelMacroSquares) :
    TilesPlane figure18ScaffoldTiles :=
  tilesPlane_figure18ScaffoldTiles_of_figure16RecognizedCompatible
    (figure16RecognizedCompatibleRobinsonBoardLevelMacroSquares_of_checked
      hlevel)

theorem tilesPlane_figure18ScaffoldTiles_of_canonicalCheckedFigure16RecognizedCompatible
    (hlevel :
      HasCanonicalCheckedFigure16RecognizedCompatibleRobinsonBoardLevelMacroSquares) :
    TilesPlane figure18ScaffoldTiles :=
  tilesPlane_figure18ScaffoldTiles_of_checkedFigure16RecognizedCompatible
    (checkedFigure16RecognizedCompatibleRobinsonBoardLevelMacroSquares_of_canonical
      hlevel)

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

/--
Finite check that no two listed sites are horizontally adjacent in the Figure 18
site graph.
-/
def noSiteHCompatiblePairsBool
    (sites : List Figure18Site) : Bool :=
  sites.all fun left =>
    sites.all fun right =>
      !Figure18Site.hCompatible left right

/--
Finite check that no two listed sites are vertically adjacent in the Figure 18
site graph.
-/
def noSiteVCompatiblePairsBool
    (sites : List Figure18Site) : Bool :=
  sites.all fun lower =>
    sites.all fun upper =>
      !Figure18Site.vCompatible lower upper

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

theorem noSiteHCompatiblePairsBool_eq_true_iff
    {sites : List Figure18Site} :
    noSiteHCompatiblePairsBool sites = true ↔
      ∀ left : Figure18Site, left ∈ sites →
        ∀ right : Figure18Site, right ∈ sites →
          Figure18Site.hCompatible left right = false := by
  constructor
  · intro hcheck left hleft right hright
    unfold noSiteHCompatiblePairsBool at hcheck
    have hleftCheck := List.all_eq_true.1 hcheck left hleft
    have hrightCheck := List.all_eq_true.1 hleftCheck right hright
    cases hcompat : Figure18Site.hCompatible left right <;>
      simp [hcompat] at hrightCheck ⊢
  · intro hpairs
    unfold noSiteHCompatiblePairsBool
    apply List.all_eq_true.2
    intro left hleft
    apply List.all_eq_true.2
    intro right hright
    simp [hpairs left hleft right hright]

theorem noSiteVCompatiblePairsBool_eq_true_iff
    {sites : List Figure18Site} :
    noSiteVCompatiblePairsBool sites = true ↔
      ∀ lower : Figure18Site, lower ∈ sites →
        ∀ upper : Figure18Site, upper ∈ sites →
          Figure18Site.vCompatible lower upper = false := by
  constructor
  · intro hcheck lower hlower upper hupper
    unfold noSiteVCompatiblePairsBool at hcheck
    have hlowerCheck := List.all_eq_true.1 hcheck lower hlower
    have hupperCheck := List.all_eq_true.1 hlowerCheck upper hupper
    cases vcompat : Figure18Site.vCompatible lower upper <;>
      simp [vcompat] at hupperCheck ⊢
  · intro hpairs
    unfold noSiteVCompatiblePairsBool
    apply List.all_eq_true.2
    intro lower hlower
    apply List.all_eq_true.2
    intro upper hupper
    simp [hpairs lower hlower upper hupper]

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

def noGeneratedStackAllowedSiteHPairsBool
    (activeSiteData : Figure18Site.CheckedNatSpecs)
    (cornerSite : Figure18Site) : Bool :=
  noSiteHCompatiblePairsBool
    (generatedStackAllowedSites activeSiteData cornerSite)

def noGeneratedStackAllowedSiteVPairsBool
    (activeSiteData : Figure18Site.CheckedNatSpecs)
    (cornerSite : Figure18Site) : Bool :=
  noSiteVCompatiblePairsBool
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

theorem noGeneratedStackAllowedSiteHPairsBool_eq_true_iff
    {activeSiteData : Figure18Site.CheckedNatSpecs}
    {cornerSite : Figure18Site} :
    noGeneratedStackAllowedSiteHPairsBool activeSiteData cornerSite = true ↔
      ∀ left : Figure18Site,
        left = cornerSite ∨ left ∈ activeSiteData.sites →
        ∀ right : Figure18Site,
          right = cornerSite ∨ right ∈ activeSiteData.sites →
          Figure18Site.hCompatible left right = false := by
  constructor
  · intro hcheck left hleft right hright
    exact
      noSiteHCompatiblePairsBool_eq_true_iff.1 hcheck
        left (mem_generatedStackAllowedSites_of_listed hleft)
        right (mem_generatedStackAllowedSites_of_listed hright)
  · intro hpairs
    apply noSiteHCompatiblePairsBool_eq_true_iff.2
    intro left hleft right hright
    have hleft' :
        left = cornerSite ∨ left ∈ activeSiteData.sites := by
      simpa [generatedStackAllowedSites] using hleft
    have hright' :
        right = cornerSite ∨ right ∈ activeSiteData.sites := by
      simpa [generatedStackAllowedSites] using hright
    exact hpairs left hleft' right hright'

theorem noGeneratedStackAllowedSiteVPairsBool_eq_true_iff
    {activeSiteData : Figure18Site.CheckedNatSpecs}
    {cornerSite : Figure18Site} :
    noGeneratedStackAllowedSiteVPairsBool activeSiteData cornerSite = true ↔
      ∀ lower : Figure18Site,
        lower = cornerSite ∨ lower ∈ activeSiteData.sites →
        ∀ upper : Figure18Site,
          upper = cornerSite ∨ upper ∈ activeSiteData.sites →
          Figure18Site.vCompatible lower upper = false := by
  constructor
  · intro hcheck lower hlower upper hupper
    exact
      noSiteVCompatiblePairsBool_eq_true_iff.1 hcheck
        lower (mem_generatedStackAllowedSites_of_listed hlower)
        upper (mem_generatedStackAllowedSites_of_listed hupper)
  · intro hpairs
    apply noSiteVCompatiblePairsBool_eq_true_iff.2
    intro lower hlower upper hupper
    have hlower' :
        lower = cornerSite ∨ lower ∈ activeSiteData.sites := by
      simpa [generatedStackAllowedSites] using hlower
    have hupper' :
        upper = cornerSite ∨ upper ∈ activeSiteData.sites := by
      simpa [generatedStackAllowedSites] using hupper
    exact hpairs lower hlower' upper hupper'

/--
If a generated flat role table has no horizontally adjacent active/corner site
pairs, then no locally compatible Robinson free grid of side at least two can
use only that generated active/corner set.

This records the key diagnostic from Robinson's Section 7 board route: virtual
payload neighbors are routed through board cells and should not be forced to be
adjacent Figure 18 sites.
-/
theorem false_of_noAllowedSiteHPairs_of_flatRoleTable_robinsonBoardSiteCompatible
    {activeSiteData : Figure18Site.CheckedNatSpecs}
    {cornerSite : Figure18Site}
    (hno :
      noGeneratedStackAllowedSiteHPairsBool activeSiteData cornerSite = true)
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold
      (Figure18RoleTable.FlatRoleTable.ofActiveSites
        activeSiteData.sites cornerSite).toRoleTable.presentation.toScaffold
        T seed)}
    {n : Nat} {hn : 0 < n}
    (grid :
      Figure18RobinsonBoardRoutedFreeGrid
        (Figure18RoleTable.FlatRoleTable.ofActiveSites
          activeSiteData.sites cornerSite).toRoleTable x n hn)
    (hsite : grid.SiteCompatible)
    (hsize : 1 < n) : False := by
  let i0 : Fin n := ⟨0, hn⟩
  let i1 : Fin n := ⟨1, hsize⟩
  let j0 : Fin n := ⟨0, hn⟩
  have hi : i0.val + 1 < n := by
    simpa [i0] using hsize
  have hcompatTrue :
      Figure18Site.hCompatible (grid.siteRect i0 j0)
        (grid.siteRect i1 j0) = true := by
    simpa [i0, i1, j0] using hsite.1 i0 j0 hi
  have hleft :
      grid.siteRect i0 j0 = cornerSite ∨
        grid.siteRect i0 j0 ∈ activeSiteData.sites := by
    have hactiveRole :
        CellRole.isActive
          ((Figure18RoleTable.FlatRoleTable.ofActiveSites
            activeSiteData.sites cornerSite).toRoleTable.roleAtSite
              (grid.siteRect i0 j0)) = true := by
      exact grid.active i0 j0
    exact (Figure18RoleTable.isActive_roleOfActiveSites_iff
      activeSiteData.sites cornerSite (grid.siteRect i0 j0)).1
      (by
        simpa [Figure18RoleTable.FlatRoleTable.ofActiveSites_roleAtSite]
          using hactiveRole)
  have hright :
      grid.siteRect i1 j0 = cornerSite ∨
        grid.siteRect i1 j0 ∈ activeSiteData.sites := by
    have hactiveRole :
        CellRole.isActive
          ((Figure18RoleTable.FlatRoleTable.ofActiveSites
            activeSiteData.sites cornerSite).toRoleTable.roleAtSite
              (grid.siteRect i1 j0)) = true := by
      exact grid.active i1 j0
    exact (Figure18RoleTable.isActive_roleOfActiveSites_iff
      activeSiteData.sites cornerSite (grid.siteRect i1 j0)).1
      (by
        simpa [Figure18RoleTable.FlatRoleTable.ofActiveSites_roleAtSite]
          using hactiveRole)
  have hcompatFalse :
      Figure18Site.hCompatible (grid.siteRect i0 j0)
        (grid.siteRect i1 j0) = false :=
    noGeneratedStackAllowedSiteHPairsBool_eq_true_iff.1 hno
      (grid.siteRect i0 j0) hleft (grid.siteRect i1 j0) hright
  rw [hcompatFalse] at hcompatTrue
  simp at hcompatTrue

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
      grid.SiteCompatible

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
      grid.SiteCompatible

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
      grid.SiteCompatible

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
      grid.SiteCompatible

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
  have hsite := hcompatible grid
  refine ⟨?_, hsite⟩
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
  have hsite := hcompatible level grid
  refine ⟨?_, hsite⟩
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
  rcases hallowed grid with ⟨hsites, hgridSite⟩
  let window := grid.toIndexedRoutedFixedCornerSquare
  let R := siteRectangleOfIndexedRoutedFixedCornerSquare window
  have hh : ∀ i : Fin n, ∀ j : Fin n, ∀ hi : i.val + 1 < n,
      Figure18Site.hCompatible
        (siteRectangleOfIndexedRoutedFixedCornerSquare window i j)
        (siteRectangleOfIndexedRoutedFixedCornerSquare window
          ⟨i.val + 1, hi⟩ j) = true := by
    simpa [window, Figure18RobinsonBoardRoutedFreeGrid.SiteCompatible,
      Figure18RobinsonBoardRoutedFreeGrid.toIndexedRoutedFixedCornerSquare,
      Figure18IndexedRoutedFixedCornerSquare.ofSiteMatches,
      siteRectangleOfIndexedRoutedFixedCornerSquare] using hgridSite.1
  have hv : ∀ i : Fin n, ∀ j : Fin n, ∀ hj : j.val + 1 < n,
      Figure18Site.vCompatible
        (siteRectangleOfIndexedRoutedFixedCornerSquare window i j)
        (siteRectangleOfIndexedRoutedFixedCornerSquare window
          i ⟨j.val + 1, hj⟩) = true := by
    simpa [window, Figure18RobinsonBoardRoutedFreeGrid.SiteCompatible,
      Figure18RobinsonBoardRoutedFreeGrid.toIndexedRoutedFixedCornerSquare,
      Figure18IndexedRoutedFixedCornerSquare.ofSiteMatches,
      siteRectangleOfIndexedRoutedFixedCornerSquare] using hgridSite.2
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
  rcases hallowed level bigGrid with ⟨hsitesBig, hbigSite⟩
  have hgridSite : grid.SiteCompatible :=
    hbigSite.restrict hn hcap
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
    simpa [Figure18RobinsonBoardRoutedFreeGrid.SiteCompatible,
      Figure18RobinsonBoardRoutedFreeGrid.toIndexedRoutedFixedCornerSquare,
      Figure18IndexedRoutedFixedCornerSquare.ofSiteMatches,
      siteRectangleOfIndexedRoutedFixedCornerSquare] using hgridSite.1
  have hv : ∀ i : Fin n, ∀ j : Fin n, ∀ hj : j.val + 1 < n,
      Figure18Site.vCompatible
        (siteRectangleOfIndexedRoutedFixedCornerSquare
          grid.toIndexedRoutedFixedCornerSquare i j)
        (siteRectangleOfIndexedRoutedFixedCornerSquare
          grid.toIndexedRoutedFixedCornerSquare i ⟨j.val + 1, hj⟩) =
          true := by
    simpa [Figure18RobinsonBoardRoutedFreeGrid.SiteCompatible,
      Figure18RobinsonBoardRoutedFreeGrid.toIndexedRoutedFixedCornerSquare,
      Figure18IndexedRoutedFixedCornerSquare.ofSiteMatches,
      siteRectangleOfIndexedRoutedFixedCornerSquare] using hgridSite.2
  let window := grid.toIndexedRoutedFixedCornerSquare
  let R := siteRectangleOfIndexedRoutedFixedCornerSquare window
  rcases sparseRawDataOfSites_exists_compatible_checkedLayerStackRectangle
      activeSiteData cornerSite hcheck R hsites hh hv with
    ⟨stackData, hsite, hmatch, hcompatible⟩
  exact ⟨grid, stackData, hsite, hmatch, hcompatible⟩

theorem sparseRawDataOfSites_hasRobinsonBoardRoutedFreeGridCheckedStacks_of_levelCompatible
    (activeSiteData : Figure18Site.CheckedNatSpecs)
    (cornerSite : Figure18Site)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool activeSiteData cornerSite =
        true)
    (hgrids :
      HasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable
        (Figure18RoleTable.FlatRoleTable.ofActiveSites
          activeSiteData.sites cornerSite).toRoleTable) :
    (sparseRawDataOfSites
      activeSiteData cornerSite).HasRobinsonBoardRoutedFreeGridCheckedStacks
      (Figure18RoleTable.FlatRoleTable.ofActiveSites
        activeSiteData.sites cornerSite).toRoleTable := by
  intro T seed x hx n hn
  rcases RobinsonSquare.exists_level_with_payload_capacity n with
    ⟨level, hcap⟩
  rcases hgrids x hx level with ⟨bigGrid, hbigSite⟩
  let grid := bigGrid.restrict hn hcap
  have hgridSite : grid.SiteCompatible :=
    hbigSite.restrict hn hcap
  have hsites : ∀ i : Fin n, ∀ j : Fin n,
      siteRectangleOfIndexedRoutedFixedCornerSquare
          grid.toIndexedRoutedFixedCornerSquare i j =
        cornerSite ∨
      siteRectangleOfIndexedRoutedFixedCornerSquare
          grid.toIndexedRoutedFixedCornerSquare i j ∈
        activeSiteData.sites := by
    intro i j
    have hactiveRole :
        CellRole.isActive
          ((Figure18RoleTable.FlatRoleTable.ofActiveSites
            activeSiteData.sites cornerSite).toRoleTable.roleAtSite
              (siteRectangleOfIndexedRoutedFixedCornerSquare
                grid.toIndexedRoutedFixedCornerSquare i j)) = true := by
      simpa [grid, Figure18RobinsonBoardRoutedFreeGrid.restrict,
        Figure18RobinsonBoardRoutedFreeGrid.toIndexedRoutedFixedCornerSquare,
        Figure18IndexedRoutedFixedCornerSquare.ofSiteMatches,
        siteRectangleOfIndexedRoutedFixedCornerSquare] using
        bigGrid.active (Fin.castLE hcap i) (Fin.castLE hcap j)
    exact (Figure18RoleTable.isActive_roleOfActiveSites_iff
      activeSiteData.sites cornerSite
      (siteRectangleOfIndexedRoutedFixedCornerSquare
        grid.toIndexedRoutedFixedCornerSquare i j)).1
      (by
        simpa [Figure18RoleTable.FlatRoleTable.ofActiveSites_roleAtSite]
          using hactiveRole)
  have hh : ∀ i : Fin n, ∀ j : Fin n, ∀ hi : i.val + 1 < n,
      Figure18Site.hCompatible
        (siteRectangleOfIndexedRoutedFixedCornerSquare
          grid.toIndexedRoutedFixedCornerSquare i j)
        (siteRectangleOfIndexedRoutedFixedCornerSquare
          grid.toIndexedRoutedFixedCornerSquare ⟨i.val + 1, hi⟩ j) =
          true := by
    simpa [Figure18RobinsonBoardRoutedFreeGrid.SiteCompatible,
      Figure18RobinsonBoardRoutedFreeGrid.toIndexedRoutedFixedCornerSquare,
      Figure18IndexedRoutedFixedCornerSquare.ofSiteMatches,
      siteRectangleOfIndexedRoutedFixedCornerSquare] using hgridSite.1
  have hv : ∀ i : Fin n, ∀ j : Fin n, ∀ hj : j.val + 1 < n,
      Figure18Site.vCompatible
        (siteRectangleOfIndexedRoutedFixedCornerSquare
          grid.toIndexedRoutedFixedCornerSquare i j)
        (siteRectangleOfIndexedRoutedFixedCornerSquare
          grid.toIndexedRoutedFixedCornerSquare i ⟨j.val + 1, hj⟩) =
          true := by
    simpa [Figure18RobinsonBoardRoutedFreeGrid.SiteCompatible,
      Figure18RobinsonBoardRoutedFreeGrid.toIndexedRoutedFixedCornerSquare,
      Figure18IndexedRoutedFixedCornerSquare.ofSiteMatches,
      siteRectangleOfIndexedRoutedFixedCornerSquare] using hgridSite.2
  let window := grid.toIndexedRoutedFixedCornerSquare
  let R := siteRectangleOfIndexedRoutedFixedCornerSquare window
  rcases sparseRawDataOfSites_exists_compatible_checkedLayerStackRectangle
      activeSiteData cornerSite hcheck R hsites hh hv with
    ⟨stackData, hsite, hmatch, hcompatible⟩
  exact ⟨grid, stackData, hsite, hmatch, hcompatible⟩

theorem sparseRawDataOfSites_hasRobinsonBoardRoutedFreeGridCheckedStacks_of_levelSignalLocal
    (activeSiteData : Figure18Site.CheckedNatSpecs)
    (cornerSite : Figure18Site)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool activeSiteData cornerSite =
        true)
    (hsignal :
      HasFigure18RobinsonBoardLevelSignalLocalCertificatesForTable
        (Figure18RoleTable.FlatRoleTable.ofActiveSites
          activeSiteData.sites cornerSite).toRoleTable) :
    (sparseRawDataOfSites
      activeSiteData cornerSite).HasRobinsonBoardRoutedFreeGridCheckedStacks
      (Figure18RoleTable.FlatRoleTable.ofActiveSites
        activeSiteData.sites cornerSite).toRoleTable := by
  exact sparseRawDataOfSites_hasRobinsonBoardRoutedFreeGridCheckedStacks_of_levelCompatible
    activeSiteData cornerSite hcheck
    (hasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable_of_localSignalCertificates
      hsignal)

theorem sparseRawDataOfSites_hasRobinsonBoardRoutedFreeGridCheckedStacks_of_levelSignalLocalTower
    (activeSiteData : Figure18Site.CheckedNatSpecs)
    (cornerSite : Figure18Site)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool activeSiteData cornerSite =
        true)
    (htower :
      HasFigure18RobinsonBoardLevelSignalLocalTowerForTable
        (Figure18RoleTable.FlatRoleTable.ofActiveSites
          activeSiteData.sites cornerSite).toRoleTable) :
    (sparseRawDataOfSites
      activeSiteData cornerSite).HasRobinsonBoardRoutedFreeGridCheckedStacks
      (Figure18RoleTable.FlatRoleTable.ofActiveSites
        activeSiteData.sites cornerSite).toRoleTable := by
  exact sparseRawDataOfSites_hasRobinsonBoardRoutedFreeGridCheckedStacks_of_levelCompatible
    activeSiteData cornerSite hcheck
    (hasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable_of_localTower
      htower)

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

/--
Robinson Section 7 level-compatible free grids, together with the finite
Figure 13/Figure 16 pair-compatibility check, give the preferred indexed-routed
scaffold certificate.

This is the direct board/free-row route from Robinson's argument: the geometry
only has to produce compatible free grids at each board level, while arbitrary
finite payload squares are obtained by restriction.
-/
def scaffoldDataOfSitesIndexedRoutedCertificateOfLevelCompatibleRobinsonFreeGrids
    (activeSiteData : Figure18Site.CheckedNatSpecs)
    (cornerSite : Figure18Site)
    (hpair :
      generatedStackAllowedSitePairCompatibilityBool activeSiteData cornerSite =
        true)
    (hgrids :
      HasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable
        (Figure18RoleTable.FlatRoleTable.ofActiveSites
          activeSiteData.sites cornerSite).toRoleTable)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfSites activeSiteData cornerSite).table.presentation.toScaffold) :
    (scaffoldDataOfSites activeSiteData cornerSite).IndexedRoutedCertificate := by
  refine scaffoldDataOfSitesIndexedRoutedCertificateOfRobinsonBoardRoutedFreeGridCheckedStacks
    activeSiteData cornerSite ?_ realizes
  exact
    sparseRawDataOfSites_hasRobinsonBoardRoutedFreeGridCheckedStacks_of_levelCompatible
      activeSiteData cornerSite hpair hgrids

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

theorem l2Component1BlankCandidateNoHCompatibleAllowedSitesBool :
    noGeneratedStackAllowedSiteHPairsBool
      l2Component1BlankCandidateActiveSiteData
      l2Component1BlankCandidateCornerSite = true := by
  decide

theorem l2Component1BlankCandidateNoVCompatibleAllowedSitesBool :
    noGeneratedStackAllowedSiteVPairsBool
      l2Component1BlankCandidateActiveSiteData
      l2Component1BlankCandidateCornerSite = true := by
  decide

theorem l2Component1BlankCandidate_hCompatible_allowed_eq_false
    {left right : Figure18Site}
    (hleft :
      left = l2Component1BlankCandidateCornerSite ∨
        left ∈ l2Component1BlankCandidateActiveSiteData.sites)
    (hright :
      right = l2Component1BlankCandidateCornerSite ∨
        right ∈ l2Component1BlankCandidateActiveSiteData.sites) :
    Figure18Site.hCompatible left right = false :=
  noGeneratedStackAllowedSiteHPairsBool_eq_true_iff.1
    l2Component1BlankCandidateNoHCompatibleAllowedSitesBool
    left hleft right hright

theorem l2Component1BlankCandidate_vCompatible_allowed_eq_false
    {lower upper : Figure18Site}
    (hlower :
      lower = l2Component1BlankCandidateCornerSite ∨
        lower ∈ l2Component1BlankCandidateActiveSiteData.sites)
    (hupper :
      upper = l2Component1BlankCandidateCornerSite ∨
        upper ∈ l2Component1BlankCandidateActiveSiteData.sites) :
    Figure18Site.vCompatible lower upper = false :=
  noGeneratedStackAllowedSiteVPairsBool_eq_true_iff.1
    l2Component1BlankCandidateNoVCompatibleAllowedSitesBool
    lower hlower upper hupper

theorem l2Component1BlankCandidate_no_flatRoleTable_robinsonBoardSiteCompatible
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold
      (Figure18RoleTable.FlatRoleTable.ofActiveSites
        l2Component1BlankCandidateActiveSiteData.sites
        l2Component1BlankCandidateCornerSite).toRoleTable.presentation.toScaffold
        T seed)}
    {n : Nat} {hn : 0 < n}
    (grid :
      Figure18RobinsonBoardRoutedFreeGrid
        (Figure18RoleTable.FlatRoleTable.ofActiveSites
          l2Component1BlankCandidateActiveSiteData.sites
          l2Component1BlankCandidateCornerSite).toRoleTable x n hn)
    (hsite : grid.SiteCompatible)
    (hsize : 1 < n) : False :=
  false_of_noAllowedSiteHPairs_of_flatRoleTable_robinsonBoardSiteCompatible
    l2Component1BlankCandidateNoHCompatibleAllowedSitesBool
    grid hsite hsize

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

theorem l2Component2BlankCandidateNoHCompatibleAllowedSitesBool :
    noGeneratedStackAllowedSiteHPairsBool
      l2Component2BlankCandidateActiveSiteData
      l2Component2BlankCandidateCornerSite = true := by
  decide

theorem l2Component2BlankCandidateNoVCompatibleAllowedSitesBool :
    noGeneratedStackAllowedSiteVPairsBool
      l2Component2BlankCandidateActiveSiteData
      l2Component2BlankCandidateCornerSite = true := by
  decide

theorem l2Component2BlankCandidate_hCompatible_allowed_eq_false
    {left right : Figure18Site}
    (hleft :
      left = l2Component2BlankCandidateCornerSite ∨
        left ∈ l2Component2BlankCandidateActiveSiteData.sites)
    (hright :
      right = l2Component2BlankCandidateCornerSite ∨
        right ∈ l2Component2BlankCandidateActiveSiteData.sites) :
    Figure18Site.hCompatible left right = false :=
  noGeneratedStackAllowedSiteHPairsBool_eq_true_iff.1
    l2Component2BlankCandidateNoHCompatibleAllowedSitesBool
    left hleft right hright

theorem l2Component2BlankCandidate_vCompatible_allowed_eq_false
    {lower upper : Figure18Site}
    (hlower :
      lower = l2Component2BlankCandidateCornerSite ∨
        lower ∈ l2Component2BlankCandidateActiveSiteData.sites)
    (hupper :
      upper = l2Component2BlankCandidateCornerSite ∨
        upper ∈ l2Component2BlankCandidateActiveSiteData.sites) :
    Figure18Site.vCompatible lower upper = false :=
  noGeneratedStackAllowedSiteVPairsBool_eq_true_iff.1
    l2Component2BlankCandidateNoVCompatibleAllowedSitesBool
    lower hlower upper hupper

theorem l2Component2BlankCandidate_no_flatRoleTable_robinsonBoardSiteCompatible
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold
      (Figure18RoleTable.FlatRoleTable.ofActiveSites
        l2Component2BlankCandidateActiveSiteData.sites
        l2Component2BlankCandidateCornerSite).toRoleTable.presentation.toScaffold
        T seed)}
    {n : Nat} {hn : 0 < n}
    (grid :
      Figure18RobinsonBoardRoutedFreeGrid
        (Figure18RoleTable.FlatRoleTable.ofActiveSites
          l2Component2BlankCandidateActiveSiteData.sites
          l2Component2BlankCandidateCornerSite).toRoleTable x n hn)
    (hsite : grid.SiteCompatible)
    (hsize : 1 < n) : False :=
  false_of_noAllowedSiteHPairs_of_flatRoleTable_robinsonBoardSiteCompatible
    l2Component2BlankCandidateNoHCompatibleAllowedSitesBool
    grid hsite hsize

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

theorem scaffoldDataOfNatSites_flatTable
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true) :
    (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid).flatTable =
        flatRoleTableOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid :=
  rfl

theorem scaffoldDataOfNatSites_table
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true) :
    (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid).table =
        (flatRoleTableOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).toRoleTable := by
  simp [LayeredFigure18ScaffoldData.table,
    scaffoldDataOfNatSites_flatTable]

/--
Realization of a Nat-site Figure 18 scaffold follows from finite active-indexed
box witnesses.  This is the backward half of the scaffold argument in the
current theorem-facing form.
-/
def scaffoldDataOfNatSitesRealizesOfActiveCornerIndexedBoxes
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hboxes :
      ∀ r : Nat, Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).scaffold r)) :
    RealizesActiveCornerSquares
      (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold := by
  change RealizesActiveCornerSquares
    (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid).scaffold
  exact realizesActiveCornerSquares_of_realizesActiveCornerBoxes
    (realizesActiveCornerBoxes_of_activeCornerLayerBoxPatches
      (activeCornerLayerBoxPatches_of_activeCornerIndexedBoxes hboxes))

/--
Layer-patch realization of a Nat-site Figure 18 scaffold from
positive-radius active-corner indexed boxes.

This is the finite backward target used by the Section 7 layer-patch route:
the radius-zero layer patch is supplied by the distinguished scaffold corner,
so concrete proofs only need to construct positive-radius indexed boxes.
-/
def scaffoldDataOfNatSitesLayerPatchesOfPositiveActiveCornerIndexedBoxes
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hboxes_pos :
      ∀ r : Nat, 0 < r → Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).scaffold r)) :
    HasActiveCornerLayerBoxPatches
      (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold :=
  activeCornerLayerBoxPatches_of_positiveActiveCornerIndexedBoxes
    (by
      simpa [LayeredFigure18ScaffoldData.scaffold,
        LayeredFigure18ScaffoldData.presentation] using
        Figure18RoleTable.scaffold_corner_mem
          (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
            cornerIndex cornerQuadrant cornerIndex_valid).table)
    hboxes_pos

/--
Layer-patch realization of a Nat-site Figure 18 scaffold from translated
positive-radius active-corner indexed boxes.
-/
def scaffoldDataOfNatSitesLayerPatchesOfPositiveTranslatedIndexedBoxes
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hboxes_pos :
      ∀ r : Nat, 0 < r →
        ∃ origin : Int × Int,
          Nonempty (TranslatedActiveCornerIndexedBox
            (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
              cornerIndex cornerQuadrant cornerIndex_valid).scaffold r
            origin)) :
    HasActiveCornerLayerBoxPatches
      (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold :=
  scaffoldDataOfNatSitesLayerPatchesOfPositiveActiveCornerIndexedBoxes
    activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
    cornerIndex_valid
    (TranslatedActiveCornerIndexedBox.nonempty_centered_pos_of_translated_pos
      hboxes_pos)

/--
View concrete Nat-site layer patches as the layered Figure 13 realization
invariant.
-/
def scaffoldDataOfNatSitesLayerPatchRealizationInvariant
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant
          cornerIndex_valid).table.presentation.toScaffold) :
    (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid).HasLayerPatchRealizationInvariant := by
  simpa [LayeredFigure18ScaffoldData.HasLayerPatchRealizationInvariant,
    Figure18ScaffoldData.HasLayerPatchRealizationInvariant,
    LayeredFigure18ScaffoldData.scaffold,
    LayeredFigure18ScaffoldData.presentation,
    LayeredFigure18ScaffoldData.table,
    LayeredFigure18ScaffoldData.flatTable,
    Figure18ScaffoldData.scaffold,
    Figure18ScaffoldData.presentation,
    Figure18ScaffoldData.table,
    Figure18ScaffoldData.activeSites] using patches

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

def scaffoldDataOfNatSitesCertificateOfCheckedStacksLayerPatches
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
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant
          cornerIndex_valid).table.presentation.toScaffold) :
    (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid).Certificate :=
  CheckedSparseRawData.certificateOfCheckedIndexedActiveStacksLayerPatches
    (sparseRawDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid)
    hchecked
    (scaffoldDataOfNatSitesLayerPatchRealizationInvariant
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid patches)

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

def scaffoldDataOfNatSitesIndexedRoutedCertificateOfCheckedStacksLayerPatches
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
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant
          cornerIndex_valid).table.presentation.toScaffold) :
    (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid).IndexedRoutedCertificate :=
  CheckedSparseRawData.indexedRoutedCertificateOfCheckedStacksLayerPatches
    (sparseRawDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid)
    hchecked
    (scaffoldDataOfNatSitesLayerPatchRealizationInvariant
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid patches)

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

def scaffoldDataOfNatSitesIndexedRoutedCertificateOfCheckedFreeGridStacksLayerPatches
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
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant
          cornerIndex_valid).table.presentation.toScaffold) :
    (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid).IndexedRoutedCertificate :=
  let data :=
    sparseRawDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid
  data.indexedRoutedCertificateOfRobinsonBoardRoutedFreeGridCheckedStacksLayerPatches
    hchecked
    (scaffoldDataOfNatSitesLayerPatchRealizationInvariant
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid patches)

def scaffoldDataOfNatSitesIndexedRoutedCertificateOfIndexedBoxes
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
    (hboxes :
      ∀ r : Nat, Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).scaffold r)) :
    (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid).IndexedRoutedCertificate :=
  scaffoldDataOfNatSitesIndexedRoutedCertificateOfRobinsonBoardRoutedFreeGridCheckedStacks
    activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
    cornerIndex_valid hchecked
    (scaffoldDataOfNatSitesRealizesOfActiveCornerIndexedBoxes
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid hboxes)

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

def scaffoldDataOfNatSitesIndexedRoutedCertificateOfRobinsonBoardRoutedFreeGridsLayerPatches
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
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant
          cornerIndex_valid).table.presentation.toScaffold) :
    (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid).IndexedRoutedCertificate :=
  CheckedSparseRawData.indexedRoutedCertificateOfRobinsonBoardRoutedFreeGridsLayerPatches
    (sparseRawDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid)
    hgrids hstacks
    (scaffoldDataOfNatSitesLayerPatchRealizationInvariant
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid patches)

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

theorem sparseRawDataOfNatSites_hasCheckedRectanglesForFlatRoleTable
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
      cornerIndex_valid).HasCheckedStacksForListedActiveSiteRectangles
        (flatRoleTableOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).activeSites
        (flatRoleTableOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).cornerSite := by
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
  exact sparseRawDataOfNatSites_hasCheckedRectanglesForFlatRoleTable
    activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
    cornerIndex_valid hpair

/--
Origin-zero active/corner windows plus the generated finite Figure 13/Figure 16
pair-compatibility check attach compatible checked layer stacks to the selected
origin-zero rectangles.
-/
theorem sparseRawDataOfNatSites_hasOriginZeroCheckedStacksForFlatRoleTable
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hwindows :
      HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (flatRoleTableOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).toRoleTable)
    (hpair :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true) :
    (sparseRawDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant
      cornerIndex_valid).HasIndexedActiveOriginZeroWindowCheckedStacks
        (flatRoleTableOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).toRoleTable := by
  open CheckedSparseRawData in
  exact
    hasIndexedActiveOriginZeroWindowCheckedStacks_of_originZeroWindowsForFlatTable
      hwindows
      (sparseRawDataOfNatSites_hasCheckedRectanglesForFlatRoleTable
        activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
        cornerIndex_valid hpair)

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

def scaffoldDataOfNatSitesRealizesOfPositiveTranslatedIndexedBoxes
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hboxes :
      Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant
        (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid)) :
    RealizesActiveCornerSquares
      (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold := by
  change RealizesActiveCornerSquares
    (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid).scaffold
  have hrealizes :
      Figure18ScaffoldData.HasRealizationInvariant
        (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid) :=
    Figure18ScaffoldData.HasRealizationInvariant.ofPositiveTranslatedActiveCornerIndexedBoxes
      hboxes
  simpa [Figure18ScaffoldData.HasRealizationInvariant,
    figure18ScaffoldDataOfNatSites, scaffoldDataOfNatSites,
    LayeredFigure18ScaffoldData.scaffold,
    LayeredFigure18ScaffoldData.presentation,
    LayeredFigure18ScaffoldData.table,
    LayeredFigure18ScaffoldData.flatTable,
    Figure18ScaffoldData.scaffold,
    Figure18ScaffoldData.presentation,
    Figure18ScaffoldData.table] using hrealizes

def figure18ScaffoldDataOfNatSitesRoutedCertificateOfOriginZeroPairCompatibility
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hwindows :
      HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (flatRoleTableOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).toRoleTable)
    (hpair :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (boxes :
      Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant
        (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid)) :
    (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid).RoutedCertificate := by
  open CheckedSparseRawData in
  exact CheckedSparseRawData.routedCertificateOfOriginZeroCheckedStacks
    (sparseRawDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid)
    (sparseRawDataOfNatSites_hasOriginZeroCheckedStacksForFlatRoleTable
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid hwindows hpair)
    (by
      simpa [figure18ScaffoldDataOfNatSites, scaffoldDataOfNatSites] using
        boxes)

/--
Origin-zero active/corner windows supply Robinson Section 7 obstruction routing
for the concrete Nat-indexed Figure 18 scaffold data.

This is the theorem-facing bridge from the local origin-zero geometry to
Robinson's board argument: obstruction signals identify the free rows and
columns, represented here by canonical free-site-rectangle routing.
-/
theorem figure18ScaffoldDataOfNatSitesSection7ObstructionRoutingOfOriginZeroWindows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (originZeroWindows :
      HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table) :
    (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant
      cornerIndex_valid).HasRobinsonSection7ObstructionRoutingInvariant := by
  change
    HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable
      (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).table.toRoleTable
  rw [figure18ScaffoldDataOfNatSites_table,
    ← scaffoldDataOfNatSites_table]
  exact
    hasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable_of_originZeroWindows
      originZeroWindows

/--
Origin-zero active/corner windows supply the stronger board/free-line
active-corner invariant for the concrete Nat-indexed Figure 18 scaffold data.

The pure Robinson board geometry is the canonical tower; the origin-zero
windows discharge the finite active/corner recognition at the canonical free
crossings.
-/
theorem figure18ScaffoldDataOfNatSitesBoardFreeLineActiveCornerOfOriginZeroWindows
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (originZeroWindows :
      HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table) :
    (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant
      cornerIndex_valid).HasRobinsonSection7BoardFreeLineActiveCornerInvariant := by
  refine ⟨hasRobinsonBoardSignalGeometryTower, ?_⟩
  change
    HasFigure18RobinsonBoardCanonicalFreeSiteRectActiveCornerForTable
      (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).table.toRoleTable
  rw [figure18ScaffoldDataOfNatSites_table,
    ← scaffoldDataOfNatSites_table]
  exact
    hasFigure18RobinsonBoardCanonicalFreeSiteRectActiveCornerForTable_of_originZeroWindows
      originZeroWindows

/--
Finite origin-zero checked layer stacks supply Robinson Section 7 obstruction
routing for the concrete Nat-indexed layered Figure 18 scaffold data.

This is the checked-data version of the origin-zero route: the finite
Figure 13/Figure 16 stack certificate first recovers the origin-zero
active/corner windows, and then Robinson's board argument identifies the free
rows and columns.
-/
theorem scaffoldDataOfNatSitesSection7ObstructionRoutingOfOriginZeroCheckedStacks
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (hchecked :
      (sparseRawDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant
        cornerIndex_valid).HasIndexedActiveOriginZeroWindowCheckedStacks
          (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
            cornerIndex cornerQuadrant cornerIndex_valid).table) :
    (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant
      cornerIndex_valid).HasRobinsonSection7ObstructionRoutingInvariant := by
  exact
    CheckedSparseRawData.hasRobinsonSection7ObstructionRoutingInvariant_of_originZeroCheckedStacks
      hchecked

def l2Component1Figure18ScaffoldData : Figure18ScaffoldData :=
  figure18ScaffoldDataOfNatSites
    l2Component1BlankCandidateActiveSiteSpecs
    l2Component1BlankCandidateSanity.activeSiteSpecs_valid
    0 Quadrant.southwest
    l2Component1BlankCandidateSanity.cornerIndex_valid

def l2Component2Figure18ScaffoldData : Figure18ScaffoldData :=
  figure18ScaffoldDataOfNatSites
    l2Component2BlankCandidateActiveSiteSpecs
    l2Component2BlankCandidateSanity.activeSiteSpecs_valid
    0 Quadrant.northeast
    l2Component2BlankCandidateSanity.cornerIndex_valid

/--
Robinson Section 7 obstruction routing for the first audited L2-blank
candidate, from origin-zero active/corner windows.
-/
theorem l2Component1Figure18ScaffoldDataSection7ObstructionRoutingOfOriginZeroWindows
    (originZeroWindows :
      HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table) :
    l2Component1Figure18ScaffoldData.HasRobinsonSection7ObstructionRoutingInvariant := by
  change
    (figure18ScaffoldDataOfNatSites
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
        |>.HasRobinsonSection7ObstructionRoutingInvariant
  exact
    figure18ScaffoldDataOfNatSitesSection7ObstructionRoutingOfOriginZeroWindows
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      originZeroWindows

/--
Robinson Section 7 obstruction routing for the second audited L2-blank
candidate, from origin-zero active/corner windows.
-/
theorem l2Component2Figure18ScaffoldDataSection7ObstructionRoutingOfOriginZeroWindows
    (originZeroWindows :
      HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table) :
    l2Component2Figure18ScaffoldData.HasRobinsonSection7ObstructionRoutingInvariant := by
  change
    (figure18ScaffoldDataOfNatSites
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
        |>.HasRobinsonSection7ObstructionRoutingInvariant
  exact
    figure18ScaffoldDataOfNatSitesSection7ObstructionRoutingOfOriginZeroWindows
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      originZeroWindows

/--
Robinson Section 7 obstruction routing for the first audited L2-blank
candidate, from finite origin-zero checked layer stacks.
-/
theorem l2Component1Section7ObstructionRoutingOfOriginZeroCheckedStacks
    (hchecked :
      (sparseRawDataOfNatSites
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid)
          |>.HasIndexedActiveOriginZeroWindowCheckedStacks
            (scaffoldDataOfNatSites
              l2Component1BlankCandidateActiveSiteSpecs
              l2Component1BlankCandidateSanity.activeSiteSpecs_valid
              0 Quadrant.southwest
              l2Component1BlankCandidateSanity.cornerIndex_valid).table) :
    (scaffoldDataOfNatSites
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
        |>.HasRobinsonSection7ObstructionRoutingInvariant :=
  scaffoldDataOfNatSitesSection7ObstructionRoutingOfOriginZeroCheckedStacks
    l2Component1BlankCandidateActiveSiteSpecs
    l2Component1BlankCandidateSanity.activeSiteSpecs_valid
    0 Quadrant.southwest
    l2Component1BlankCandidateSanity.cornerIndex_valid
    hchecked

/--
Robinson Section 7 obstruction routing for the second audited L2-blank
candidate, from finite origin-zero checked layer stacks.
-/
theorem l2Component2Section7ObstructionRoutingOfOriginZeroCheckedStacks
    (hchecked :
      (sparseRawDataOfNatSites
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid)
          |>.HasIndexedActiveOriginZeroWindowCheckedStacks
            (scaffoldDataOfNatSites
              l2Component2BlankCandidateActiveSiteSpecs
              l2Component2BlankCandidateSanity.activeSiteSpecs_valid
              0 Quadrant.northeast
              l2Component2BlankCandidateSanity.cornerIndex_valid).table) :
    (scaffoldDataOfNatSites
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
        |>.HasRobinsonSection7ObstructionRoutingInvariant :=
  scaffoldDataOfNatSitesSection7ObstructionRoutingOfOriginZeroCheckedStacks
    l2Component2BlankCandidateActiveSiteSpecs
    l2Component2BlankCandidateSanity.activeSiteSpecs_valid
    0 Quadrant.northeast
    l2Component2BlankCandidateSanity.cornerIndex_valid
    hchecked

theorem l2Component1Figure18ScaffoldDataNoHCompatibleAllowedSitesBool :
    noGeneratedStackAllowedSiteHPairsBool
      l2Component1Figure18ScaffoldData.activeSiteData
      l2Component1Figure18ScaffoldData.cornerSite = true := by
  decide

theorem l2Component1Figure18ScaffoldDataNoVCompatibleAllowedSitesBool :
    noGeneratedStackAllowedSiteVPairsBool
      l2Component1Figure18ScaffoldData.activeSiteData
      l2Component1Figure18ScaffoldData.cornerSite = true := by
  decide

theorem l2Component2Figure18ScaffoldDataNoHCompatibleAllowedSitesBool :
    noGeneratedStackAllowedSiteHPairsBool
      l2Component2Figure18ScaffoldData.activeSiteData
      l2Component2Figure18ScaffoldData.cornerSite = true := by
  decide

theorem l2Component2Figure18ScaffoldDataNoVCompatibleAllowedSitesBool :
    noGeneratedStackAllowedSiteVPairsBool
      l2Component2Figure18ScaffoldData.activeSiteData
      l2Component2Figure18ScaffoldData.cornerSite = true := by
  decide

theorem l2Component1PositiveTranslatedIsolatedBoxesOfValidBoxes
    (hboxes :
      ∀ r : Nat, 0 < r →
        ∃ origin : Int × Int,
          ∃ base : TranslatedBoxPattern
            l2Component1Figure18ScaffoldData.scaffold.tiles r origin,
            ValidTranslatedBoxTiling
              l2Component1Figure18ScaffoldData.scaffold.tiles r origin base) :
    Figure18ScaffoldData.HasPositiveTranslatedIsolatedActiveBoxInvariant
      l2Component1Figure18ScaffoldData := by
  apply
    Figure18ScaffoldData.HasPositiveTranslatedIsolatedActiveBoxInvariant.ofValidTranslatedBoxes
  · intro left hleft right hright
    exact
      (noGeneratedStackAllowedSiteHPairsBool_eq_true_iff.1
        l2Component1Figure18ScaffoldDataNoHCompatibleAllowedSitesBool)
        left hleft right hright
  · intro lower hlower upper hupper
    exact
      (noGeneratedStackAllowedSiteVPairsBool_eq_true_iff.1
        l2Component1Figure18ScaffoldDataNoVCompatibleAllowedSitesBool)
        lower hlower upper hupper
  · exact hboxes

theorem l2Component1PositiveTranslatedIsolatedBoxesOfTileableBoxes
    (hboxes :
      ∀ r : Nat, 0 < r →
        TileableBox l2Component1Figure18ScaffoldData.scaffold.tiles r) :
    Figure18ScaffoldData.HasPositiveTranslatedIsolatedActiveBoxInvariant
      l2Component1Figure18ScaffoldData :=
  l2Component1PositiveTranslatedIsolatedBoxesOfValidBoxes
    (positiveTranslatedValidBoxes_of_tileableBoxes hboxes)

theorem l2Component1PositiveTranslatedIsolatedBoxesOfFigure18ScaffoldTileableBoxes
    (hboxes : ∀ r : Nat, 0 < r → TileableBox figure18ScaffoldTiles r) :
    Figure18ScaffoldData.HasPositiveTranslatedIsolatedActiveBoxInvariant
      l2Component1Figure18ScaffoldData := by
  apply
    Figure18ScaffoldData.isolatedActiveBoxes_ofFigure18ScaffoldTileableBoxes
  · intro left hleft right hright
    exact
      (noGeneratedStackAllowedSiteHPairsBool_eq_true_iff.1
        l2Component1Figure18ScaffoldDataNoHCompatibleAllowedSitesBool)
        left hleft right hright
  · intro lower hlower upper hupper
    exact
      (noGeneratedStackAllowedSiteVPairsBool_eq_true_iff.1
        l2Component1Figure18ScaffoldDataNoVCompatibleAllowedSitesBool)
        lower hlower upper hupper
  · exact hboxes

theorem l2Component1PositiveTranslatedIsolatedBoxesOfCompatibleSquares
    (hsquares : HasCompatibleFigure18ScaffoldSquares) :
    Figure18ScaffoldData.HasPositiveTranslatedIsolatedActiveBoxInvariant
      l2Component1Figure18ScaffoldData :=
  l2Component1PositiveTranslatedIsolatedBoxesOfFigure18ScaffoldTileableBoxes
    (fun r _hr => tileableBoxes_of_compatibleFigure18ScaffoldSquares hsquares r)

theorem l2Component1PositiveTranslatedIsolatedBoxesOfFigure18ScaffoldTilesPlane
    (hplane : TilesPlane figure18ScaffoldTiles) :
    Figure18ScaffoldData.HasPositiveTranslatedIsolatedActiveBoxInvariant
      l2Component1Figure18ScaffoldData :=
  l2Component1PositiveTranslatedIsolatedBoxesOfCompatibleSquares
    (compatibleFigure18ScaffoldSquares_of_tilesPlane hplane)

theorem l2Component1PositiveTranslatedIsolatedBoxesOfFig13TilesPlane
    (hplane : TilesPlane fig13Tiles) :
    Figure18ScaffoldData.HasPositiveTranslatedIsolatedActiveBoxInvariant
      l2Component1Figure18ScaffoldData :=
  l2Component1PositiveTranslatedIsolatedBoxesOfFigure18ScaffoldTilesPlane
    (tilesPlane_figure18ScaffoldTiles_of_tilesPlane_fig13Tiles hplane)

theorem l2Component1PositiveTranslatedIsolatedBoxesOfFig13TileableBoxes
    (hboxes : ∀ r : Nat, TileableBox fig13Tiles r) :
    Figure18ScaffoldData.HasPositiveTranslatedIsolatedActiveBoxInvariant
      l2Component1Figure18ScaffoldData :=
  l2Component1PositiveTranslatedIsolatedBoxesOfFig13TilesPlane
    (tilesPlane_fig13Tiles_of_tileableBoxes hboxes)

theorem l2Component1PositiveTranslatedIsolatedBoxesOfFig13CofinalSquares
    (hsquares : ∀ n : Nat, ∃ m : Nat, n ≤ m ∧ TileableSquare fig13Tiles m) :
    Figure18ScaffoldData.HasPositiveTranslatedIsolatedActiveBoxInvariant
      l2Component1Figure18ScaffoldData :=
  l2Component1PositiveTranslatedIsolatedBoxesOfFig13TilesPlane
    (tilesPlane_fig13Tiles_of_cofinal_tileableSquares hsquares)

theorem l2Component1PositiveTranslatedIsolatedBoxesOfRobinsonBoardLevelAlignedMacroSquares
    (hlevel : HasFigure13RobinsonBoardLevelAlignedMacroSquares) :
    Figure18ScaffoldData.HasPositiveTranslatedIsolatedActiveBoxInvariant
      l2Component1Figure18ScaffoldData :=
  l2Component1PositiveTranslatedIsolatedBoxesOfFig13TilesPlane
    (tilesPlane_fig13Tiles_of_robinsonBoardLevelAlignedMacroSquares hlevel)

theorem l2Component1PositiveTranslatedIsolatedBoxesOfCheckedFigure16MacroSquares
    (hlevel : HasCheckedFigure16RecognizedRobinsonBoardLevelMacroSquares) :
    Figure18ScaffoldData.HasPositiveTranslatedIsolatedActiveBoxInvariant
      l2Component1Figure18ScaffoldData :=
  l2Component1PositiveTranslatedIsolatedBoxesOfFig13TilesPlane
    (tilesPlane_fig13Tiles_of_checkedFigure16RecognizedRobinsonBoardLevelMacroSquares
      hlevel)

theorem l2Component1PositiveTranslatedIsolatedBoxesOfCanonicalCheckedFigure16MacroSquares
    (hlevel : HasCanonicalCheckedFigure16RecognizedRobinsonBoardLevelMacroSquares) :
    Figure18ScaffoldData.HasPositiveTranslatedIsolatedActiveBoxInvariant
      l2Component1Figure18ScaffoldData :=
  l2Component1PositiveTranslatedIsolatedBoxesOfFig13TilesPlane
    (tilesPlane_fig13Tiles_of_canonicalCheckedFigure16RecognizedRobinsonBoardLevelMacroSquares
      hlevel)

theorem l2Component1PositiveTranslatedIsolatedBoxesOfCheckedCompatibleFigure16MacroSquares
    (hlevel :
      HasCheckedFigure16RecognizedCompatibleRobinsonBoardLevelMacroSquares) :
    Figure18ScaffoldData.HasPositiveTranslatedIsolatedActiveBoxInvariant
      l2Component1Figure18ScaffoldData :=
  l2Component1PositiveTranslatedIsolatedBoxesOfFigure18ScaffoldTilesPlane
    (tilesPlane_figure18ScaffoldTiles_of_checkedFigure16RecognizedCompatible
      hlevel)

theorem
    l2Component1PositiveTranslatedIsolatedBoxesOfCanonicalCheckedCompatibleFigure16MacroSquares
    (hlevel :
      HasCanonicalCheckedFigure16RecognizedCompatibleRobinsonBoardLevelMacroSquares) :
    Figure18ScaffoldData.HasPositiveTranslatedIsolatedActiveBoxInvariant
      l2Component1Figure18ScaffoldData :=
  l2Component1PositiveTranslatedIsolatedBoxesOfFigure18ScaffoldTilesPlane
    (tilesPlane_figure18ScaffoldTiles_of_canonicalCheckedFigure16RecognizedCompatible
      hlevel)

theorem
    l2Component1PositiveTranslatedIsolatedBoxesOfCanonicalCheckedCompatibleFigure16LevelData
    (hlevel : HasCanonicalCheckedFigure16RecognizedCompatibleLevelData) :
    Figure18ScaffoldData.HasPositiveTranslatedIsolatedActiveBoxInvariant
      l2Component1Figure18ScaffoldData :=
  l2Component1PositiveTranslatedIsolatedBoxesOfCanonicalCheckedCompatibleFigure16MacroSquares
    (canonicalCheckedFigure16RecognizedCompatible_of_checkedLevelData hlevel)

theorem l2Component2PositiveTranslatedIsolatedBoxesOfValidBoxes
    (hboxes :
      ∀ r : Nat, 0 < r →
        ∃ origin : Int × Int,
          ∃ base : TranslatedBoxPattern
            l2Component2Figure18ScaffoldData.scaffold.tiles r origin,
            ValidTranslatedBoxTiling
              l2Component2Figure18ScaffoldData.scaffold.tiles r origin base) :
    Figure18ScaffoldData.HasPositiveTranslatedIsolatedActiveBoxInvariant
      l2Component2Figure18ScaffoldData := by
  apply
    Figure18ScaffoldData.HasPositiveTranslatedIsolatedActiveBoxInvariant.ofValidTranslatedBoxes
  · intro left hleft right hright
    exact
      (noGeneratedStackAllowedSiteHPairsBool_eq_true_iff.1
        l2Component2Figure18ScaffoldDataNoHCompatibleAllowedSitesBool)
        left hleft right hright
  · intro lower hlower upper hupper
    exact
      (noGeneratedStackAllowedSiteVPairsBool_eq_true_iff.1
        l2Component2Figure18ScaffoldDataNoVCompatibleAllowedSitesBool)
        lower hlower upper hupper
  · exact hboxes

theorem l2Component2PositiveTranslatedIsolatedBoxesOfTileableBoxes
    (hboxes :
      ∀ r : Nat, 0 < r →
        TileableBox l2Component2Figure18ScaffoldData.scaffold.tiles r) :
    Figure18ScaffoldData.HasPositiveTranslatedIsolatedActiveBoxInvariant
      l2Component2Figure18ScaffoldData :=
  l2Component2PositiveTranslatedIsolatedBoxesOfValidBoxes
    (positiveTranslatedValidBoxes_of_tileableBoxes hboxes)

theorem l2Component2PositiveTranslatedIsolatedBoxesOfFigure18ScaffoldTileableBoxes
    (hboxes : ∀ r : Nat, 0 < r → TileableBox figure18ScaffoldTiles r) :
    Figure18ScaffoldData.HasPositiveTranslatedIsolatedActiveBoxInvariant
      l2Component2Figure18ScaffoldData := by
  apply
    Figure18ScaffoldData.isolatedActiveBoxes_ofFigure18ScaffoldTileableBoxes
  · intro left hleft right hright
    exact
      (noGeneratedStackAllowedSiteHPairsBool_eq_true_iff.1
        l2Component2Figure18ScaffoldDataNoHCompatibleAllowedSitesBool)
        left hleft right hright
  · intro lower hlower upper hupper
    exact
      (noGeneratedStackAllowedSiteVPairsBool_eq_true_iff.1
        l2Component2Figure18ScaffoldDataNoVCompatibleAllowedSitesBool)
        lower hlower upper hupper
  · exact hboxes

theorem l2Component2PositiveTranslatedIsolatedBoxesOfCompatibleSquares
    (hsquares : HasCompatibleFigure18ScaffoldSquares) :
    Figure18ScaffoldData.HasPositiveTranslatedIsolatedActiveBoxInvariant
      l2Component2Figure18ScaffoldData :=
  l2Component2PositiveTranslatedIsolatedBoxesOfFigure18ScaffoldTileableBoxes
    (fun r _hr => tileableBoxes_of_compatibleFigure18ScaffoldSquares hsquares r)

theorem l2Component2PositiveTranslatedIsolatedBoxesOfFigure18ScaffoldTilesPlane
    (hplane : TilesPlane figure18ScaffoldTiles) :
    Figure18ScaffoldData.HasPositiveTranslatedIsolatedActiveBoxInvariant
      l2Component2Figure18ScaffoldData :=
  l2Component2PositiveTranslatedIsolatedBoxesOfCompatibleSquares
    (compatibleFigure18ScaffoldSquares_of_tilesPlane hplane)

theorem l2Component2PositiveTranslatedIsolatedBoxesOfFig13TilesPlane
    (hplane : TilesPlane fig13Tiles) :
    Figure18ScaffoldData.HasPositiveTranslatedIsolatedActiveBoxInvariant
      l2Component2Figure18ScaffoldData :=
  l2Component2PositiveTranslatedIsolatedBoxesOfFigure18ScaffoldTilesPlane
    (tilesPlane_figure18ScaffoldTiles_of_tilesPlane_fig13Tiles hplane)

theorem l2Component2PositiveTranslatedIsolatedBoxesOfFig13TileableBoxes
    (hboxes : ∀ r : Nat, TileableBox fig13Tiles r) :
    Figure18ScaffoldData.HasPositiveTranslatedIsolatedActiveBoxInvariant
      l2Component2Figure18ScaffoldData :=
  l2Component2PositiveTranslatedIsolatedBoxesOfFig13TilesPlane
    (tilesPlane_fig13Tiles_of_tileableBoxes hboxes)

theorem l2Component2PositiveTranslatedIsolatedBoxesOfFig13CofinalSquares
    (hsquares : ∀ n : Nat, ∃ m : Nat, n ≤ m ∧ TileableSquare fig13Tiles m) :
    Figure18ScaffoldData.HasPositiveTranslatedIsolatedActiveBoxInvariant
      l2Component2Figure18ScaffoldData :=
  l2Component2PositiveTranslatedIsolatedBoxesOfFig13TilesPlane
    (tilesPlane_fig13Tiles_of_cofinal_tileableSquares hsquares)

theorem l2Component2PositiveTranslatedIsolatedBoxesOfRobinsonBoardLevelAlignedMacroSquares
    (hlevel : HasFigure13RobinsonBoardLevelAlignedMacroSquares) :
    Figure18ScaffoldData.HasPositiveTranslatedIsolatedActiveBoxInvariant
      l2Component2Figure18ScaffoldData :=
  l2Component2PositiveTranslatedIsolatedBoxesOfFig13TilesPlane
    (tilesPlane_fig13Tiles_of_robinsonBoardLevelAlignedMacroSquares hlevel)

theorem l2Component2PositiveTranslatedIsolatedBoxesOfCheckedFigure16MacroSquares
    (hlevel : HasCheckedFigure16RecognizedRobinsonBoardLevelMacroSquares) :
    Figure18ScaffoldData.HasPositiveTranslatedIsolatedActiveBoxInvariant
      l2Component2Figure18ScaffoldData :=
  l2Component2PositiveTranslatedIsolatedBoxesOfFig13TilesPlane
    (tilesPlane_fig13Tiles_of_checkedFigure16RecognizedRobinsonBoardLevelMacroSquares
      hlevel)

theorem l2Component2PositiveTranslatedIsolatedBoxesOfCanonicalCheckedFigure16MacroSquares
    (hlevel : HasCanonicalCheckedFigure16RecognizedRobinsonBoardLevelMacroSquares) :
    Figure18ScaffoldData.HasPositiveTranslatedIsolatedActiveBoxInvariant
      l2Component2Figure18ScaffoldData :=
  l2Component2PositiveTranslatedIsolatedBoxesOfFig13TilesPlane
    (tilesPlane_fig13Tiles_of_canonicalCheckedFigure16RecognizedRobinsonBoardLevelMacroSquares
      hlevel)

theorem l2Component2PositiveTranslatedIsolatedBoxesOfCheckedCompatibleFigure16MacroSquares
    (hlevel :
      HasCheckedFigure16RecognizedCompatibleRobinsonBoardLevelMacroSquares) :
    Figure18ScaffoldData.HasPositiveTranslatedIsolatedActiveBoxInvariant
      l2Component2Figure18ScaffoldData :=
  l2Component2PositiveTranslatedIsolatedBoxesOfFigure18ScaffoldTilesPlane
    (tilesPlane_figure18ScaffoldTiles_of_checkedFigure16RecognizedCompatible
      hlevel)

theorem
    l2Component2PositiveTranslatedIsolatedBoxesOfCanonicalCheckedCompatibleFigure16MacroSquares
    (hlevel :
      HasCanonicalCheckedFigure16RecognizedCompatibleRobinsonBoardLevelMacroSquares) :
    Figure18ScaffoldData.HasPositiveTranslatedIsolatedActiveBoxInvariant
      l2Component2Figure18ScaffoldData :=
  l2Component2PositiveTranslatedIsolatedBoxesOfFigure18ScaffoldTilesPlane
    (tilesPlane_figure18ScaffoldTiles_of_canonicalCheckedFigure16RecognizedCompatible
      hlevel)

theorem
    l2Component2PositiveTranslatedIsolatedBoxesOfCanonicalCheckedCompatibleFigure16LevelData
    (hlevel : HasCanonicalCheckedFigure16RecognizedCompatibleLevelData) :
    Figure18ScaffoldData.HasPositiveTranslatedIsolatedActiveBoxInvariant
      l2Component2Figure18ScaffoldData :=
  l2Component2PositiveTranslatedIsolatedBoxesOfCanonicalCheckedCompatibleFigure16MacroSquares
    (canonicalCheckedFigure16RecognizedCompatible_of_checkedLevelData hlevel)

/--
Direct origin-zero routed certificate for the first audited L2-blank candidate.

The finite Figure 13/Figure 16 pair-compatibility check is discharged by the
candidate data; the raw Figure 13 plane tiling supplies the positive translated
active boxes used for realization.
-/
def l2Component1Figure18ScaffoldDataRoutedCertificateOfOriginZeroFig13TilesPlane
    (originZeroWindows :
      HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles) :
    l2Component1Figure18ScaffoldData.RoutedCertificate := by
  have boxes :
      Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant
        l2Component1Figure18ScaffoldData :=
    Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant.ofIsolatedActiveBoxes
        (l2Component1PositiveTranslatedIsolatedBoxesOfFig13TilesPlane hplane)
  simpa [l2Component1Figure18ScaffoldData] using
    figure18ScaffoldDataOfNatSitesRoutedCertificateOfOriginZeroPairCompatibility
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid
      originZeroWindows l2Component1BlankCandidatePairCompatibilityBool boxes

/--
Direct origin-zero routed certificate for the second audited L2-blank candidate.

The finite Figure 13/Figure 16 pair-compatibility check is discharged by the
candidate data; the raw Figure 13 plane tiling supplies the positive translated
active boxes used for realization.
-/
def l2Component2Figure18ScaffoldDataRoutedCertificateOfOriginZeroFig13TilesPlane
    (originZeroWindows :
      HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles) :
    l2Component2Figure18ScaffoldData.RoutedCertificate := by
  have boxes :
      Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant
        l2Component2Figure18ScaffoldData :=
    Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant.ofIsolatedActiveBoxes
        (l2Component2PositiveTranslatedIsolatedBoxesOfFig13TilesPlane hplane)
  simpa [l2Component2Figure18ScaffoldData] using
    figure18ScaffoldDataOfNatSitesRoutedCertificateOfOriginZeroPairCompatibility
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      originZeroWindows l2Component2BlankCandidatePairCompatibilityBool boxes

/--
Public routed Figure 18 certificate from the direct origin-zero Section 7 route
for the first audited L2-blank candidate.
-/
def l2Component1Figure18RoutedCertificateOfOriginZeroFig13TilesPlane
    (originZeroWindows :
      HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles) :
    Figure18RoutedCertificate l2Component1Figure18ScaffoldData.table.toRoleTable :=
  (l2Component1Figure18ScaffoldDataRoutedCertificateOfOriginZeroFig13TilesPlane
    originZeroWindows hplane).toRoutedCertificate

/--
Public routed Figure 18 certificate from the direct origin-zero Section 7 route
for the second audited L2-blank candidate.
-/
def l2Component2Figure18RoutedCertificateOfOriginZeroFig13TilesPlane
    (originZeroWindows :
      HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles) :
    Figure18RoutedCertificate l2Component2Figure18ScaffoldData.table.toRoleTable :=
  (l2Component2Figure18ScaffoldDataRoutedCertificateOfOriginZeroFig13TilesPlane
    originZeroWindows hplane).toRoutedCertificate

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
Patch-preserving version of `NatSiteRobinsonScaffoldCertificate`.

This keeps the finite Figure 13/Figure 16 layer patches visible through the
checked-stack Robinson route, instead of immediately compactifying them to a
plain active-corner realization certificate.
-/
structure NatSiteRobinsonLayerPatchScaffoldCertificate where
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
  patches :
    HasActiveCornerLayerBoxPatches
      (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold

/--
The same Robinson scaffold package, but with the backward scaffold construction
stated as active-indexed finite boxes instead of the already-forgotten
realization theorem.
-/
structure NatSiteRobinsonIndexedBoxScaffoldCertificate where
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
  indexedBoxes :
    ∀ r : Nat, Nonempty (ActiveCornerIndexedBox
      (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).scaffold r)

/--
Bundled Robinson Section 7 target using the local obstruction-signal tower and
finite active-corner indexed boxes.

This is the smallest current theorem-facing surface for the scaffold side:
Robinson geometry should prove the coherent board-level signal tower and
construct finite indexed boxes around every requested square; the remaining
finite compatibility check is generated from the Figure 13/Figure 16
transcription.
-/
structure NatSiteRobinsonTowerIndexedBoxObligations
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true) : Prop where
  signalLocalTower :
    HasFigure18RobinsonBoardLevelSignalLocalTowerForTable
      (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).table
  pairCompatibility :
    generatedStackAllowedSitePairCompatibilityBool
      (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
      (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
        true
  indexedBoxes :
    ∀ r : Nat, Nonempty (ActiveCornerIndexedBox
      (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).scaffold r)

/--
Canonical-routing scaffold target with the finite-box construction stated only
for positive radii.

For the audited L2 candidates the generated pair-compatibility check is already
known, so this is the clean remaining scaffold-side obligation: prove the
canonical Robinson-board routing and build finite active-corner indexed boxes
for every positive radius.
-/
structure NatSiteRobinsonCanonicalPositiveBoxObligations
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true) : Prop where
  canonicalRouting :
    HasFigure18RobinsonBoardCanonicalRoutingForTable
      (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).table
  positiveIndexedBoxes :
    ∀ r : Nat, 0 < r → Nonempty (ActiveCornerIndexedBox
      (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).scaffold r)

/--
Canonical-routing scaffold target with positive-radius boxes allowed to live at
radius-dependent translated origins.

This matches the Robinson board construction more closely: Section 7 produces
large boards at natural plane coordinates, and those boxes can be recentered
only at the interface with the generic scaffold reduction.
-/
structure NatSiteRobinsonCanonicalTranslatedPositiveBoxObligations
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true) : Prop where
  canonicalRouting :
    HasFigure18RobinsonBoardCanonicalRoutingForTable
      (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).table
  positiveTranslatedIndexedBoxes :
    ∀ r : Nat, 0 < r →
      ∃ origin : Int × Int,
        Nonempty (TranslatedActiveCornerIndexedBox
          (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
            cornerIndex cornerQuadrant cornerIndex_valid).scaffold r origin)

/--
Canonical decoded combined-site corridor-routing scaffold target with
positive-radius boxes allowed to live at radius-dependent translated origins.

This is the theorem-facing Robinson-board target for the Figure 13 reduction:
the geometry proof should supply the local combined-site corridor routing
together with arbitrarily large translated active-corner boxes.
-/
structure NatSiteRobinsonCanonicalCombinedSiteTranslatedPositiveBoxObligations
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true) : Prop where
  canonicalCombinedSiteRouting :
    HasFigure18RobinsonBoardCanonicalCombinedSiteCorridorRoutingForTable
      (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).table
  positiveTranslatedIndexedBoxes :
    ∀ r : Nat, 0 < r →
      ∃ origin : Int × Int,
        Nonempty (TranslatedActiveCornerIndexedBox
          (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
            cornerIndex cornerQuadrant cornerIndex_valid).scaffold r origin)

/--
Canonical named-site-rectangle routing target with positive-radius translated
boxes.

This is the more concrete finite scaffold target: the local Figure 13/Figure 16
proof can select an explicit Figure 18 site rectangle at each free-grid level,
then forget it when using the existing combined-site routing pipeline.
-/
structure NatSiteRobinsonCanonicalSiteRectTranslatedPositiveBoxObligations
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true) : Prop where
  canonicalSiteRectCombinedSiteRouting :
    HasFigure18RobinsonBoardCanonicalSiteRectCombinedSiteCorridorRoutingForTable
      (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).table
  positiveTranslatedIndexedBoxes :
    ∀ r : Nat, 0 < r →
      ∃ origin : Int × Int,
        Nonempty (TranslatedActiveCornerIndexedBox
          (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
            cornerIndex cornerQuadrant cornerIndex_valid).scaffold r origin)

/--
Canonical free-site-rectangle routing target with positive-radius translated
boxes.

This is the current proof-facing Robinson Section 7 target.  The obstruction
argument has already identified free rows and columns, so the routing premise
uses the selected free/free site rectangle directly instead of exposing clear
row/column side conditions.
-/
structure NatSiteRobinsonCanonicalFreeSiteRectTranslatedPositiveBoxObligations
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true) : Prop where
  canonicalFreeSiteRectRouting :
    HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable
      (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).table
  positiveTranslatedIndexedBoxes :
    ∀ r : Nat, 0 < r →
      ∃ origin : Int × Int,
        Nonempty (TranslatedActiveCornerIndexedBox
          (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
            cornerIndex cornerQuadrant cornerIndex_valid).scaffold r origin)

/--
Robinson Section 7 board/free-line target with finite active-corner layer
patches.

This is the finite-check-facing scaffold surface closest to the current proof
plan: Robinson's obstruction/free-line argument supplies active/corner
recognition at canonical free crossings, the Figure 13/Figure 16 finite decoder
supplies layer patches for all positive boxes, and the generated pair
compatibility check connects the local Figure 18 sites.
-/
structure NatSiteRobinsonSection7BoardFreeLineLayerPatchObligations
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true) : Prop where
  boardFreeLineActiveCorner :
    Figure18ScaffoldData.HasRobinsonSection7BoardFreeLineActiveCornerInvariant
      (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid)
  pairCompatibility :
    generatedStackAllowedSitePairCompatibilityBool
      (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
      (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
        true
  patches :
    HasActiveCornerLayerBoxPatches
      (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold

/--
Origin-zero active/corner window target with generated finite compatibility and
positive translated boxes.

This is the scaffold-facing target for the current Figure 13/Figure 16 route:
the geometry proof supplies canonical origin-zero active/corner windows, the
finite transcription supplies generated pair compatibility, and the backward
construction supplies translated active-corner boxes.
-/
structure NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true) : Prop where
  originZeroWindows :
    HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
      (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).table
  pairCompatibility :
    generatedStackAllowedSitePairCompatibilityBool
      (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
      (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
        true
  positiveTranslatedIndexedBoxes :
    ∀ r : Nat, 0 < r →
      ∃ origin : Int × Int,
        Nonempty (TranslatedActiveCornerIndexedBox
          (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
            cornerIndex cornerQuadrant cornerIndex_valid).scaffold r origin)

/--
Translation-invariant indexed-active scaffold target.

Unlike the origin-zero target, the indexed active/corner window carries its own
origin.  This matches plane tilings, which are closed under translation, while
still using the generated Figure 13/Figure 16 compatibility checker and the
translated active-box realization route.
-/
structure NatSiteRobinsonIndexedActiveTranslatedPositiveBoxObligations
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true) : Prop where
  indexedActiveWindows :
    HasFigure18IndexedActiveCornerWindows
      (Figure18RoleTable.FlatRoleTable.ofActiveSites
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid).sites
        (cornerSiteOfNat cornerIndex cornerQuadrant
          cornerIndex_valid)).toRoleTable
  pairCompatibility :
    generatedStackAllowedSitePairCompatibilityBool
      (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
      (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
        true
  positiveTranslatedIndexedBoxes :
    ∀ r : Nat, 0 < r →
      ∃ origin : Int × Int,
        Nonempty (TranslatedActiveCornerIndexedBox
          (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
            cornerIndex cornerQuadrant cornerIndex_valid).scaffold r origin)

/--
Tiling-dependent geometry-tower decoded combined-site corridor-routing
scaffold target, with positive-radius boxes allowed to live at
radius-dependent translated origins.

This is the theorem-facing Robinson-board target closest to the paper:
Section 7 supplies the board geometry from the tiling itself, and the decoded
payload is routed through the combined-site corridors on that geometry.
-/
structure NatSiteRobinsonGeomCombinedTranslatedPositiveBoxObligations
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true) : Prop where
  geomCombinedSiteRouting :
    HasFigure18RobinsonBoardGeometryTowerCombinedSiteCorridorRoutingForTable
      (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).table
  positiveTranslatedIndexedBoxes :
    ∀ r : Nat, 0 < r →
      ∃ origin : Int × Int,
        Nonempty (TranslatedActiveCornerIndexedBox
          (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
            cornerIndex cornerQuadrant cornerIndex_valid).scaffold r origin)

namespace NatSiteRobinsonIndexedBoxScaffoldCertificate

def toScaffoldCertificate
    (C : NatSiteRobinsonIndexedBoxScaffoldCertificate) :
    NatSiteRobinsonScaffoldCertificate where
  activeSiteSpecs := C.activeSiteSpecs
  activeSiteSpecs_valid := C.activeSiteSpecs_valid
  cornerIndex := C.cornerIndex
  cornerQuadrant := C.cornerQuadrant
  cornerIndex_valid := C.cornerIndex_valid
  robinsonStacks := C.robinsonStacks
  realizes :=
    scaffoldDataOfNatSitesRealizesOfActiveCornerIndexedBoxes
      C.activeSiteSpecs C.activeSiteSpecs_valid C.cornerIndex
      C.cornerQuadrant C.cornerIndex_valid C.indexedBoxes

end NatSiteRobinsonIndexedBoxScaffoldCertificate

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

/--
Level-indexed Robinson-board/free-grid obligations with local compatibility
bundled into the routed grid witness.

This is the clean target for the Robinson Section 7 scaffold argument: the
finite stack checker needs each generated level grid together with the local
horizontal and vertical Figure 18 site compatibility it induces.
-/
structure NatSiteRobinsonCompatibleLevelObligations
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true) : Prop where
  levelCompatibleRoutedFreeGrids :
    HasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable
      (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).table
  pairCompatibility :
    generatedStackAllowedSitePairCompatibilityBool
      (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
      (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
        true
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

def ofSignalLocalCompatibility
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (signalCertificates :
      HasFigure18RobinsonBoardLevelSignalCertificatesForTable
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
      cornerIndex cornerQuadrant cornerIndex_valid :=
  ofLocalCompatibility activeSiteSpecs activeSiteSpecs_valid
    cornerIndex cornerQuadrant cornerIndex_valid
    (hasFigure18RobinsonBoardLevelRoutedFreeGridsForTable_of_signalCertificates
      signalCertificates)
    levelLocalCompatibility realizes hcheck

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

namespace NatSiteRobinsonCompatibleLevelObligations

/--
The compatible level-grid part of the Nat-site Section 7 obligation is exactly
the forward forcing half of the abstract scaffold instance.
-/
def forces
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (O : NatSiteRobinsonCompatibleLevelObligations activeSiteSpecs
      activeSiteSpecs_valid cornerIndex cornerQuadrant cornerIndex_valid) :
    ForcesFixedCornerSquares
      (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold :=
  forcesFixedCornerSquares_of_robinsonBoardLevelCompatibleRoutedFreeGridsForTable
    O.levelCompatibleRoutedFreeGrids

/-- Compatible level Nat-site obligations are already a flexible Figure 18 certificate. -/
def flexibleCertificate
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (O : NatSiteRobinsonCompatibleLevelObligations activeSiteSpecs
      activeSiteSpecs_valid cornerIndex cornerQuadrant cornerIndex_valid) :
    Figure18FlexibleCertificate
      (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).table where
  forces := O.forces
  realizes := O.realizes

/-- Package compatible level Nat-site obligations as a flexible Figure 18 instance. -/
def flexibleInstance
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (O : NatSiteRobinsonCompatibleLevelObligations activeSiteSpecs
      activeSiteSpecs_valid cornerIndex cornerQuadrant cornerIndex_valid) :
    Figure18FlexibleInstance where
  table :=
    (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid).table
  certificate := O.flexibleCertificate

/-- The direct flexible instance keeps the audited Figure 13 scaffold tiles. -/
theorem flexibleInstance_presentation_tiles
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (O : NatSiteRobinsonCompatibleLevelObligations activeSiteSpecs
      activeSiteSpecs_valid cornerIndex cornerQuadrant cornerIndex_valid) :
    O.flexibleInstance.presentation.tiles =
      TileSubdivision.subdivideTileSet fig13Tiles :=
  O.flexibleInstance.presentation_tiles

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
    NatSiteRobinsonCompatibleLevelObligations activeSiteSpecs
      activeSiteSpecs_valid cornerIndex cornerQuadrant cornerIndex_valid where
  levelCompatibleRoutedFreeGrids := by
    intro T seed x hx level
    rcases levelRoutedFreeGrids x hx level with ⟨grid⟩
    exact ⟨⟨grid, levelLocalCompatibility level grid⟩⟩
  pairCompatibility := hcheck
  realizes := realizes

/--
Version of `ofLocalCompatibility` whose backward scaffold input is the finite
box realization supplied by Robinson's nested-board construction.
-/
def ofLocalCompatibilityBoxes
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
      RealizesActiveCornerBoxes
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true) :
    NatSiteRobinsonCompatibleLevelObligations activeSiteSpecs
      activeSiteSpecs_valid cornerIndex cornerQuadrant cornerIndex_valid :=
  ofLocalCompatibility activeSiteSpecs activeSiteSpecs_valid
    cornerIndex cornerQuadrant cornerIndex_valid
    levelRoutedFreeGrids levelLocalCompatibility
    (realizesActiveCornerSquares_of_realizesActiveCornerBoxes realizes)
    hcheck

/--
Patch-witness version of `ofLocalCompatibility`.  This exposes the compatible
level-grid route through the finite patches produced by the Robinson board
construction, before compactifying them to a plane realization.
-/
def ofLocalCompatibilityPatches
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
    (patches :
      HasActiveCornerBoxPatches
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true) :
    NatSiteRobinsonCompatibleLevelObligations activeSiteSpecs
      activeSiteSpecs_valid cornerIndex cornerQuadrant cornerIndex_valid :=
  ofLocalCompatibilityBoxes activeSiteSpecs activeSiteSpecs_valid
    cornerIndex cornerQuadrant cornerIndex_valid
    levelRoutedFreeGrids levelLocalCompatibility
    (realizesActiveCornerBoxes_of_activeCornerBoxPatches patches)
    hcheck

/--
Layer-patch version of `ofLocalCompatibility`.  This is the structured target
for the compatible-level route: a scaffold/base box plus a compatible payload
labelling is enough to discharge the backward scaffold realization.
-/
def ofLocalCompatibilityLayerPatches
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
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true) :
    NatSiteRobinsonCompatibleLevelObligations activeSiteSpecs
      activeSiteSpecs_valid cornerIndex cornerQuadrant cornerIndex_valid :=
  ofLocalCompatibilityPatches activeSiteSpecs activeSiteSpecs_valid
    cornerIndex cornerQuadrant cornerIndex_valid
    levelRoutedFreeGrids levelLocalCompatibility
    (activeCornerBoxPatches_of_layerBoxPatches patches)
    hcheck

/--
Layer-patch version for already-compatible Robinson level grids.

This is the finite scaffold-target form used once the Section 7 construction
has bundled the local horizontal and vertical Figure 18 compatibility into each
level grid witness.
-/
def ofLevelCompatibleLayerPatches
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (levelCompatibleRoutedFreeGrids :
      HasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true) :
    NatSiteRobinsonCompatibleLevelObligations activeSiteSpecs
      activeSiteSpecs_valid cornerIndex cornerQuadrant cornerIndex_valid where
  levelCompatibleRoutedFreeGrids := levelCompatibleRoutedFreeGrids
  pairCompatibility := hcheck
  realizes :=
    realizesActiveCornerSquares_of_realizesActiveCornerBoxes
      (realizesActiveCornerBoxes_of_activeCornerLayerBoxPatches patches)

/--
Positive-indexed-box version for already-compatible Robinson level grids.

The radius-zero combined patch is supplied by the scaffold corner tile, so the
finite realization side only has to construct active-corner indexed boxes at
positive radii.
-/
def ofLevelCompatiblePositiveBoxes
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (levelCompatibleRoutedFreeGrids :
      HasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hboxes_pos :
      ∀ r : Nat, 0 < r → Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).scaffold r))
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true) :
    NatSiteRobinsonCompatibleLevelObligations activeSiteSpecs
      activeSiteSpecs_valid cornerIndex cornerQuadrant cornerIndex_valid :=
  ofLevelCompatibleLayerPatches activeSiteSpecs activeSiteSpecs_valid
    cornerIndex cornerQuadrant cornerIndex_valid levelCompatibleRoutedFreeGrids
    (activeCornerLayerBoxPatches_of_positiveActiveCornerIndexedBoxes
      (by
        simpa [LayeredFigure18ScaffoldData.scaffold,
          LayeredFigure18ScaffoldData.presentation] using
          Figure18RoleTable.scaffold_corner_mem
            (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
              cornerIndex cornerQuadrant cornerIndex_valid).table)
      hboxes_pos)
    hcheck

/--
Translated-positive-box version for already-compatible Robinson level grids.

This is the natural interface for boxes produced inside large Robinson boards:
they may be centered at radius-dependent plane origins, and are recentered only
when discharging the generic positive-box realization side.
-/
def ofLevelCompatiblePositiveTranslatedBoxes
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (levelCompatibleRoutedFreeGrids :
      HasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (translatedBoxes_pos :
      ∀ r : Nat, 0 < r →
        ∃ origin : Int × Int,
          Nonempty (TranslatedActiveCornerIndexedBox
            (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
              cornerIndex cornerQuadrant cornerIndex_valid).scaffold r origin))
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true) :
    NatSiteRobinsonCompatibleLevelObligations activeSiteSpecs
      activeSiteSpecs_valid cornerIndex cornerQuadrant cornerIndex_valid :=
  ofLevelCompatiblePositiveBoxes activeSiteSpecs activeSiteSpecs_valid
    cornerIndex cornerQuadrant cornerIndex_valid levelCompatibleRoutedFreeGrids
    (TranslatedActiveCornerIndexedBox.nonempty_centered_pos_of_translated_pos
      translatedBoxes_pos)
    hcheck

/--
Paper-shaped Section 7 constructor: decoded combined-site corridor routing
supplies the compatible routed free grids, while translated positive boxes
provide the backward scaffold realization.
-/
def ofGeometryCombinedPositiveTranslatedBoxes
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (geomCombinedSiteRouting :
      HasFigure18RobinsonBoardGeometryTowerCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (translatedBoxes_pos :
      ∀ r : Nat, 0 < r →
        ∃ origin : Int × Int,
          Nonempty (TranslatedActiveCornerIndexedBox
            (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
              cornerIndex cornerQuadrant cornerIndex_valid).scaffold r origin))
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true) :
    NatSiteRobinsonCompatibleLevelObligations activeSiteSpecs
      activeSiteSpecs_valid cornerIndex cornerQuadrant cornerIndex_valid :=
  ofLevelCompatiblePositiveTranslatedBoxes activeSiteSpecs
    activeSiteSpecs_valid cornerIndex cornerQuadrant cornerIndex_valid
    (hasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable_of_geometryTowerCombinedSites
      geomCombinedSiteRouting)
    translatedBoxes_pos hcheck

set_option linter.style.longLine false in
/--
Robinson Section 7 obstruction-routing version of
`ofGeometryCombinedPositiveTranslatedBoxes`.

This is the paper-facing constructor: the obstruction/free-line argument is
recorded as `HasRobinsonSection7ObstructionRoutingInvariant`; the existing
Figure 18 scaffold bridges turn it into compatible routed level grids.
-/
def ofSection7ObstructionRoutingPositiveTranslatedBoxes
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (section7Routing :
      Figure18ScaffoldData.HasRobinsonSection7ObstructionRoutingInvariant
        (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid))
    (translatedBoxes_pos :
      ∀ r : Nat, 0 < r →
        ∃ origin : Int × Int,
          Nonempty (TranslatedActiveCornerIndexedBox
            (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
              cornerIndex cornerQuadrant cornerIndex_valid).scaffold r origin))
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true) :
    NatSiteRobinsonCompatibleLevelObligations activeSiteSpecs
      activeSiteSpecs_valid cornerIndex cornerQuadrant cornerIndex_valid :=
  ofLevelCompatiblePositiveTranslatedBoxes activeSiteSpecs
    activeSiteSpecs_valid cornerIndex cornerQuadrant cornerIndex_valid
    (hasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable_of_localTower
      (Figure18ScaffoldData.HasRobinsonBoardLevelSignalLocalTowerInvariant.ofSection7ObstructionRouting
        section7Routing))
    translatedBoxes_pos hcheck

set_option linter.style.longLine false in
/--
Robinson Section 7 board/free-line version of
`ofSection7ObstructionRoutingPositiveTranslatedBoxes`.

This is the most direct constructor for Robinson's wording: the board/free-line
argument supplies the canonical geometry together with active/corner
recognition at the free crossings.  The lower-level bridge then packages this
as the obstruction-routing data needed by the compatible routed-grid checker.
-/
def ofSection7BoardFreeLinePositiveTranslatedBoxes
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (boardFreeLine :
      Figure18ScaffoldData.HasRobinsonSection7BoardFreeLineActiveCornerInvariant
        (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid))
    (translatedBoxes_pos :
      ∀ r : Nat, 0 < r →
        ∃ origin : Int × Int,
          Nonempty (TranslatedActiveCornerIndexedBox
            (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
              cornerIndex cornerQuadrant cornerIndex_valid).scaffold r origin))
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true) :
    NatSiteRobinsonCompatibleLevelObligations activeSiteSpecs
      activeSiteSpecs_valid cornerIndex cornerQuadrant cornerIndex_valid :=
  ofLevelCompatiblePositiveTranslatedBoxes activeSiteSpecs
    activeSiteSpecs_valid cornerIndex cornerQuadrant cornerIndex_valid
    (hasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable_of_localTower
      (Figure18ScaffoldData.HasRobinsonBoardLevelSignalLocalTowerInvariant.ofBoardFreeLineActiveCorner
        boardFreeLine))
    translatedBoxes_pos hcheck

set_option linter.style.longLine false in
/--
Robinson Section 7 board/free-line version with finite layer patches.

This is the finite-check-facing form of `ofSection7BoardFreeLinePositiveTranslatedBoxes`:
the board/free-line argument supplies the compatible routed free grids, while
the layer patches supply the active-corner realization directly.
-/
def ofSection7BoardFreeLineLayerPatches
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (boardFreeLine :
      Figure18ScaffoldData.HasRobinsonSection7BoardFreeLineActiveCornerInvariant
        (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid))
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true) :
    NatSiteRobinsonCompatibleLevelObligations activeSiteSpecs
      activeSiteSpecs_valid cornerIndex cornerQuadrant cornerIndex_valid :=
  ofLevelCompatibleLayerPatches activeSiteSpecs activeSiteSpecs_valid
    cornerIndex cornerQuadrant cornerIndex_valid
    (hasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable_of_localTower
      (Figure18ScaffoldData.HasRobinsonBoardLevelSignalLocalTowerInvariant.ofBoardFreeLineActiveCorner
        boardFreeLine))
    patches hcheck

/--
Canonical decoded corridor routing version of
`ofGeometryCombinedPositiveTranslatedBoxes`.
-/
def ofCanonicalCombinedPositiveTranslatedBoxes
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (canonicalCombinedSiteRouting :
      HasFigure18RobinsonBoardCanonicalCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (translatedBoxes_pos :
      ∀ r : Nat, 0 < r →
        ∃ origin : Int × Int,
          Nonempty (TranslatedActiveCornerIndexedBox
            (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
              cornerIndex cornerQuadrant cornerIndex_valid).scaffold r origin))
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true) :
    NatSiteRobinsonCompatibleLevelObligations activeSiteSpecs
      activeSiteSpecs_valid cornerIndex cornerQuadrant cornerIndex_valid :=
  ofLevelCompatiblePositiveTranslatedBoxes activeSiteSpecs
    activeSiteSpecs_valid cornerIndex cornerQuadrant cornerIndex_valid
    (hasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable_of_canonicalCombinedSites
      canonicalCombinedSiteRouting)
    translatedBoxes_pos hcheck

def ofLocalSignalCoordinateSteps
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (signalLocalCoordinateSteps :
      HasFigure18RobinsonBoardLevelSignalLocalCoordinateStepsForTable
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
    NatSiteRobinsonCompatibleLevelObligations activeSiteSpecs
      activeSiteSpecs_valid cornerIndex cornerQuadrant cornerIndex_valid where
  levelCompatibleRoutedFreeGrids :=
    hasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable_of_localCoordinateSteps
      signalLocalCoordinateSteps
  pairCompatibility := hcheck
  realizes := realizes

/--
Coherent tower version of `ofLocalSignalCoordinateSteps`.

This is the closest constructor to Robinson's nested-board proof: the geometry
supplies a compatible signal certificate at every level and coordinate steps
between consecutive levels, then the existing finite stack checker and
realization data finish the scaffold certificate.
-/
def ofLocalSignalTower
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (signalLocalTower :
      HasFigure18RobinsonBoardLevelSignalLocalTowerForTable
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
    NatSiteRobinsonCompatibleLevelObligations activeSiteSpecs
      activeSiteSpecs_valid cornerIndex cornerQuadrant cornerIndex_valid :=
  ofLocalSignalCoordinateSteps activeSiteSpecs activeSiteSpecs_valid
    cornerIndex cornerQuadrant cornerIndex_valid
    (hasFigure18RobinsonBoardLevelSignalLocalCoordinateStepsForTable_of_localTower
      signalLocalTower)
    realizes hcheck

/--
Fixed-geometry-routing version of `ofLocalSignalTower`.

This is the split Robinson Section 7 target: prove one payload-independent
geometry tower, then prove Figure 18 routing over that tower for each combined
tiling.
-/
def ofFixedGeometryTowerRouting
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (fixedGeometryRouting :
      HasFigure18RobinsonBoardFixedGeometryTowerRoutingForTable
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
    NatSiteRobinsonCompatibleLevelObligations activeSiteSpecs
      activeSiteSpecs_valid cornerIndex cornerQuadrant cornerIndex_valid :=
  ofLocalSignalTower activeSiteSpecs activeSiteSpecs_valid
    cornerIndex cornerQuadrant cornerIndex_valid
    (hasFigure18RobinsonBoardLevelSignalLocalTowerForTable_of_fixedGeometryTowerRouting
      fixedGeometryRouting)
    realizes hcheck

/--
Preferred Section 7 constructor with both local coordinate-step certificates
and finite-box realization.  This is the proof target closest to Robinson's
description: local obstruction signals give the level grids, while finite board
patches give every centered box and compactness supplies the plane tiling.
-/
def ofLocalSignalCoordinateStepsBoxes
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (signalLocalCoordinateSteps :
      HasFigure18RobinsonBoardLevelSignalLocalCoordinateStepsForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerBoxes
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true) :
    NatSiteRobinsonCompatibleLevelObligations activeSiteSpecs
      activeSiteSpecs_valid cornerIndex cornerQuadrant cornerIndex_valid :=
  ofLocalSignalCoordinateSteps activeSiteSpecs activeSiteSpecs_valid
    cornerIndex cornerQuadrant cornerIndex_valid
    signalLocalCoordinateSteps
    (realizesActiveCornerSquares_of_realizesActiveCornerBoxes realizes)
    hcheck

/-- Coherent tower version of `ofLocalSignalCoordinateStepsBoxes`. -/
def ofLocalSignalTowerBoxes
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (signalLocalTower :
      HasFigure18RobinsonBoardLevelSignalLocalTowerForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerBoxes
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true) :
    NatSiteRobinsonCompatibleLevelObligations activeSiteSpecs
      activeSiteSpecs_valid cornerIndex cornerQuadrant cornerIndex_valid :=
  ofLocalSignalTower activeSiteSpecs activeSiteSpecs_valid
    cornerIndex cornerQuadrant cornerIndex_valid
    signalLocalTower
    (realizesActiveCornerSquares_of_realizesActiveCornerBoxes realizes)
    hcheck

/-- Fixed-geometry-routing version of `ofLocalSignalTowerBoxes`. -/
def ofFixedGeometryTowerRoutingBoxes
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (fixedGeometryRouting :
      HasFigure18RobinsonBoardFixedGeometryTowerRoutingForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerBoxes
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true) :
    NatSiteRobinsonCompatibleLevelObligations activeSiteSpecs
      activeSiteSpecs_valid cornerIndex cornerQuadrant cornerIndex_valid :=
  ofFixedGeometryTowerRouting activeSiteSpecs activeSiteSpecs_valid
    cornerIndex cornerQuadrant cornerIndex_valid
    fixedGeometryRouting
    (realizesActiveCornerSquares_of_realizesActiveCornerBoxes realizes)
    hcheck

/--
Patch-witness version of the preferred Section 7 constructor.  The geometric
Robinson proof can now construct finite combined box patches directly; the
generic scaffold layer turns those patches into finite boxes and then into
plane realization by compactness.
-/
def ofLocalSignalCoordinateStepsPatches
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (signalLocalCoordinateSteps :
      HasFigure18RobinsonBoardLevelSignalLocalCoordinateStepsForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (patches :
      HasActiveCornerBoxPatches
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true) :
    NatSiteRobinsonCompatibleLevelObligations activeSiteSpecs
      activeSiteSpecs_valid cornerIndex cornerQuadrant cornerIndex_valid :=
  ofLocalSignalCoordinateStepsBoxes activeSiteSpecs activeSiteSpecs_valid
    cornerIndex cornerQuadrant cornerIndex_valid
    signalLocalCoordinateSteps
    (realizesActiveCornerBoxes_of_activeCornerBoxPatches patches)
    hcheck

/-- Coherent tower version of `ofLocalSignalCoordinateStepsPatches`. -/
def ofLocalSignalTowerPatches
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (signalLocalTower :
      HasFigure18RobinsonBoardLevelSignalLocalTowerForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (patches :
      HasActiveCornerBoxPatches
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true) :
    NatSiteRobinsonCompatibleLevelObligations activeSiteSpecs
      activeSiteSpecs_valid cornerIndex cornerQuadrant cornerIndex_valid :=
  ofLocalSignalTowerBoxes activeSiteSpecs activeSiteSpecs_valid
    cornerIndex cornerQuadrant cornerIndex_valid
    signalLocalTower
    (realizesActiveCornerBoxes_of_activeCornerBoxPatches patches)
    hcheck

/-- Fixed-geometry-routing version of `ofLocalSignalTowerPatches`. -/
def ofFixedGeometryTowerRoutingPatches
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (fixedGeometryRouting :
      HasFigure18RobinsonBoardFixedGeometryTowerRoutingForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (patches :
      HasActiveCornerBoxPatches
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true) :
    NatSiteRobinsonCompatibleLevelObligations activeSiteSpecs
      activeSiteSpecs_valid cornerIndex cornerQuadrant cornerIndex_valid :=
  ofFixedGeometryTowerRoutingBoxes activeSiteSpecs activeSiteSpecs_valid
    cornerIndex cornerQuadrant cornerIndex_valid
    fixedGeometryRouting
    (realizesActiveCornerBoxes_of_activeCornerBoxPatches patches)
    hcheck

/--
Layer-patch version of the preferred Section 7 constructor.  This is the most
structured backward target: Robinson supplies a valid scaffold/base box and a
payload labelling over it; the generic layer-patch conversion assembles the
combined finite boxes needed for compactness.
-/
def ofLocalSignalCoordinateStepsLayerPatches
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (signalLocalCoordinateSteps :
      HasFigure18RobinsonBoardLevelSignalLocalCoordinateStepsForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true) :
    NatSiteRobinsonCompatibleLevelObligations activeSiteSpecs
      activeSiteSpecs_valid cornerIndex cornerQuadrant cornerIndex_valid :=
  ofLocalSignalCoordinateStepsPatches activeSiteSpecs activeSiteSpecs_valid
    cornerIndex cornerQuadrant cornerIndex_valid
    signalLocalCoordinateSteps
    (activeCornerBoxPatches_of_layerBoxPatches patches)
    hcheck

/-- Coherent tower version of `ofLocalSignalCoordinateStepsLayerPatches`. -/
def ofLocalSignalTowerLayerPatches
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (signalLocalTower :
      HasFigure18RobinsonBoardLevelSignalLocalTowerForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true) :
    NatSiteRobinsonCompatibleLevelObligations activeSiteSpecs
      activeSiteSpecs_valid cornerIndex cornerQuadrant cornerIndex_valid :=
  ofLocalSignalTowerPatches activeSiteSpecs activeSiteSpecs_valid
    cornerIndex cornerQuadrant cornerIndex_valid
    signalLocalTower
    (activeCornerBoxPatches_of_layerBoxPatches patches)
    hcheck

/-- Fixed-geometry-routing version of `ofLocalSignalTowerLayerPatches`. -/
def ofFixedGeometryTowerRoutingLayerPatches
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (fixedGeometryRouting :
      HasFigure18RobinsonBoardFixedGeometryTowerRoutingForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true) :
    NatSiteRobinsonCompatibleLevelObligations activeSiteSpecs
      activeSiteSpecs_valid cornerIndex cornerQuadrant cornerIndex_valid :=
  ofFixedGeometryTowerRoutingPatches activeSiteSpecs activeSiteSpecs_valid
    cornerIndex cornerQuadrant cornerIndex_valid
    fixedGeometryRouting
    (activeCornerBoxPatches_of_layerBoxPatches patches)
    hcheck

/--
Product-witness fixed-geometry-routing version of
`ofFixedGeometryTowerRoutingLayerPatches`.
-/
def ofFixedGeometryTowerProductWitnessRoutingLayerPatches
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (fixedGeometryRouting :
      HasFigure18RobinsonBoardFixedGeometryTowerProductWitnessRoutingForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true) :
    NatSiteRobinsonCompatibleLevelObligations activeSiteSpecs
      activeSiteSpecs_valid cornerIndex cornerQuadrant cornerIndex_valid :=
  ofFixedGeometryTowerRoutingLayerPatches
    activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
    cornerIndex_valid
    (hasFigure18RobinsonBoardFixedGeometryTowerRoutingForTable_of_productWitnessRouting
      fixedGeometryRouting)
    patches hcheck

def ofPairFailures
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (levelCompatibleRoutedFreeGrids :
      HasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable
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
    NatSiteRobinsonCompatibleLevelObligations activeSiteSpecs
      activeSiteSpecs_valid cornerIndex cornerQuadrant cornerIndex_valid where
  levelCompatibleRoutedFreeGrids := levelCompatibleRoutedFreeGrids
  pairCompatibility :=
    generatedStackAllowedSitePairCompatibilityBool_of_failures_eq_nil
      pairFailures
  realizes := realizes

def ofL2Component1BlankCandidate
    (levelCompatibleRoutedFreeGrids :
      HasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable
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
    NatSiteRobinsonCompatibleLevelObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid where
  levelCompatibleRoutedFreeGrids := levelCompatibleRoutedFreeGrids
  pairCompatibility := by
    simpa [l2Component1BlankCandidateActiveSiteData,
      l2Component1BlankCandidateCornerSite, NatSiteSpecSanity.activeSiteData,
      NatSiteSpecSanity.cornerSite] using
      l2Component1BlankCandidatePairCompatibilityBool
  realizes := realizes

/--
Compatible-level L2 component-1 entry point using Robinson finite box patches.
-/
def ofL2Component1BlankCandidatePatches
    (levelCompatibleRoutedFreeGrids :
      HasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (patches :
      HasActiveCornerBoxPatches
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold) :
    NatSiteRobinsonCompatibleLevelObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofL2Component1BlankCandidate levelCompatibleRoutedFreeGrids
    (realizesActiveCornerSquares_of_realizesActiveCornerBoxes
      (realizesActiveCornerBoxes_of_activeCornerBoxPatches patches))

/-- L2 component-1 specialization of the Section 7 obstruction-routing constructor. -/
def ofL2Component1Section7ObstructionRoutingPositiveTranslatedBoxes
    (section7Routing :
      Figure18ScaffoldData.HasRobinsonSection7ObstructionRoutingInvariant
        (figure18ScaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid))
    (translatedBoxes_pos :
      ∀ r : Nat, 0 < r →
        ∃ origin : Int × Int,
          Nonempty (TranslatedActiveCornerIndexedBox
            (scaffoldDataOfNatSites
              l2Component1BlankCandidateActiveSiteSpecs
              l2Component1BlankCandidateSanity.activeSiteSpecs_valid
              0 Quadrant.southwest
              l2Component1BlankCandidateSanity.cornerIndex_valid).scaffold
            r origin)) :
    NatSiteRobinsonCompatibleLevelObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofSection7ObstructionRoutingPositiveTranslatedBoxes
    l2Component1BlankCandidateActiveSiteSpecs
    l2Component1BlankCandidateSanity.activeSiteSpecs_valid
    0 Quadrant.southwest
    l2Component1BlankCandidateSanity.cornerIndex_valid
    section7Routing translatedBoxes_pos
    (by
      simpa [l2Component1BlankCandidateActiveSiteData,
        l2Component1BlankCandidateCornerSite, NatSiteSpecSanity.activeSiteData,
        NatSiteSpecSanity.cornerSite] using
        l2Component1BlankCandidatePairCompatibilityBool)

/-- L2 component-1 specialization of the Section 7 board/free-line constructor. -/
def ofL2Component1Section7BoardFreeLinePositiveTranslatedBoxes
    (boardFreeLine :
      Figure18ScaffoldData.HasRobinsonSection7BoardFreeLineActiveCornerInvariant
        (figure18ScaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid))
    (translatedBoxes_pos :
      ∀ r : Nat, 0 < r →
        ∃ origin : Int × Int,
          Nonempty (TranslatedActiveCornerIndexedBox
            (scaffoldDataOfNatSites
              l2Component1BlankCandidateActiveSiteSpecs
              l2Component1BlankCandidateSanity.activeSiteSpecs_valid
              0 Quadrant.southwest
              l2Component1BlankCandidateSanity.cornerIndex_valid).scaffold
            r origin)) :
    NatSiteRobinsonCompatibleLevelObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofSection7BoardFreeLinePositiveTranslatedBoxes
    l2Component1BlankCandidateActiveSiteSpecs
    l2Component1BlankCandidateSanity.activeSiteSpecs_valid
    0 Quadrant.southwest
    l2Component1BlankCandidateSanity.cornerIndex_valid
    boardFreeLine translatedBoxes_pos
    (by
      simpa [l2Component1BlankCandidateActiveSiteData,
        l2Component1BlankCandidateCornerSite, NatSiteSpecSanity.activeSiteData,
        NatSiteSpecSanity.cornerSite] using
        l2Component1BlankCandidatePairCompatibilityBool)

/--
L2 component-1 specialization of the Section 7 board/free-line layer-patch
constructor.
-/
def ofL2Component1Section7BoardFreeLineLayerPatches
    (boardFreeLine :
      Figure18ScaffoldData.HasRobinsonSection7BoardFreeLineActiveCornerInvariant
        (figure18ScaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid))
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold) :
    NatSiteRobinsonCompatibleLevelObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofSection7BoardFreeLineLayerPatches
    l2Component1BlankCandidateActiveSiteSpecs
    l2Component1BlankCandidateSanity.activeSiteSpecs_valid
    0 Quadrant.southwest
    l2Component1BlankCandidateSanity.cornerIndex_valid
    boardFreeLine patches
    (by
      simpa [l2Component1BlankCandidateActiveSiteData,
        l2Component1BlankCandidateCornerSite, NatSiteSpecSanity.activeSiteData,
        NatSiteSpecSanity.cornerSite] using
        l2Component1BlankCandidatePairCompatibilityBool)

/--
Compatible-level L2 component-1 entry point using Robinson finite layer patches.
-/
def ofL2Component1BlankCandidateLayerPatches
    (levelCompatibleRoutedFreeGrids :
      HasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold) :
    NatSiteRobinsonCompatibleLevelObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofL2Component1BlankCandidatePatches levelCompatibleRoutedFreeGrids
    (activeCornerBoxPatches_of_layerBoxPatches patches)

def ofL2Component2BlankCandidate
    (levelCompatibleRoutedFreeGrids :
      HasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable
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
    NatSiteRobinsonCompatibleLevelObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid where
  levelCompatibleRoutedFreeGrids := levelCompatibleRoutedFreeGrids
  pairCompatibility := by
    simpa [l2Component2BlankCandidateActiveSiteData,
      l2Component2BlankCandidateCornerSite, NatSiteSpecSanity.activeSiteData,
      NatSiteSpecSanity.cornerSite] using
      l2Component2BlankCandidatePairCompatibilityBool
  realizes := realizes

/--
Compatible-level L2 component-2 entry point using Robinson finite box patches.
-/
def ofL2Component2BlankCandidatePatches
    (levelCompatibleRoutedFreeGrids :
      HasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (patches :
      HasActiveCornerBoxPatches
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold) :
    NatSiteRobinsonCompatibleLevelObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofL2Component2BlankCandidate levelCompatibleRoutedFreeGrids
    (realizesActiveCornerSquares_of_realizesActiveCornerBoxes
      (realizesActiveCornerBoxes_of_activeCornerBoxPatches patches))

/-- L2 component-2 specialization of the Section 7 obstruction-routing constructor. -/
def ofL2Component2Section7ObstructionRoutingPositiveTranslatedBoxes
    (section7Routing :
      Figure18ScaffoldData.HasRobinsonSection7ObstructionRoutingInvariant
        (figure18ScaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid))
    (translatedBoxes_pos :
      ∀ r : Nat, 0 < r →
        ∃ origin : Int × Int,
          Nonempty (TranslatedActiveCornerIndexedBox
            (scaffoldDataOfNatSites
              l2Component2BlankCandidateActiveSiteSpecs
              l2Component2BlankCandidateSanity.activeSiteSpecs_valid
              0 Quadrant.northeast
              l2Component2BlankCandidateSanity.cornerIndex_valid).scaffold
            r origin)) :
    NatSiteRobinsonCompatibleLevelObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofSection7ObstructionRoutingPositiveTranslatedBoxes
    l2Component2BlankCandidateActiveSiteSpecs
    l2Component2BlankCandidateSanity.activeSiteSpecs_valid
    0 Quadrant.northeast
    l2Component2BlankCandidateSanity.cornerIndex_valid
    section7Routing translatedBoxes_pos
    (by
      simpa [l2Component2BlankCandidateActiveSiteData,
        l2Component2BlankCandidateCornerSite, NatSiteSpecSanity.activeSiteData,
        NatSiteSpecSanity.cornerSite] using
        l2Component2BlankCandidatePairCompatibilityBool)

/-- L2 component-2 specialization of the Section 7 board/free-line constructor. -/
def ofL2Component2Section7BoardFreeLinePositiveTranslatedBoxes
    (boardFreeLine :
      Figure18ScaffoldData.HasRobinsonSection7BoardFreeLineActiveCornerInvariant
        (figure18ScaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid))
    (translatedBoxes_pos :
      ∀ r : Nat, 0 < r →
        ∃ origin : Int × Int,
          Nonempty (TranslatedActiveCornerIndexedBox
            (scaffoldDataOfNatSites
              l2Component2BlankCandidateActiveSiteSpecs
              l2Component2BlankCandidateSanity.activeSiteSpecs_valid
              0 Quadrant.northeast
              l2Component2BlankCandidateSanity.cornerIndex_valid).scaffold
            r origin)) :
    NatSiteRobinsonCompatibleLevelObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofSection7BoardFreeLinePositiveTranslatedBoxes
    l2Component2BlankCandidateActiveSiteSpecs
    l2Component2BlankCandidateSanity.activeSiteSpecs_valid
    0 Quadrant.northeast
    l2Component2BlankCandidateSanity.cornerIndex_valid
    boardFreeLine translatedBoxes_pos
    (by
      simpa [l2Component2BlankCandidateActiveSiteData,
        l2Component2BlankCandidateCornerSite, NatSiteSpecSanity.activeSiteData,
        NatSiteSpecSanity.cornerSite] using
        l2Component2BlankCandidatePairCompatibilityBool)

/--
L2 component-2 specialization of the Section 7 board/free-line layer-patch
constructor.
-/
def ofL2Component2Section7BoardFreeLineLayerPatches
    (boardFreeLine :
      Figure18ScaffoldData.HasRobinsonSection7BoardFreeLineActiveCornerInvariant
        (figure18ScaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid))
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold) :
    NatSiteRobinsonCompatibleLevelObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofSection7BoardFreeLineLayerPatches
    l2Component2BlankCandidateActiveSiteSpecs
    l2Component2BlankCandidateSanity.activeSiteSpecs_valid
    0 Quadrant.northeast
    l2Component2BlankCandidateSanity.cornerIndex_valid
    boardFreeLine patches
    (by
      simpa [l2Component2BlankCandidateActiveSiteData,
        l2Component2BlankCandidateCornerSite, NatSiteSpecSanity.activeSiteData,
        NatSiteSpecSanity.cornerSite] using
        l2Component2BlankCandidatePairCompatibilityBool)

/--
Compatible-level L2 component-2 entry point using Robinson finite layer patches.
-/
def ofL2Component2BlankCandidateLayerPatches
    (levelCompatibleRoutedFreeGrids :
      HasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold) :
    NatSiteRobinsonCompatibleLevelObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofL2Component2BlankCandidatePatches levelCompatibleRoutedFreeGrids
    (activeCornerBoxPatches_of_layerBoxPatches patches)

/--
Compatible-level L2 component-1 entry point using fixed Robinson Section 7
obstruction geometry with Figure 18 routing and finite layer patches.
-/
def ofL2C1FixedGeometryTowerRoutingLayerPatches
    (fixedGeometryRouting :
      HasFigure18RobinsonBoardFixedGeometryTowerRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold) :
    NatSiteRobinsonCompatibleLevelObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofFixedGeometryTowerRoutingLayerPatches
    l2Component1BlankCandidateActiveSiteSpecs
    l2Component1BlankCandidateSanity.activeSiteSpecs_valid
    0 Quadrant.southwest
    l2Component1BlankCandidateSanity.cornerIndex_valid
    fixedGeometryRouting patches
    (by
      simpa [l2Component1BlankCandidateActiveSiteData,
        l2Component1BlankCandidateCornerSite, NatSiteSpecSanity.activeSiteData,
        NatSiteSpecSanity.cornerSite] using
        l2Component1BlankCandidatePairCompatibilityBool)

/--
Compatible-level L2 component-2 entry point using fixed Robinson Section 7
obstruction geometry with Figure 18 routing and finite layer patches.
-/
def ofL2C2FixedGeometryTowerRoutingLayerPatches
    (fixedGeometryRouting :
      HasFigure18RobinsonBoardFixedGeometryTowerRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold) :
    NatSiteRobinsonCompatibleLevelObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofFixedGeometryTowerRoutingLayerPatches
    l2Component2BlankCandidateActiveSiteSpecs
    l2Component2BlankCandidateSanity.activeSiteSpecs_valid
    0 Quadrant.northeast
    l2Component2BlankCandidateSanity.cornerIndex_valid
    fixedGeometryRouting patches
    (by
      simpa [l2Component2BlankCandidateActiveSiteData,
        l2Component2BlankCandidateCornerSite, NatSiteSpecSanity.activeSiteData,
        NatSiteSpecSanity.cornerSite] using
        l2Component2BlankCandidatePairCompatibilityBool)

/--
Compatible-level L2 component-1 entry point using product-witness fixed
Robinson Section 7 obstruction geometry with Figure 18 routing and finite
layer patches.
-/
def ofL2C1FixedGeometryProductRoutingLayerPatches
    (fixedGeometryRouting :
      HasFigure18RobinsonBoardFixedGeometryTowerProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold) :
    NatSiteRobinsonCompatibleLevelObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofFixedGeometryTowerProductWitnessRoutingLayerPatches
    l2Component1BlankCandidateActiveSiteSpecs
    l2Component1BlankCandidateSanity.activeSiteSpecs_valid
    0 Quadrant.southwest
    l2Component1BlankCandidateSanity.cornerIndex_valid
    fixedGeometryRouting patches
    (by
      simpa [l2Component1BlankCandidateActiveSiteData,
        l2Component1BlankCandidateCornerSite, NatSiteSpecSanity.activeSiteData,
        NatSiteSpecSanity.cornerSite] using
        l2Component1BlankCandidatePairCompatibilityBool)

/--
Compatible-level L2 component-2 entry point using product-witness fixed
Robinson Section 7 obstruction geometry with Figure 18 routing and finite
layer patches.
-/
def ofL2C2FixedGeometryProductRoutingLayerPatches
    (fixedGeometryRouting :
      HasFigure18RobinsonBoardFixedGeometryTowerProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold) :
    NatSiteRobinsonCompatibleLevelObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofFixedGeometryTowerProductWitnessRoutingLayerPatches
    l2Component2BlankCandidateActiveSiteSpecs
    l2Component2BlankCandidateSanity.activeSiteSpecs_valid
    0 Quadrant.northeast
    l2Component2BlankCandidateSanity.cornerIndex_valid
    fixedGeometryRouting patches
    (by
      simpa [l2Component2BlankCandidateActiveSiteData,
        l2Component2BlankCandidateCornerSite, NatSiteSpecSanity.activeSiteData,
        NatSiteSpecSanity.cornerSite] using
        l2Component2BlankCandidatePairCompatibilityBool)

/--
Compatible-level L2 component-1 entry point using product witnesses over the
canonical Robinson Section 7 obstruction geometry and finite layer patches.
-/
def ofL2C1CanonicalProductRoutingLayerPatches
    (canonicalRouting :
      HasFigure18RobinsonBoardCanonicalProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold) :
    NatSiteRobinsonCompatibleLevelObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofL2C1FixedGeometryProductRoutingLayerPatches
    (hasFigure18RobinsonBoardFixedGeometryTowerProductWitnessRoutingForTable_of_canonical
      canonicalRouting)
    patches

/--
Compatible-level L2 component-2 entry point using product witnesses over the
canonical Robinson Section 7 obstruction geometry and finite layer patches.
-/
def ofL2C2CanonicalProductRoutingLayerPatches
    (canonicalRouting :
      HasFigure18RobinsonBoardCanonicalProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold) :
    NatSiteRobinsonCompatibleLevelObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofL2C2FixedGeometryProductRoutingLayerPatches
    (hasFigure18RobinsonBoardFixedGeometryTowerProductWitnessRoutingForTable_of_canonical
      canonicalRouting)
    patches

def ofL2C1SignalLocalStepFreeGrids
    (signalLocalCoordinateSteps :
      HasFigure18RobinsonBoardLevelSignalLocalCoordinateStepsForTable
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
    NatSiteRobinsonCompatibleLevelObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofLocalSignalCoordinateSteps
    l2Component1BlankCandidateActiveSiteSpecs
    l2Component1BlankCandidateSanity.activeSiteSpecs_valid
    0 Quadrant.southwest
    l2Component1BlankCandidateSanity.cornerIndex_valid
    signalLocalCoordinateSteps realizes
    (by
      simpa [l2Component1BlankCandidateActiveSiteData,
        l2Component1BlankCandidateCornerSite, NatSiteSpecSanity.activeSiteData,
        NatSiteSpecSanity.cornerSite] using
        l2Component1BlankCandidatePairCompatibilityBool)

/--
Concrete L2 component-1 entry point using Robinson finite-box realization
instead of the already-compactified realization property.
-/
def ofL2C1SignalLocalStepFreeGridsBoxes
    (signalLocalCoordinateSteps :
      HasFigure18RobinsonBoardLevelSignalLocalCoordinateStepsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerBoxes
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold) :
    NatSiteRobinsonCompatibleLevelObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofLocalSignalCoordinateStepsBoxes
    l2Component1BlankCandidateActiveSiteSpecs
    l2Component1BlankCandidateSanity.activeSiteSpecs_valid
    0 Quadrant.southwest
    l2Component1BlankCandidateSanity.cornerIndex_valid
    signalLocalCoordinateSteps realizes
    (by
      simpa [l2Component1BlankCandidateActiveSiteData,
        l2Component1BlankCandidateCornerSite, NatSiteSpecSanity.activeSiteData,
        NatSiteSpecSanity.cornerSite] using
        l2Component1BlankCandidatePairCompatibilityBool)

/--
Concrete L2 component-1 entry point using Robinson finite box patches.
-/
def ofL2C1SignalLocalStepFreeGridsPatches
    (signalLocalCoordinateSteps :
      HasFigure18RobinsonBoardLevelSignalLocalCoordinateStepsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (patches :
      HasActiveCornerBoxPatches
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold) :
    NatSiteRobinsonCompatibleLevelObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofLocalSignalCoordinateStepsPatches
    l2Component1BlankCandidateActiveSiteSpecs
    l2Component1BlankCandidateSanity.activeSiteSpecs_valid
    0 Quadrant.southwest
    l2Component1BlankCandidateSanity.cornerIndex_valid
    signalLocalCoordinateSteps patches
    (by
      simpa [l2Component1BlankCandidateActiveSiteData,
        l2Component1BlankCandidateCornerSite, NatSiteSpecSanity.activeSiteData,
        NatSiteSpecSanity.cornerSite] using
        l2Component1BlankCandidatePairCompatibilityBool)

/--
Concrete L2 component-1 entry point using Robinson finite layer patches.
-/
def ofL2C1SignalLocalStepFreeGridsLayerPatches
    (signalLocalCoordinateSteps :
      HasFigure18RobinsonBoardLevelSignalLocalCoordinateStepsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold) :
    NatSiteRobinsonCompatibleLevelObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofLocalSignalCoordinateStepsLayerPatches
    l2Component1BlankCandidateActiveSiteSpecs
    l2Component1BlankCandidateSanity.activeSiteSpecs_valid
    0 Quadrant.southwest
    l2Component1BlankCandidateSanity.cornerIndex_valid
    signalLocalCoordinateSteps patches
    (by
      simpa [l2Component1BlankCandidateActiveSiteData,
        l2Component1BlankCandidateCornerSite, NatSiteSpecSanity.activeSiteData,
        NatSiteSpecSanity.cornerSite] using
        l2Component1BlankCandidatePairCompatibilityBool)

def ofL2C2SignalLocalStepFreeGrids
    (signalLocalCoordinateSteps :
      HasFigure18RobinsonBoardLevelSignalLocalCoordinateStepsForTable
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
    NatSiteRobinsonCompatibleLevelObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofLocalSignalCoordinateSteps
    l2Component2BlankCandidateActiveSiteSpecs
    l2Component2BlankCandidateSanity.activeSiteSpecs_valid
    0 Quadrant.northeast
    l2Component2BlankCandidateSanity.cornerIndex_valid
    signalLocalCoordinateSteps realizes
    (by
      simpa [l2Component2BlankCandidateActiveSiteData,
        l2Component2BlankCandidateCornerSite, NatSiteSpecSanity.activeSiteData,
        NatSiteSpecSanity.cornerSite] using
        l2Component2BlankCandidatePairCompatibilityBool)

/--
Concrete L2 component-2 entry point using Robinson finite-box realization
instead of the already-compactified realization property.
-/
def ofL2C2SignalLocalStepFreeGridsBoxes
    (signalLocalCoordinateSteps :
      HasFigure18RobinsonBoardLevelSignalLocalCoordinateStepsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (realizes :
      RealizesActiveCornerBoxes
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold) :
    NatSiteRobinsonCompatibleLevelObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofLocalSignalCoordinateStepsBoxes
    l2Component2BlankCandidateActiveSiteSpecs
    l2Component2BlankCandidateSanity.activeSiteSpecs_valid
    0 Quadrant.northeast
    l2Component2BlankCandidateSanity.cornerIndex_valid
    signalLocalCoordinateSteps realizes
    (by
      simpa [l2Component2BlankCandidateActiveSiteData,
        l2Component2BlankCandidateCornerSite, NatSiteSpecSanity.activeSiteData,
        NatSiteSpecSanity.cornerSite] using
        l2Component2BlankCandidatePairCompatibilityBool)

/--
Concrete L2 component-2 entry point using Robinson finite box patches.
-/
def ofL2C2SignalLocalStepFreeGridsPatches
    (signalLocalCoordinateSteps :
      HasFigure18RobinsonBoardLevelSignalLocalCoordinateStepsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (patches :
      HasActiveCornerBoxPatches
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold) :
    NatSiteRobinsonCompatibleLevelObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofLocalSignalCoordinateStepsPatches
    l2Component2BlankCandidateActiveSiteSpecs
    l2Component2BlankCandidateSanity.activeSiteSpecs_valid
    0 Quadrant.northeast
    l2Component2BlankCandidateSanity.cornerIndex_valid
    signalLocalCoordinateSteps patches
    (by
      simpa [l2Component2BlankCandidateActiveSiteData,
        l2Component2BlankCandidateCornerSite, NatSiteSpecSanity.activeSiteData,
        NatSiteSpecSanity.cornerSite] using
        l2Component2BlankCandidatePairCompatibilityBool)

/--
Concrete L2 component-2 entry point using Robinson finite layer patches.
-/
def ofL2C2SignalLocalStepFreeGridsLayerPatches
    (signalLocalCoordinateSteps :
      HasFigure18RobinsonBoardLevelSignalLocalCoordinateStepsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold) :
    NatSiteRobinsonCompatibleLevelObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofLocalSignalCoordinateStepsLayerPatches
    l2Component2BlankCandidateActiveSiteSpecs
    l2Component2BlankCandidateSanity.activeSiteSpecs_valid
    0 Quadrant.northeast
    l2Component2BlankCandidateSanity.cornerIndex_valid
    signalLocalCoordinateSteps patches
    (by
      simpa [l2Component2BlankCandidateActiveSiteData,
        l2Component2BlankCandidateCornerSite, NatSiteSpecSanity.activeSiteData,
        NatSiteSpecSanity.cornerSite] using
        l2Component2BlankCandidatePairCompatibilityBool)

end NatSiteRobinsonCompatibleLevelObligations

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

def ofLevelCompatibleFreeGrids
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (levelCompatibleRoutedFreeGrids :
      HasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
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
    sparseRawDataOfSites_hasRobinsonBoardRoutedFreeGridCheckedStacks_of_levelCompatible
      (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
      (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid)
      hcheck levelCompatibleRoutedFreeGrids
  realizes := realizes

def ofCompatibleLevelObligations
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (obligations :
      NatSiteRobinsonCompatibleLevelObligations activeSiteSpecs
        activeSiteSpecs_valid cornerIndex cornerQuadrant cornerIndex_valid) :
    NatSiteRobinsonScaffoldCertificate :=
  ofLevelCompatibleFreeGrids activeSiteSpecs activeSiteSpecs_valid
    cornerIndex cornerQuadrant cornerIndex_valid
    obligations.levelCompatibleRoutedFreeGrids obligations.pairCompatibility
    obligations.realizes

def ofLevelSignalLocallyCompatibleFreeGrids
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (signalCertificates :
      HasFigure18RobinsonBoardLevelSignalCertificatesForTable
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
  ofLevelLocallyCompatibleFreeGrids activeSiteSpecs activeSiteSpecs_valid
    cornerIndex cornerQuadrant cornerIndex_valid
    (hasFigure18RobinsonBoardLevelRoutedFreeGridsForTable_of_signalCertificates
      signalCertificates)
    hcheck hcompatible realizes

def ofLevelSignalLocalFreeGrids
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (signalLocalCertificates :
      HasFigure18RobinsonBoardLevelSignalLocalCertificatesForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold) :
    NatSiteRobinsonScaffoldCertificate :=
  ofLevelCompatibleFreeGrids activeSiteSpecs activeSiteSpecs_valid
    cornerIndex cornerQuadrant cornerIndex_valid
    (hasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable_of_localSignalCertificates
      signalLocalCertificates)
    hcheck realizes

def ofLevelSignalLocalCoordinateStepFreeGrids
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (signalLocalCoordinateSteps :
      HasFigure18RobinsonBoardLevelSignalLocalCoordinateStepsForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold) :
    NatSiteRobinsonScaffoldCertificate :=
  ofCompatibleLevelObligations activeSiteSpecs activeSiteSpecs_valid
    cornerIndex cornerQuadrant cornerIndex_valid
    (NatSiteRobinsonCompatibleLevelObligations.ofLocalSignalCoordinateSteps
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid signalLocalCoordinateSteps realizes hcheck)

def ofLevelSignalLocalTowerFreeGrids
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (signalLocalTower :
      HasFigure18RobinsonBoardLevelSignalLocalTowerForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold) :
    NatSiteRobinsonScaffoldCertificate :=
  ofCompatibleLevelObligations activeSiteSpecs activeSiteSpecs_valid
    cornerIndex cornerQuadrant cornerIndex_valid
    (NatSiteRobinsonCompatibleLevelObligations.ofLocalSignalTower
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid signalLocalTower realizes hcheck)

/--
Fixed-geometry-routing version of `ofLevelSignalLocalTowerFreeGrids`.
-/
def ofFixedGeometryTowerRoutingFreeGrids
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (fixedGeometryRouting :
      HasFigure18RobinsonBoardFixedGeometryTowerRoutingForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (realizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold) :
    NatSiteRobinsonScaffoldCertificate :=
  ofLevelSignalLocalTowerFreeGrids activeSiteSpecs activeSiteSpecs_valid
    cornerIndex cornerQuadrant cornerIndex_valid
    (hasFigure18RobinsonBoardLevelSignalLocalTowerForTable_of_fixedGeometryTowerRouting
      fixedGeometryRouting)
    hcheck realizes

def ofLevelSignalLocalTowerFreeGridsBoxes
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (signalLocalTower :
      HasFigure18RobinsonBoardLevelSignalLocalTowerForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (realizes :
      RealizesActiveCornerBoxes
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold) :
    NatSiteRobinsonScaffoldCertificate :=
  ofLevelSignalLocalTowerFreeGrids activeSiteSpecs activeSiteSpecs_valid
    cornerIndex cornerQuadrant cornerIndex_valid signalLocalTower hcheck
    (realizesActiveCornerSquares_of_realizesActiveCornerBoxes realizes)

/-- Fixed-geometry-routing version of `ofLevelSignalLocalTowerFreeGridsBoxes`. -/
def ofFixedGeometryTowerRoutingFreeGridsBoxes
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (fixedGeometryRouting :
      HasFigure18RobinsonBoardFixedGeometryTowerRoutingForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (realizes :
      RealizesActiveCornerBoxes
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold) :
    NatSiteRobinsonScaffoldCertificate :=
  ofFixedGeometryTowerRoutingFreeGrids activeSiteSpecs activeSiteSpecs_valid
    cornerIndex cornerQuadrant cornerIndex_valid fixedGeometryRouting hcheck
    (realizesActiveCornerSquares_of_realizesActiveCornerBoxes realizes)

def ofLevelSignalLocalTowerFreeGridsPatches
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (signalLocalTower :
      HasFigure18RobinsonBoardLevelSignalLocalTowerForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (patches :
      HasActiveCornerBoxPatches
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold) :
    NatSiteRobinsonScaffoldCertificate :=
  ofLevelSignalLocalTowerFreeGridsBoxes activeSiteSpecs activeSiteSpecs_valid
    cornerIndex cornerQuadrant cornerIndex_valid signalLocalTower hcheck
    (realizesActiveCornerBoxes_of_activeCornerBoxPatches patches)

/-- Fixed-geometry-routing version of `ofLevelSignalLocalTowerFreeGridsPatches`. -/
def ofFixedGeometryTowerRoutingFreeGridsPatches
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (fixedGeometryRouting :
      HasFigure18RobinsonBoardFixedGeometryTowerRoutingForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (patches :
      HasActiveCornerBoxPatches
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold) :
    NatSiteRobinsonScaffoldCertificate :=
  ofFixedGeometryTowerRoutingFreeGridsBoxes activeSiteSpecs
    activeSiteSpecs_valid cornerIndex cornerQuadrant cornerIndex_valid
    fixedGeometryRouting hcheck
    (realizesActiveCornerBoxes_of_activeCornerBoxPatches patches)

def ofLevelSignalLocalTowerFreeGridsLayerPatches
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (signalLocalTower :
      HasFigure18RobinsonBoardLevelSignalLocalTowerForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold) :
    NatSiteRobinsonScaffoldCertificate :=
  ofLevelSignalLocalTowerFreeGridsPatches activeSiteSpecs activeSiteSpecs_valid
    cornerIndex cornerQuadrant cornerIndex_valid signalLocalTower hcheck
    (activeCornerBoxPatches_of_layerBoxPatches patches)

/--
Fixed-geometry-routing version of
`ofLevelSignalLocalTowerFreeGridsLayerPatches`.
-/
def ofFixedGeometryTowerRoutingFreeGridsLayerPatches
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (fixedGeometryRouting :
      HasFigure18RobinsonBoardFixedGeometryTowerRoutingForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold) :
    NatSiteRobinsonScaffoldCertificate :=
  ofFixedGeometryTowerRoutingFreeGridsPatches activeSiteSpecs
    activeSiteSpecs_valid cornerIndex cornerQuadrant cornerIndex_valid
    fixedGeometryRouting hcheck
    (activeCornerBoxPatches_of_layerBoxPatches patches)

/--
Product-witness fixed-geometry-routing version of
`ofFixedGeometryTowerRoutingFreeGridsLayerPatches`.
-/
def ofFixedGeometryTowerProductWitnessRoutingFreeGridsLayerPatches
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (fixedGeometryRouting :
      HasFigure18RobinsonBoardFixedGeometryTowerProductWitnessRoutingForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold) :
    NatSiteRobinsonScaffoldCertificate :=
  ofFixedGeometryTowerRoutingFreeGridsLayerPatches activeSiteSpecs
    activeSiteSpecs_valid cornerIndex cornerQuadrant cornerIndex_valid
    (hasFigure18RobinsonBoardFixedGeometryTowerRoutingForTable_of_productWitnessRouting
      fixedGeometryRouting)
    hcheck patches

def ofLevelSignalLocalTowerFreeGridsIndexedBoxes
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (signalLocalTower :
      HasFigure18RobinsonBoardLevelSignalLocalTowerForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (hboxes :
      ∀ r : Nat, Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).scaffold r)) :
    NatSiteRobinsonScaffoldCertificate :=
  ofLevelSignalLocalTowerFreeGridsLayerPatches
    activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
    cornerIndex_valid signalLocalTower hcheck
    (activeCornerLayerBoxPatches_of_activeCornerIndexedBoxes hboxes)

/-- Fixed-geometry-routing version of `ofLevelSignalLocalTowerFreeGridsIndexedBoxes`. -/
def ofFixedGeometryTowerRoutingFreeGridsIndexedBoxes
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (fixedGeometryRouting :
      HasFigure18RobinsonBoardFixedGeometryTowerRoutingForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (hboxes :
      ∀ r : Nat, Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).scaffold r)) :
    NatSiteRobinsonScaffoldCertificate :=
  ofFixedGeometryTowerRoutingFreeGridsLayerPatches activeSiteSpecs
    activeSiteSpecs_valid cornerIndex cornerQuadrant cornerIndex_valid
    fixedGeometryRouting hcheck
    (activeCornerLayerBoxPatches_of_activeCornerIndexedBoxes hboxes)

def ofLevelSignalCoordinateStepLocallyCompatibleFreeGrids
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (signalCoordinateSteps :
      HasFigure18RobinsonBoardLevelSignalCoordinateStepsForTable
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
  ofLevelSignalLocallyCompatibleFreeGrids activeSiteSpecs
    activeSiteSpecs_valid cornerIndex cornerQuadrant cornerIndex_valid
    (hasFigure18RobinsonBoardLevelSignalCertificatesForTable_of_coordinateSteps
      signalCoordinateSteps)
    hcheck hcompatible realizes

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

def ofL2Component1BlankCandidateLevelSignalLocal
    (signalCertificates :
      HasFigure18RobinsonBoardLevelSignalCertificatesForTable
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
  ofLevelSignalLocallyCompatibleFreeGrids
    l2Component1BlankCandidateActiveSiteSpecs
    l2Component1BlankCandidateSanity.activeSiteSpecs_valid
    0 Quadrant.southwest
    l2Component1BlankCandidateSanity.cornerIndex_valid
    signalCertificates
    (by
      simpa [l2Component1BlankCandidateActiveSiteData,
        l2Component1BlankCandidateCornerSite, NatSiteSpecSanity.activeSiteData,
        NatSiteSpecSanity.cornerSite] using
        l2Component1BlankCandidatePairCompatibilityBool)
    levelLocalCompatibility realizes

def ofL2Component1BlankCandidateLevelSignalLocalFreeGrids
    (signalLocalCertificates :
      HasFigure18RobinsonBoardLevelSignalLocalCertificatesForTable
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
  ofLevelSignalLocalFreeGrids
    l2Component1BlankCandidateActiveSiteSpecs
    l2Component1BlankCandidateSanity.activeSiteSpecs_valid
    0 Quadrant.southwest
    l2Component1BlankCandidateSanity.cornerIndex_valid
    signalLocalCertificates
    (by
      simpa [l2Component1BlankCandidateActiveSiteData,
        l2Component1BlankCandidateCornerSite, NatSiteSpecSanity.activeSiteData,
        NatSiteSpecSanity.cornerSite] using
        l2Component1BlankCandidatePairCompatibilityBool)
    realizes

def ofL2C1SignalLocalStepFreeGrids
    (signalLocalCoordinateSteps :
      HasFigure18RobinsonBoardLevelSignalLocalCoordinateStepsForTable
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
  ofCompatibleLevelObligations
    l2Component1BlankCandidateActiveSiteSpecs
    l2Component1BlankCandidateSanity.activeSiteSpecs_valid
    0 Quadrant.southwest
    l2Component1BlankCandidateSanity.cornerIndex_valid
    (NatSiteRobinsonCompatibleLevelObligations.ofL2C1SignalLocalStepFreeGrids
      signalLocalCoordinateSteps realizes)

def ofL2C1SignalLocalTowerFreeGrids
    (signalLocalTower :
      HasFigure18RobinsonBoardLevelSignalLocalTowerForTable
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
  ofLevelSignalLocalTowerFreeGrids
    l2Component1BlankCandidateActiveSiteSpecs
    l2Component1BlankCandidateSanity.activeSiteSpecs_valid
    0 Quadrant.southwest
    l2Component1BlankCandidateSanity.cornerIndex_valid
    signalLocalTower
    (by
      simpa [l2Component1BlankCandidateActiveSiteData,
        l2Component1BlankCandidateCornerSite, NatSiteSpecSanity.activeSiteData,
        NatSiteSpecSanity.cornerSite] using
        l2Component1BlankCandidatePairCompatibilityBool)
    realizes

def ofL2C1SignalLocalTowerFreeGridsLayerPatches
    (signalLocalTower :
      HasFigure18RobinsonBoardLevelSignalLocalTowerForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold) :
    NatSiteRobinsonScaffoldCertificate :=
  ofLevelSignalLocalTowerFreeGridsLayerPatches
    l2Component1BlankCandidateActiveSiteSpecs
    l2Component1BlankCandidateSanity.activeSiteSpecs_valid
    0 Quadrant.southwest
    l2Component1BlankCandidateSanity.cornerIndex_valid
    signalLocalTower
    (by
      simpa [l2Component1BlankCandidateActiveSiteData,
        l2Component1BlankCandidateCornerSite, NatSiteSpecSanity.activeSiteData,
        NatSiteSpecSanity.cornerSite] using
        l2Component1BlankCandidatePairCompatibilityBool)
    patches

def ofL2C1SignalLocalTowerFreeGridsIndexedBoxes
    (signalLocalTower :
      HasFigure18RobinsonBoardLevelSignalLocalTowerForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hboxes :
      ∀ r : Nat, Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).scaffold r)) :
    NatSiteRobinsonScaffoldCertificate :=
  ofL2C1SignalLocalTowerFreeGridsLayerPatches signalLocalTower
    (activeCornerLayerBoxPatches_of_activeCornerIndexedBoxes hboxes)

def ofL2Component1BlankCandidateLevelSignalCoordinateStepLocal
    (signalCoordinateSteps :
      HasFigure18RobinsonBoardLevelSignalCoordinateStepsForTable
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
  ofLevelSignalCoordinateStepLocallyCompatibleFreeGrids
    l2Component1BlankCandidateActiveSiteSpecs
    l2Component1BlankCandidateSanity.activeSiteSpecs_valid
    0 Quadrant.southwest
    l2Component1BlankCandidateSanity.cornerIndex_valid
    signalCoordinateSteps
    (by
      simpa [l2Component1BlankCandidateActiveSiteData,
        l2Component1BlankCandidateCornerSite, NatSiteSpecSanity.activeSiteData,
        NatSiteSpecSanity.cornerSite] using
        l2Component1BlankCandidatePairCompatibilityBool)
    levelLocalCompatibility realizes

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

def ofL2Component2BlankCandidateLevelSignalLocal
    (signalCertificates :
      HasFigure18RobinsonBoardLevelSignalCertificatesForTable
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
  ofLevelSignalLocallyCompatibleFreeGrids
    l2Component2BlankCandidateActiveSiteSpecs
    l2Component2BlankCandidateSanity.activeSiteSpecs_valid
    0 Quadrant.northeast
    l2Component2BlankCandidateSanity.cornerIndex_valid
    signalCertificates
    (by
      simpa [l2Component2BlankCandidateActiveSiteData,
        l2Component2BlankCandidateCornerSite, NatSiteSpecSanity.activeSiteData,
        NatSiteSpecSanity.cornerSite] using
        l2Component2BlankCandidatePairCompatibilityBool)
    levelLocalCompatibility realizes

def ofL2Component2BlankCandidateLevelSignalLocalFreeGrids
    (signalLocalCertificates :
      HasFigure18RobinsonBoardLevelSignalLocalCertificatesForTable
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
  ofLevelSignalLocalFreeGrids
    l2Component2BlankCandidateActiveSiteSpecs
    l2Component2BlankCandidateSanity.activeSiteSpecs_valid
    0 Quadrant.northeast
    l2Component2BlankCandidateSanity.cornerIndex_valid
    signalLocalCertificates
    (by
      simpa [l2Component2BlankCandidateActiveSiteData,
        l2Component2BlankCandidateCornerSite, NatSiteSpecSanity.activeSiteData,
        NatSiteSpecSanity.cornerSite] using
        l2Component2BlankCandidatePairCompatibilityBool)
    realizes

def ofL2C2SignalLocalStepFreeGrids
    (signalLocalCoordinateSteps :
      HasFigure18RobinsonBoardLevelSignalLocalCoordinateStepsForTable
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
  ofCompatibleLevelObligations
    l2Component2BlankCandidateActiveSiteSpecs
    l2Component2BlankCandidateSanity.activeSiteSpecs_valid
    0 Quadrant.northeast
    l2Component2BlankCandidateSanity.cornerIndex_valid
    (NatSiteRobinsonCompatibleLevelObligations.ofL2C2SignalLocalStepFreeGrids
      signalLocalCoordinateSteps realizes)

def ofL2C2SignalLocalTowerFreeGrids
    (signalLocalTower :
      HasFigure18RobinsonBoardLevelSignalLocalTowerForTable
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
  ofLevelSignalLocalTowerFreeGrids
    l2Component2BlankCandidateActiveSiteSpecs
    l2Component2BlankCandidateSanity.activeSiteSpecs_valid
    0 Quadrant.northeast
    l2Component2BlankCandidateSanity.cornerIndex_valid
    signalLocalTower
    (by
      simpa [l2Component2BlankCandidateActiveSiteData,
        l2Component2BlankCandidateCornerSite, NatSiteSpecSanity.activeSiteData,
        NatSiteSpecSanity.cornerSite] using
        l2Component2BlankCandidatePairCompatibilityBool)
    realizes

def ofL2C2SignalLocalTowerFreeGridsLayerPatches
    (signalLocalTower :
      HasFigure18RobinsonBoardLevelSignalLocalTowerForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold) :
    NatSiteRobinsonScaffoldCertificate :=
  ofLevelSignalLocalTowerFreeGridsLayerPatches
    l2Component2BlankCandidateActiveSiteSpecs
    l2Component2BlankCandidateSanity.activeSiteSpecs_valid
    0 Quadrant.northeast
    l2Component2BlankCandidateSanity.cornerIndex_valid
    signalLocalTower
    (by
      simpa [l2Component2BlankCandidateActiveSiteData,
        l2Component2BlankCandidateCornerSite, NatSiteSpecSanity.activeSiteData,
        NatSiteSpecSanity.cornerSite] using
        l2Component2BlankCandidatePairCompatibilityBool)
    patches

/--
Concrete L2 component-1 entry point using fixed Robinson Section 7 obstruction
geometry with Figure 18 routing and finite layer patches.
-/
def ofL2C1FixedGeometryTowerRoutingFreeGridsLayerPatches
    (fixedGeometryRouting :
      HasFigure18RobinsonBoardFixedGeometryTowerRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold) :
    NatSiteRobinsonScaffoldCertificate :=
  ofCompatibleLevelObligations
    l2Component1BlankCandidateActiveSiteSpecs
    l2Component1BlankCandidateSanity.activeSiteSpecs_valid
    0 Quadrant.southwest
    l2Component1BlankCandidateSanity.cornerIndex_valid
    (NatSiteRobinsonCompatibleLevelObligations.ofL2C1FixedGeometryTowerRoutingLayerPatches
      fixedGeometryRouting patches)

/--
Concrete L2 component-2 entry point using fixed Robinson Section 7 obstruction
geometry with Figure 18 routing and finite layer patches.
-/
def ofL2C2FixedGeometryTowerRoutingFreeGridsLayerPatches
    (fixedGeometryRouting :
      HasFigure18RobinsonBoardFixedGeometryTowerRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold) :
    NatSiteRobinsonScaffoldCertificate :=
  ofCompatibleLevelObligations
    l2Component2BlankCandidateActiveSiteSpecs
    l2Component2BlankCandidateSanity.activeSiteSpecs_valid
    0 Quadrant.northeast
    l2Component2BlankCandidateSanity.cornerIndex_valid
    (NatSiteRobinsonCompatibleLevelObligations.ofL2C2FixedGeometryTowerRoutingLayerPatches
      fixedGeometryRouting patches)

/--
Concrete L2 component-1 entry point using product-witness fixed Robinson
Section 7 obstruction geometry with Figure 18 routing and finite layer patches.
-/
def ofL2C1FixedGeometryProductRoutingFreeGridsLayerPatches
    (fixedGeometryRouting :
      HasFigure18RobinsonBoardFixedGeometryTowerProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold) :
    NatSiteRobinsonScaffoldCertificate :=
  ofCompatibleLevelObligations
    l2Component1BlankCandidateActiveSiteSpecs
    l2Component1BlankCandidateSanity.activeSiteSpecs_valid
    0 Quadrant.southwest
    l2Component1BlankCandidateSanity.cornerIndex_valid
    (NatSiteRobinsonCompatibleLevelObligations.ofL2C1FixedGeometryProductRoutingLayerPatches
      fixedGeometryRouting patches)

/--
Concrete L2 component-2 entry point using product-witness fixed Robinson
Section 7 obstruction geometry with Figure 18 routing and finite layer patches.
-/
def ofL2C2FixedGeometryProductRoutingFreeGridsLayerPatches
    (fixedGeometryRouting :
      HasFigure18RobinsonBoardFixedGeometryTowerProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold) :
    NatSiteRobinsonScaffoldCertificate :=
  ofCompatibleLevelObligations
    l2Component2BlankCandidateActiveSiteSpecs
    l2Component2BlankCandidateSanity.activeSiteSpecs_valid
    0 Quadrant.northeast
    l2Component2BlankCandidateSanity.cornerIndex_valid
    (NatSiteRobinsonCompatibleLevelObligations.ofL2C2FixedGeometryProductRoutingLayerPatches
      fixedGeometryRouting patches)

/--
Concrete L2 component-1 entry point using product witnesses over the canonical
Robinson Section 7 obstruction geometry and finite layer patches.
-/
def ofL2C1CanonicalProductRoutingFreeGridsLayerPatches
    (canonicalRouting :
      HasFigure18RobinsonBoardCanonicalProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold) :
    NatSiteRobinsonScaffoldCertificate :=
  ofL2C1FixedGeometryProductRoutingFreeGridsLayerPatches
    (hasFigure18RobinsonBoardFixedGeometryTowerProductWitnessRoutingForTable_of_canonical
      canonicalRouting)
    patches

/--
Concrete L2 component-2 entry point using product witnesses over the canonical
Robinson Section 7 obstruction geometry and finite layer patches.
-/
def ofL2C2CanonicalProductRoutingFreeGridsLayerPatches
    (canonicalRouting :
      HasFigure18RobinsonBoardCanonicalProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold) :
    NatSiteRobinsonScaffoldCertificate :=
  ofL2C2FixedGeometryProductRoutingFreeGridsLayerPatches
    (hasFigure18RobinsonBoardFixedGeometryTowerProductWitnessRoutingForTable_of_canonical
      canonicalRouting)
    patches

/--
Concrete L2 component-1 entry point using canonical product witnesses and
positive-radius indexed boxes.  The radius-zero box is supplied by the
scaffold corner tile.
-/
def ofL2C1CanonicalProductRoutingFreeGridsPositiveBoxes
    (canonicalRouting :
      HasFigure18RobinsonBoardCanonicalProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hboxes_pos :
      ∀ r : Nat, 0 < r → Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).scaffold r)) :
    NatSiteRobinsonScaffoldCertificate :=
  ofL2C1CanonicalProductRoutingFreeGridsLayerPatches canonicalRouting
    (activeCornerLayerBoxPatches_of_positiveActiveCornerIndexedBoxes
      (by
        simpa [LayeredFigure18ScaffoldData.scaffold,
          LayeredFigure18ScaffoldData.presentation] using
          Figure18RoleTable.scaffold_corner_mem
            (scaffoldDataOfNatSites
              l2Component1BlankCandidateActiveSiteSpecs
              l2Component1BlankCandidateSanity.activeSiteSpecs_valid
              0 Quadrant.southwest
              l2Component1BlankCandidateSanity.cornerIndex_valid).table)
      hboxes_pos)

/--
Concrete L2 component-2 entry point using canonical product witnesses and
positive-radius indexed boxes.  The radius-zero box is supplied by the
scaffold corner tile.
-/
def ofL2C2CanonicalProductRoutingFreeGridsPositiveBoxes
    (canonicalRouting :
      HasFigure18RobinsonBoardCanonicalProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hboxes_pos :
      ∀ r : Nat, 0 < r → Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).scaffold r)) :
    NatSiteRobinsonScaffoldCertificate :=
  ofL2C2CanonicalProductRoutingFreeGridsLayerPatches canonicalRouting
    (activeCornerLayerBoxPatches_of_positiveActiveCornerIndexedBoxes
      (by
        simpa [LayeredFigure18ScaffoldData.scaffold,
          LayeredFigure18ScaffoldData.presentation] using
          Figure18RoleTable.scaffold_corner_mem
            (scaffoldDataOfNatSites
              l2Component2BlankCandidateActiveSiteSpecs
              l2Component2BlankCandidateSanity.activeSiteSpecs_valid
              0 Quadrant.northeast
              l2Component2BlankCandidateSanity.cornerIndex_valid).table)
      hboxes_pos)

/--
Concrete L2 component-1 entry point using canonical ordinary routing and
positive-radius indexed boxes.
-/
def ofL2C1CanonicalRoutingFreeGridsPositiveBoxes
    (canonicalRouting :
      HasFigure18RobinsonBoardCanonicalRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hboxes_pos :
      ∀ r : Nat, 0 < r → Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).scaffold r)) :
    NatSiteRobinsonScaffoldCertificate :=
  ofL2C1CanonicalProductRoutingFreeGridsPositiveBoxes
    (hasFigure18RobinsonBoardCanonicalProductWitnessRoutingForTable_of_routing
      canonicalRouting)
    hboxes_pos

/--
Concrete L2 component-2 entry point using canonical ordinary routing and
positive-radius indexed boxes.
-/
def ofL2C2CanonicalRoutingFreeGridsPositiveBoxes
    (canonicalRouting :
      HasFigure18RobinsonBoardCanonicalRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hboxes_pos :
      ∀ r : Nat, 0 < r → Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).scaffold r)) :
    NatSiteRobinsonScaffoldCertificate :=
  ofL2C2CanonicalProductRoutingFreeGridsPositiveBoxes
    (hasFigure18RobinsonBoardCanonicalProductWitnessRoutingForTable_of_routing
      canonicalRouting)
    hboxes_pos

/--
Concrete L2 component-1 entry point using product-witness fixed Robinson
Section 7 obstruction geometry with Figure 18 routing and active-corner
indexed boxes.
-/
def ofL2C1FixedGeometryProductRoutingFreeGridsIndexedBoxes
    (fixedGeometryRouting :
      HasFigure18RobinsonBoardFixedGeometryTowerProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hboxes :
      ∀ r : Nat, Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).scaffold r)) :
    NatSiteRobinsonScaffoldCertificate :=
  ofL2C1FixedGeometryProductRoutingFreeGridsLayerPatches fixedGeometryRouting
    (activeCornerLayerBoxPatches_of_activeCornerIndexedBoxes hboxes)

/--
Concrete L2 component-2 entry point using product-witness fixed Robinson
Section 7 obstruction geometry with Figure 18 routing and active-corner
indexed boxes.
-/
def ofL2C2FixedGeometryProductRoutingFreeGridsIndexedBoxes
    (fixedGeometryRouting :
      HasFigure18RobinsonBoardFixedGeometryTowerProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hboxes :
      ∀ r : Nat, Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).scaffold r)) :
    NatSiteRobinsonScaffoldCertificate :=
  ofL2C2FixedGeometryProductRoutingFreeGridsLayerPatches fixedGeometryRouting
    (activeCornerLayerBoxPatches_of_activeCornerIndexedBoxes hboxes)

def ofL2C2SignalLocalTowerFreeGridsIndexedBoxes
    (signalLocalTower :
      HasFigure18RobinsonBoardLevelSignalLocalTowerForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hboxes :
      ∀ r : Nat, Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).scaffold r)) :
    NatSiteRobinsonScaffoldCertificate :=
  ofL2C2SignalLocalTowerFreeGridsLayerPatches signalLocalTower
    (activeCornerLayerBoxPatches_of_activeCornerIndexedBoxes hboxes)

def ofL2Component2BlankCandidateLevelSignalCoordinateStepLocal
    (signalCoordinateSteps :
      HasFigure18RobinsonBoardLevelSignalCoordinateStepsForTable
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
  ofLevelSignalCoordinateStepLocallyCompatibleFreeGrids
    l2Component2BlankCandidateActiveSiteSpecs
    l2Component2BlankCandidateSanity.activeSiteSpecs_valid
    0 Quadrant.northeast
    l2Component2BlankCandidateSanity.cornerIndex_valid
    signalCoordinateSteps
    (by
      simpa [l2Component2BlankCandidateActiveSiteData,
        l2Component2BlankCandidateCornerSite, NatSiteSpecSanity.activeSiteData,
        NatSiteSpecSanity.cornerSite] using
        l2Component2BlankCandidatePairCompatibilityBool)
    levelLocalCompatibility realizes

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

namespace NatSiteRobinsonLayerPatchScaffoldCertificate

def scaffoldData (C : NatSiteRobinsonLayerPatchScaffoldCertificate) :
    LayeredFigure18ScaffoldData :=
  scaffoldDataOfNatSites C.activeSiteSpecs C.activeSiteSpecs_valid
    C.cornerIndex C.cornerQuadrant C.cornerIndex_valid

def figure18ScaffoldData (C : NatSiteRobinsonLayerPatchScaffoldCertificate) :
    Figure18ScaffoldData :=
  figure18ScaffoldDataOfNatSites C.activeSiteSpecs C.activeSiteSpecs_valid
    C.cornerIndex C.cornerQuadrant C.cornerIndex_valid

def toScaffoldCertificate (C : NatSiteRobinsonLayerPatchScaffoldCertificate) :
    NatSiteRobinsonScaffoldCertificate where
  activeSiteSpecs := C.activeSiteSpecs
  activeSiteSpecs_valid := C.activeSiteSpecs_valid
  cornerIndex := C.cornerIndex
  cornerQuadrant := C.cornerQuadrant
  cornerIndex_valid := C.cornerIndex_valid
  robinsonStacks := C.robinsonStacks
  realizes :=
    realizesActiveCornerSquares_of_realizesActiveCornerBoxes
      (realizesActiveCornerBoxes_of_activeCornerLayerBoxPatches C.patches)

def indexedRoutedCertificate
    (C : NatSiteRobinsonLayerPatchScaffoldCertificate) :
    C.scaffoldData.IndexedRoutedCertificate :=
  scaffoldDataOfNatSitesIndexedRoutedCertificateOfCheckedFreeGridStacksLayerPatches
    C.activeSiteSpecs C.activeSiteSpecs_valid
    C.cornerIndex C.cornerQuadrant C.cornerIndex_valid
    C.robinsonStacks C.patches

def indexedRoutedInstance (C : NatSiteRobinsonLayerPatchScaffoldCertificate) :
    Figure18IndexedRoutedInstance :=
  C.indexedRoutedCertificate.toFigure18IndexedRoutedInstance

def flexibleInstance (C : NatSiteRobinsonLayerPatchScaffoldCertificate) :
    Figure18FlexibleInstance :=
  C.indexedRoutedCertificate.toFigure18FlexibleInstance

theorem isScaffold (C : NatSiteRobinsonLayerPatchScaffoldCertificate) :
    IsScaffold C.scaffoldData.scaffold :=
  C.indexedRoutedCertificate.isScaffold

theorem indexedRoutedInstance_isScaffold
    (C : NatSiteRobinsonLayerPatchScaffoldCertificate) :
    IsScaffold C.indexedRoutedInstance.presentation.toScaffold :=
  C.indexedRoutedInstance.isScaffold

def ofLevelCompatibleFreeGridsLayerPatches
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (levelCompatibleRoutedFreeGrids :
      HasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold) :
    NatSiteRobinsonLayerPatchScaffoldCertificate where
  activeSiteSpecs := activeSiteSpecs
  activeSiteSpecs_valid := activeSiteSpecs_valid
  cornerIndex := cornerIndex
  cornerQuadrant := cornerQuadrant
  cornerIndex_valid := cornerIndex_valid
  robinsonStacks :=
    sparseRawDataOfSites_hasRobinsonBoardRoutedFreeGridCheckedStacks_of_levelCompatible
      (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
      (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid)
      hcheck levelCompatibleRoutedFreeGrids
  patches := patches

def ofLevelSignalLocalTowerFreeGridsLayerPatches
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (signalLocalTower :
      HasFigure18RobinsonBoardLevelSignalLocalTowerForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold) :
    NatSiteRobinsonLayerPatchScaffoldCertificate :=
  ofLevelCompatibleFreeGridsLayerPatches activeSiteSpecs activeSiteSpecs_valid
    cornerIndex cornerQuadrant cornerIndex_valid
    (hasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable_of_localTower
      signalLocalTower)
    hcheck patches

def ofSection7BoardFreeLineLayerPatches
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (boardFreeLine :
      Figure18ScaffoldData.HasRobinsonSection7BoardFreeLineActiveCornerInvariant
        (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid))
    (hcheck :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold) :
    NatSiteRobinsonLayerPatchScaffoldCertificate :=
  ofLevelSignalLocalTowerFreeGridsLayerPatches activeSiteSpecs
    activeSiteSpecs_valid cornerIndex cornerQuadrant cornerIndex_valid
    (Figure18ScaffoldData.HasRobinsonBoardLevelSignalLocalTowerInvariant.ofBoardFreeLineActiveCorner
      boardFreeLine)
    hcheck patches

def ofL2C1Section7BoardFreeLineLayerPatches
    (boardFreeLine :
      Figure18ScaffoldData.HasRobinsonSection7BoardFreeLineActiveCornerInvariant
        l2Component1Figure18ScaffoldData)
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold) :
    NatSiteRobinsonLayerPatchScaffoldCertificate :=
  ofSection7BoardFreeLineLayerPatches
    l2Component1BlankCandidateActiveSiteSpecs
    l2Component1BlankCandidateSanity.activeSiteSpecs_valid
    0 Quadrant.southwest
    l2Component1BlankCandidateSanity.cornerIndex_valid
    boardFreeLine
    (by
      simpa [l2Component1BlankCandidateActiveSiteData,
        l2Component1BlankCandidateCornerSite, NatSiteSpecSanity.activeSiteData,
        NatSiteSpecSanity.cornerSite] using
        l2Component1BlankCandidatePairCompatibilityBool)
    patches

def ofL2C2Section7BoardFreeLineLayerPatches
    (boardFreeLine :
      Figure18ScaffoldData.HasRobinsonSection7BoardFreeLineActiveCornerInvariant
        l2Component2Figure18ScaffoldData)
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold) :
    NatSiteRobinsonLayerPatchScaffoldCertificate :=
  ofSection7BoardFreeLineLayerPatches
    l2Component2BlankCandidateActiveSiteSpecs
    l2Component2BlankCandidateSanity.activeSiteSpecs_valid
    0 Quadrant.northeast
    l2Component2BlankCandidateSanity.cornerIndex_valid
    boardFreeLine
    (by
      simpa [l2Component2BlankCandidateActiveSiteData,
        l2Component2BlankCandidateCornerSite, NatSiteSpecSanity.activeSiteData,
        NatSiteSpecSanity.cornerSite] using
        l2Component2BlankCandidatePairCompatibilityBool)
    patches

end NatSiteRobinsonLayerPatchScaffoldCertificate

def HasNatSiteSignalLocalTower
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true) :
    Prop :=
  ∀ {T : TileSet} {seed : WangTile}
    (x : Int × Int → TileIn (combineWithScaffold
      (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant
        cornerIndex_valid).table.presentation.toScaffold T seed)),
    ValidPlaneTiling (combineWithScaffold
      (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant
        cornerIndex_valid).table.presentation.toScaffold T seed) x →
      Nonempty (Figure18RobinsonBoardSignalLocalTower
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table x)

/--
Origin-zero active/corner windows supply Robinson's field-based local signal
tower for the selected Nat-indexed Figure 18 scaffold.

This is the direct Section 7 bridge: obstruction signals identify the free
rows and columns, and the resulting local tower is the geometry used by the
signal-tower scaffold route.
-/
def hasNatSiteSignalLocalTowerOfOriginZeroWindows
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (originZeroWindows :
      HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table) :
    HasNatSiteSignalLocalTower activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid :=
  hasFigure18RobinsonBoardLevelSignalLocalTowerForTable_iff_tower.1
    (hasFigure18RobinsonBoardLevelSignalLocalTowerForTable_of_originZeroWindows
      originZeroWindows)

/--
Direct Robinson Section 7 scaffold target using a field-based local signal
tower and positive-radius translated boxes.

This is the pair-free surface for the routed proof path: the signal tower
extracts payload squares directly, and the translated boxes realize the
scaffold.  The generated pair-compatibility check is intentionally absent; it
belongs only to the older checked-stack route.
-/
structure NatSiteRobinsonSignalTowerDirectTranslatedBoxObligations
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true) : Prop where
  signalLocalTower :
    HasNatSiteSignalLocalTower activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid
  positiveTranslatedIndexedBoxes :
    ∀ r : Nat, 0 < r →
      ∃ origin : Int × Int,
        Nonempty (TranslatedActiveCornerIndexedBox
          (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
            cornerIndex cornerQuadrant cornerIndex_valid).scaffold r origin)

/-- First L2 candidate version of `hasNatSiteSignalLocalTowerOfOriginZeroWindows`. -/
def l2Component1SignalLocalTowerOfOriginZeroWindows
    (originZeroWindows :
      HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table) :
    HasNatSiteSignalLocalTower
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  hasNatSiteSignalLocalTowerOfOriginZeroWindows originZeroWindows

/-- Second L2 candidate version of `hasNatSiteSignalLocalTowerOfOriginZeroWindows`. -/
def l2Component2SignalLocalTowerOfOriginZeroWindows
    (originZeroWindows :
      HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table) :
    HasNatSiteSignalLocalTower
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  hasNatSiteSignalLocalTowerOfOriginZeroWindows originZeroWindows

/--
Robinson Section 7 scaffold target using a field-based local signal tower and
positive-radius boxes at translated origins.

This bundles the two geometric facts supplied by the board argument: nested
red boards give the coherent local obstruction-signal tower, and arbitrarily
large boards give translated active-corner indexed boxes.  The generated
pair-compatibility check is kept as a field so the target can be used for
non-audited site lists as well as the two L2 candidates.
-/
structure NatSiteRobinsonSignalTowerTranslatedPositiveBoxObligations
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true) : Prop where
  signalLocalTower :
    HasNatSiteSignalLocalTower activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid
  pairCompatibility :
    generatedStackAllowedSitePairCompatibilityBool
      (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
      (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
        true
  positiveTranslatedIndexedBoxes :
    ∀ r : Nat, 0 < r →
      ∃ origin : Int × Int,
        Nonempty (TranslatedActiveCornerIndexedBox
          (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
            cornerIndex cornerQuadrant cornerIndex_valid).scaffold r origin)

namespace NatSiteRobinsonTowerIndexedBoxObligations

def toIndexedBoxScaffoldCertificate
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (O : NatSiteRobinsonTowerIndexedBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid) :
    NatSiteRobinsonIndexedBoxScaffoldCertificate where
  activeSiteSpecs := activeSiteSpecs
  activeSiteSpecs_valid := activeSiteSpecs_valid
  cornerIndex := cornerIndex
  cornerQuadrant := cornerQuadrant
  cornerIndex_valid := cornerIndex_valid
  robinsonStacks :=
    sparseRawDataOfSites_hasRobinsonBoardRoutedFreeGridCheckedStacks_of_levelSignalLocalTower
      (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
      (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid)
      O.pairCompatibility O.signalLocalTower
  indexedBoxes := O.indexedBoxes

def toScaffoldCertificate
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (O : NatSiteRobinsonTowerIndexedBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid) :
    NatSiteRobinsonScaffoldCertificate :=
  O.toIndexedBoxScaffoldCertificate.toScaffoldCertificate

def ofPositiveBoxes
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (signalLocalTower :
      HasFigure18RobinsonBoardLevelSignalLocalTowerForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (pairCompatibility :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (indexedBoxes_pos :
      ∀ r : Nat, 0 < r → Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).scaffold r)) :
    NatSiteRobinsonTowerIndexedBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid where
  signalLocalTower := signalLocalTower
  pairCompatibility := pairCompatibility
  indexedBoxes :=
    ActiveCornerIndexedBox.nonempty_all_of_pos_and_corner_mem
      (by
        simpa [LayeredFigure18ScaffoldData.scaffold,
          LayeredFigure18ScaffoldData.presentation] using
          Figure18RoleTable.scaffold_corner_mem
            (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
              cornerIndex cornerQuadrant cornerIndex_valid).table)
      indexedBoxes_pos

def ofPositiveTranslatedBoxes
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (signalLocalTower :
      HasFigure18RobinsonBoardLevelSignalLocalTowerForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (pairCompatibility :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (translatedBoxes_pos :
      ∀ r : Nat, 0 < r →
        ∃ origin : Int × Int,
          Nonempty (TranslatedActiveCornerIndexedBox
            (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
              cornerIndex cornerQuadrant cornerIndex_valid).scaffold r origin)) :
    NatSiteRobinsonTowerIndexedBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid :=
  ofPositiveBoxes signalLocalTower pairCompatibility
    (TranslatedActiveCornerIndexedBox.nonempty_centered_pos_of_translated_pos
      translatedBoxes_pos)

def ofFigure18ScaffoldDataPositiveTranslatedBoxes
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (signalLocalTower :
      HasFigure18RobinsonBoardLevelSignalLocalTowerForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (pairCompatibility :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (translatedBoxes :
      Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant
        (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid)) :
    NatSiteRobinsonTowerIndexedBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid :=
  ofPositiveTranslatedBoxes signalLocalTower pairCompatibility
    (by
      intro r hr
      simpa [figure18ScaffoldDataOfNatSites, scaffoldDataOfNatSites,
        LayeredFigure18ScaffoldData.scaffold,
        LayeredFigure18ScaffoldData.presentation,
        LayeredFigure18ScaffoldData.table,
        LayeredFigure18ScaffoldData.flatTable,
        Figure18ScaffoldData.scaffold,
        Figure18ScaffoldData.presentation,
        Figure18ScaffoldData.table] using translatedBoxes r hr)

def ofSignalLocalTowerPositiveBoxes
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (signalLocalTower :
      HasNatSiteSignalLocalTower activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid)
    (pairCompatibility :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (indexedBoxes_pos :
      ∀ r : Nat, 0 < r → Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).scaffold r)) :
    NatSiteRobinsonTowerIndexedBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid :=
  ofPositiveBoxes
    (hasFigure18RobinsonBoardLevelSignalLocalTowerForTable_of_tower
      signalLocalTower)
    pairCompatibility
    indexedBoxes_pos

/--
Build the tower/indexed-box obligation package from Robinson's field-based
local signal tower and positive-radius translated boxes.

This is the shape closest to Robinson's Section 7 text: the obstruction
argument supplies a coherent tower of boards, while the red-board construction
finds arbitrarily large payload boxes at translated positions.
-/
def ofSignalLocalTowerFigure18ScaffoldDataPositiveTranslatedBoxes
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (signalLocalTower :
      HasNatSiteSignalLocalTower activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid)
    (pairCompatibility :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (translatedBoxes :
      Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant
        (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid)) :
    NatSiteRobinsonTowerIndexedBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid :=
  ofFigure18ScaffoldDataPositiveTranslatedBoxes
    (hasFigure18RobinsonBoardLevelSignalLocalTowerForTable_of_tower
      signalLocalTower)
    pairCompatibility
    translatedBoxes

/--
Build the tower/indexed-box obligation package from canonical Robinson-board
routing and positive-radius indexed boxes.
-/
def ofCanonicalRoutingPositiveBoxes
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (canonicalRouting :
      HasFigure18RobinsonBoardCanonicalRoutingForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (pairCompatibility :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (indexedBoxes_pos :
      ∀ r : Nat, 0 < r → Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).scaffold r)) :
    NatSiteRobinsonTowerIndexedBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid :=
  ofPositiveBoxes
    (hasFigure18RobinsonBoardLevelSignalLocalTowerForTable_of_canonicalRouting
      canonicalRouting)
    pairCompatibility
    indexedBoxes_pos

def ofCanonicalRoutingFigure18ScaffoldDataPositiveTranslatedBoxes
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (canonicalRouting :
      HasFigure18RobinsonBoardCanonicalRoutingForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (pairCompatibility :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (translatedBoxes :
      Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant
        (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid)) :
    NatSiteRobinsonTowerIndexedBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid :=
  ofFigure18ScaffoldDataPositiveTranslatedBoxes
    (hasFigure18RobinsonBoardLevelSignalLocalTowerForTable_of_canonicalRouting
      canonicalRouting)
    pairCompatibility
    translatedBoxes

def ofL2C1SignalLocalTowerPositiveBoxes
    (signalLocalTower :
      HasNatSiteSignalLocalTower
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid)
    (indexedBoxes_pos :
      ∀ r : Nat, 0 < r → Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).scaffold r)) :
    NatSiteRobinsonTowerIndexedBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofSignalLocalTowerPositiveBoxes signalLocalTower
    (by
      simpa [l2Component1BlankCandidateActiveSiteData,
        l2Component1BlankCandidateCornerSite, NatSiteSpecSanity.activeSiteData,
        NatSiteSpecSanity.cornerSite] using
        l2Component1BlankCandidatePairCompatibilityBool)
    indexedBoxes_pos

def ofL2C2SignalLocalTowerPositiveBoxes
    (signalLocalTower :
      HasNatSiteSignalLocalTower
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid)
    (indexedBoxes_pos :
      ∀ r : Nat, 0 < r → Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).scaffold r)) :
    NatSiteRobinsonTowerIndexedBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofSignalLocalTowerPositiveBoxes signalLocalTower
    (by
      simpa [l2Component2BlankCandidateActiveSiteData,
        l2Component2BlankCandidateCornerSite, NatSiteSpecSanity.activeSiteData,
        NatSiteSpecSanity.cornerSite] using
        l2Component2BlankCandidatePairCompatibilityBool)
    indexedBoxes_pos

def ofL2C1SignalLocalTowerFigure18ScaffoldDataPositiveTranslatedBoxes
    (signalLocalTower :
      HasNatSiteSignalLocalTower
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid)
    (translatedBoxes :
      Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant
        (figure18ScaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid)) :
    NatSiteRobinsonTowerIndexedBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofSignalLocalTowerFigure18ScaffoldDataPositiveTranslatedBoxes
    signalLocalTower
    (by
      simpa [l2Component1BlankCandidateActiveSiteData,
        l2Component1BlankCandidateCornerSite, NatSiteSpecSanity.activeSiteData,
        NatSiteSpecSanity.cornerSite] using
        l2Component1BlankCandidatePairCompatibilityBool)
    translatedBoxes

def ofL2C2SignalLocalTowerFigure18ScaffoldDataPositiveTranslatedBoxes
    (signalLocalTower :
      HasNatSiteSignalLocalTower
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid)
    (translatedBoxes :
      Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant
        (figure18ScaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid)) :
    NatSiteRobinsonTowerIndexedBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofSignalLocalTowerFigure18ScaffoldDataPositiveTranslatedBoxes
    signalLocalTower
    (by
      simpa [l2Component2BlankCandidateActiveSiteData,
        l2Component2BlankCandidateCornerSite, NatSiteSpecSanity.activeSiteData,
        NatSiteSpecSanity.cornerSite] using
        l2Component2BlankCandidatePairCompatibilityBool)
    translatedBoxes

/--
Build the first L2 tower/indexed-box obligations from the Robinson local signal
tower and a raw Figure 13 plane tiling.
-/
def ofL2C1SignalLocalTowerFig13TilesPlane
    (signalLocalTower :
      HasNatSiteSignalLocalTower
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hplane : TilesPlane fig13Tiles) :
    NatSiteRobinsonTowerIndexedBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofL2C1SignalLocalTowerFigure18ScaffoldDataPositiveTranslatedBoxes
    signalLocalTower
    (Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant.ofIsolatedActiveBoxes
      (l2Component1PositiveTranslatedIsolatedBoxesOfFig13TilesPlane hplane))

/--
Build the second L2 tower/indexed-box obligations from the Robinson local
signal tower and a raw Figure 13 plane tiling.
-/
def ofL2C2SignalLocalTowerFig13TilesPlane
    (signalLocalTower :
      HasNatSiteSignalLocalTower
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hplane : TilesPlane fig13Tiles) :
    NatSiteRobinsonTowerIndexedBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofL2C2SignalLocalTowerFigure18ScaffoldDataPositiveTranslatedBoxes
    signalLocalTower
    (Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant.ofIsolatedActiveBoxes
      (l2Component2PositiveTranslatedIsolatedBoxesOfFig13TilesPlane hplane))

def ofL2C1CanonicalRoutingPositiveBoxes
    (canonicalRouting :
      HasFigure18RobinsonBoardCanonicalRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (indexedBoxes_pos :
      ∀ r : Nat, 0 < r → Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).scaffold r)) :
    NatSiteRobinsonTowerIndexedBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofCanonicalRoutingPositiveBoxes canonicalRouting
    (by
      simpa [l2Component1BlankCandidateActiveSiteData,
        l2Component1BlankCandidateCornerSite, NatSiteSpecSanity.activeSiteData,
        NatSiteSpecSanity.cornerSite] using
        l2Component1BlankCandidatePairCompatibilityBool)
    indexedBoxes_pos

def ofL2C1CanonicalRoutingFigure18ScaffoldDataPositiveTranslatedBoxes
    (canonicalRouting :
      HasFigure18RobinsonBoardCanonicalRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (translatedBoxes :
      Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant
        (figure18ScaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid)) :
    NatSiteRobinsonTowerIndexedBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofCanonicalRoutingFigure18ScaffoldDataPositiveTranslatedBoxes canonicalRouting
    (by
      simpa [l2Component1BlankCandidateActiveSiteData,
        l2Component1BlankCandidateCornerSite, NatSiteSpecSanity.activeSiteData,
        NatSiteSpecSanity.cornerSite] using
        l2Component1BlankCandidatePairCompatibilityBool)
    translatedBoxes

def ofL2C2CanonicalRoutingPositiveBoxes
    (canonicalRouting :
      HasFigure18RobinsonBoardCanonicalRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (indexedBoxes_pos :
      ∀ r : Nat, 0 < r → Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).scaffold r)) :
    NatSiteRobinsonTowerIndexedBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofCanonicalRoutingPositiveBoxes canonicalRouting
    (by
      simpa [l2Component2BlankCandidateActiveSiteData,
        l2Component2BlankCandidateCornerSite, NatSiteSpecSanity.activeSiteData,
        NatSiteSpecSanity.cornerSite] using
        l2Component2BlankCandidatePairCompatibilityBool)
    indexedBoxes_pos

def ofL2C2CanonicalRoutingFigure18ScaffoldDataPositiveTranslatedBoxes
    (canonicalRouting :
      HasFigure18RobinsonBoardCanonicalRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (translatedBoxes :
      Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant
        (figure18ScaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid)) :
    NatSiteRobinsonTowerIndexedBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofCanonicalRoutingFigure18ScaffoldDataPositiveTranslatedBoxes canonicalRouting
    (by
      simpa [l2Component2BlankCandidateActiveSiteData,
        l2Component2BlankCandidateCornerSite, NatSiteSpecSanity.activeSiteData,
        NatSiteSpecSanity.cornerSite] using
        l2Component2BlankCandidatePairCompatibilityBool)
    translatedBoxes

def ofL2C1PositiveBoxes
    (signalLocalTower :
      HasFigure18RobinsonBoardLevelSignalLocalTowerForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (indexedBoxes_pos :
      ∀ r : Nat, 0 < r → Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).scaffold r)) :
    NatSiteRobinsonTowerIndexedBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofPositiveBoxes signalLocalTower
    (by
      simpa [l2Component1BlankCandidateActiveSiteData,
        l2Component1BlankCandidateCornerSite, NatSiteSpecSanity.activeSiteData,
        NatSiteSpecSanity.cornerSite] using
        l2Component1BlankCandidatePairCompatibilityBool)
    indexedBoxes_pos

def ofL2C2PositiveBoxes
    (signalLocalTower :
      HasFigure18RobinsonBoardLevelSignalLocalTowerForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (indexedBoxes_pos :
      ∀ r : Nat, 0 < r → Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).scaffold r)) :
    NatSiteRobinsonTowerIndexedBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofPositiveBoxes signalLocalTower
    (by
      simpa [l2Component2BlankCandidateActiveSiteData,
        l2Component2BlankCandidateCornerSite, NatSiteSpecSanity.activeSiteData,
        NatSiteSpecSanity.cornerSite] using
        l2Component2BlankCandidatePairCompatibilityBool)
    indexedBoxes_pos

def ofL2C1
    (signalLocalTower :
      HasFigure18RobinsonBoardLevelSignalLocalTowerForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (indexedBoxes :
      ∀ r : Nat, Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).scaffold r)) :
    NatSiteRobinsonTowerIndexedBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid where
  signalLocalTower := signalLocalTower
  pairCompatibility := by
    simpa [l2Component1BlankCandidateActiveSiteData,
      l2Component1BlankCandidateCornerSite, NatSiteSpecSanity.activeSiteData,
      NatSiteSpecSanity.cornerSite] using
      l2Component1BlankCandidatePairCompatibilityBool
  indexedBoxes := indexedBoxes

def ofL2C2
    (signalLocalTower :
      HasFigure18RobinsonBoardLevelSignalLocalTowerForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (indexedBoxes :
      ∀ r : Nat, Nonempty (ActiveCornerIndexedBox
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).scaffold r)) :
    NatSiteRobinsonTowerIndexedBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid where
  signalLocalTower := signalLocalTower
  pairCompatibility := by
    simpa [l2Component2BlankCandidateActiveSiteData,
      l2Component2BlankCandidateCornerSite, NatSiteSpecSanity.activeSiteData,
      NatSiteSpecSanity.cornerSite] using
      l2Component2BlankCandidatePairCompatibilityBool
  indexedBoxes := indexedBoxes

end NatSiteRobinsonTowerIndexedBoxObligations

/--
Direct routed Figure 18 certificate from Robinson's field-based local signal
tower and positive-radius translated active-corner boxes.

This is the direct version of the Section 7 scaffold route currently used by
the proof surface: the signal tower gives routed free grids of every requested
payload size, and the positive translated boxes supply the realization half of
the scaffold certificate.
-/
def natSiteFigure18RoutedCertificateOfSignalLocalTowerPositiveTranslatedBoxes
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (signalLocalTower :
      HasNatSiteSignalLocalTower activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid)
    (translatedBoxes :
      Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant
        (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid)) :
    Figure18RoutedCertificate
      (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).table where
  routedForces :=
    hasFigure18RoutedFixedCornerSquares_of_robinsonBoardSignalLocalTower
      (hasFigure18RobinsonBoardLevelSignalLocalTowerForTable_of_tower
        signalLocalTower)
  realizes := by
    have hrealizes :
        Figure18ScaffoldData.HasRealizationInvariant
          (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
            cornerIndex cornerQuadrant cornerIndex_valid) :=
      Figure18ScaffoldData.HasRealizationInvariant.ofPositiveTranslatedActiveCornerIndexedBoxes
        translatedBoxes
    simpa [Figure18ScaffoldData.HasRealizationInvariant,
      figure18ScaffoldDataOfNatSites, scaffoldDataOfNatSites,
      LayeredFigure18ScaffoldData.scaffold,
      LayeredFigure18ScaffoldData.presentation,
      LayeredFigure18ScaffoldData.table,
      LayeredFigure18ScaffoldData.flatTable,
      Figure18ScaffoldData.scaffold,
      Figure18ScaffoldData.presentation,
      Figure18ScaffoldData.table] using hrealizes

namespace NatSiteRobinsonSignalTowerDirectTranslatedBoxObligations

def toFigure18RoutedCertificate
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (O : NatSiteRobinsonSignalTowerDirectTranslatedBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid) :
    Figure18RoutedCertificate
      (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).table :=
  natSiteFigure18RoutedCertificateOfSignalLocalTowerPositiveTranslatedBoxes
    O.signalLocalTower
    (by
      intro r hr
      simpa [figure18ScaffoldDataOfNatSites, scaffoldDataOfNatSites,
        LayeredFigure18ScaffoldData.scaffold,
        LayeredFigure18ScaffoldData.presentation,
        LayeredFigure18ScaffoldData.table,
        LayeredFigure18ScaffoldData.flatTable,
        Figure18ScaffoldData.scaffold,
        Figure18ScaffoldData.presentation,
        Figure18ScaffoldData.table] using
        O.positiveTranslatedIndexedBoxes r hr)

def ofFigure18ScaffoldDataPositiveTranslatedBoxes
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (signalLocalTower :
      HasNatSiteSignalLocalTower activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid)
    (translatedBoxes :
      Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant
        (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid)) :
    NatSiteRobinsonSignalTowerDirectTranslatedBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid where
  signalLocalTower := signalLocalTower
  positiveTranslatedIndexedBoxes := by
    intro r hr
    simpa [figure18ScaffoldDataOfNatSites, scaffoldDataOfNatSites,
      LayeredFigure18ScaffoldData.scaffold,
      LayeredFigure18ScaffoldData.presentation,
      LayeredFigure18ScaffoldData.table,
      LayeredFigure18ScaffoldData.flatTable,
      Figure18ScaffoldData.scaffold,
      Figure18ScaffoldData.presentation,
      Figure18ScaffoldData.table] using translatedBoxes r hr

def ofFigure18ScaffoldDataPositiveTranslatedIsolatedBoxes
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (signalLocalTower :
      HasNatSiteSignalLocalTower activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid)
    (isolatedBoxes :
      Figure18ScaffoldData.HasPositiveTranslatedIsolatedActiveBoxInvariant
        (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid)) :
    NatSiteRobinsonSignalTowerDirectTranslatedBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid :=
  ofFigure18ScaffoldDataPositiveTranslatedBoxes signalLocalTower
    (Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant.ofIsolatedActiveBoxes
      isolatedBoxes)

def ofL2C1Figure18ScaffoldDataPositiveTranslatedBoxes
    (signalLocalTower :
      HasNatSiteSignalLocalTower
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid)
    (translatedBoxes :
      Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant
        (figure18ScaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid)) :
    NatSiteRobinsonSignalTowerDirectTranslatedBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofFigure18ScaffoldDataPositiveTranslatedBoxes signalLocalTower translatedBoxes

def ofL2C2Figure18ScaffoldDataPositiveTranslatedBoxes
    (signalLocalTower :
      HasNatSiteSignalLocalTower
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid)
    (translatedBoxes :
      Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant
        (figure18ScaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid)) :
    NatSiteRobinsonSignalTowerDirectTranslatedBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofFigure18ScaffoldDataPositiveTranslatedBoxes signalLocalTower translatedBoxes

def ofL2C1Fig13TilesPlane
    (signalLocalTower :
      HasNatSiteSignalLocalTower
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hplane : TilesPlane fig13Tiles) :
    NatSiteRobinsonSignalTowerDirectTranslatedBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofL2C1Figure18ScaffoldDataPositiveTranslatedBoxes signalLocalTower
    (Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant.ofIsolatedActiveBoxes
      (l2Component1PositiveTranslatedIsolatedBoxesOfFig13TilesPlane hplane))

def ofL2C2Fig13TilesPlane
    (signalLocalTower :
      HasNatSiteSignalLocalTower
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hplane : TilesPlane fig13Tiles) :
    NatSiteRobinsonSignalTowerDirectTranslatedBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofL2C2Figure18ScaffoldDataPositiveTranslatedBoxes signalLocalTower
    (Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant.ofIsolatedActiveBoxes
      (l2Component2PositiveTranslatedIsolatedBoxesOfFig13TilesPlane hplane))

end NatSiteRobinsonSignalTowerDirectTranslatedBoxObligations

namespace NatSiteRobinsonSignalTowerTranslatedPositiveBoxObligations

def toDirectTranslatedBoxObligations
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (O : NatSiteRobinsonSignalTowerTranslatedPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid) :
    NatSiteRobinsonSignalTowerDirectTranslatedBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid where
  signalLocalTower := O.signalLocalTower
  positiveTranslatedIndexedBoxes := O.positiveTranslatedIndexedBoxes

def toTowerIndexedBoxObligations
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (O : NatSiteRobinsonSignalTowerTranslatedPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid) :
    NatSiteRobinsonTowerIndexedBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid :=
  NatSiteRobinsonTowerIndexedBoxObligations.ofPositiveTranslatedBoxes
    (hasFigure18RobinsonBoardLevelSignalLocalTowerForTable_of_tower
      O.signalLocalTower)
    O.pairCompatibility
    O.positiveTranslatedIndexedBoxes

def toCompatibleLevelObligations
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (O : NatSiteRobinsonSignalTowerTranslatedPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid) :
    NatSiteRobinsonCompatibleLevelObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid :=
  NatSiteRobinsonCompatibleLevelObligations.ofLevelCompatiblePositiveTranslatedBoxes
    activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
    cornerIndex_valid
    (hasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable_of_localTower
      (hasFigure18RobinsonBoardLevelSignalLocalTowerForTable_of_tower
        O.signalLocalTower))
    O.positiveTranslatedIndexedBoxes
    O.pairCompatibility

def toL2C1CompatibleLevelObligations
    (O : NatSiteRobinsonSignalTowerTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid) :
    NatSiteRobinsonCompatibleLevelObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  O.toCompatibleLevelObligations

def toL2C2CompatibleLevelObligations
    (O : NatSiteRobinsonSignalTowerTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid) :
    NatSiteRobinsonCompatibleLevelObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  O.toCompatibleLevelObligations

def toFigure18RoutedCertificate
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (O : NatSiteRobinsonSignalTowerTranslatedPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid) :
    Figure18RoutedCertificate
      (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).table :=
  natSiteFigure18RoutedCertificateOfSignalLocalTowerPositiveTranslatedBoxes
    O.signalLocalTower
    (by
      intro r hr
      simpa [figure18ScaffoldDataOfNatSites, scaffoldDataOfNatSites,
        LayeredFigure18ScaffoldData.scaffold,
        LayeredFigure18ScaffoldData.presentation,
        LayeredFigure18ScaffoldData.table,
        LayeredFigure18ScaffoldData.flatTable,
        Figure18ScaffoldData.scaffold,
        Figure18ScaffoldData.presentation,
        Figure18ScaffoldData.table] using
        O.positiveTranslatedIndexedBoxes r hr)

def ofFigure18ScaffoldDataPositiveTranslatedBoxes
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (signalLocalTower :
      HasNatSiteSignalLocalTower activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid)
    (pairCompatibility :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (translatedBoxes :
      Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant
        (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid)) :
    NatSiteRobinsonSignalTowerTranslatedPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid where
  signalLocalTower := signalLocalTower
  pairCompatibility := pairCompatibility
  positiveTranslatedIndexedBoxes := by
    intro r hr
    simpa [figure18ScaffoldDataOfNatSites, scaffoldDataOfNatSites,
      LayeredFigure18ScaffoldData.scaffold,
      LayeredFigure18ScaffoldData.presentation,
      LayeredFigure18ScaffoldData.table,
      LayeredFigure18ScaffoldData.flatTable,
      Figure18ScaffoldData.scaffold,
      Figure18ScaffoldData.presentation,
      Figure18ScaffoldData.table] using translatedBoxes r hr

def ofFigure18ScaffoldDataPositiveTranslatedIsolatedBoxes
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (signalLocalTower :
      HasNatSiteSignalLocalTower activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid)
    (pairCompatibility :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (isolatedBoxes :
      Figure18ScaffoldData.HasPositiveTranslatedIsolatedActiveBoxInvariant
        (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid)) :
    NatSiteRobinsonSignalTowerTranslatedPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid :=
  ofFigure18ScaffoldDataPositiveTranslatedBoxes signalLocalTower
    pairCompatibility
    (Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant.ofIsolatedActiveBoxes
      isolatedBoxes)

def ofL2C1Figure18ScaffoldDataPositiveTranslatedBoxes
    (signalLocalTower :
      HasNatSiteSignalLocalTower
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid)
    (translatedBoxes :
      Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant
        (figure18ScaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid)) :
    NatSiteRobinsonSignalTowerTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofFigure18ScaffoldDataPositiveTranslatedBoxes signalLocalTower
    (by
      simpa [l2Component1BlankCandidateActiveSiteData,
        l2Component1BlankCandidateCornerSite, NatSiteSpecSanity.activeSiteData,
        NatSiteSpecSanity.cornerSite] using
        l2Component1BlankCandidatePairCompatibilityBool)
    translatedBoxes

def ofL2C2Figure18ScaffoldDataPositiveTranslatedBoxes
    (signalLocalTower :
      HasNatSiteSignalLocalTower
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid)
    (translatedBoxes :
      Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant
        (figure18ScaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid)) :
    NatSiteRobinsonSignalTowerTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofFigure18ScaffoldDataPositiveTranslatedBoxes signalLocalTower
    (by
      simpa [l2Component2BlankCandidateActiveSiteData,
        l2Component2BlankCandidateCornerSite, NatSiteSpecSanity.activeSiteData,
        NatSiteSpecSanity.cornerSite] using
        l2Component2BlankCandidatePairCompatibilityBool)
    translatedBoxes

def ofL2C1Fig13TilesPlane
    (signalLocalTower :
      HasNatSiteSignalLocalTower
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hplane : TilesPlane fig13Tiles) :
    NatSiteRobinsonSignalTowerTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofL2C1Figure18ScaffoldDataPositiveTranslatedBoxes signalLocalTower
    (Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant.ofIsolatedActiveBoxes
      (l2Component1PositiveTranslatedIsolatedBoxesOfFig13TilesPlane hplane))

def ofL2C2Fig13TilesPlane
    (signalLocalTower :
      HasNatSiteSignalLocalTower
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hplane : TilesPlane fig13Tiles) :
    NatSiteRobinsonSignalTowerTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofL2C2Figure18ScaffoldDataPositiveTranslatedBoxes signalLocalTower
    (Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant.ofIsolatedActiveBoxes
      (l2Component2PositiveTranslatedIsolatedBoxesOfFig13TilesPlane hplane))

def ofL2C1OriginZeroFigure18ScaffoldDataPositiveTranslatedBoxes
    (originZeroWindows :
      HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (translatedBoxes :
      Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant
        (figure18ScaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid)) :
    NatSiteRobinsonSignalTowerTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofL2C1Figure18ScaffoldDataPositiveTranslatedBoxes
    (l2Component1SignalLocalTowerOfOriginZeroWindows originZeroWindows)
    translatedBoxes

def ofL2C2OriginZeroFigure18ScaffoldDataPositiveTranslatedBoxes
    (originZeroWindows :
      HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (translatedBoxes :
      Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant
        (figure18ScaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid)) :
    NatSiteRobinsonSignalTowerTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofL2C2Figure18ScaffoldDataPositiveTranslatedBoxes
    (l2Component2SignalLocalTowerOfOriginZeroWindows originZeroWindows)
    translatedBoxes

def ofL2C1OriginZeroFig13TilesPlane
    (originZeroWindows :
      HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles) :
    NatSiteRobinsonSignalTowerTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofL2C1OriginZeroFigure18ScaffoldDataPositiveTranslatedBoxes
    originZeroWindows
    (Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant.ofIsolatedActiveBoxes
      (l2Component1PositiveTranslatedIsolatedBoxesOfFig13TilesPlane hplane))

def ofL2C2OriginZeroFig13TilesPlane
    (originZeroWindows :
      HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles) :
    NatSiteRobinsonSignalTowerTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofL2C2OriginZeroFigure18ScaffoldDataPositiveTranslatedBoxes
    originZeroWindows
    (Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant.ofIsolatedActiveBoxes
      (l2Component2PositiveTranslatedIsolatedBoxesOfFig13TilesPlane hplane))

def ofL2C1OriginZeroFig13TileableBoxes
    (originZeroWindows :
      HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hboxes : ∀ r : Nat, TileableBox fig13Tiles r) :
    NatSiteRobinsonSignalTowerTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofL2C1OriginZeroFigure18ScaffoldDataPositiveTranslatedBoxes
    originZeroWindows
    (Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant.ofIsolatedActiveBoxes
      (l2Component1PositiveTranslatedIsolatedBoxesOfFig13TileableBoxes hboxes))

def ofL2C2OriginZeroFig13TileableBoxes
    (originZeroWindows :
      HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hboxes : ∀ r : Nat, TileableBox fig13Tiles r) :
    NatSiteRobinsonSignalTowerTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofL2C2OriginZeroFigure18ScaffoldDataPositiveTranslatedBoxes
    originZeroWindows
    (Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant.ofIsolatedActiveBoxes
      (l2Component2PositiveTranslatedIsolatedBoxesOfFig13TileableBoxes hboxes))

end NatSiteRobinsonSignalTowerTranslatedPositiveBoxObligations

namespace NatSiteRobinsonCanonicalPositiveBoxObligations

def toTowerIndexedBoxObligations
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (O : NatSiteRobinsonCanonicalPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid)
    (pairCompatibility :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true) :
    NatSiteRobinsonTowerIndexedBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid :=
  NatSiteRobinsonTowerIndexedBoxObligations.ofCanonicalRoutingPositiveBoxes
    O.canonicalRouting pairCompatibility O.positiveIndexedBoxes

def toL2C1TowerIndexedBoxObligations
    (O : NatSiteRobinsonCanonicalPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid) :
    NatSiteRobinsonTowerIndexedBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  O.toTowerIndexedBoxObligations
    (by
      simpa [l2Component1BlankCandidateActiveSiteData,
        l2Component1BlankCandidateCornerSite, NatSiteSpecSanity.activeSiteData,
        NatSiteSpecSanity.cornerSite] using
        l2Component1BlankCandidatePairCompatibilityBool)

def toL2C2TowerIndexedBoxObligations
    (O : NatSiteRobinsonCanonicalPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid) :
    NatSiteRobinsonTowerIndexedBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  O.toTowerIndexedBoxObligations
    (by
      simpa [l2Component2BlankCandidateActiveSiteData,
        l2Component2BlankCandidateCornerSite, NatSiteSpecSanity.activeSiteData,
        NatSiteSpecSanity.cornerSite] using
        l2Component2BlankCandidatePairCompatibilityBool)

end NatSiteRobinsonCanonicalPositiveBoxObligations

namespace NatSiteRobinsonCanonicalTranslatedPositiveBoxObligations

def ofFigure18ScaffoldDataPositiveTranslatedBoxes
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (canonicalRouting :
      HasFigure18RobinsonBoardCanonicalRoutingForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (translatedBoxes :
      Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant
        (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid)) :
    NatSiteRobinsonCanonicalTranslatedPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid where
  canonicalRouting := canonicalRouting
  positiveTranslatedIndexedBoxes := by
    intro r hr
    simpa [figure18ScaffoldDataOfNatSites, scaffoldDataOfNatSites,
      LayeredFigure18ScaffoldData.scaffold,
      LayeredFigure18ScaffoldData.presentation,
      LayeredFigure18ScaffoldData.table,
      LayeredFigure18ScaffoldData.flatTable,
      Figure18ScaffoldData.scaffold,
      Figure18ScaffoldData.presentation,
      Figure18ScaffoldData.table] using translatedBoxes r hr

def ofFigure18ScaffoldDataPositiveTranslatedIsolatedBoxes
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (canonicalRouting :
      HasFigure18RobinsonBoardCanonicalRoutingForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (isolatedBoxes :
      Figure18ScaffoldData.HasPositiveTranslatedIsolatedActiveBoxInvariant
        (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid)) :
    NatSiteRobinsonCanonicalTranslatedPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid :=
  ofFigure18ScaffoldDataPositiveTranslatedBoxes canonicalRouting
    (Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant.ofIsolatedActiveBoxes
      isolatedBoxes)

def ofL2C1Figure18ScaffoldDataPositiveTranslatedBoxes
    (canonicalRouting :
      HasFigure18RobinsonBoardCanonicalRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (translatedBoxes :
      Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant
        (figure18ScaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid)) :
    NatSiteRobinsonCanonicalTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofFigure18ScaffoldDataPositiveTranslatedBoxes canonicalRouting translatedBoxes

def ofL2C1Figure18ScaffoldDataPositiveTranslatedIsolatedBoxes
    (canonicalRouting :
      HasFigure18RobinsonBoardCanonicalRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (isolatedBoxes :
      Figure18ScaffoldData.HasPositiveTranslatedIsolatedActiveBoxInvariant
        (figure18ScaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid)) :
    NatSiteRobinsonCanonicalTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofFigure18ScaffoldDataPositiveTranslatedIsolatedBoxes
    canonicalRouting isolatedBoxes

def ofL2C1Figure18ScaffoldDataPositiveTranslatedValidBoxes
    (canonicalRouting :
      HasFigure18RobinsonBoardCanonicalRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (validBoxes :
      ∀ r : Nat, 0 < r →
        ∃ origin : Int × Int,
          ∃ base : TranslatedBoxPattern
            l2Component1Figure18ScaffoldData.scaffold.tiles r origin,
            ValidTranslatedBoxTiling
              l2Component1Figure18ScaffoldData.scaffold.tiles r origin base) :
    NatSiteRobinsonCanonicalTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofL2C1Figure18ScaffoldDataPositiveTranslatedIsolatedBoxes
    canonicalRouting
    (by
      simpa [l2Component1Figure18ScaffoldData] using
        l2Component1PositiveTranslatedIsolatedBoxesOfValidBoxes validBoxes)

def ofL2C1Figure18ScaffoldDataPositiveTileableBoxes
    (canonicalRouting :
      HasFigure18RobinsonBoardCanonicalRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (tileableBoxes :
      ∀ r : Nat, 0 < r →
        TileableBox l2Component1Figure18ScaffoldData.scaffold.tiles r) :
    NatSiteRobinsonCanonicalTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofL2C1Figure18ScaffoldDataPositiveTranslatedValidBoxes canonicalRouting
    (positiveTranslatedValidBoxes_of_tileableBoxes tileableBoxes)

def ofL2C1Figure18ScaffoldDataPositiveFigure18ScaffoldTileableBoxes
    (canonicalRouting :
      HasFigure18RobinsonBoardCanonicalRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (tileableBoxes :
      ∀ r : Nat, 0 < r → TileableBox figure18ScaffoldTiles r) :
    NatSiteRobinsonCanonicalTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofL2C1Figure18ScaffoldDataPositiveTranslatedIsolatedBoxes
    canonicalRouting
    (by
      simpa [l2Component1Figure18ScaffoldData] using
        l2Component1PositiveTranslatedIsolatedBoxesOfFigure18ScaffoldTileableBoxes
          tileableBoxes)

def ofL2C1Figure18ScaffoldDataPositiveCompatibleSquares
    (canonicalRouting :
      HasFigure18RobinsonBoardCanonicalRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hsquares : HasCompatibleFigure18ScaffoldSquares) :
    NatSiteRobinsonCanonicalTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofL2C1Figure18ScaffoldDataPositiveFigure18ScaffoldTileableBoxes
    canonicalRouting
    (fun r _hr => tileableBoxes_of_compatibleFigure18ScaffoldSquares hsquares r)

def ofL2C1Figure18ScaffoldDataPositiveFigure18ScaffoldTilesPlane
    (canonicalRouting :
      HasFigure18RobinsonBoardCanonicalRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane figure18ScaffoldTiles) :
    NatSiteRobinsonCanonicalTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofL2C1Figure18ScaffoldDataPositiveCompatibleSquares canonicalRouting
    (compatibleFigure18ScaffoldSquares_of_tilesPlane hplane)

def ofL2C1Figure18ScaffoldDataPositiveFig13TilesPlane
    (canonicalRouting :
      HasFigure18RobinsonBoardCanonicalRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles) :
    NatSiteRobinsonCanonicalTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofL2C1Figure18ScaffoldDataPositiveFigure18ScaffoldTilesPlane
    canonicalRouting
    (tilesPlane_figure18ScaffoldTiles_of_tilesPlane_fig13Tiles hplane)

def ofL2C2Figure18ScaffoldDataPositiveTranslatedBoxes
    (canonicalRouting :
      HasFigure18RobinsonBoardCanonicalRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (translatedBoxes :
      Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant
        (figure18ScaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid)) :
    NatSiteRobinsonCanonicalTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofFigure18ScaffoldDataPositiveTranslatedBoxes canonicalRouting translatedBoxes

def ofL2C2Figure18ScaffoldDataPositiveTranslatedIsolatedBoxes
    (canonicalRouting :
      HasFigure18RobinsonBoardCanonicalRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (isolatedBoxes :
      Figure18ScaffoldData.HasPositiveTranslatedIsolatedActiveBoxInvariant
        (figure18ScaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid)) :
    NatSiteRobinsonCanonicalTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofFigure18ScaffoldDataPositiveTranslatedIsolatedBoxes
    canonicalRouting isolatedBoxes

def ofL2C2Figure18ScaffoldDataPositiveTranslatedValidBoxes
    (canonicalRouting :
      HasFigure18RobinsonBoardCanonicalRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (validBoxes :
      ∀ r : Nat, 0 < r →
        ∃ origin : Int × Int,
          ∃ base : TranslatedBoxPattern
            l2Component2Figure18ScaffoldData.scaffold.tiles r origin,
            ValidTranslatedBoxTiling
              l2Component2Figure18ScaffoldData.scaffold.tiles r origin base) :
    NatSiteRobinsonCanonicalTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofL2C2Figure18ScaffoldDataPositiveTranslatedIsolatedBoxes
    canonicalRouting
    (by
      simpa [l2Component2Figure18ScaffoldData] using
        l2Component2PositiveTranslatedIsolatedBoxesOfValidBoxes validBoxes)

def ofL2C2Figure18ScaffoldDataPositiveTileableBoxes
    (canonicalRouting :
      HasFigure18RobinsonBoardCanonicalRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (tileableBoxes :
      ∀ r : Nat, 0 < r →
        TileableBox l2Component2Figure18ScaffoldData.scaffold.tiles r) :
    NatSiteRobinsonCanonicalTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofL2C2Figure18ScaffoldDataPositiveTranslatedValidBoxes canonicalRouting
    (positiveTranslatedValidBoxes_of_tileableBoxes tileableBoxes)

def ofL2C2Figure18ScaffoldDataPositiveFigure18ScaffoldTileableBoxes
    (canonicalRouting :
      HasFigure18RobinsonBoardCanonicalRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (tileableBoxes :
      ∀ r : Nat, 0 < r → TileableBox figure18ScaffoldTiles r) :
    NatSiteRobinsonCanonicalTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofL2C2Figure18ScaffoldDataPositiveTranslatedIsolatedBoxes
    canonicalRouting
    (by
      simpa [l2Component2Figure18ScaffoldData] using
        l2Component2PositiveTranslatedIsolatedBoxesOfFigure18ScaffoldTileableBoxes
          tileableBoxes)

def ofL2C2Figure18ScaffoldDataPositiveCompatibleSquares
    (canonicalRouting :
      HasFigure18RobinsonBoardCanonicalRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hsquares : HasCompatibleFigure18ScaffoldSquares) :
    NatSiteRobinsonCanonicalTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofL2C2Figure18ScaffoldDataPositiveFigure18ScaffoldTileableBoxes
    canonicalRouting
    (fun r _hr => tileableBoxes_of_compatibleFigure18ScaffoldSquares hsquares r)

def ofL2C2Figure18ScaffoldDataPositiveFigure18ScaffoldTilesPlane
    (canonicalRouting :
      HasFigure18RobinsonBoardCanonicalRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane figure18ScaffoldTiles) :
    NatSiteRobinsonCanonicalTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofL2C2Figure18ScaffoldDataPositiveCompatibleSquares canonicalRouting
    (compatibleFigure18ScaffoldSquares_of_tilesPlane hplane)

def ofL2C2Figure18ScaffoldDataPositiveFig13TilesPlane
    (canonicalRouting :
      HasFigure18RobinsonBoardCanonicalRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles) :
    NatSiteRobinsonCanonicalTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofL2C2Figure18ScaffoldDataPositiveFigure18ScaffoldTilesPlane
    canonicalRouting
    (tilesPlane_figure18ScaffoldTiles_of_tilesPlane_fig13Tiles hplane)

def ofPositiveTranslatedBoxes
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (canonicalRouting :
      HasFigure18RobinsonBoardCanonicalRoutingForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (translatedBoxes :
      Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant
        (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid)) :
    NatSiteRobinsonCanonicalTranslatedPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid :=
  ofFigure18ScaffoldDataPositiveTranslatedBoxes canonicalRouting
    translatedBoxes

def ofPositiveTranslatedIsolatedBoxes
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (canonicalRouting :
      HasFigure18RobinsonBoardCanonicalRoutingForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (isolatedBoxes :
      Figure18ScaffoldData.HasPositiveTranslatedIsolatedActiveBoxInvariant
        (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid)) :
    NatSiteRobinsonCanonicalTranslatedPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid :=
  ofFigure18ScaffoldDataPositiveTranslatedIsolatedBoxes canonicalRouting
    isolatedBoxes

def toCanonicalPositiveBoxObligations
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (O : NatSiteRobinsonCanonicalTranslatedPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid) :
    NatSiteRobinsonCanonicalPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid where
  canonicalRouting := O.canonicalRouting
  positiveIndexedBoxes :=
    TranslatedActiveCornerIndexedBox.nonempty_centered_pos_of_translated_pos
      O.positiveTranslatedIndexedBoxes

def toTowerIndexedBoxObligations
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (O : NatSiteRobinsonCanonicalTranslatedPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid)
    (pairCompatibility :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true) :
    NatSiteRobinsonTowerIndexedBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid :=
  O.toCanonicalPositiveBoxObligations.toTowerIndexedBoxObligations
    pairCompatibility

def toL2C1TowerIndexedBoxObligations
    (O : NatSiteRobinsonCanonicalTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid) :
    NatSiteRobinsonTowerIndexedBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  O.toCanonicalPositiveBoxObligations.toL2C1TowerIndexedBoxObligations

def toL2C2TowerIndexedBoxObligations
    (O : NatSiteRobinsonCanonicalTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid) :
    NatSiteRobinsonTowerIndexedBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  O.toCanonicalPositiveBoxObligations.toL2C2TowerIndexedBoxObligations

end NatSiteRobinsonCanonicalTranslatedPositiveBoxObligations

namespace NatSiteRobinsonCanonicalCombinedSiteTranslatedPositiveBoxObligations

def productRoutingOfCombinedSiteRouting
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (canonicalCombinedSiteRouting :
      HasFigure18RobinsonBoardCanonicalCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table) :
    HasFigure18RobinsonBoardCanonicalProductWitnessRoutingForTable
      (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).table :=
  hasFigure18RobinsonBoardCanonicalProductWitnessRoutingForTable_of_corridor
    (hasFigure18RobinsonBoardCanonicalCorridorProductWitnessRoutingForTable_of_combinedSites
      canonicalCombinedSiteRouting)

def canonicalRoutingOfCombinedSiteRouting
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (canonicalCombinedSiteRouting :
      HasFigure18RobinsonBoardCanonicalCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table) :
    HasFigure18RobinsonBoardCanonicalRoutingForTable
      (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).table :=
  hasFigure18RobinsonBoardRoutingForGeometryTowerForTable_of_productWitnessRouting
    (productRoutingOfCombinedSiteRouting canonicalCombinedSiteRouting)

def toCanonicalTranslatedPositiveBoxObligations
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (O : NatSiteRobinsonCanonicalCombinedSiteTranslatedPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid) :
    NatSiteRobinsonCanonicalTranslatedPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid where
  canonicalRouting :=
    canonicalRoutingOfCombinedSiteRouting O.canonicalCombinedSiteRouting
  positiveTranslatedIndexedBoxes := O.positiveTranslatedIndexedBoxes

def ofCanonicalTranslatedPositiveBoxObligations
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (canonicalCombinedSiteRouting :
      HasFigure18RobinsonBoardCanonicalCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (O : NatSiteRobinsonCanonicalTranslatedPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid) :
    NatSiteRobinsonCanonicalCombinedSiteTranslatedPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid where
  canonicalCombinedSiteRouting := canonicalCombinedSiteRouting
  positiveTranslatedIndexedBoxes := O.positiveTranslatedIndexedBoxes

def ofFigure18ScaffoldDataPositiveTranslatedBoxes
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (canonicalCombinedSiteRouting :
      HasFigure18RobinsonBoardCanonicalCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (translatedBoxes :
      Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant
        (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid)) :
    NatSiteRobinsonCanonicalCombinedSiteTranslatedPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid :=
  ofCanonicalTranslatedPositiveBoxObligations canonicalCombinedSiteRouting
    (NatSiteRobinsonCanonicalTranslatedPositiveBoxObligations.ofPositiveTranslatedBoxes
        (canonicalRoutingOfCombinedSiteRouting canonicalCombinedSiteRouting)
        translatedBoxes)

def ofFigure18ScaffoldDataPositiveTranslatedIsolatedBoxes
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (canonicalCombinedSiteRouting :
      HasFigure18RobinsonBoardCanonicalCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (isolatedBoxes :
      Figure18ScaffoldData.HasPositiveTranslatedIsolatedActiveBoxInvariant
        (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid)) :
    NatSiteRobinsonCanonicalCombinedSiteTranslatedPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid :=
  ofCanonicalTranslatedPositiveBoxObligations canonicalCombinedSiteRouting
    (NatSiteRobinsonCanonicalTranslatedPositiveBoxObligations.ofPositiveTranslatedIsolatedBoxes
        (canonicalRoutingOfCombinedSiteRouting canonicalCombinedSiteRouting)
        isolatedBoxes)

def ofL2C1Figure18ScaffoldDataPositiveTranslatedBoxes
    (canonicalCombinedSiteRouting :
      HasFigure18RobinsonBoardCanonicalCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (translatedBoxes :
      Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant
        (figure18ScaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid)) :
    NatSiteRobinsonCanonicalCombinedSiteTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofFigure18ScaffoldDataPositiveTranslatedBoxes canonicalCombinedSiteRouting
    translatedBoxes

def ofL2C1Figure18ScaffoldDataPositiveTranslatedIsolatedBoxes
    (canonicalCombinedSiteRouting :
      HasFigure18RobinsonBoardCanonicalCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (isolatedBoxes :
      Figure18ScaffoldData.HasPositiveTranslatedIsolatedActiveBoxInvariant
        (figure18ScaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid)) :
    NatSiteRobinsonCanonicalCombinedSiteTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofFigure18ScaffoldDataPositiveTranslatedIsolatedBoxes
    canonicalCombinedSiteRouting isolatedBoxes

def ofL2C1Figure18ScaffoldDataPositiveTranslatedValidBoxes
    (canonicalCombinedSiteRouting :
      HasFigure18RobinsonBoardCanonicalCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (validBoxes :
      ∀ r : Nat, 0 < r →
        ∃ origin : Int × Int,
          ∃ base : TranslatedBoxPattern
            l2Component1Figure18ScaffoldData.scaffold.tiles r origin,
            ValidTranslatedBoxTiling
              l2Component1Figure18ScaffoldData.scaffold.tiles r origin base) :
    NatSiteRobinsonCanonicalCombinedSiteTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofL2C1Figure18ScaffoldDataPositiveTranslatedIsolatedBoxes
    canonicalCombinedSiteRouting
    (by
      simpa [l2Component1Figure18ScaffoldData] using
        l2Component1PositiveTranslatedIsolatedBoxesOfValidBoxes validBoxes)

def ofL2C1Figure18ScaffoldDataPositiveTileableBoxes
    (canonicalCombinedSiteRouting :
      HasFigure18RobinsonBoardCanonicalCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (tileableBoxes :
      ∀ r : Nat, 0 < r →
        TileableBox l2Component1Figure18ScaffoldData.scaffold.tiles r) :
    NatSiteRobinsonCanonicalCombinedSiteTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofL2C1Figure18ScaffoldDataPositiveTranslatedValidBoxes
    canonicalCombinedSiteRouting
    (positiveTranslatedValidBoxes_of_tileableBoxes tileableBoxes)

def ofL2C1Figure18ScaffoldDataPositiveFigure18ScaffoldTileableBoxes
    (canonicalCombinedSiteRouting :
      HasFigure18RobinsonBoardCanonicalCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (tileableBoxes :
      ∀ r : Nat, 0 < r → TileableBox figure18ScaffoldTiles r) :
    NatSiteRobinsonCanonicalCombinedSiteTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofL2C1Figure18ScaffoldDataPositiveTranslatedIsolatedBoxes
    canonicalCombinedSiteRouting
    (by
      simpa [l2Component1Figure18ScaffoldData] using
        l2Component1PositiveTranslatedIsolatedBoxesOfFigure18ScaffoldTileableBoxes
          tileableBoxes)

def ofL2C1Figure18ScaffoldDataPositiveCompatibleSquares
    (canonicalCombinedSiteRouting :
      HasFigure18RobinsonBoardCanonicalCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hsquares : HasCompatibleFigure18ScaffoldSquares) :
    NatSiteRobinsonCanonicalCombinedSiteTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofL2C1Figure18ScaffoldDataPositiveFigure18ScaffoldTileableBoxes
    canonicalCombinedSiteRouting
    (fun r _hr => tileableBoxes_of_compatibleFigure18ScaffoldSquares hsquares r)

def ofL2C1Figure18ScaffoldDataPositiveFigure18ScaffoldTilesPlane
    (canonicalCombinedSiteRouting :
      HasFigure18RobinsonBoardCanonicalCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane figure18ScaffoldTiles) :
    NatSiteRobinsonCanonicalCombinedSiteTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofL2C1Figure18ScaffoldDataPositiveCompatibleSquares
    canonicalCombinedSiteRouting
    (compatibleFigure18ScaffoldSquares_of_tilesPlane hplane)

def ofL2C1Figure18ScaffoldDataPositiveFig13TilesPlane
    (canonicalCombinedSiteRouting :
      HasFigure18RobinsonBoardCanonicalCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles) :
    NatSiteRobinsonCanonicalCombinedSiteTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofL2C1Figure18ScaffoldDataPositiveFigure18ScaffoldTilesPlane
    canonicalCombinedSiteRouting
    (tilesPlane_figure18ScaffoldTiles_of_tilesPlane_fig13Tiles hplane)

def ofL2C2Figure18ScaffoldDataPositiveTranslatedBoxes
    (canonicalCombinedSiteRouting :
      HasFigure18RobinsonBoardCanonicalCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (translatedBoxes :
      Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant
        (figure18ScaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid)) :
    NatSiteRobinsonCanonicalCombinedSiteTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofFigure18ScaffoldDataPositiveTranslatedBoxes canonicalCombinedSiteRouting
    translatedBoxes

def ofL2C2Figure18ScaffoldDataPositiveTranslatedIsolatedBoxes
    (canonicalCombinedSiteRouting :
      HasFigure18RobinsonBoardCanonicalCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (isolatedBoxes :
      Figure18ScaffoldData.HasPositiveTranslatedIsolatedActiveBoxInvariant
        (figure18ScaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid)) :
    NatSiteRobinsonCanonicalCombinedSiteTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofFigure18ScaffoldDataPositiveTranslatedIsolatedBoxes
    canonicalCombinedSiteRouting isolatedBoxes

def ofL2C2Figure18ScaffoldDataPositiveTranslatedValidBoxes
    (canonicalCombinedSiteRouting :
      HasFigure18RobinsonBoardCanonicalCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (validBoxes :
      ∀ r : Nat, 0 < r →
        ∃ origin : Int × Int,
          ∃ base : TranslatedBoxPattern
            l2Component2Figure18ScaffoldData.scaffold.tiles r origin,
            ValidTranslatedBoxTiling
              l2Component2Figure18ScaffoldData.scaffold.tiles r origin base) :
    NatSiteRobinsonCanonicalCombinedSiteTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofL2C2Figure18ScaffoldDataPositiveTranslatedIsolatedBoxes
    canonicalCombinedSiteRouting
    (by
      simpa [l2Component2Figure18ScaffoldData] using
        l2Component2PositiveTranslatedIsolatedBoxesOfValidBoxes validBoxes)

def ofL2C2Figure18ScaffoldDataPositiveTileableBoxes
    (canonicalCombinedSiteRouting :
      HasFigure18RobinsonBoardCanonicalCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (tileableBoxes :
      ∀ r : Nat, 0 < r →
        TileableBox l2Component2Figure18ScaffoldData.scaffold.tiles r) :
    NatSiteRobinsonCanonicalCombinedSiteTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofL2C2Figure18ScaffoldDataPositiveTranslatedValidBoxes
    canonicalCombinedSiteRouting
    (positiveTranslatedValidBoxes_of_tileableBoxes tileableBoxes)

def ofL2C2Figure18ScaffoldDataPositiveFigure18ScaffoldTileableBoxes
    (canonicalCombinedSiteRouting :
      HasFigure18RobinsonBoardCanonicalCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (tileableBoxes :
      ∀ r : Nat, 0 < r → TileableBox figure18ScaffoldTiles r) :
    NatSiteRobinsonCanonicalCombinedSiteTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofL2C2Figure18ScaffoldDataPositiveTranslatedIsolatedBoxes
    canonicalCombinedSiteRouting
    (by
      simpa [l2Component2Figure18ScaffoldData] using
        l2Component2PositiveTranslatedIsolatedBoxesOfFigure18ScaffoldTileableBoxes
          tileableBoxes)

def ofL2C2Figure18ScaffoldDataPositiveCompatibleSquares
    (canonicalCombinedSiteRouting :
      HasFigure18RobinsonBoardCanonicalCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hsquares : HasCompatibleFigure18ScaffoldSquares) :
    NatSiteRobinsonCanonicalCombinedSiteTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofL2C2Figure18ScaffoldDataPositiveFigure18ScaffoldTileableBoxes
    canonicalCombinedSiteRouting
    (fun r _hr => tileableBoxes_of_compatibleFigure18ScaffoldSquares hsquares r)

def ofL2C2Figure18ScaffoldDataPositiveFigure18ScaffoldTilesPlane
    (canonicalCombinedSiteRouting :
      HasFigure18RobinsonBoardCanonicalCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane figure18ScaffoldTiles) :
    NatSiteRobinsonCanonicalCombinedSiteTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofL2C2Figure18ScaffoldDataPositiveCompatibleSquares
    canonicalCombinedSiteRouting
    (compatibleFigure18ScaffoldSquares_of_tilesPlane hplane)

def ofL2C2Figure18ScaffoldDataPositiveFig13TilesPlane
    (canonicalCombinedSiteRouting :
      HasFigure18RobinsonBoardCanonicalCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles) :
    NatSiteRobinsonCanonicalCombinedSiteTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofL2C2Figure18ScaffoldDataPositiveFigure18ScaffoldTilesPlane
    canonicalCombinedSiteRouting
    (tilesPlane_figure18ScaffoldTiles_of_tilesPlane_fig13Tiles hplane)

def toCanonicalPositiveBoxObligations
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (O : NatSiteRobinsonCanonicalCombinedSiteTranslatedPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid) :
    NatSiteRobinsonCanonicalPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid :=
  O.toCanonicalTranslatedPositiveBoxObligations.toCanonicalPositiveBoxObligations

def toTowerIndexedBoxObligations
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (O : NatSiteRobinsonCanonicalCombinedSiteTranslatedPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid)
    (pairCompatibility :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true) :
    NatSiteRobinsonTowerIndexedBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid :=
  O.toCanonicalPositiveBoxObligations.toTowerIndexedBoxObligations
    pairCompatibility

def toL2C1TowerIndexedBoxObligations
    (O : NatSiteRobinsonCanonicalCombinedSiteTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid) :
    NatSiteRobinsonTowerIndexedBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  O.toCanonicalPositiveBoxObligations.toL2C1TowerIndexedBoxObligations

def toL2C2TowerIndexedBoxObligations
    (O : NatSiteRobinsonCanonicalCombinedSiteTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid) :
    NatSiteRobinsonTowerIndexedBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  O.toCanonicalPositiveBoxObligations.toL2C2TowerIndexedBoxObligations

end NatSiteRobinsonCanonicalCombinedSiteTranslatedPositiveBoxObligations

/--
Direct routed Figure 18 certificate from Robinson's canonical board routing
and positive-radius translated active-corner boxes.

Unlike the older checked-stack route, this uses the payload-level routed
free-grid theorem directly and does not require virtual neighboring free-grid
crossings to be adjacent Figure 18 sites.
-/
def natSiteFigure18RoutedCertificateOfCanonicalRoutingPositiveTranslatedBoxes
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (canonicalRouting :
      HasFigure18RobinsonBoardCanonicalRoutingForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (translatedBoxes :
      Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant
        (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid)) :
    Figure18RoutedCertificate
      (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).table where
  routedForces :=
    hasFigure18RoutedFixedCornerSquares_of_indexed
      (hasFigure18IndexedRoutedFixedCornerSquares_of_robinsonBoardRoutedFreeGrids
        (hasFigure18RobinsonBoardRoutedFreeGridsForTable_of_canonicalRouting
          canonicalRouting))
  realizes := by
    have hrealizes :
        Figure18ScaffoldData.HasRealizationInvariant
          (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
            cornerIndex cornerQuadrant cornerIndex_valid) :=
      Figure18ScaffoldData.HasRealizationInvariant.ofPositiveTranslatedActiveCornerIndexedBoxes
        translatedBoxes
    simpa [Figure18ScaffoldData.HasRealizationInvariant,
      figure18ScaffoldDataOfNatSites, scaffoldDataOfNatSites,
      LayeredFigure18ScaffoldData.scaffold,
      LayeredFigure18ScaffoldData.presentation,
      LayeredFigure18ScaffoldData.table,
      LayeredFigure18ScaffoldData.flatTable,
      Figure18ScaffoldData.scaffold,
      Figure18ScaffoldData.presentation,
      Figure18ScaffoldData.table] using hrealizes

/--
Direct routed Figure 18 certificate from Robinson's canonical product-witness
board routing and positive-radius translated active-corner boxes.
-/
def natSiteFigure18RoutedCertificateOfCanonicalProductRoutingPositiveTranslatedBoxes
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (canonicalProductRouting :
      HasFigure18RobinsonBoardCanonicalProductWitnessRoutingForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (translatedBoxes :
      Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant
        (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid)) :
    Figure18RoutedCertificate
      (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).table where
  routedForces :=
    hasFigure18RoutedFixedCornerSquares_of_indexed
      (hasFigure18IndexedRoutedFixedCornerSquaresForTable_of_canonicalProductWitnessRouting
        canonicalProductRouting)
  realizes := by
    have hrealizes :
        Figure18ScaffoldData.HasRealizationInvariant
          (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
            cornerIndex cornerQuadrant cornerIndex_valid) :=
      Figure18ScaffoldData.HasRealizationInvariant.ofPositiveTranslatedActiveCornerIndexedBoxes
        translatedBoxes
    simpa [Figure18ScaffoldData.HasRealizationInvariant,
      figure18ScaffoldDataOfNatSites, scaffoldDataOfNatSites,
      LayeredFigure18ScaffoldData.scaffold,
      LayeredFigure18ScaffoldData.presentation,
      LayeredFigure18ScaffoldData.table,
      LayeredFigure18ScaffoldData.flatTable,
      Figure18ScaffoldData.scaffold,
      Figure18ScaffoldData.presentation,
       Figure18ScaffoldData.table] using hrealizes

/--
Direct routed Figure 18 certificate from Robinson's canonical
corridor-transmission routing and positive-radius translated active-corner
boxes.
-/
def natSiteFigure18RoutedCertificateOfCanonicalCorridorRoutingPositiveTranslatedBoxes
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (canonicalCorridorRouting :
      HasFigure18RobinsonBoardCanonicalCorridorProductWitnessRoutingForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (translatedBoxes :
      Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant
        (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid)) :
    Figure18RoutedCertificate
      (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).table :=
  natSiteFigure18RoutedCertificateOfCanonicalProductRoutingPositiveTranslatedBoxes
    (hasFigure18RobinsonBoardCanonicalProductWitnessRoutingForTable_of_corridor
      canonicalCorridorRouting)
    translatedBoxes

/--
Direct routed Figure 18 certificate from Robinson's canonical decoded
combined-site corridor routing and positive-radius translated active-corner
boxes.
-/
def natSiteFigure18RoutedCertificateOfCanonicalCombinedSiteRoutingPositiveTranslatedBoxes
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (canonicalCombinedSiteRouting :
      HasFigure18RobinsonBoardCanonicalCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (translatedBoxes :
      Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant
        (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid)) :
    Figure18RoutedCertificate
      (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).table :=
  natSiteFigure18RoutedCertificateOfCanonicalCorridorRoutingPositiveTranslatedBoxes
    (hasFigure18RobinsonBoardCanonicalCorridorProductWitnessRoutingForTable_of_combinedSites
      canonicalCombinedSiteRouting)
    translatedBoxes

/--
Direct routed Figure 18 certificate from Robinson's canonical named
site-rectangle routing and positive-radius translated active-corner boxes.
-/
def natSiteFigure18RoutedCertificateOfCanonicalSiteRectRoutingPositiveTranslatedBoxes
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (canonicalSiteRectRouting :
      HasFigure18RobinsonBoardCanonicalSiteRectCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (translatedBoxes :
      Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant
        (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid)) :
    Figure18RoutedCertificate
      (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).table :=
  natSiteFigure18RoutedCertificateOfCanonicalCombinedSiteRoutingPositiveTranslatedBoxes
    (hasFigure18RobinsonBoardCanonicalCombinedSiteCorridorRoutingForTable_of_siteRect
      canonicalSiteRectRouting)
    translatedBoxes

/--
Direct flexible Figure 18 certificate from Robinson's canonical free-site-
rectangle routing and positive-radius translated active-corner boxes.

This is the same Section 7 proof-facing package as the routed constructor
below, but it lands immediately on the abstract scaffold certificate.
-/
def natSiteFigure18FlexibleCertificateOfCanonicalFreeSiteRectRoutingPositiveTranslatedBoxes
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (canonicalFreeSiteRectRouting :
      HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (translatedBoxes :
      Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant
        (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid)) :
    Figure18FlexibleCertificate
      (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).table :=
  Figure18FlexibleCertificate.ofRobinsonBoardCanonicalFreeSiteRectRouting
    canonicalFreeSiteRectRouting
    (by
      have hrealizes :
          Figure18ScaffoldData.HasRealizationInvariant
            (figure18ScaffoldDataOfNatSites activeSiteSpecs
              activeSiteSpecs_valid cornerIndex cornerQuadrant
              cornerIndex_valid) :=
        Figure18ScaffoldData.HasRealizationInvariant.ofPositiveTranslatedActiveCornerIndexedBoxes
          translatedBoxes
      simpa [Figure18ScaffoldData.HasRealizationInvariant,
        figure18ScaffoldDataOfNatSites, scaffoldDataOfNatSites,
        LayeredFigure18ScaffoldData.scaffold,
        LayeredFigure18ScaffoldData.presentation,
        LayeredFigure18ScaffoldData.table,
        LayeredFigure18ScaffoldData.flatTable,
        Figure18ScaffoldData.scaffold,
        Figure18ScaffoldData.presentation,
        Figure18ScaffoldData.table] using hrealizes)

/--
Direct routed Figure 18 certificate from Robinson's canonical free-site-
rectangle routing and positive-radius translated active-corner boxes.

This is the proof-facing form for the Section 7 obstruction argument: the
clear-row and clear-column premises have already been discharged by the
canonical free-line geometry.
-/
def natSiteFigure18RoutedCertificateOfCanonicalFreeSiteRectRoutingPositiveTranslatedBoxes
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (canonicalFreeSiteRectRouting :
      HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (translatedBoxes :
      Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant
        (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid)) :
    Figure18RoutedCertificate
      (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).table :=
  natSiteFigure18RoutedCertificateOfCanonicalSiteRectRoutingPositiveTranslatedBoxes
    (hasFigure18RobinsonBoardCanonicalSiteRectCombinedSiteCorridorRoutingForTable_of_freeSiteRect
      canonicalFreeSiteRectRouting)
    translatedBoxes

/--
Direct routed Figure 18 certificate from Robinson Section 7 combined-site
corridor routing, where the board geometry tower may be selected from the
given tiling, and positive-radius translated active-corner boxes.

This is the proof-facing version closest to Robinson's paper: first extract
red boards/free corridors from the tiling, then route the decoded payload
through those corridors.
-/
def natSiteFigure18RoutedCertificateOfGeomCombinedPositiveTranslatedBoxes
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (geometryCombinedSiteRouting :
      HasFigure18RobinsonBoardGeometryTowerCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (translatedBoxes :
      Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant
        (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid)) :
    Figure18RoutedCertificate
      (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).table where
  routedForces :=
    hasFigure18RoutedFixedCornerSquares_of_indexed
      (hasFigure18IndexedRoutedFixedCornerSquares_of_robinsonBoardRoutedFreeGrids
        (hasFigure18RobinsonBoardRoutedFreeGridsForTable_of_geometryTowerRouting
          (hasFigure18RobinsonBoardGeometryTowerRoutingForTable_of_geometryTowerCombinedSites
            geometryCombinedSiteRouting)))
  realizes := by
    have hrealizes :
        Figure18ScaffoldData.HasRealizationInvariant
          (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
            cornerIndex cornerQuadrant cornerIndex_valid) :=
      Figure18ScaffoldData.HasRealizationInvariant.ofPositiveTranslatedActiveCornerIndexedBoxes
        translatedBoxes
    simpa [Figure18ScaffoldData.HasRealizationInvariant,
      figure18ScaffoldDataOfNatSites, scaffoldDataOfNatSites,
      LayeredFigure18ScaffoldData.scaffold,
      LayeredFigure18ScaffoldData.presentation,
      LayeredFigure18ScaffoldData.table,
      LayeredFigure18ScaffoldData.flatTable,
      Figure18ScaffoldData.scaffold,
      Figure18ScaffoldData.presentation,
      Figure18ScaffoldData.table] using hrealizes

namespace NatSiteRobinsonCanonicalSiteRectTranslatedPositiveBoxObligations

def ofFigure18ScaffoldDataPositiveTranslatedBoxes
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (canonicalSiteRectRouting :
      HasFigure18RobinsonBoardCanonicalSiteRectCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (translatedBoxes :
      Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant
        (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid)) :
    NatSiteRobinsonCanonicalSiteRectTranslatedPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid where
  canonicalSiteRectCombinedSiteRouting := canonicalSiteRectRouting
  positiveTranslatedIndexedBoxes := by
    intro r hr
    simpa [figure18ScaffoldDataOfNatSites, scaffoldDataOfNatSites,
      LayeredFigure18ScaffoldData.scaffold,
      LayeredFigure18ScaffoldData.presentation,
      LayeredFigure18ScaffoldData.table,
      LayeredFigure18ScaffoldData.flatTable,
      Figure18ScaffoldData.scaffold,
      Figure18ScaffoldData.presentation,
      Figure18ScaffoldData.table] using translatedBoxes r hr

def ofFigure18ScaffoldDataPositiveTranslatedBoxesFreeSiteRect
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (canonicalFreeSiteRectRouting :
      HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (translatedBoxes :
      Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant
        (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid)) :
    NatSiteRobinsonCanonicalSiteRectTranslatedPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid :=
  ofFigure18ScaffoldDataPositiveTranslatedBoxes
    (hasFigure18RobinsonBoardCanonicalSiteRectCombinedSiteCorridorRoutingForTable_of_freeSiteRect
      canonicalFreeSiteRectRouting)
    translatedBoxes

def ofFigure18ScaffoldDataPositiveTranslatedIsolatedBoxes
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (canonicalSiteRectRouting :
      HasFigure18RobinsonBoardCanonicalSiteRectCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (isolatedBoxes :
      Figure18ScaffoldData.HasPositiveTranslatedIsolatedActiveBoxInvariant
        (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid)) :
    NatSiteRobinsonCanonicalSiteRectTranslatedPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid :=
  ofFigure18ScaffoldDataPositiveTranslatedBoxes canonicalSiteRectRouting
    (Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant.ofIsolatedActiveBoxes
      isolatedBoxes)

def ofL2C1Figure18ScaffoldDataPositiveTranslatedBoxes
    (canonicalSiteRectRouting :
      HasFigure18RobinsonBoardCanonicalSiteRectCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (translatedBoxes :
      Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant
        (figure18ScaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid)) :
    NatSiteRobinsonCanonicalSiteRectTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofFigure18ScaffoldDataPositiveTranslatedBoxes canonicalSiteRectRouting
    translatedBoxes

def ofL2C1Figure18ScaffoldDataPositiveTranslatedIsolatedBoxes
    (canonicalSiteRectRouting :
      HasFigure18RobinsonBoardCanonicalSiteRectCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (isolatedBoxes :
      Figure18ScaffoldData.HasPositiveTranslatedIsolatedActiveBoxInvariant
        (figure18ScaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid)) :
    NatSiteRobinsonCanonicalSiteRectTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofFigure18ScaffoldDataPositiveTranslatedIsolatedBoxes
    canonicalSiteRectRouting isolatedBoxes

def ofL2C1Figure18ScaffoldDataPositiveTranslatedValidBoxes
    (canonicalSiteRectRouting :
      HasFigure18RobinsonBoardCanonicalSiteRectCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (validBoxes :
      ∀ r : Nat, 0 < r →
        ∃ origin : Int × Int,
          ∃ base : TranslatedBoxPattern
            l2Component1Figure18ScaffoldData.scaffold.tiles r origin,
            ValidTranslatedBoxTiling
              l2Component1Figure18ScaffoldData.scaffold.tiles r origin base) :
    NatSiteRobinsonCanonicalSiteRectTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofL2C1Figure18ScaffoldDataPositiveTranslatedIsolatedBoxes
    canonicalSiteRectRouting
    (by
      simpa [l2Component1Figure18ScaffoldData] using
        l2Component1PositiveTranslatedIsolatedBoxesOfValidBoxes validBoxes)

def ofL2C1Figure18ScaffoldDataPositiveTileableBoxes
    (canonicalSiteRectRouting :
      HasFigure18RobinsonBoardCanonicalSiteRectCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (tileableBoxes :
      ∀ r : Nat, 0 < r →
        TileableBox l2Component1Figure18ScaffoldData.scaffold.tiles r) :
    NatSiteRobinsonCanonicalSiteRectTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofL2C1Figure18ScaffoldDataPositiveTranslatedValidBoxes
    canonicalSiteRectRouting
    (positiveTranslatedValidBoxes_of_tileableBoxes tileableBoxes)

def ofL2C1Figure18ScaffoldDataPositiveFigure18ScaffoldTileableBoxes
    (canonicalSiteRectRouting :
      HasFigure18RobinsonBoardCanonicalSiteRectCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (tileableBoxes :
      ∀ r : Nat, 0 < r → TileableBox figure18ScaffoldTiles r) :
    NatSiteRobinsonCanonicalSiteRectTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofL2C1Figure18ScaffoldDataPositiveTranslatedIsolatedBoxes
    canonicalSiteRectRouting
    (by
      simpa [l2Component1Figure18ScaffoldData] using
        l2Component1PositiveTranslatedIsolatedBoxesOfFigure18ScaffoldTileableBoxes
          tileableBoxes)

def ofL2C1Figure18ScaffoldDataPositiveCompatibleSquares
    (canonicalSiteRectRouting :
      HasFigure18RobinsonBoardCanonicalSiteRectCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hsquares : HasCompatibleFigure18ScaffoldSquares) :
    NatSiteRobinsonCanonicalSiteRectTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofL2C1Figure18ScaffoldDataPositiveFigure18ScaffoldTileableBoxes
    canonicalSiteRectRouting
    (fun r _hr => tileableBoxes_of_compatibleFigure18ScaffoldSquares hsquares r)

def ofL2C1Figure18ScaffoldDataPositiveFigure18ScaffoldTilesPlane
    (canonicalSiteRectRouting :
      HasFigure18RobinsonBoardCanonicalSiteRectCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane figure18ScaffoldTiles) :
    NatSiteRobinsonCanonicalSiteRectTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofL2C1Figure18ScaffoldDataPositiveCompatibleSquares
    canonicalSiteRectRouting
    (compatibleFigure18ScaffoldSquares_of_tilesPlane hplane)

def ofL2C1Figure18ScaffoldDataPositiveFig13TilesPlane
    (canonicalSiteRectRouting :
      HasFigure18RobinsonBoardCanonicalSiteRectCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles) :
    NatSiteRobinsonCanonicalSiteRectTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofL2C1Figure18ScaffoldDataPositiveFigure18ScaffoldTilesPlane
    canonicalSiteRectRouting
    (tilesPlane_figure18ScaffoldTiles_of_tilesPlane_fig13Tiles hplane)

def ofL2C1Figure18ScaffoldDataPositiveFig13TilesPlaneFreeSiteRect
    (canonicalFreeSiteRectRouting :
      HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles) :
    NatSiteRobinsonCanonicalSiteRectTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofL2C1Figure18ScaffoldDataPositiveFig13TilesPlane
    (hasFigure18RobinsonBoardCanonicalSiteRectCombinedSiteCorridorRoutingForTable_of_freeSiteRect
      canonicalFreeSiteRectRouting)
    hplane

def ofL2C2Figure18ScaffoldDataPositiveTranslatedBoxes
    (canonicalSiteRectRouting :
      HasFigure18RobinsonBoardCanonicalSiteRectCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (translatedBoxes :
      Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant
        (figure18ScaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid)) :
    NatSiteRobinsonCanonicalSiteRectTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofFigure18ScaffoldDataPositiveTranslatedBoxes canonicalSiteRectRouting
    translatedBoxes

def ofL2C2Figure18ScaffoldDataPositiveTranslatedIsolatedBoxes
    (canonicalSiteRectRouting :
      HasFigure18RobinsonBoardCanonicalSiteRectCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (isolatedBoxes :
      Figure18ScaffoldData.HasPositiveTranslatedIsolatedActiveBoxInvariant
        (figure18ScaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid)) :
    NatSiteRobinsonCanonicalSiteRectTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofFigure18ScaffoldDataPositiveTranslatedIsolatedBoxes
    canonicalSiteRectRouting isolatedBoxes

def ofL2C2Figure18ScaffoldDataPositiveTranslatedValidBoxes
    (canonicalSiteRectRouting :
      HasFigure18RobinsonBoardCanonicalSiteRectCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (validBoxes :
      ∀ r : Nat, 0 < r →
        ∃ origin : Int × Int,
          ∃ base : TranslatedBoxPattern
            l2Component2Figure18ScaffoldData.scaffold.tiles r origin,
            ValidTranslatedBoxTiling
              l2Component2Figure18ScaffoldData.scaffold.tiles r origin base) :
    NatSiteRobinsonCanonicalSiteRectTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofL2C2Figure18ScaffoldDataPositiveTranslatedIsolatedBoxes
    canonicalSiteRectRouting
    (by
      simpa [l2Component2Figure18ScaffoldData] using
        l2Component2PositiveTranslatedIsolatedBoxesOfValidBoxes validBoxes)

def ofL2C2Figure18ScaffoldDataPositiveTileableBoxes
    (canonicalSiteRectRouting :
      HasFigure18RobinsonBoardCanonicalSiteRectCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (tileableBoxes :
      ∀ r : Nat, 0 < r →
        TileableBox l2Component2Figure18ScaffoldData.scaffold.tiles r) :
    NatSiteRobinsonCanonicalSiteRectTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofL2C2Figure18ScaffoldDataPositiveTranslatedValidBoxes
    canonicalSiteRectRouting
    (positiveTranslatedValidBoxes_of_tileableBoxes tileableBoxes)

def ofL2C2Figure18ScaffoldDataPositiveFigure18ScaffoldTileableBoxes
    (canonicalSiteRectRouting :
      HasFigure18RobinsonBoardCanonicalSiteRectCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (tileableBoxes :
      ∀ r : Nat, 0 < r → TileableBox figure18ScaffoldTiles r) :
    NatSiteRobinsonCanonicalSiteRectTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofL2C2Figure18ScaffoldDataPositiveTranslatedIsolatedBoxes
    canonicalSiteRectRouting
    (by
      simpa [l2Component2Figure18ScaffoldData] using
        l2Component2PositiveTranslatedIsolatedBoxesOfFigure18ScaffoldTileableBoxes
          tileableBoxes)

def ofL2C2Figure18ScaffoldDataPositiveCompatibleSquares
    (canonicalSiteRectRouting :
      HasFigure18RobinsonBoardCanonicalSiteRectCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hsquares : HasCompatibleFigure18ScaffoldSquares) :
    NatSiteRobinsonCanonicalSiteRectTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofL2C2Figure18ScaffoldDataPositiveFigure18ScaffoldTileableBoxes
    canonicalSiteRectRouting
    (fun r _hr => tileableBoxes_of_compatibleFigure18ScaffoldSquares hsquares r)

def ofL2C2Figure18ScaffoldDataPositiveFigure18ScaffoldTilesPlane
    (canonicalSiteRectRouting :
      HasFigure18RobinsonBoardCanonicalSiteRectCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane figure18ScaffoldTiles) :
    NatSiteRobinsonCanonicalSiteRectTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofL2C2Figure18ScaffoldDataPositiveCompatibleSquares
    canonicalSiteRectRouting
    (compatibleFigure18ScaffoldSquares_of_tilesPlane hplane)

def ofL2C2Figure18ScaffoldDataPositiveFig13TilesPlane
    (canonicalSiteRectRouting :
      HasFigure18RobinsonBoardCanonicalSiteRectCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles) :
    NatSiteRobinsonCanonicalSiteRectTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofL2C2Figure18ScaffoldDataPositiveFigure18ScaffoldTilesPlane
    canonicalSiteRectRouting
    (tilesPlane_figure18ScaffoldTiles_of_tilesPlane_fig13Tiles hplane)

def ofL2C2Figure18ScaffoldDataPositiveFig13TilesPlaneFreeSiteRect
    (canonicalFreeSiteRectRouting :
      HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles) :
    NatSiteRobinsonCanonicalSiteRectTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofL2C2Figure18ScaffoldDataPositiveFig13TilesPlane
    (hasFigure18RobinsonBoardCanonicalSiteRectCombinedSiteCorridorRoutingForTable_of_freeSiteRect
      canonicalFreeSiteRectRouting)
    hplane

def toCanonicalCombinedSiteTranslatedPositiveBoxObligations
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (O : NatSiteRobinsonCanonicalSiteRectTranslatedPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid) :
    NatSiteRobinsonCanonicalCombinedSiteTranslatedPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid where
  canonicalCombinedSiteRouting :=
    hasFigure18RobinsonBoardCanonicalCombinedSiteCorridorRoutingForTable_of_siteRect
      O.canonicalSiteRectCombinedSiteRouting
  positiveTranslatedIndexedBoxes := O.positiveTranslatedIndexedBoxes

def toCanonicalTranslatedPositiveBoxObligations
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (O : NatSiteRobinsonCanonicalSiteRectTranslatedPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid) :
    NatSiteRobinsonCanonicalTranslatedPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid :=
  O.toCanonicalCombinedSiteTranslatedPositiveBoxObligations
    |>.toCanonicalTranslatedPositiveBoxObligations

def toCanonicalPositiveBoxObligations
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (O : NatSiteRobinsonCanonicalSiteRectTranslatedPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid) :
    NatSiteRobinsonCanonicalPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid :=
  O.toCanonicalTranslatedPositiveBoxObligations.toCanonicalPositiveBoxObligations

def toTowerIndexedBoxObligations
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (O : NatSiteRobinsonCanonicalSiteRectTranslatedPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid)
    (pairCompatibility :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true) :
    NatSiteRobinsonTowerIndexedBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid :=
  O.toCanonicalTranslatedPositiveBoxObligations.toTowerIndexedBoxObligations
    pairCompatibility

def toL2C1TowerIndexedBoxObligations
    (O : NatSiteRobinsonCanonicalSiteRectTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid) :
    NatSiteRobinsonTowerIndexedBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  O.toCanonicalTranslatedPositiveBoxObligations.toL2C1TowerIndexedBoxObligations

def toL2C2TowerIndexedBoxObligations
    (O : NatSiteRobinsonCanonicalSiteRectTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid) :
    NatSiteRobinsonTowerIndexedBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  O.toCanonicalTranslatedPositiveBoxObligations.toL2C2TowerIndexedBoxObligations

def toGeomCombinedTranslatedPositiveBoxObligations
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (O : NatSiteRobinsonCanonicalSiteRectTranslatedPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid) :
    NatSiteRobinsonGeomCombinedTranslatedPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid where
  geomCombinedSiteRouting :=
    hasFigure18RobinsonBoardGeometryTowerCombinedSiteRoutingForTable_of_canonical
      (hasFigure18RobinsonBoardCanonicalCombinedSiteCorridorRoutingForTable_of_siteRect
        O.canonicalSiteRectCombinedSiteRouting)
  positiveTranslatedIndexedBoxes := O.positiveTranslatedIndexedBoxes

def toFigure18RoutedCertificate
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (O : NatSiteRobinsonCanonicalSiteRectTranslatedPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid) :
    Figure18RoutedCertificate
      (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).table :=
  natSiteFigure18RoutedCertificateOfCanonicalSiteRectRoutingPositiveTranslatedBoxes
    O.canonicalSiteRectCombinedSiteRouting O.positiveTranslatedIndexedBoxes

end NatSiteRobinsonCanonicalSiteRectTranslatedPositiveBoxObligations

namespace NatSiteRobinsonCanonicalFreeSiteRectTranslatedPositiveBoxObligations

def ofFigure18ScaffoldDataPositiveTranslatedBoxes
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (canonicalFreeSiteRectRouting :
      HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (translatedBoxes :
      Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant
        (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid)) :
    NatSiteRobinsonCanonicalFreeSiteRectTranslatedPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid where
  canonicalFreeSiteRectRouting := canonicalFreeSiteRectRouting
  positiveTranslatedIndexedBoxes := by
    intro r hr
    simpa [figure18ScaffoldDataOfNatSites, scaffoldDataOfNatSites,
      LayeredFigure18ScaffoldData.scaffold,
      LayeredFigure18ScaffoldData.presentation,
      LayeredFigure18ScaffoldData.table,
      LayeredFigure18ScaffoldData.flatTable,
      Figure18ScaffoldData.scaffold,
      Figure18ScaffoldData.presentation,
      Figure18ScaffoldData.table] using translatedBoxes r hr

def ofFigure18ScaffoldDataPositiveTranslatedIsolatedBoxes
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (canonicalFreeSiteRectRouting :
      HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (isolatedBoxes :
      Figure18ScaffoldData.HasPositiveTranslatedIsolatedActiveBoxInvariant
        (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid)) :
    NatSiteRobinsonCanonicalFreeSiteRectTranslatedPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid :=
  ofFigure18ScaffoldDataPositiveTranslatedBoxes canonicalFreeSiteRectRouting
    (Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant.ofIsolatedActiveBoxes
      isolatedBoxes)

def ofL2C1Figure18ScaffoldDataPositiveFig13TilesPlane
    (canonicalFreeSiteRectRouting :
      HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles) :
    NatSiteRobinsonCanonicalFreeSiteRectTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofFigure18ScaffoldDataPositiveTranslatedIsolatedBoxes
    canonicalFreeSiteRectRouting
    (by
      simpa [l2Component1Figure18ScaffoldData] using
        l2Component1PositiveTranslatedIsolatedBoxesOfFig13TilesPlane hplane)

def ofL2C2Figure18ScaffoldDataPositiveFig13TilesPlane
    (canonicalFreeSiteRectRouting :
      HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles) :
    NatSiteRobinsonCanonicalFreeSiteRectTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofFigure18ScaffoldDataPositiveTranslatedIsolatedBoxes
    canonicalFreeSiteRectRouting
    (by
      simpa [l2Component2Figure18ScaffoldData] using
        l2Component2PositiveTranslatedIsolatedBoxesOfFig13TilesPlane hplane)

def ofL2C1Figure18ScaffoldDataPositiveFig13TileableBoxes
    (canonicalFreeSiteRectRouting :
      HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hboxes : ∀ r : Nat, TileableBox fig13Tiles r) :
    NatSiteRobinsonCanonicalFreeSiteRectTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofFigure18ScaffoldDataPositiveTranslatedIsolatedBoxes
    canonicalFreeSiteRectRouting
    (by
      simpa [l2Component1Figure18ScaffoldData] using
        l2Component1PositiveTranslatedIsolatedBoxesOfFig13TileableBoxes hboxes)

def ofL2C2Figure18ScaffoldDataPositiveFig13TileableBoxes
    (canonicalFreeSiteRectRouting :
      HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hboxes : ∀ r : Nat, TileableBox fig13Tiles r) :
    NatSiteRobinsonCanonicalFreeSiteRectTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofFigure18ScaffoldDataPositiveTranslatedIsolatedBoxes
    canonicalFreeSiteRectRouting
    (by
      simpa [l2Component2Figure18ScaffoldData] using
        l2Component2PositiveTranslatedIsolatedBoxesOfFig13TileableBoxes hboxes)

def ofL2C1Figure18ScaffoldDataPositiveFig13CofinalSquares
    (canonicalFreeSiteRectRouting :
      HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hsquares :
      ∀ n : Nat, ∃ m : Nat, n ≤ m ∧ TileableSquare fig13Tiles m) :
    NatSiteRobinsonCanonicalFreeSiteRectTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofFigure18ScaffoldDataPositiveTranslatedIsolatedBoxes
    canonicalFreeSiteRectRouting
    (by
      simpa [l2Component1Figure18ScaffoldData] using
        l2Component1PositiveTranslatedIsolatedBoxesOfFig13CofinalSquares
          hsquares)

def ofL2C2Figure18ScaffoldDataPositiveFig13CofinalSquares
    (canonicalFreeSiteRectRouting :
      HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hsquares :
      ∀ n : Nat, ∃ m : Nat, n ≤ m ∧ TileableSquare fig13Tiles m) :
    NatSiteRobinsonCanonicalFreeSiteRectTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofFigure18ScaffoldDataPositiveTranslatedIsolatedBoxes
    canonicalFreeSiteRectRouting
    (by
      simpa [l2Component2Figure18ScaffoldData] using
        l2Component2PositiveTranslatedIsolatedBoxesOfFig13CofinalSquares
          hsquares)

def ofL2C1Figure18ScaffoldDataPositiveRobinsonBoardLevelAlignedMacroSquares
    (canonicalFreeSiteRectRouting :
      HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : HasFigure13RobinsonBoardLevelAlignedMacroSquares) :
    NatSiteRobinsonCanonicalFreeSiteRectTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofFigure18ScaffoldDataPositiveTranslatedIsolatedBoxes
    canonicalFreeSiteRectRouting
    (by
      simpa [l2Component1Figure18ScaffoldData] using
        l2Component1PositiveTranslatedIsolatedBoxesOfRobinsonBoardLevelAlignedMacroSquares
          hlevel)

def ofL2C2Figure18ScaffoldDataPositiveRobinsonBoardLevelAlignedMacroSquares
    (canonicalFreeSiteRectRouting :
      HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : HasFigure13RobinsonBoardLevelAlignedMacroSquares) :
    NatSiteRobinsonCanonicalFreeSiteRectTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofFigure18ScaffoldDataPositiveTranslatedIsolatedBoxes
    canonicalFreeSiteRectRouting
    (by
      simpa [l2Component2Figure18ScaffoldData] using
        l2Component2PositiveTranslatedIsolatedBoxesOfRobinsonBoardLevelAlignedMacroSquares
          hlevel)

def ofL2C1Figure18ScaffoldDataPositiveCheckedFigure16MacroSquares
    (canonicalFreeSiteRectRouting :
      HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : HasCheckedFigure16RecognizedRobinsonBoardLevelMacroSquares) :
    NatSiteRobinsonCanonicalFreeSiteRectTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofFigure18ScaffoldDataPositiveTranslatedIsolatedBoxes
    canonicalFreeSiteRectRouting
    (by
      simpa [l2Component1Figure18ScaffoldData] using
        l2Component1PositiveTranslatedIsolatedBoxesOfCheckedFigure16MacroSquares
          hlevel)

def ofL2C2Figure18ScaffoldDataPositiveCheckedFigure16MacroSquares
    (canonicalFreeSiteRectRouting :
      HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : HasCheckedFigure16RecognizedRobinsonBoardLevelMacroSquares) :
    NatSiteRobinsonCanonicalFreeSiteRectTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofFigure18ScaffoldDataPositiveTranslatedIsolatedBoxes
    canonicalFreeSiteRectRouting
    (by
      simpa [l2Component2Figure18ScaffoldData] using
        l2Component2PositiveTranslatedIsolatedBoxesOfCheckedFigure16MacroSquares
          hlevel)

def ofL2C1Figure18ScaffoldDataPositiveCanonicalCheckedFigure16MacroSquares
    (canonicalFreeSiteRectRouting :
      HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : HasCanonicalCheckedFigure16RecognizedRobinsonBoardLevelMacroSquares) :
    NatSiteRobinsonCanonicalFreeSiteRectTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofFigure18ScaffoldDataPositiveTranslatedIsolatedBoxes
    canonicalFreeSiteRectRouting
    (by
      simpa [l2Component1Figure18ScaffoldData] using
        l2Component1PositiveTranslatedIsolatedBoxesOfCanonicalCheckedFigure16MacroSquares
          hlevel)

def ofL2C2Figure18ScaffoldDataPositiveCanonicalCheckedFigure16MacroSquares
    (canonicalFreeSiteRectRouting :
      HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : HasCanonicalCheckedFigure16RecognizedRobinsonBoardLevelMacroSquares) :
    NatSiteRobinsonCanonicalFreeSiteRectTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofFigure18ScaffoldDataPositiveTranslatedIsolatedBoxes
    canonicalFreeSiteRectRouting
    (by
      simpa [l2Component2Figure18ScaffoldData] using
        l2Component2PositiveTranslatedIsolatedBoxesOfCanonicalCheckedFigure16MacroSquares
          hlevel)

def ofL2C1Figure18ScaffoldDataPositiveCheckedCompatibleFigure16MacroSquares
    (canonicalFreeSiteRectRouting :
      HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel :
      HasCheckedFigure16RecognizedCompatibleRobinsonBoardLevelMacroSquares) :
    NatSiteRobinsonCanonicalFreeSiteRectTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofFigure18ScaffoldDataPositiveTranslatedIsolatedBoxes
    canonicalFreeSiteRectRouting
    (by
      simpa [l2Component1Figure18ScaffoldData] using
        l2Component1PositiveTranslatedIsolatedBoxesOfCheckedCompatibleFigure16MacroSquares
          hlevel)

def ofL2C2Figure18ScaffoldDataPositiveCheckedCompatibleFigure16MacroSquares
    (canonicalFreeSiteRectRouting :
      HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel :
      HasCheckedFigure16RecognizedCompatibleRobinsonBoardLevelMacroSquares) :
    NatSiteRobinsonCanonicalFreeSiteRectTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofFigure18ScaffoldDataPositiveTranslatedIsolatedBoxes
    canonicalFreeSiteRectRouting
    (by
      simpa [l2Component2Figure18ScaffoldData] using
        l2Component2PositiveTranslatedIsolatedBoxesOfCheckedCompatibleFigure16MacroSquares
          hlevel)

def ofL2C1Figure18ScaffoldDataPositiveCanonicalCheckedCompatibleFigure16MacroSquares
    (canonicalFreeSiteRectRouting :
      HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel :
      HasCanonicalCheckedFigure16RecognizedCompatibleRobinsonBoardLevelMacroSquares) :
    NatSiteRobinsonCanonicalFreeSiteRectTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofFigure18ScaffoldDataPositiveTranslatedIsolatedBoxes
    canonicalFreeSiteRectRouting
    (by
      simpa [l2Component1Figure18ScaffoldData] using
        l2Component1PositiveTranslatedIsolatedBoxesOfCanonicalCheckedCompatibleFigure16MacroSquares
          hlevel)

def ofL2C2Figure18ScaffoldDataPositiveCanonicalCheckedCompatibleFigure16MacroSquares
    (canonicalFreeSiteRectRouting :
      HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel :
      HasCanonicalCheckedFigure16RecognizedCompatibleRobinsonBoardLevelMacroSquares) :
    NatSiteRobinsonCanonicalFreeSiteRectTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofFigure18ScaffoldDataPositiveTranslatedIsolatedBoxes
    canonicalFreeSiteRectRouting
    (by
      simpa [l2Component2Figure18ScaffoldData] using
        l2Component2PositiveTranslatedIsolatedBoxesOfCanonicalCheckedCompatibleFigure16MacroSquares
          hlevel)

def ofL2C1Figure18ScaffoldDataPositiveCanonicalCheckedCompatibleFigure16LevelData
    (canonicalFreeSiteRectRouting :
      HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : HasCanonicalCheckedFigure16RecognizedCompatibleLevelData) :
    NatSiteRobinsonCanonicalFreeSiteRectTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofFigure18ScaffoldDataPositiveTranslatedIsolatedBoxes
    canonicalFreeSiteRectRouting
    (by
      simpa [l2Component1Figure18ScaffoldData] using
        l2Component1PositiveTranslatedIsolatedBoxesOfCanonicalCheckedCompatibleFigure16LevelData
          hlevel)

def ofL2C2Figure18ScaffoldDataPositiveCanonicalCheckedCompatibleFigure16LevelData
    (canonicalFreeSiteRectRouting :
      HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hlevel : HasCanonicalCheckedFigure16RecognizedCompatibleLevelData) :
    NatSiteRobinsonCanonicalFreeSiteRectTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofFigure18ScaffoldDataPositiveTranslatedIsolatedBoxes
    canonicalFreeSiteRectRouting
    (by
      simpa [l2Component2Figure18ScaffoldData] using
        l2Component2PositiveTranslatedIsolatedBoxesOfCanonicalCheckedCompatibleFigure16LevelData
          hlevel)

def toCanonicalSiteRectTranslatedPositiveBoxObligations
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (O : NatSiteRobinsonCanonicalFreeSiteRectTranslatedPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid) :
    NatSiteRobinsonCanonicalSiteRectTranslatedPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid where
  canonicalSiteRectCombinedSiteRouting :=
    hasFigure18RobinsonBoardCanonicalSiteRectCombinedSiteCorridorRoutingForTable_of_freeSiteRect
      O.canonicalFreeSiteRectRouting
  positiveTranslatedIndexedBoxes := O.positiveTranslatedIndexedBoxes

def toCanonicalCombinedSiteTranslatedPositiveBoxObligations
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (O : NatSiteRobinsonCanonicalFreeSiteRectTranslatedPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid) :
    NatSiteRobinsonCanonicalCombinedSiteTranslatedPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid :=
  O.toCanonicalSiteRectTranslatedPositiveBoxObligations
    |>.toCanonicalCombinedSiteTranslatedPositiveBoxObligations

def toCanonicalTranslatedPositiveBoxObligations
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (O : NatSiteRobinsonCanonicalFreeSiteRectTranslatedPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid) :
    NatSiteRobinsonCanonicalTranslatedPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid :=
  O.toCanonicalSiteRectTranslatedPositiveBoxObligations
    |>.toCanonicalTranslatedPositiveBoxObligations

/--
Canonical free-site-rectangle routing plus translated positive boxes supplies
the compatible level-grid obligation surface.

The only extra input is the generated finite pair-compatibility check used by
the Figure 13/Figure 16 stack decoder.
-/
def toCompatibleLevelObligations
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (O : NatSiteRobinsonCanonicalFreeSiteRectTranslatedPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid)
    (pairCompatibility :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true) :
    NatSiteRobinsonCompatibleLevelObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid :=
  NatSiteRobinsonCompatibleLevelObligations.ofLevelCompatiblePositiveTranslatedBoxes
    activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
    cornerIndex_valid
    (hasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable_of_localTower
      (hasFigure18RobinsonBoardLevelSignalLocalTowerForTable_of_canonicalFreeSiteRectRouting
        O.canonicalFreeSiteRectRouting))
    O.positiveTranslatedIndexedBoxes
    pairCompatibility

def toL2C1CompatibleLevelObligations
    (O : NatSiteRobinsonCanonicalFreeSiteRectTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid) :
    NatSiteRobinsonCompatibleLevelObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  O.toCompatibleLevelObligations
    (by
      simpa [l2Component1BlankCandidateActiveSiteData,
        l2Component1BlankCandidateCornerSite, NatSiteSpecSanity.activeSiteData,
        NatSiteSpecSanity.cornerSite] using
        l2Component1BlankCandidatePairCompatibilityBool)

def toL2C2CompatibleLevelObligations
    (O : NatSiteRobinsonCanonicalFreeSiteRectTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid) :
    NatSiteRobinsonCompatibleLevelObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  O.toCompatibleLevelObligations
    (by
      simpa [l2Component2BlankCandidateActiveSiteData,
        l2Component2BlankCandidateCornerSite, NatSiteSpecSanity.activeSiteData,
        NatSiteSpecSanity.cornerSite] using
        l2Component2BlankCandidatePairCompatibilityBool)

def toTowerIndexedBoxObligations
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (O : NatSiteRobinsonCanonicalFreeSiteRectTranslatedPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid)
    (pairCompatibility :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true) :
    NatSiteRobinsonTowerIndexedBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid :=
  O.toCanonicalSiteRectTranslatedPositiveBoxObligations
    |>.toTowerIndexedBoxObligations pairCompatibility

def toL2C1TowerIndexedBoxObligations
    (O : NatSiteRobinsonCanonicalFreeSiteRectTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid) :
    NatSiteRobinsonTowerIndexedBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  O.toCanonicalSiteRectTranslatedPositiveBoxObligations
    |>.toL2C1TowerIndexedBoxObligations

def toL2C2TowerIndexedBoxObligations
    (O : NatSiteRobinsonCanonicalFreeSiteRectTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid) :
    NatSiteRobinsonTowerIndexedBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  O.toCanonicalSiteRectTranslatedPositiveBoxObligations
    |>.toL2C2TowerIndexedBoxObligations

def toGeomCombinedTranslatedPositiveBoxObligations
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (O : NatSiteRobinsonCanonicalFreeSiteRectTranslatedPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid) :
    NatSiteRobinsonGeomCombinedTranslatedPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid :=
  O.toCanonicalSiteRectTranslatedPositiveBoxObligations
    |>.toGeomCombinedTranslatedPositiveBoxObligations

def toFigure18RoutedCertificate
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (O : NatSiteRobinsonCanonicalFreeSiteRectTranslatedPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid) :
    Figure18RoutedCertificate
      (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).table :=
  natSiteFigure18RoutedCertificateOfCanonicalFreeSiteRectRoutingPositiveTranslatedBoxes
    O.canonicalFreeSiteRectRouting O.positiveTranslatedIndexedBoxes

def toFigure18FlexibleCertificate
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (O : NatSiteRobinsonCanonicalFreeSiteRectTranslatedPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid) :
    Figure18FlexibleCertificate
      (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).table :=
  natSiteFigure18FlexibleCertificateOfCanonicalFreeSiteRectRoutingPositiveTranslatedBoxes
    O.canonicalFreeSiteRectRouting O.positiveTranslatedIndexedBoxes

end NatSiteRobinsonCanonicalFreeSiteRectTranslatedPositiveBoxObligations

namespace NatSiteRobinsonSection7BoardFreeLineLayerPatchObligations

def ofOriginZeroWindowsLayerPatches
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (originZeroWindows :
      HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (pairCompatibility :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold) :
    NatSiteRobinsonSection7BoardFreeLineLayerPatchObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid where
  boardFreeLineActiveCorner :=
    figure18ScaffoldDataOfNatSitesBoardFreeLineActiveCornerOfOriginZeroWindows
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid originZeroWindows
  pairCompatibility := pairCompatibility
  patches := patches

def ofL2C1OriginZeroWindowsLayerPatches
    (originZeroWindows :
      HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold) :
    NatSiteRobinsonSection7BoardFreeLineLayerPatchObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofOriginZeroWindowsLayerPatches
    l2Component1BlankCandidateActiveSiteSpecs
    l2Component1BlankCandidateSanity.activeSiteSpecs_valid
    0 Quadrant.southwest
    l2Component1BlankCandidateSanity.cornerIndex_valid
    originZeroWindows
    (by
      simpa [l2Component1BlankCandidateActiveSiteData,
        l2Component1BlankCandidateCornerSite, NatSiteSpecSanity.activeSiteData,
        NatSiteSpecSanity.cornerSite] using
        l2Component1BlankCandidatePairCompatibilityBool)
    patches

def ofL2C2OriginZeroWindowsLayerPatches
    (originZeroWindows :
      HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (patches :
      HasActiveCornerLayerBoxPatches
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table.presentation.toScaffold) :
    NatSiteRobinsonSection7BoardFreeLineLayerPatchObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofOriginZeroWindowsLayerPatches
    l2Component2BlankCandidateActiveSiteSpecs
    l2Component2BlankCandidateSanity.activeSiteSpecs_valid
    0 Quadrant.northeast
    l2Component2BlankCandidateSanity.cornerIndex_valid
    originZeroWindows
    (by
      simpa [l2Component2BlankCandidateActiveSiteData,
        l2Component2BlankCandidateCornerSite, NatSiteSpecSanity.activeSiteData,
        NatSiteSpecSanity.cornerSite] using
        l2Component2BlankCandidatePairCompatibilityBool)
    patches

def toCompatibleLevelObligations
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (O : NatSiteRobinsonSection7BoardFreeLineLayerPatchObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid) :
    NatSiteRobinsonCompatibleLevelObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid :=
  NatSiteRobinsonCompatibleLevelObligations.ofSection7BoardFreeLineLayerPatches
    activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
    cornerIndex_valid O.boardFreeLineActiveCorner O.patches
    O.pairCompatibility

def toL2C1CompatibleLevelObligations
    (O : NatSiteRobinsonSection7BoardFreeLineLayerPatchObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid) :
    NatSiteRobinsonCompatibleLevelObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  O.toCompatibleLevelObligations

def toL2C2CompatibleLevelObligations
    (O : NatSiteRobinsonSection7BoardFreeLineLayerPatchObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid) :
    NatSiteRobinsonCompatibleLevelObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  O.toCompatibleLevelObligations

def toLayerPatchScaffoldCertificate
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (O : NatSiteRobinsonSection7BoardFreeLineLayerPatchObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid) :
    NatSiteRobinsonLayerPatchScaffoldCertificate :=
  NatSiteRobinsonLayerPatchScaffoldCertificate.ofSection7BoardFreeLineLayerPatches
    activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
    cornerIndex_valid O.boardFreeLineActiveCorner O.pairCompatibility
    O.patches

def toL2C1LayerPatchScaffoldCertificate
    (O : NatSiteRobinsonSection7BoardFreeLineLayerPatchObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid) :
    NatSiteRobinsonLayerPatchScaffoldCertificate :=
  O.toLayerPatchScaffoldCertificate

def toL2C2LayerPatchScaffoldCertificate
    (O : NatSiteRobinsonSection7BoardFreeLineLayerPatchObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid) :
    NatSiteRobinsonLayerPatchScaffoldCertificate :=
  O.toLayerPatchScaffoldCertificate

end NatSiteRobinsonSection7BoardFreeLineLayerPatchObligations

namespace NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations

def toCanonicalFreeSiteRectTranslatedPositiveBoxObligations
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (O : NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid) :
    NatSiteRobinsonCanonicalFreeSiteRectTranslatedPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid where
  canonicalFreeSiteRectRouting :=
    hasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable_of_activeCorner
      (hasFigure18RobinsonBoardCanonicalFreeSiteRectActiveCornerForTable_of_originZeroWindows
        O.originZeroWindows)
  positiveTranslatedIndexedBoxes := O.positiveTranslatedIndexedBoxes

def toSignalTowerTranslatedPositiveBoxObligations
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (O : NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid) :
    NatSiteRobinsonSignalTowerTranslatedPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid where
  signalLocalTower :=
    hasFigure18RobinsonBoardLevelSignalLocalTowerForTable_iff_tower.1
      (hasFigure18RobinsonBoardLevelSignalLocalTowerForTable_of_originZeroWindows
        O.originZeroWindows)
  pairCompatibility := O.pairCompatibility
  positiveTranslatedIndexedBoxes := O.positiveTranslatedIndexedBoxes

def toSignalTowerDirectTranslatedBoxObligations
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (O : NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid) :
    NatSiteRobinsonSignalTowerDirectTranslatedBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid where
  signalLocalTower :=
    hasFigure18RobinsonBoardLevelSignalLocalTowerForTable_iff_tower.1
      (hasFigure18RobinsonBoardLevelSignalLocalTowerForTable_of_originZeroWindows
        O.originZeroWindows)
  positiveTranslatedIndexedBoxes := O.positiveTranslatedIndexedBoxes

def toFigure18ScaffoldDataRoutedCertificate
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (O : NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid) :
    (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid).RoutedCertificate :=
  figure18ScaffoldDataOfNatSitesRoutedCertificateOfOriginZeroPairCompatibility
    activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
    cornerIndex_valid O.originZeroWindows O.pairCompatibility
    (by
      intro r hr
      simpa [figure18ScaffoldDataOfNatSites, scaffoldDataOfNatSites,
        LayeredFigure18ScaffoldData.scaffold,
        LayeredFigure18ScaffoldData.presentation,
        LayeredFigure18ScaffoldData.table,
        LayeredFigure18ScaffoldData.flatTable,
        Figure18ScaffoldData.scaffold,
        Figure18ScaffoldData.presentation,
        Figure18ScaffoldData.table] using
        O.positiveTranslatedIndexedBoxes r hr)

def toFigure18RoutedCertificate
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (O : NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid) :
    Figure18RoutedCertificate
      (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).table :=
  O.toSignalTowerDirectTranslatedBoxObligations.toFigure18RoutedCertificate

@[reducible] def positiveActiveCornerIndexedBoxes
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (O : NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid) :
    ∀ r : Nat, 0 < r → Nonempty (ActiveCornerIndexedBox
      (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).scaffold r) :=
  TranslatedActiveCornerIndexedBox.nonempty_centered_pos_of_translated_pos
    O.positiveTranslatedIndexedBoxes

def toActiveCornerLayerBoxPatches
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (O : NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid) :
    HasActiveCornerLayerBoxPatches
      (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold :=
  scaffoldDataOfNatSitesLayerPatchesOfPositiveActiveCornerIndexedBoxes
    activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
    cornerIndex_valid O.positiveActiveCornerIndexedBoxes

def toBoardFreeLineActiveCorner
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (O : NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid) :
    (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid)
        |>.HasRobinsonSection7BoardFreeLineActiveCornerInvariant := by
  refine ⟨hasRobinsonBoardSignalGeometryTower, ?_⟩
  change
    HasFigure18RobinsonBoardCanonicalFreeSiteRectActiveCornerForTable
      (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).table.toRoleTable
  rw [figure18ScaffoldDataOfNatSites_table,
    ← scaffoldDataOfNatSites_table]
  exact
    hasFigure18RobinsonBoardCanonicalFreeSiteRectActiveCornerForTable_of_originZeroWindows
      O.originZeroWindows

def toSection7BoardFreeLineLayerPatchObligations
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (O : NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid) :
    NatSiteRobinsonSection7BoardFreeLineLayerPatchObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid where
  boardFreeLineActiveCorner := O.toBoardFreeLineActiveCorner
  pairCompatibility := O.pairCompatibility
  patches := O.toActiveCornerLayerBoxPatches

def toL2C1Section7BoardFreeLineLayerPatchObligations
    (O : NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid) :
    NatSiteRobinsonSection7BoardFreeLineLayerPatchObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  O.toSection7BoardFreeLineLayerPatchObligations

def toL2C2Section7BoardFreeLineLayerPatchObligations
    (O : NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid) :
    NatSiteRobinsonSection7BoardFreeLineLayerPatchObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  O.toSection7BoardFreeLineLayerPatchObligations

def toL2C1LayerPatchScaffoldCertificate
    (O : NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid) :
    NatSiteRobinsonLayerPatchScaffoldCertificate :=
  O.toL2C1Section7BoardFreeLineLayerPatchObligations
    |>.toL2C1LayerPatchScaffoldCertificate

def toL2C2LayerPatchScaffoldCertificate
    (O : NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid) :
    NatSiteRobinsonLayerPatchScaffoldCertificate :=
  O.toL2C2Section7BoardFreeLineLayerPatchObligations
    |>.toL2C2LayerPatchScaffoldCertificate

def toCompatibleLevelObligationsOfLayerPatches
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (O : NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid) :
    NatSiteRobinsonCompatibleLevelObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid :=
  O.toSection7BoardFreeLineLayerPatchObligations.toCompatibleLevelObligations

def toCompatibleLevelObligations
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (O : NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid) :
    NatSiteRobinsonCompatibleLevelObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid :=
  O.toCompatibleLevelObligationsOfLayerPatches

def toL2C1CompatibleLevelObligations
    (O : NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid) :
    NatSiteRobinsonCompatibleLevelObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  O.toCompatibleLevelObligations

def toL2C2CompatibleLevelObligations
    (O : NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid) :
    NatSiteRobinsonCompatibleLevelObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  O.toCompatibleLevelObligations

def toTowerIndexedBoxObligations
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (O : NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid) :
    NatSiteRobinsonTowerIndexedBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid :=
  O.toCanonicalFreeSiteRectTranslatedPositiveBoxObligations
    |>.toTowerIndexedBoxObligations O.pairCompatibility

def toL2C1TowerIndexedBoxObligations
    (O : NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid) :
    NatSiteRobinsonTowerIndexedBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  O.toTowerIndexedBoxObligations

def toL2C2TowerIndexedBoxObligations
    (O : NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid) :
    NatSiteRobinsonTowerIndexedBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  O.toTowerIndexedBoxObligations

def toL2C1SignalTowerTranslatedPositiveBoxObligations
    (O : NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid) :
    NatSiteRobinsonSignalTowerTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  O.toSignalTowerTranslatedPositiveBoxObligations

def toL2C2SignalTowerTranslatedPositiveBoxObligations
    (O : NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid) :
    NatSiteRobinsonSignalTowerTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  O.toSignalTowerTranslatedPositiveBoxObligations

def toL2C1SignalTowerDirectTranslatedBoxObligations
    (O : NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid) :
    NatSiteRobinsonSignalTowerDirectTranslatedBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  O.toSignalTowerDirectTranslatedBoxObligations

def toL2C2SignalTowerDirectTranslatedBoxObligations
    (O : NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid) :
    NatSiteRobinsonSignalTowerDirectTranslatedBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  O.toSignalTowerDirectTranslatedBoxObligations

def ofFigure18ScaffoldDataPositiveTranslatedBoxes
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (originZeroWindows :
      HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (pairCompatibility :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (translatedBoxes :
      Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant
        (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid)) :
    NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid where
  originZeroWindows := originZeroWindows
  pairCompatibility := pairCompatibility
  positiveTranslatedIndexedBoxes := by
    intro r hr
    simpa [figure18ScaffoldDataOfNatSites, scaffoldDataOfNatSites,
      LayeredFigure18ScaffoldData.scaffold,
      LayeredFigure18ScaffoldData.presentation,
      LayeredFigure18ScaffoldData.table,
      LayeredFigure18ScaffoldData.flatTable,
      Figure18ScaffoldData.scaffold,
      Figure18ScaffoldData.presentation,
      Figure18ScaffoldData.table] using translatedBoxes r hr

def ofFigure18ScaffoldDataPositiveTranslatedIsolatedBoxes
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (originZeroWindows :
      HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (pairCompatibility :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (isolatedBoxes :
      Figure18ScaffoldData.HasPositiveTranslatedIsolatedActiveBoxInvariant
        (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid)) :
    NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid :=
  ofFigure18ScaffoldDataPositiveTranslatedBoxes originZeroWindows
    pairCompatibility
    (Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant.ofIsolatedActiveBoxes
      isolatedBoxes)

def ofL2C1Figure18ScaffoldDataPositiveFig13TilesPlane
    (originZeroWindows :
      HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles) :
    NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofFigure18ScaffoldDataPositiveTranslatedIsolatedBoxes
    originZeroWindows l2Component1BlankCandidatePairCompatibilityBool
    (by
      simpa [l2Component1Figure18ScaffoldData] using
        l2Component1PositiveTranslatedIsolatedBoxesOfFig13TilesPlane hplane)

def ofL2C2Figure18ScaffoldDataPositiveFig13TilesPlane
    (originZeroWindows :
      HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles) :
    NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofFigure18ScaffoldDataPositiveTranslatedIsolatedBoxes
    originZeroWindows l2Component2BlankCandidatePairCompatibilityBool
    (by
      simpa [l2Component2Figure18ScaffoldData] using
        l2Component2PositiveTranslatedIsolatedBoxesOfFig13TilesPlane hplane)

def ofL2C1Figure18ScaffoldDataPositiveFig13TileableBoxes
    (originZeroWindows :
      HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hboxes : ∀ r : Nat, TileableBox fig13Tiles r) :
    NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofFigure18ScaffoldDataPositiveTranslatedIsolatedBoxes
    originZeroWindows l2Component1BlankCandidatePairCompatibilityBool
    (by
      simpa [l2Component1Figure18ScaffoldData] using
        l2Component1PositiveTranslatedIsolatedBoxesOfFig13TileableBoxes hboxes)

def ofL2C2Figure18ScaffoldDataPositiveFig13TileableBoxes
    (originZeroWindows :
      HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hboxes : ∀ r : Nat, TileableBox fig13Tiles r) :
    NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofFigure18ScaffoldDataPositiveTranslatedIsolatedBoxes
    originZeroWindows l2Component2BlankCandidatePairCompatibilityBool
    (by
      simpa [l2Component2Figure18ScaffoldData] using
        l2Component2PositiveTranslatedIsolatedBoxesOfFig13TileableBoxes hboxes)

def ofL2C1Figure18ScaffoldDataPositiveFig13CofinalSquares
    (originZeroWindows :
      HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hsquares :
      ∀ n : Nat, ∃ m : Nat, n ≤ m ∧ TileableSquare fig13Tiles m) :
    NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofFigure18ScaffoldDataPositiveTranslatedIsolatedBoxes
    originZeroWindows l2Component1BlankCandidatePairCompatibilityBool
    (by
      simpa [l2Component1Figure18ScaffoldData] using
        l2Component1PositiveTranslatedIsolatedBoxesOfFig13CofinalSquares
          hsquares)

def ofL2C2Figure18ScaffoldDataPositiveFig13CofinalSquares
    (originZeroWindows :
      HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hsquares :
      ∀ n : Nat, ∃ m : Nat, n ≤ m ∧ TileableSquare fig13Tiles m) :
    NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofFigure18ScaffoldDataPositiveTranslatedIsolatedBoxes
    originZeroWindows l2Component2BlankCandidatePairCompatibilityBool
    (by
      simpa [l2Component2Figure18ScaffoldData] using
        l2Component2PositiveTranslatedIsolatedBoxesOfFig13CofinalSquares
          hsquares)

end NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations

namespace NatSiteRobinsonIndexedActiveTranslatedPositiveBoxObligations

def toIndexedRoutedCertificate
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (O : NatSiteRobinsonIndexedActiveTranslatedPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid) :
    (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid).IndexedRoutedCertificate := by
  have hindexed :
      HasFigure18IndexedActiveCornerWindows
        (Figure18RoleTable.FlatRoleTable.ofActiveSites
          (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid).sites
          (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid)).toRoleTable := by
    exact O.indexedActiveWindows
  have hlisted :
      HasFigure18ListedActiveSiteFixedCornerSquareWindows
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid).sites
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) :=
    hasFigure18ListedActiveSiteFixedCornerSquareWindows_of_indexedActive hindexed
  have hboxes :
      Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant
        (figure18ScaffoldDataOfNatSites activeSiteSpecs
          activeSiteSpecs_valid cornerIndex cornerQuadrant
          cornerIndex_valid) := by
    intro r hr
    simpa [figure18ScaffoldDataOfNatSites, scaffoldDataOfNatSites,
      LayeredFigure18ScaffoldData.scaffold,
      LayeredFigure18ScaffoldData.presentation,
      LayeredFigure18ScaffoldData.table,
      LayeredFigure18ScaffoldData.flatTable,
      Figure18ScaffoldData.scaffold,
      Figure18ScaffoldData.presentation,
      Figure18ScaffoldData.table] using
      O.positiveTranslatedIndexedBoxes r hr
  have hrealizes :
      RealizesActiveCornerSquares
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.presentation.toScaffold :=
    scaffoldDataOfNatSitesRealizesOfPositiveTranslatedIndexedBoxes
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid hboxes
  exact scaffoldDataOfNatSitesIndexedRoutedCertificateOfListedActiveSitePairCompatibility
    activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
    cornerIndex_valid hlisted O.pairCompatibility hrealizes

def toFigure18RoutedCertificate
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (O : NatSiteRobinsonIndexedActiveTranslatedPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid) :
    Figure18RoutedCertificate
      (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).table :=
  O.toIndexedRoutedCertificate.certificate.toFigure18RoutedCertificate

def ofFigure18ScaffoldDataPositiveTranslatedBoxes
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (indexedActiveWindows :
      HasFigure18IndexedActiveCornerWindows
        (Figure18RoleTable.FlatRoleTable.ofActiveSites
          (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid).sites
          (cornerSiteOfNat cornerIndex cornerQuadrant
            cornerIndex_valid)).toRoleTable)
    (pairCompatibility :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (translatedBoxes :
      Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant
        (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid)) :
    NatSiteRobinsonIndexedActiveTranslatedPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid where
  indexedActiveWindows := indexedActiveWindows
  pairCompatibility := pairCompatibility
  positiveTranslatedIndexedBoxes := by
    intro r hr
    simpa [figure18ScaffoldDataOfNatSites, scaffoldDataOfNatSites,
      LayeredFigure18ScaffoldData.scaffold,
      LayeredFigure18ScaffoldData.presentation,
      LayeredFigure18ScaffoldData.table,
      LayeredFigure18ScaffoldData.flatTable,
      Figure18ScaffoldData.scaffold,
      Figure18ScaffoldData.presentation,
      Figure18ScaffoldData.table] using translatedBoxes r hr

def ofFigure18ScaffoldDataPositiveTranslatedIsolatedBoxes
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (indexedActiveWindows :
      HasFigure18IndexedActiveCornerWindows
        (Figure18RoleTable.FlatRoleTable.ofActiveSites
          (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid).sites
          (cornerSiteOfNat cornerIndex cornerQuadrant
            cornerIndex_valid)).toRoleTable)
    (pairCompatibility :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true)
    (isolatedBoxes :
      Figure18ScaffoldData.HasPositiveTranslatedIsolatedActiveBoxInvariant
        (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid)) :
    NatSiteRobinsonIndexedActiveTranslatedPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid :=
  ofFigure18ScaffoldDataPositiveTranslatedBoxes indexedActiveWindows
    pairCompatibility
    (Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant.ofIsolatedActiveBoxes
      isolatedBoxes)

def ofL2C1Figure18ScaffoldDataPositiveFig13TilesPlane
    (indexedActiveWindows :
      HasFigure18IndexedActiveCornerWindows
        (Figure18RoleTable.FlatRoleTable.ofActiveSites
          (activeSiteDataOfSpecs l2Component1BlankCandidateActiveSiteSpecs
            l2Component1BlankCandidateSanity.activeSiteSpecs_valid).sites
          (cornerSiteOfNat 0 Quadrant.southwest
            l2Component1BlankCandidateSanity.cornerIndex_valid)).toRoleTable)
    (hplane : TilesPlane fig13Tiles) :
    NatSiteRobinsonIndexedActiveTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofFigure18ScaffoldDataPositiveTranslatedIsolatedBoxes
    indexedActiveWindows l2Component1BlankCandidatePairCompatibilityBool
    (by
      simpa [l2Component1Figure18ScaffoldData] using
        l2Component1PositiveTranslatedIsolatedBoxesOfFig13TilesPlane hplane)

def ofL2C2Figure18ScaffoldDataPositiveFig13TilesPlane
    (indexedActiveWindows :
      HasFigure18IndexedActiveCornerWindows
        (Figure18RoleTable.FlatRoleTable.ofActiveSites
          (activeSiteDataOfSpecs l2Component2BlankCandidateActiveSiteSpecs
            l2Component2BlankCandidateSanity.activeSiteSpecs_valid).sites
          (cornerSiteOfNat 0 Quadrant.northeast
            l2Component2BlankCandidateSanity.cornerIndex_valid)).toRoleTable)
    (hplane : TilesPlane fig13Tiles) :
    NatSiteRobinsonIndexedActiveTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofFigure18ScaffoldDataPositiveTranslatedIsolatedBoxes
    indexedActiveWindows l2Component2BlankCandidatePairCompatibilityBool
    (by
      simpa [l2Component2Figure18ScaffoldData] using
        l2Component2PositiveTranslatedIsolatedBoxesOfFig13TilesPlane hplane)

end NatSiteRobinsonIndexedActiveTranslatedPositiveBoxObligations

namespace NatSiteRobinsonGeomCombinedTranslatedPositiveBoxObligations

def ofFigure18ScaffoldDataPositiveTranslatedBoxes
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (geomCombinedSiteRouting :
      HasFigure18RobinsonBoardGeometryTowerCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (translatedBoxes :
      Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant
        (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid)) :
    NatSiteRobinsonGeomCombinedTranslatedPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid where
  geomCombinedSiteRouting := geomCombinedSiteRouting
  positiveTranslatedIndexedBoxes := translatedBoxes

def ofFigure18ScaffoldDataPositiveTranslatedIsolatedBoxes
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (geomCombinedSiteRouting :
      HasFigure18RobinsonBoardGeometryTowerCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table)
    (isolatedBoxes :
      Figure18ScaffoldData.HasPositiveTranslatedIsolatedActiveBoxInvariant
        (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid)) :
    NatSiteRobinsonGeomCombinedTranslatedPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid :=
  ofFigure18ScaffoldDataPositiveTranslatedBoxes geomCombinedSiteRouting
    (Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant.ofIsolatedActiveBoxes
      isolatedBoxes)

def ofCanonicalCombinedSiteTranslatedPositiveBoxObligations
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (O : NatSiteRobinsonCanonicalCombinedSiteTranslatedPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid) :
    NatSiteRobinsonGeomCombinedTranslatedPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid where
  geomCombinedSiteRouting :=
    hasFigure18RobinsonBoardGeometryTowerCombinedSiteRoutingForTable_of_canonical
      O.canonicalCombinedSiteRouting
  positiveTranslatedIndexedBoxes := O.positiveTranslatedIndexedBoxes

/--
Forget the tiling-dependent combined-site corridor details to the older
local-tower plus indexed-box obligation surface.

This keeps the proof route closest to Robinson's Section 7 argument: the
geometry-combined premise supplies the coherent obstruction-signal tower, while
the translated boxes supply the finite active-corner boxes.
-/
def toTowerIndexedBoxObligations
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (O : NatSiteRobinsonGeomCombinedTranslatedPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid)
    (pairCompatibility :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true) :
    NatSiteRobinsonTowerIndexedBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid :=
  NatSiteRobinsonTowerIndexedBoxObligations.ofFigure18ScaffoldDataPositiveTranslatedBoxes
    (hasFigure18RobinsonBoardLevelSignalLocalTowerForTable_of_geometryTowerCombinedSites
      O.geomCombinedSiteRouting)
    pairCompatibility
    (by
      intro r hr
      simpa [figure18ScaffoldDataOfNatSites, scaffoldDataOfNatSites,
        LayeredFigure18ScaffoldData.scaffold,
        LayeredFigure18ScaffoldData.presentation,
        LayeredFigure18ScaffoldData.table,
        LayeredFigure18ScaffoldData.flatTable,
        Figure18ScaffoldData.scaffold,
        Figure18ScaffoldData.presentation,
        Figure18ScaffoldData.table] using
        O.positiveTranslatedIndexedBoxes r hr)

def toL2C1TowerIndexedBoxObligations
    (O : NatSiteRobinsonGeomCombinedTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid) :
    NatSiteRobinsonTowerIndexedBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  O.toTowerIndexedBoxObligations
    (by
      simpa [l2Component1BlankCandidateActiveSiteData,
        l2Component1BlankCandidateCornerSite, NatSiteSpecSanity.activeSiteData,
        NatSiteSpecSanity.cornerSite] using
        l2Component1BlankCandidatePairCompatibilityBool)

def toL2C2TowerIndexedBoxObligations
    (O : NatSiteRobinsonGeomCombinedTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid) :
    NatSiteRobinsonTowerIndexedBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  O.toTowerIndexedBoxObligations
    (by
      simpa [l2Component2BlankCandidateActiveSiteData,
        l2Component2BlankCandidateCornerSite, NatSiteSpecSanity.activeSiteData,
        NatSiteSpecSanity.cornerSite] using
        l2Component2BlankCandidatePairCompatibilityBool)

def toCompatibleLevelObligations
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (O : NatSiteRobinsonGeomCombinedTranslatedPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid)
    (pairCompatibility :
      generatedStackAllowedSitePairCompatibilityBool
        (activeSiteDataOfSpecs activeSiteSpecs activeSiteSpecs_valid)
        (cornerSiteOfNat cornerIndex cornerQuadrant cornerIndex_valid) =
          true) :
    NatSiteRobinsonCompatibleLevelObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid :=
  NatSiteRobinsonCompatibleLevelObligations.ofGeometryCombinedPositiveTranslatedBoxes
    activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
    cornerIndex_valid O.geomCombinedSiteRouting
    O.positiveTranslatedIndexedBoxes pairCompatibility

def toL2C1CompatibleLevelObligations
    (O : NatSiteRobinsonGeomCombinedTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid) :
    NatSiteRobinsonCompatibleLevelObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  O.toCompatibleLevelObligations
    (by
      simpa [l2Component1BlankCandidateActiveSiteData,
        l2Component1BlankCandidateCornerSite, NatSiteSpecSanity.activeSiteData,
        NatSiteSpecSanity.cornerSite] using
        l2Component1BlankCandidatePairCompatibilityBool)

def toL2C2CompatibleLevelObligations
    (O : NatSiteRobinsonGeomCombinedTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid) :
    NatSiteRobinsonCompatibleLevelObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  O.toCompatibleLevelObligations
    (by
      simpa [l2Component2BlankCandidateActiveSiteData,
        l2Component2BlankCandidateCornerSite, NatSiteSpecSanity.activeSiteData,
        NatSiteSpecSanity.cornerSite] using
        l2Component2BlankCandidatePairCompatibilityBool)

def toFigure18RoutedCertificate
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (O : NatSiteRobinsonGeomCombinedTranslatedPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid) :
    Figure18RoutedCertificate
      (scaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).table :=
  natSiteFigure18RoutedCertificateOfGeomCombinedPositiveTranslatedBoxes
    O.geomCombinedSiteRouting O.positiveTranslatedIndexedBoxes

def toSignalTowerDirectTranslatedBoxObligations
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (O : NatSiteRobinsonGeomCombinedTranslatedPositiveBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid) :
    NatSiteRobinsonSignalTowerDirectTranslatedBoxObligations
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid where
  signalLocalTower :=
    hasFigure18RobinsonBoardLevelSignalLocalTowerForTable_iff_tower.1
      (hasFigure18RobinsonBoardLevelSignalLocalTowerForTable_of_geometryTowerCombinedSites
        O.geomCombinedSiteRouting)
  positiveTranslatedIndexedBoxes := O.positiveTranslatedIndexedBoxes

def toL2C1SignalTowerDirectTranslatedBoxObligations
    (O : NatSiteRobinsonGeomCombinedTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid) :
    NatSiteRobinsonSignalTowerDirectTranslatedBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  O.toSignalTowerDirectTranslatedBoxObligations

def toL2C2SignalTowerDirectTranslatedBoxObligations
    (O : NatSiteRobinsonGeomCombinedTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid) :
    NatSiteRobinsonSignalTowerDirectTranslatedBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  O.toSignalTowerDirectTranslatedBoxObligations

def ofL2C1Figure18ScaffoldDataPositiveTranslatedBoxes
    (geomCombinedSiteRouting :
      HasFigure18RobinsonBoardGeometryTowerCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (translatedBoxes :
      Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant
        (figure18ScaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid)) :
    NatSiteRobinsonGeomCombinedTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofFigure18ScaffoldDataPositiveTranslatedBoxes geomCombinedSiteRouting
    translatedBoxes

def ofL2C1Figure18ScaffoldDataPositiveTranslatedIsolatedBoxes
    (geomCombinedSiteRouting :
      HasFigure18RobinsonBoardGeometryTowerCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (isolatedBoxes :
      Figure18ScaffoldData.HasPositiveTranslatedIsolatedActiveBoxInvariant
        (figure18ScaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid)) :
    NatSiteRobinsonGeomCombinedTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofFigure18ScaffoldDataPositiveTranslatedIsolatedBoxes
    geomCombinedSiteRouting isolatedBoxes

def ofL2C1Figure18ScaffoldDataPositiveFig13TilesPlane
    (geomCombinedSiteRouting :
      HasFigure18RobinsonBoardGeometryTowerCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles) :
    NatSiteRobinsonGeomCombinedTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid :=
  ofL2C1Figure18ScaffoldDataPositiveTranslatedIsolatedBoxes
    geomCombinedSiteRouting
    (by
      simpa [l2Component1Figure18ScaffoldData] using
        l2Component1PositiveTranslatedIsolatedBoxesOfFig13TilesPlane hplane)

def ofL2C2Figure18ScaffoldDataPositiveTranslatedBoxes
    (geomCombinedSiteRouting :
      HasFigure18RobinsonBoardGeometryTowerCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (translatedBoxes :
      Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant
        (figure18ScaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid)) :
    NatSiteRobinsonGeomCombinedTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofFigure18ScaffoldDataPositiveTranslatedBoxes geomCombinedSiteRouting
    translatedBoxes

def ofL2C2Figure18ScaffoldDataPositiveTranslatedIsolatedBoxes
    (geomCombinedSiteRouting :
      HasFigure18RobinsonBoardGeometryTowerCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (isolatedBoxes :
      Figure18ScaffoldData.HasPositiveTranslatedIsolatedActiveBoxInvariant
        (figure18ScaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid)) :
    NatSiteRobinsonGeomCombinedTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofFigure18ScaffoldDataPositiveTranslatedIsolatedBoxes
    geomCombinedSiteRouting isolatedBoxes

def ofL2C2Figure18ScaffoldDataPositiveFig13TilesPlane
    (geomCombinedSiteRouting :
      HasFigure18RobinsonBoardGeometryTowerCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles) :
    NatSiteRobinsonGeomCombinedTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid :=
  ofL2C2Figure18ScaffoldDataPositiveTranslatedIsolatedBoxes
    geomCombinedSiteRouting
    (by
      simpa [l2Component2Figure18ScaffoldData] using
        l2Component2PositiveTranslatedIsolatedBoxesOfFig13TilesPlane hplane)

end NatSiteRobinsonGeomCombinedTranslatedPositiveBoxObligations

def l2Component1Figure18RoutedCertificateOfCanonicalRoutingPositiveTranslatedBoxes
    (canonicalRouting :
      HasFigure18RobinsonBoardCanonicalRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (translatedBoxes :
      Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant
        (figure18ScaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid)) :
    Figure18RoutedCertificate
      (scaffoldDataOfNatSites
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid).table :=
  natSiteFigure18RoutedCertificateOfCanonicalRoutingPositiveTranslatedBoxes
    canonicalRouting translatedBoxes

/--
L2 component-1 routed Figure 18 certificate from canonical product-witness
routing and positive-radius translated active-corner boxes.
-/
def l2Component1Figure18RoutedCertificateOfCanonicalProductRoutingPositiveTranslatedBoxes
    (canonicalProductRouting :
      HasFigure18RobinsonBoardCanonicalProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (translatedBoxes :
      Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant
        (figure18ScaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid)) :
    Figure18RoutedCertificate
      (scaffoldDataOfNatSites
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid).table :=
  natSiteFigure18RoutedCertificateOfCanonicalProductRoutingPositiveTranslatedBoxes
    canonicalProductRouting translatedBoxes

def l2Component1Figure18RoutedCertificateOfCanonicalRoutingPositiveTranslatedValidBoxes
    (canonicalRouting :
      HasFigure18RobinsonBoardCanonicalRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (validBoxes :
      ∀ r : Nat, 0 < r →
        ∃ origin : Int × Int,
          ∃ base : TranslatedBoxPattern
            l2Component1Figure18ScaffoldData.scaffold.tiles r origin,
            ValidTranslatedBoxTiling
              l2Component1Figure18ScaffoldData.scaffold.tiles r origin base) :
    Figure18RoutedCertificate
      (scaffoldDataOfNatSites
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid).table :=
  l2Component1Figure18RoutedCertificateOfCanonicalRoutingPositiveTranslatedBoxes
    canonicalRouting
    (Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant.ofIsolatedActiveBoxes
      (by
        simpa [l2Component1Figure18ScaffoldData] using
          l2Component1PositiveTranslatedIsolatedBoxesOfValidBoxes validBoxes))

def l2Component1Figure18RoutedCertificateOfCanonicalRoutingPositiveTileableBoxes
    (canonicalRouting :
      HasFigure18RobinsonBoardCanonicalRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (tileableBoxes :
      ∀ r : Nat, 0 < r →
        TileableBox l2Component1Figure18ScaffoldData.scaffold.tiles r) :
    Figure18RoutedCertificate
      (scaffoldDataOfNatSites
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid).table :=
  l2Component1Figure18RoutedCertificateOfCanonicalRoutingPositiveTranslatedValidBoxes
    canonicalRouting
    (positiveTranslatedValidBoxes_of_tileableBoxes tileableBoxes)

def l2Component1Figure18RoutedCertificateOfCanonicalRoutingPositiveFigure18ScaffoldTileableBoxes
    (canonicalRouting :
      HasFigure18RobinsonBoardCanonicalRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (tileableBoxes :
      ∀ r : Nat, 0 < r → TileableBox figure18ScaffoldTiles r) :
    Figure18RoutedCertificate
      (scaffoldDataOfNatSites
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid).table :=
  l2Component1Figure18RoutedCertificateOfCanonicalRoutingPositiveTranslatedBoxes
    canonicalRouting
    (Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant.ofIsolatedActiveBoxes
      (by
        simpa [l2Component1Figure18ScaffoldData] using
          l2Component1PositiveTranslatedIsolatedBoxesOfFigure18ScaffoldTileableBoxes
            tileableBoxes))

def l2Component1Figure18RoutedCertificateOfCanonicalRoutingPositiveCompatibleSquares
    (canonicalRouting :
      HasFigure18RobinsonBoardCanonicalRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hsquares : HasCompatibleFigure18ScaffoldSquares) :
    Figure18RoutedCertificate
      (scaffoldDataOfNatSites
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid).table :=
  l2Component1Figure18RoutedCertificateOfCanonicalRoutingPositiveFigure18ScaffoldTileableBoxes
    canonicalRouting
    (fun r _hr => tileableBoxes_of_compatibleFigure18ScaffoldSquares hsquares r)

def l2Component1Figure18RoutedCertificateOfCanonicalRoutingPositiveFigure18ScaffoldTilesPlane
    (canonicalRouting :
      HasFigure18RobinsonBoardCanonicalRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane figure18ScaffoldTiles) :
    Figure18RoutedCertificate
      (scaffoldDataOfNatSites
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid).table :=
  l2Component1Figure18RoutedCertificateOfCanonicalRoutingPositiveCompatibleSquares
    canonicalRouting
    (compatibleFigure18ScaffoldSquares_of_tilesPlane hplane)

def l2Component1Figure18RoutedCertificateOfCanonicalRoutingPositiveFig13TilesPlane
    (canonicalRouting :
      HasFigure18RobinsonBoardCanonicalRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles) :
    Figure18RoutedCertificate
      (scaffoldDataOfNatSites
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid).table :=
  l2Component1Figure18RoutedCertificateOfCanonicalRoutingPositiveFigure18ScaffoldTilesPlane
    canonicalRouting
    (tilesPlane_figure18ScaffoldTiles_of_tilesPlane_fig13Tiles hplane)

/--
L2 component-1 routed Figure 18 certificate from canonical product-witness
routing and a raw Figure 13 plane tiling.
-/
def l2Component1Figure18RoutedCertificateOfCanonicalProductRoutingPositiveFig13TilesPlane
    (canonicalProductRouting :
      HasFigure18RobinsonBoardCanonicalProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles) :
    Figure18RoutedCertificate
      (scaffoldDataOfNatSites
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid).table :=
  l2Component1Figure18RoutedCertificateOfCanonicalProductRoutingPositiveTranslatedBoxes
    canonicalProductRouting
    (Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant.ofIsolatedActiveBoxes
      (by
        simpa [l2Component1Figure18ScaffoldData] using
          l2Component1PositiveTranslatedIsolatedBoxesOfFig13TilesPlane hplane))

/--
L2 component-1 routed Figure 18 certificate from canonical corridor-transmission
routing and a raw Figure 13 plane tiling.
-/
def l2Component1Figure18RoutedCertificateOfCanonicalCorridorRoutingPositiveFig13TilesPlane
    (canonicalCorridorRouting :
      HasFigure18RobinsonBoardCanonicalCorridorProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles) :
    Figure18RoutedCertificate
      (scaffoldDataOfNatSites
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid).table :=
  natSiteFigure18RoutedCertificateOfCanonicalCorridorRoutingPositiveTranslatedBoxes
    canonicalCorridorRouting
    (Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant.ofIsolatedActiveBoxes
      (by
        simpa [l2Component1Figure18ScaffoldData] using
          l2Component1PositiveTranslatedIsolatedBoxesOfFig13TilesPlane hplane))

/--
L2 component-1 routed Figure 18 certificate from canonical decoded combined-site
corridor routing and a raw Figure 13 plane tiling.
-/
def l2Component1Figure18RoutedCertificateOfCanonicalCombinedSiteRoutingPositiveFig13TilesPlane
    (canonicalCombinedSiteRouting :
      HasFigure18RobinsonBoardCanonicalCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles) :
    Figure18RoutedCertificate
      (scaffoldDataOfNatSites
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid).table :=
  natSiteFigure18RoutedCertificateOfCanonicalCombinedSiteRoutingPositiveTranslatedBoxes
    canonicalCombinedSiteRouting
    (Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant.ofIsolatedActiveBoxes
      (by
        simpa [l2Component1Figure18ScaffoldData] using
          l2Component1PositiveTranslatedIsolatedBoxesOfFig13TilesPlane hplane))

/--
L2 component-1 routed Figure 18 certificate from canonical free-site-rectangle
routing and a raw Figure 13 plane tiling.
-/
def l2Component1Figure18RoutedCertificateOfCanonicalFreeSiteRectRoutingPositiveFig13TilesPlane
    (canonicalFreeSiteRectRouting :
      HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles) :
    Figure18RoutedCertificate
      (scaffoldDataOfNatSites
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid).table :=
  natSiteFigure18RoutedCertificateOfCanonicalFreeSiteRectRoutingPositiveTranslatedBoxes
    canonicalFreeSiteRectRouting
    (Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant.ofIsolatedActiveBoxes
      (by
        simpa [l2Component1Figure18ScaffoldData] using
          l2Component1PositiveTranslatedIsolatedBoxesOfFig13TilesPlane hplane))

/--
L2 component-1 routed Figure 18 certificate from tiling-dependent
Robinson-board geometry plus decoded combined-site corridor routing and a raw
Figure 13 plane tiling.
-/
def l2Component1Figure18RoutedCertificateOfGeomCombinedPositiveFig13TilesPlane
    (geometryCombinedSiteRouting :
      HasFigure18RobinsonBoardGeometryTowerCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component1BlankCandidateActiveSiteSpecs
          l2Component1BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.southwest
          l2Component1BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles) :
    Figure18RoutedCertificate
      (scaffoldDataOfNatSites
        l2Component1BlankCandidateActiveSiteSpecs
        l2Component1BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.southwest
        l2Component1BlankCandidateSanity.cornerIndex_valid).table :=
  natSiteFigure18RoutedCertificateOfGeomCombinedPositiveTranslatedBoxes
    geometryCombinedSiteRouting
    (Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant.ofIsolatedActiveBoxes
      (by
        simpa [l2Component1Figure18ScaffoldData] using
          l2Component1PositiveTranslatedIsolatedBoxesOfFig13TilesPlane hplane))

def l2Component2Figure18RoutedCertificateOfCanonicalRoutingPositiveTranslatedBoxes
    (canonicalRouting :
      HasFigure18RobinsonBoardCanonicalRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (translatedBoxes :
      Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant
        (figure18ScaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid)) :
    Figure18RoutedCertificate
      (scaffoldDataOfNatSites
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid).table :=
  natSiteFigure18RoutedCertificateOfCanonicalRoutingPositiveTranslatedBoxes
    canonicalRouting translatedBoxes

/--
L2 component-2 routed Figure 18 certificate from canonical product-witness
routing and positive-radius translated active-corner boxes.
-/
def l2Component2Figure18RoutedCertificateOfCanonicalProductRoutingPositiveTranslatedBoxes
    (canonicalProductRouting :
      HasFigure18RobinsonBoardCanonicalProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (translatedBoxes :
      Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant
        (figure18ScaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid)) :
    Figure18RoutedCertificate
      (scaffoldDataOfNatSites
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid).table :=
  natSiteFigure18RoutedCertificateOfCanonicalProductRoutingPositiveTranslatedBoxes
    canonicalProductRouting translatedBoxes

def l2Component2Figure18RoutedCertificateOfCanonicalRoutingPositiveTranslatedValidBoxes
    (canonicalRouting :
      HasFigure18RobinsonBoardCanonicalRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (validBoxes :
      ∀ r : Nat, 0 < r →
        ∃ origin : Int × Int,
          ∃ base : TranslatedBoxPattern
            l2Component2Figure18ScaffoldData.scaffold.tiles r origin,
            ValidTranslatedBoxTiling
              l2Component2Figure18ScaffoldData.scaffold.tiles r origin base) :
    Figure18RoutedCertificate
      (scaffoldDataOfNatSites
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid).table :=
  l2Component2Figure18RoutedCertificateOfCanonicalRoutingPositiveTranslatedBoxes
    canonicalRouting
    (Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant.ofIsolatedActiveBoxes
      (by
        simpa [l2Component2Figure18ScaffoldData] using
          l2Component2PositiveTranslatedIsolatedBoxesOfValidBoxes validBoxes))

def l2Component2Figure18RoutedCertificateOfCanonicalRoutingPositiveTileableBoxes
    (canonicalRouting :
      HasFigure18RobinsonBoardCanonicalRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (tileableBoxes :
      ∀ r : Nat, 0 < r →
        TileableBox l2Component2Figure18ScaffoldData.scaffold.tiles r) :
    Figure18RoutedCertificate
      (scaffoldDataOfNatSites
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid).table :=
  l2Component2Figure18RoutedCertificateOfCanonicalRoutingPositiveTranslatedValidBoxes
    canonicalRouting
    (positiveTranslatedValidBoxes_of_tileableBoxes tileableBoxes)

def l2Component2Figure18RoutedCertificateOfCanonicalRoutingPositiveFigure18ScaffoldTileableBoxes
    (canonicalRouting :
      HasFigure18RobinsonBoardCanonicalRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (tileableBoxes :
      ∀ r : Nat, 0 < r → TileableBox figure18ScaffoldTiles r) :
    Figure18RoutedCertificate
      (scaffoldDataOfNatSites
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid).table :=
  l2Component2Figure18RoutedCertificateOfCanonicalRoutingPositiveTranslatedBoxes
    canonicalRouting
    (Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant.ofIsolatedActiveBoxes
      (by
        simpa [l2Component2Figure18ScaffoldData] using
          l2Component2PositiveTranslatedIsolatedBoxesOfFigure18ScaffoldTileableBoxes
            tileableBoxes))

def l2Component2Figure18RoutedCertificateOfCanonicalRoutingPositiveCompatibleSquares
    (canonicalRouting :
      HasFigure18RobinsonBoardCanonicalRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hsquares : HasCompatibleFigure18ScaffoldSquares) :
    Figure18RoutedCertificate
      (scaffoldDataOfNatSites
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid).table :=
  l2Component2Figure18RoutedCertificateOfCanonicalRoutingPositiveFigure18ScaffoldTileableBoxes
    canonicalRouting
    (fun r _hr => tileableBoxes_of_compatibleFigure18ScaffoldSquares hsquares r)

def l2Component2Figure18RoutedCertificateOfCanonicalRoutingPositiveFigure18ScaffoldTilesPlane
    (canonicalRouting :
      HasFigure18RobinsonBoardCanonicalRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane figure18ScaffoldTiles) :
    Figure18RoutedCertificate
      (scaffoldDataOfNatSites
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid).table :=
  l2Component2Figure18RoutedCertificateOfCanonicalRoutingPositiveCompatibleSquares
    canonicalRouting
    (compatibleFigure18ScaffoldSquares_of_tilesPlane hplane)

def l2Component2Figure18RoutedCertificateOfCanonicalRoutingPositiveFig13TilesPlane
    (canonicalRouting :
      HasFigure18RobinsonBoardCanonicalRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles) :
    Figure18RoutedCertificate
      (scaffoldDataOfNatSites
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid).table :=
  l2Component2Figure18RoutedCertificateOfCanonicalRoutingPositiveFigure18ScaffoldTilesPlane
    canonicalRouting
    (tilesPlane_figure18ScaffoldTiles_of_tilesPlane_fig13Tiles hplane)

/--
L2 component-2 routed Figure 18 certificate from canonical product-witness
routing and a raw Figure 13 plane tiling.
-/
def l2Component2Figure18RoutedCertificateOfCanonicalProductRoutingPositiveFig13TilesPlane
    (canonicalProductRouting :
      HasFigure18RobinsonBoardCanonicalProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles) :
    Figure18RoutedCertificate
      (scaffoldDataOfNatSites
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid).table :=
  l2Component2Figure18RoutedCertificateOfCanonicalProductRoutingPositiveTranslatedBoxes
    canonicalProductRouting
    (Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant.ofIsolatedActiveBoxes
      (by
        simpa [l2Component2Figure18ScaffoldData] using
          l2Component2PositiveTranslatedIsolatedBoxesOfFig13TilesPlane hplane))

/--
L2 component-2 routed Figure 18 certificate from canonical corridor-transmission
routing and a raw Figure 13 plane tiling.
-/
def l2Component2Figure18RoutedCertificateOfCanonicalCorridorRoutingPositiveFig13TilesPlane
    (canonicalCorridorRouting :
      HasFigure18RobinsonBoardCanonicalCorridorProductWitnessRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles) :
    Figure18RoutedCertificate
      (scaffoldDataOfNatSites
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid).table :=
  natSiteFigure18RoutedCertificateOfCanonicalCorridorRoutingPositiveTranslatedBoxes
    canonicalCorridorRouting
    (Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant.ofIsolatedActiveBoxes
      (by
        simpa [l2Component2Figure18ScaffoldData] using
          l2Component2PositiveTranslatedIsolatedBoxesOfFig13TilesPlane hplane))

/--
L2 component-2 routed Figure 18 certificate from canonical decoded combined-site
corridor routing and a raw Figure 13 plane tiling.
-/
def l2Component2Figure18RoutedCertificateOfCanonicalCombinedSiteRoutingPositiveFig13TilesPlane
    (canonicalCombinedSiteRouting :
      HasFigure18RobinsonBoardCanonicalCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles) :
    Figure18RoutedCertificate
      (scaffoldDataOfNatSites
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid).table :=
  natSiteFigure18RoutedCertificateOfCanonicalCombinedSiteRoutingPositiveTranslatedBoxes
    canonicalCombinedSiteRouting
    (Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant.ofIsolatedActiveBoxes
      (by
        simpa [l2Component2Figure18ScaffoldData] using
          l2Component2PositiveTranslatedIsolatedBoxesOfFig13TilesPlane hplane))

/--
L2 component-2 routed Figure 18 certificate from canonical free-site-rectangle
routing and a raw Figure 13 plane tiling.
-/
def l2Component2Figure18RoutedCertificateOfCanonicalFreeSiteRectRoutingPositiveFig13TilesPlane
    (canonicalFreeSiteRectRouting :
      HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles) :
    Figure18RoutedCertificate
      (scaffoldDataOfNatSites
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid).table :=
  natSiteFigure18RoutedCertificateOfCanonicalFreeSiteRectRoutingPositiveTranslatedBoxes
    canonicalFreeSiteRectRouting
    (Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant.ofIsolatedActiveBoxes
      (by
        simpa [l2Component2Figure18ScaffoldData] using
          l2Component2PositiveTranslatedIsolatedBoxesOfFig13TilesPlane hplane))

/--
L2 component-2 routed Figure 18 certificate from tiling-dependent
Robinson-board geometry plus decoded combined-site corridor routing and a raw
Figure 13 plane tiling.
-/
def l2Component2Figure18RoutedCertificateOfGeomCombinedPositiveFig13TilesPlane
    (geometryCombinedSiteRouting :
      HasFigure18RobinsonBoardGeometryTowerCombinedSiteCorridorRoutingForTable
        (scaffoldDataOfNatSites
          l2Component2BlankCandidateActiveSiteSpecs
          l2Component2BlankCandidateSanity.activeSiteSpecs_valid
          0 Quadrant.northeast
          l2Component2BlankCandidateSanity.cornerIndex_valid).table)
    (hplane : TilesPlane fig13Tiles) :
    Figure18RoutedCertificate
      (scaffoldDataOfNatSites
        l2Component2BlankCandidateActiveSiteSpecs
        l2Component2BlankCandidateSanity.activeSiteSpecs_valid
        0 Quadrant.northeast
        l2Component2BlankCandidateSanity.cornerIndex_valid).table :=
  natSiteFigure18RoutedCertificateOfGeomCombinedPositiveTranslatedBoxes
    geometryCombinedSiteRouting
    (Figure18ScaffoldData.HasPositiveTranslatedActiveCornerIndexedBoxInvariant.ofIsolatedActiveBoxes
      (by
        simpa [l2Component2Figure18ScaffoldData] using
          l2Component2PositiveTranslatedIsolatedBoxesOfFig13TilesPlane hplane))

namespace NatSiteRobinsonIndexedBoxScaffoldCertificate

def scaffoldData (C : NatSiteRobinsonIndexedBoxScaffoldCertificate) :
    LayeredFigure18ScaffoldData :=
  C.toScaffoldCertificate.scaffoldData

def figure18ScaffoldData (C : NatSiteRobinsonIndexedBoxScaffoldCertificate) :
    Figure18ScaffoldData :=
  C.toScaffoldCertificate.figure18ScaffoldData

def indexedRoutedCertificate
    (C : NatSiteRobinsonIndexedBoxScaffoldCertificate) :
    C.scaffoldData.IndexedRoutedCertificate :=
  C.toScaffoldCertificate.indexedRoutedCertificate

def indexedRoutedInstance
    (C : NatSiteRobinsonIndexedBoxScaffoldCertificate) :
    Figure18IndexedRoutedInstance :=
  C.toScaffoldCertificate.indexedRoutedInstance

def flexibleInstance (C : NatSiteRobinsonIndexedBoxScaffoldCertificate) :
    Figure18FlexibleInstance :=
  C.toScaffoldCertificate.flexibleInstance

theorem scaffoldData_tiles
    (C : NatSiteRobinsonIndexedBoxScaffoldCertificate) :
    C.scaffoldData.scaffold.tiles = TileSubdivision.subdivideTileSet fig13Tiles :=
  C.toScaffoldCertificate.scaffoldData_tiles

theorem indexedRoutedInstance_presentation_tiles
    (C : NatSiteRobinsonIndexedBoxScaffoldCertificate) :
    C.indexedRoutedInstance.presentation.tiles =
      TileSubdivision.subdivideTileSet fig13Tiles :=
  C.toScaffoldCertificate.indexedRoutedInstance_presentation_tiles

theorem isScaffold (C : NatSiteRobinsonIndexedBoxScaffoldCertificate) :
    IsScaffold C.scaffoldData.scaffold :=
  C.toScaffoldCertificate.isScaffold

theorem indexedRoutedInstance_isScaffold
    (C : NatSiteRobinsonIndexedBoxScaffoldCertificate) :
    IsScaffold C.indexedRoutedInstance.presentation.toScaffold :=
  C.toScaffoldCertificate.indexedRoutedInstance_isScaffold

end NatSiteRobinsonIndexedBoxScaffoldCertificate

end ConcreteData
end LayeredFigure18ScaffoldData
end Figure13Layers
end OllingerRobinson
end LeanWang
