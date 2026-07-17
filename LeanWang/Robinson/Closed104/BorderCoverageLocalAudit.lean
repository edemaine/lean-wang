/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.BorderCoverageOffsets

/-!
# Sound finite route checks inside one substitution macrocell

These checks search only the `8 x 8` quarter-cell macrocell produced by two
substitutions. Cycle sources carry weight zero and retained free-line sources
carry weight one. A successful total-odd target therefore has exactly the path
parity needed by `ProjectsTo`.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace BorderCoverageLocalAudit

open RedCycles RedShadeGraph RedShadeGraphRefinement RedShadeGraphSearch
  RedShadeGraphSearchSoundness
  RedShadeGraphWeightedSearch ShadedFreeLinePatternRefinement
  Signals.FreeCellLocal

set_option maxRecDepth 20000

inductive SourceKind where
  | cycle
  | retained
deriving DecidableEq, Repr

def SourceKind.parity : SourceKind → Bool
  | .cycle => false
  | .retained => true

def localCoordinates : List Nat := [0, 1]

def rowSourcePorts (kind : SourceKind) (x y : Nat) : List Port :=
  match kind with
  | .cycle => [⟨x, y, .west⟩, ⟨x, y, .east⟩]
  | .retained => [⟨x, y, .south⟩, ⟨x, y, .north⟩]

def columnSourcePorts (kind : SourceKind) (x y : Nat) : List Port :=
  match kind with
  | .cycle => [⟨x, y, .south⟩, ⟨x, y, .north⟩]
  | .retained => [⟨x, y, .west⟩, ⟨x, y, .east⟩]

def weightedSparseStarts (parent : Index) (kind : SourceKind)
    (ports : List Port) : List WeightedStart :=
  (ports.filter fun port => portPresent (coarseGrid parent) port).map fun port =>
    ⟨sparsePort port, kind.parity⟩

def rowStarts (parent : Index) (kind : SourceKind)
    (sourceY : Nat) : List WeightedStart :=
  weightedSparseStarts parent kind
    (localCoordinates.flatMap fun x => rowSourcePorts kind x sourceY)

def columnStarts (parent : Index) (kind : SourceKind)
    (sourceX : Nat) : List WeightedStart :=
  weightedSparseStarts parent kind
    (localCoordinates.flatMap fun y => columnSourcePorts kind sourceX y)

theorem mem_rowStarts_retained
    {parent : Index} {sourceY : Nat} {start : WeightedStart}
    (hstart : start ∈ rowStarts parent .retained sourceY) :
    ∃ sourceX, sourceX < 2 ∧ start.parity = true ∧
      ((start.port = sparsePort ⟨sourceX, sourceY, .south⟩ ∧
          portPresent (coarseGrid parent) ⟨sourceX, sourceY, .south⟩ = true) ∨
        (start.port = sparsePort ⟨sourceX, sourceY, .north⟩ ∧
          portPresent (coarseGrid parent) ⟨sourceX, sourceY, .north⟩ = true)) := by
  rw [rowStarts, weightedSparseStarts, List.mem_map] at hstart
  rcases hstart with ⟨port, hport, rfl⟩
  simp only [List.mem_filter] at hport
  rcases hport with ⟨hport, hpresent⟩
  simp only [localCoordinates, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, rowSourcePorts, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hport
  rcases hport with (rfl | rfl) | rfl | rfl
  · exact ⟨0, by decide, rfl, Or.inl ⟨rfl, hpresent⟩⟩
  · exact ⟨0, by decide, rfl, Or.inr ⟨rfl, hpresent⟩⟩
  · exact ⟨1, by decide, rfl, Or.inl ⟨rfl, hpresent⟩⟩
  · exact ⟨1, by decide, rfl, Or.inr ⟨rfl, hpresent⟩⟩

theorem mem_columnStarts_retained
    {parent : Index} {sourceX : Nat} {start : WeightedStart}
    (hstart : start ∈ columnStarts parent .retained sourceX) :
    ∃ sourceY, sourceY < 2 ∧ start.parity = true ∧
      ((start.port = sparsePort ⟨sourceX, sourceY, .west⟩ ∧
          portPresent (coarseGrid parent) ⟨sourceX, sourceY, .west⟩ = true) ∨
        (start.port = sparsePort ⟨sourceX, sourceY, .east⟩ ∧
          portPresent (coarseGrid parent) ⟨sourceX, sourceY, .east⟩ = true)) := by
  rw [columnStarts, weightedSparseStarts, List.mem_map] at hstart
  rcases hstart with ⟨port, hport, rfl⟩
  simp only [List.mem_filter] at hport
  rcases hport with ⟨hport, hpresent⟩
  simp only [localCoordinates, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, columnSourcePorts, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hport
  rcases hport with (rfl | rfl) | rfl | rfl
  · exact ⟨0, by decide, rfl, Or.inl ⟨rfl, hpresent⟩⟩
  · exact ⟨0, by decide, rfl, Or.inr ⟨rfl, hpresent⟩⟩
  · exact ⟨1, by decide, rfl, Or.inl ⟨rfl, hpresent⟩⟩
  · exact ⟨1, by decide, rfl, Or.inr ⟨rfl, hpresent⟩⟩

theorem rowStarts_retained_one_inBounds (parent : Index) :
    ∀ start ∈ rowStarts parent .retained 1, PortInBounds start.port 8 8 := by
  intro start hstart
  rcases mem_rowStarts_retained hstart with
    ⟨sourceX, hsourceX, _, (⟨hport, _⟩ | ⟨hport, _⟩)⟩ <;>
    rw [hport] <;>
    simp [PortInBounds, sparsePort, sparseCoordinate, macroOrigin,
      localCoordinate] <;> omega

theorem columnStarts_retained_one_inBounds (parent : Index) :
    ∀ start ∈ columnStarts parent .retained 1, PortInBounds start.port 8 8 := by
  intro start hstart
  rcases mem_columnStarts_retained hstart with
    ⟨sourceY, hsourceY, _, (⟨hport, _⟩ | ⟨hport, _⟩)⟩ <;>
    rw [hport] <;>
    simp [PortInBounds, sparsePort, sparseCoordinate, macroOrigin,
      localCoordinate] <;> omega

/-- Retained row starts restricted to the old segment at the target `x`. -/
def alignedRowStarts (parent : Index) (sourceY targetX : Nat) :
    List WeightedStart :=
  weightedSparseStarts parent .retained
    (((List.range 2).filter fun sourceX => sparseCoordinate sourceX = targetX).flatMap
      fun sourceX => rowSourcePorts .retained sourceX sourceY)

/-- Retained column starts restricted to the old segment at the target `y`. -/
def alignedColumnStarts (parent : Index) (sourceX targetY : Nat) :
    List WeightedStart :=
  weightedSparseStarts parent .retained
    (((List.range 2).filter fun sourceY => sparseCoordinate sourceY = targetY).flatMap
      fun sourceY => columnSourcePorts .retained sourceX sourceY)

theorem mem_alignedRowStarts
    {parent : Index} {sourceY targetX : Nat} {start : WeightedStart}
    (hstart : start ∈ alignedRowStarts parent sourceY targetX) :
    ∃ sourceX, sourceX < 2 ∧ sparseCoordinate sourceX = targetX ∧
      start.parity = true ∧
      ((start.port = sparsePort ⟨sourceX, sourceY, .south⟩ ∧
          portPresent (coarseGrid parent) ⟨sourceX, sourceY, .south⟩ = true) ∨
        (start.port = sparsePort ⟨sourceX, sourceY, .north⟩ ∧
          portPresent (coarseGrid parent) ⟨sourceX, sourceY, .north⟩ = true)) := by
  rw [alignedRowStarts, weightedSparseStarts, List.mem_map] at hstart
  rcases hstart with ⟨port, hport, rfl⟩
  simp only [List.mem_filter] at hport
  rcases hport with ⟨hport, hpresent⟩
  rw [List.mem_flatMap] at hport
  rcases hport with ⟨sourceX, hsourceX, hport⟩
  simp only [List.mem_filter, List.mem_range] at hsourceX
  have hcoordinate := decide_eq_true_eq.mp hsourceX.2
  simp only [rowSourcePorts, List.mem_cons, List.not_mem_nil, or_false] at hport
  rcases hport with rfl | rfl
  · exact ⟨sourceX, hsourceX.1, hcoordinate, rfl, Or.inl ⟨rfl, hpresent⟩⟩
  · exact ⟨sourceX, hsourceX.1, hcoordinate, rfl, Or.inr ⟨rfl, hpresent⟩⟩

theorem mem_alignedColumnStarts
    {parent : Index} {sourceX targetY : Nat} {start : WeightedStart}
    (hstart : start ∈ alignedColumnStarts parent sourceX targetY) :
    ∃ sourceY, sourceY < 2 ∧ sparseCoordinate sourceY = targetY ∧
      start.parity = true ∧
      ((start.port = sparsePort ⟨sourceX, sourceY, .west⟩ ∧
          portPresent (coarseGrid parent) ⟨sourceX, sourceY, .west⟩ = true) ∨
        (start.port = sparsePort ⟨sourceX, sourceY, .east⟩ ∧
          portPresent (coarseGrid parent) ⟨sourceX, sourceY, .east⟩ = true)) := by
  rw [alignedColumnStarts, weightedSparseStarts, List.mem_map] at hstart
  rcases hstart with ⟨port, hport, rfl⟩
  simp only [List.mem_filter] at hport
  rcases hport with ⟨hport, hpresent⟩
  rw [List.mem_flatMap] at hport
  rcases hport with ⟨sourceY, hsourceY, hport⟩
  simp only [List.mem_filter, List.mem_range] at hsourceY
  have hcoordinate := decide_eq_true_eq.mp hsourceY.2
  simp only [columnSourcePorts, List.mem_cons, List.not_mem_nil, or_false] at hport
  rcases hport with rfl | rfl
  · exact ⟨sourceY, hsourceY.1, hcoordinate, rfl, Or.inl ⟨rfl, hpresent⟩⟩
  · exact ⟨sourceY, hsourceY.1, hcoordinate, rfl, Or.inr ⟨rfl, hpresent⟩⟩

theorem alignedRowStarts_one_inBounds (parent : Index) (targetX : Nat) :
    ∀ start ∈ alignedRowStarts parent 1 targetX, PortInBounds start.port 8 8 := by
  intro start hstart
  rcases mem_alignedRowStarts hstart with
    ⟨sourceX, hsourceX, _, _, (⟨hport, _⟩ | ⟨hport, _⟩)⟩ <;>
    rw [hport] <;>
    simp [PortInBounds, sparsePort, sparseCoordinate, macroOrigin,
      localCoordinate] <;> omega

theorem alignedColumnStarts_one_inBounds (parent : Index) (targetY : Nat) :
    ∀ start ∈ alignedColumnStarts parent 1 targetY, PortInBounds start.port 8 8 := by
  intro start hstart
  rcases mem_alignedColumnStarts hstart with
    ⟨sourceY, hsourceY, _, _, (⟨hport, _⟩ | ⟨hport, _⟩)⟩ <;>
    rw [hport] <;>
    simp [PortInBounds, sparsePort, sparseCoordinate, macroOrigin,
      localCoordinate] <;> omega

def reached (parent : Index) (starts : List WeightedStart)
    (target : Port) : Bool :=
  let nodes := exploreFastWeighted (fineGrid parent) 8 8 1000 starts
  portPresent (fineGrid parent) target &&
    nodes.any fun node => node.parity && decide (node.current = target)

def LocalRoute (parent : Index) (starts : List WeightedStart)
    (target : Port) : Prop :=
  ∃ start ∈ starts,
    Path (fineGrid parent) start.port target (Bool.xor start.parity true) ∧
      portPresent (fineGrid parent) target = true

def BoundedLocalRoute (parent : Index) (starts : List WeightedStart)
    (target : Port) : Prop :=
  ∃ start ∈ starts,
    BoundedPath (fineGrid parent) 8 8 start.port target
      (Bool.xor start.parity true) ∧
      portPresent (fineGrid parent) target = true

def reachedIn (grid : Nat → Nat → Index) (width height fuel : Nat)
    (starts : List WeightedStart) (target : Port) : Bool :=
  let nodes := exploreFastWeighted grid width height fuel starts
  portPresent grid target &&
    nodes.any fun node => node.parity && decide (node.current = target)

def BoundedRouteIn (grid : Nat → Nat → Index) (width height : Nat)
    (starts : List WeightedStart) (target : Port) : Prop :=
  ∃ start ∈ starts,
    BoundedPath grid width height start.port target
      (Bool.xor start.parity true) ∧
    portPresent grid target = true

theorem reachedIn_bounded_sound
    {grid : Nat → Nat → Index} {width height fuel : Nat}
    {starts : List WeightedStart} {target : Port}
    (hstarts : ∀ start ∈ starts, PortInBounds start.port width height)
    (checked : reachedIn grid width height fuel starts target = true) :
    BoundedRouteIn grid width height starts target := by
  simp only [reachedIn, Bool.and_eq_true, List.any_eq_true,
    decide_eq_true_eq] at checked
  rcases checked.2 with ⟨node, hnode, hparity, hcurrent⟩
  rcases exploreFastWeighted_bounded_sound hstarts hnode with
    ⟨start, hstart, path⟩
  refine ⟨start, hstart, ?_, checked.1⟩
  rw [hcurrent] at path
  simpa [hparity] using path

theorem reached_sound
    {parent : Index} {starts : List WeightedStart} {target : Port}
    (checked : reached parent starts target = true) :
    LocalRoute parent starts target := by
  simp only [reached, Bool.and_eq_true, List.any_eq_true,
    decide_eq_true_eq] at checked
  rcases checked.2 with ⟨node, hnode, hparity, hcurrent⟩
  rcases exploreFastWeighted_sound hnode with ⟨start, hstart, _horigin, path⟩
  refine ⟨start, hstart, ?_, checked.1⟩
  rw [hcurrent] at path
  simpa [hparity] using path

theorem reached_bounded_sound
    {parent : Index} {starts : List WeightedStart} {target : Port}
    (hstarts : ∀ start ∈ starts, PortInBounds start.port 8 8)
    (checked : reached parent starts target = true) :
    BoundedLocalRoute parent starts target := by
  simp only [reached, Bool.and_eq_true, List.any_eq_true,
    decide_eq_true_eq] at checked
  rcases checked.2 with ⟨node, hnode, hparity, hcurrent⟩
  rcases exploreFastWeighted_bounded_sound hstarts hnode with
    ⟨start, hstart, path⟩
  refine ⟨start, hstart, ?_, checked.1⟩
  rw [hcurrent] at path
  simpa [hparity] using path

def rowCheck (parent : Index) (kind : SourceKind)
    (sourceY targetY : Nat) : Bool :=
  let starts := rowStarts parent kind sourceY
  (List.range 8).all fun x =>
    let required := (Signals.verticalInterior?
      (componentAt (fineGrid parent) x targetY)
      (quadrantAt x targetY)).isSome
    !required ||
      reached parent starts ⟨x, targetY, .south⟩ ||
      reached parent starts ⟨x, targetY, .north⟩

def columnCheck (parent : Index) (kind : SourceKind)
    (sourceX targetX : Nat) : Bool :=
  let starts := columnStarts parent kind sourceX
  (List.range 8).all fun y =>
    let required := (Signals.horizontalInterior?
      (componentAt (fineGrid parent) targetX y)
      (quadrantAt targetX y)).isSome
    !required ||
      reached parent starts ⟨targetX, y, .west⟩ ||
      reached parent starts ⟨targetX, y, .east⟩

def alignedRowCheck (parent : Index) (sourceY targetY : Nat) : Bool :=
  (List.range 8).all fun x =>
    let required := (Signals.verticalInterior?
      (componentAt (fineGrid parent) x targetY)
      (quadrantAt x targetY)).isSome
    !required ||
      reached parent (alignedRowStarts parent sourceY x) ⟨x, targetY, .south⟩ ||
      reached parent (alignedRowStarts parent sourceY x) ⟨x, targetY, .north⟩

def alignedColumnCheck (parent : Index) (sourceX targetX : Nat) : Bool :=
  (List.range 8).all fun y =>
    let required := (Signals.horizontalInterior?
      (componentAt (fineGrid parent) targetX y)
      (quadrantAt targetX y)).isSome
    !required ||
      reached parent (alignedColumnStarts parent sourceX y) ⟨targetX, y, .west⟩ ||
      reached parent (alignedColumnStarts parent sourceX y) ⟨targetX, y, .east⟩

set_option linter.flexible false in
theorem rowCheck_sound
    {parent : Index} {kind : SourceKind} {sourceY targetY : Nat}
    (checked : rowCheck parent kind sourceY targetY = true) :
    ∀ x, x < 8 →
      Signals.verticalInterior?
        (componentAt (fineGrid parent) x targetY)
        (quadrantAt x targetY) ≠ none →
      LocalRoute parent (rowStarts parent kind sourceY)
          ⟨x, targetY, .south⟩ ∨
        LocalRoute parent (rowStarts parent kind sourceY)
          ⟨x, targetY, .north⟩ := by
  simp only [rowCheck, List.all_eq_true, List.mem_range] at checked
  intro x hx interior
  have covered := checked x hx
  have required : (Signals.verticalInterior?
      (componentAt (fineGrid parent) x targetY)
      (quadrantAt x targetY)).isSome = true :=
    Option.isSome_iff_ne_none.mpr interior
  simp only [required, Bool.not_true, Bool.false_or,
    Bool.or_eq_true] at covered
  rcases covered with covered | covered
  · exact Or.inl (reached_sound covered)
  · exact Or.inr (reached_sound covered)

set_option linter.flexible false in
theorem columnCheck_sound
    {parent : Index} {kind : SourceKind} {sourceX targetX : Nat}
    (checked : columnCheck parent kind sourceX targetX = true) :
    ∀ y, y < 8 →
      Signals.horizontalInterior?
        (componentAt (fineGrid parent) targetX y)
        (quadrantAt targetX y) ≠ none →
      LocalRoute parent (columnStarts parent kind sourceX)
          ⟨targetX, y, .west⟩ ∨
        LocalRoute parent (columnStarts parent kind sourceX)
          ⟨targetX, y, .east⟩ := by
  simp only [columnCheck, List.all_eq_true, List.mem_range] at checked
  intro y hy interior
  have covered := checked y hy
  have required : (Signals.horizontalInterior?
      (componentAt (fineGrid parent) targetX y)
      (quadrantAt targetX y)).isSome = true :=
    Option.isSome_iff_ne_none.mpr interior
  simp only [required, Bool.not_true, Bool.false_or,
    Bool.or_eq_true] at covered
  rcases covered with covered | covered
  · exact Or.inl (reached_sound covered)
  · exact Or.inr (reached_sound covered)

set_option linter.flexible false in
theorem retainedRowCheck_bounded_sound
    {parent : Index} {targetY : Nat}
    (checked : rowCheck parent .retained 1 targetY = true) :
    ∀ x, x < 8 →
      Signals.verticalInterior?
        (componentAt (fineGrid parent) x targetY)
        (quadrantAt x targetY) ≠ none →
      BoundedLocalRoute parent (rowStarts parent .retained 1)
          ⟨x, targetY, .south⟩ ∨
        BoundedLocalRoute parent (rowStarts parent .retained 1)
          ⟨x, targetY, .north⟩ := by
  simp only [rowCheck, List.all_eq_true, List.mem_range] at checked
  intro x hx interior
  have covered := checked x hx
  have required : (Signals.verticalInterior?
      (componentAt (fineGrid parent) x targetY)
      (quadrantAt x targetY)).isSome = true :=
    Option.isSome_iff_ne_none.mpr interior
  simp only [required, Bool.not_true, Bool.false_or,
    Bool.or_eq_true] at covered
  rcases covered with covered | covered
  · exact Or.inl (reached_bounded_sound
      (rowStarts_retained_one_inBounds parent) covered)
  · exact Or.inr (reached_bounded_sound
      (rowStarts_retained_one_inBounds parent) covered)

set_option linter.flexible false in
theorem retainedColumnCheck_bounded_sound
    {parent : Index} {targetX : Nat}
    (checked : columnCheck parent .retained 1 targetX = true) :
    ∀ y, y < 8 →
      Signals.horizontalInterior?
        (componentAt (fineGrid parent) targetX y)
        (quadrantAt targetX y) ≠ none →
      BoundedLocalRoute parent (columnStarts parent .retained 1)
          ⟨targetX, y, .west⟩ ∨
        BoundedLocalRoute parent (columnStarts parent .retained 1)
          ⟨targetX, y, .east⟩ := by
  simp only [columnCheck, List.all_eq_true, List.mem_range] at checked
  intro y hy interior
  have covered := checked y hy
  have required : (Signals.horizontalInterior?
      (componentAt (fineGrid parent) targetX y)
      (quadrantAt targetX y)).isSome = true :=
    Option.isSome_iff_ne_none.mpr interior
  simp only [required, Bool.not_true, Bool.false_or,
    Bool.or_eq_true] at covered
  rcases covered with covered | covered
  · exact Or.inl (reached_bounded_sound
      (columnStarts_retained_one_inBounds parent) covered)
  · exact Or.inr (reached_bounded_sound
      (columnStarts_retained_one_inBounds parent) covered)

set_option linter.flexible false in
theorem alignedRowCheck_bounded_sound
    {parent : Index} {targetY : Nat}
    (checked : alignedRowCheck parent 1 targetY = true) :
    ∀ x, x < 8 →
      Signals.verticalInterior?
        (componentAt (fineGrid parent) x targetY)
        (quadrantAt x targetY) ≠ none →
      BoundedLocalRoute parent (alignedRowStarts parent 1 x)
          ⟨x, targetY, .south⟩ ∨
        BoundedLocalRoute parent (alignedRowStarts parent 1 x)
          ⟨x, targetY, .north⟩ := by
  simp only [alignedRowCheck, List.all_eq_true, List.mem_range] at checked
  intro x hx interior
  have covered := checked x hx
  have required : (Signals.verticalInterior?
      (componentAt (fineGrid parent) x targetY)
      (quadrantAt x targetY)).isSome = true :=
    Option.isSome_iff_ne_none.mpr interior
  simp only [required, Bool.not_true, Bool.false_or,
    Bool.or_eq_true] at covered
  rcases covered with covered | covered
  · exact Or.inl (reached_bounded_sound
      (alignedRowStarts_one_inBounds parent x) covered)
  · exact Or.inr (reached_bounded_sound
      (alignedRowStarts_one_inBounds parent x) covered)

set_option linter.flexible false in
theorem alignedColumnCheck_bounded_sound
    {parent : Index} {targetX : Nat}
    (checked : alignedColumnCheck parent 1 targetX = true) :
    ∀ y, y < 8 →
      Signals.horizontalInterior?
        (componentAt (fineGrid parent) targetX y)
        (quadrantAt targetX y) ≠ none →
      BoundedLocalRoute parent (alignedColumnStarts parent 1 y)
          ⟨targetX, y, .west⟩ ∨
        BoundedLocalRoute parent (alignedColumnStarts parent 1 y)
          ⟨targetX, y, .east⟩ := by
  simp only [alignedColumnCheck, List.all_eq_true, List.mem_range] at checked
  intro y hy interior
  have covered := checked y hy
  have required : (Signals.horizontalInterior?
      (componentAt (fineGrid parent) targetX y)
      (quadrantAt targetX y)).isSome = true :=
    Option.isSome_iff_ne_none.mpr interior
  simp only [required, Bool.not_true, Bool.false_or,
    Bool.or_eq_true] at covered
  rcases covered with covered | covered
  · exact Or.inl (reached_bounded_sound
      (alignedColumnStarts_one_inBounds parent y) covered)
  · exact Or.inr (reached_bounded_sound
      (alignedColumnStarts_one_inBounds parent y) covered)

/-- Whether a coarse row or column contributes no source, a board side, or a retained free line. -/
inductive LineKind where
  | none
  | cycle
  | retained
deriving DecidableEq, Repr

def rowStartsOfKind (parent : Index) (kind : LineKind) (sourceY : Nat) :
    List WeightedStart :=
  match kind with
  | .none => []
  | .cycle => rowStarts parent .cycle sourceY
  | .retained => rowStarts parent .retained sourceY

def columnStartsOfKind (parent : Index) (kind : LineKind) (sourceX : Nat) :
    List WeightedStart :=
  match kind with
  | .none => []
  | .cycle => columnStarts parent .cycle sourceX
  | .retained => columnStarts parent .retained sourceX

/-- Sources visible in one macrocell are the union of its coarse row and column sources. -/
def crossStarts (parent : Index) (rowKind columnKind : LineKind)
    (sourceX sourceY : Nat) : List WeightedStart :=
  rowStartsOfKind parent rowKind sourceY ++
    columnStartsOfKind parent columnKind sourceX

def crossRowCheck (parent : Index) (rowKind columnKind : LineKind)
    (sourceX sourceY targetY : Nat) : Bool :=
  let starts := crossStarts parent rowKind columnKind sourceX sourceY
  (List.range 8).all fun x =>
    let required := (Signals.verticalInterior?
      (componentAt (fineGrid parent) x targetY)
      (quadrantAt x targetY)).isSome
    !required ||
      reached parent starts ⟨x, targetY, .south⟩ ||
      reached parent starts ⟨x, targetY, .north⟩

def crossColumnCheck (parent : Index) (rowKind columnKind : LineKind)
    (sourceX sourceY targetX : Nat) : Bool :=
  let starts := crossStarts parent rowKind columnKind sourceX sourceY
  (List.range 8).all fun y =>
    let required := (Signals.horizontalInterior?
      (componentAt (fineGrid parent) targetX y)
      (quadrantAt targetX y)).isSome
    !required ||
      reached parent starts ⟨targetX, y, .west⟩ ||
      reached parent starts ⟨targetX, y, .east⟩

set_option linter.flexible false in
theorem crossRowCheck_sound
    {parent : Index} {rowKind columnKind : LineKind}
    {sourceX sourceY targetY : Nat}
    (checked : crossRowCheck parent rowKind columnKind sourceX sourceY targetY = true) :
    ∀ x, x < 8 →
      Signals.verticalInterior?
        (componentAt (fineGrid parent) x targetY)
        (quadrantAt x targetY) ≠ none →
      LocalRoute parent (crossStarts parent rowKind columnKind sourceX sourceY)
          ⟨x, targetY, .south⟩ ∨
        LocalRoute parent (crossStarts parent rowKind columnKind sourceX sourceY)
          ⟨x, targetY, .north⟩ := by
  simp only [crossRowCheck, List.all_eq_true, List.mem_range] at checked
  intro x hx interior
  have covered := checked x hx
  have required : (Signals.verticalInterior?
      (componentAt (fineGrid parent) x targetY)
      (quadrantAt x targetY)).isSome = true :=
    Option.isSome_iff_ne_none.mpr interior
  simp only [required, Bool.not_true, Bool.false_or, Bool.or_eq_true] at covered
  rcases covered with covered | covered
  · exact Or.inl (reached_sound covered)
  · exact Or.inr (reached_sound covered)

set_option linter.flexible false in
theorem crossColumnCheck_sound
    {parent : Index} {rowKind columnKind : LineKind}
    {sourceX sourceY targetX : Nat}
    (checked : crossColumnCheck parent rowKind columnKind sourceX sourceY targetX = true) :
    ∀ y, y < 8 →
      Signals.horizontalInterior?
        (componentAt (fineGrid parent) targetX y)
        (quadrantAt targetX y) ≠ none →
      LocalRoute parent (crossStarts parent rowKind columnKind sourceX sourceY)
          ⟨targetX, y, .west⟩ ∨
        LocalRoute parent (crossStarts parent rowKind columnKind sourceX sourceY)
          ⟨targetX, y, .east⟩ := by
  simp only [crossColumnCheck, List.all_eq_true, List.mem_range] at checked
  intro y hy interior
  have covered := checked y hy
  have required : (Signals.horizontalInterior?
      (componentAt (fineGrid parent) targetX y)
      (quadrantAt targetX y)).isSome = true :=
    Option.isSome_iff_ne_none.mpr interior
  simp only [required, Bool.not_true, Bool.false_or, Bool.or_eq_true] at covered
  rcases covered with covered | covered
  · exact Or.inl (reached_sound covered)
  · exact Or.inr (reached_sound covered)

end BorderCoverageLocalAudit
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
