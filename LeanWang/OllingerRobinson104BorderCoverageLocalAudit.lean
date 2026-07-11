/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104BorderCoverageLocalStep

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

def reached (parent : Index) (starts : List WeightedStart)
    (target : Port) : Bool :=
  let nodes := exploreFastWeightedReach (fineGrid parent) 8 8 1000 starts
  portPresent (fineGrid parent) target &&
    nodes.any fun node => node.parity && decide (node.current = target)

def LocalRoute (parent : Index) (starts : List WeightedStart)
    (target : Port) : Prop :=
  ∃ start ∈ starts,
    Path (fineGrid parent) start.port target (Bool.xor start.parity true) ∧
      portPresent (fineGrid parent) target = true

theorem reached_sound
    {parent : Index} {starts : List WeightedStart} {target : Port}
    (checked : reached parent starts target = true) :
    LocalRoute parent starts target := by
  simp only [reached, Bool.and_eq_true, List.any_eq_true,
    decide_eq_true_eq] at checked
  rcases checked.2 with ⟨node, hnode, hparity, hcurrent⟩
  rcases exploreFastWeightedReach_sound hnode with ⟨start, hstart, path⟩
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

end BorderCoverageLocalAudit
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
