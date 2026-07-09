/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinsonFigure13Data

/-!
Finite recognizability checks for the audited Figure 16 substitution.

Unlike `Figure16.Symbol.tileSet`, which only checks the internal seams of the
displayed substitution blocks, this file works with the actual 368 Figure 18
quarter-sites built from the 92 Figure 13 tiles.  A child site's quadrant fixes
its offset inside a `2 x 2` substituted parent.  We can therefore enumerate the
parent sites whose audited expansion produces that child and test whether the
parent is locally recognizable.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace LayeredFigure18ScaffoldData
namespace ConcreteData

/-- Horizontal offset selected by a child Figure 18 quadrant. -/
def childColumn (site : Figure18Site) : Fin 2 :=
  quadrantColumn site.quadrant

/-- Vertical offset selected by a child Figure 18 quadrant. -/
def childRow (site : Figure18Site) : Fin 2 :=
  quadrantRow site.quadrant

/-- Does the audited Figure 16 expansion of `source` produce `target`? -/
def expandsToBool (source target : Figure18Site) : Bool :=
  siteMatchesSymbolsBool
    ((thinBlockAtSite source).entry (childColumn target) (childRow target))
    ((thickBlockAtSite source).entry (childColumn target) (childRow target))
    ((blackBlockAtSite source).entry (childColumn target) (childRow target))
    target.quadrant target

/-- All audited parent sites whose Figure 16 expansion produces `target`. -/
def parentCandidates (target : Figure18Site) : List Figure18Site :=
  Figure18Site.all.filter fun source => expandsToBool source target

/-- Number of audited parent sites producing a target site. -/
def parentCandidateCount (target : Figure18Site) : Nat :=
  (parentCandidates target).length

/-- Diagnostic list of targets that do not have exactly one audited parent. -/
def nonUniqueParentTargets : List (Figure18Site × Nat) :=
  (Figure18Site.all.filter fun target => parentCandidateCount target != 1).map
    fun target => (target, parentCandidateCount target)

theorem mem_parentCandidates_iff {source target : Figure18Site} :
    source ∈ parentCandidates target ↔
      expandsToBool source target = true := by
  simp [parentCandidates, Figure18Site.mem_all]

/-- Canonical parent site used to test a parent tile index. -/
def parentIndexSite (index : Fin 92) : Figure18Site where
  index := index
  quadrant := .southwest

/-- Does the audited expansion of a parent tile index produce `target`? -/
def parentIndexExpandsToBool (index : Fin 92) (target : Figure18Site) : Bool :=
  expandsToBool (parentIndexSite index) target

/-- Parent Figure 13 tile indices whose audited expansion produces `target`. -/
def parentIndexCandidates (target : Figure18Site) : List (Fin 92) :=
  (List.finRange 92).filter fun index => parentIndexExpandsToBool index target

def parentIndexCandidateCount (target : Figure18Site) : Nat :=
  (parentIndexCandidates target).length

theorem mem_parentIndexCandidates_iff {index : Fin 92} {target : Figure18Site} :
    index ∈ parentIndexCandidates target ↔
      expandsToBool (parentIndexSite index) target = true := by
  simp [parentIndexCandidates, parentIndexExpandsToBool]

/-- Histogram of radius-zero parent-index candidate counts. -/
def parentIndexCandidateCountHistogram : List (Nat × Nat) :=
  (List.range 93).filterMap fun count =>
    let targets := Figure18Site.all.filter fun target =>
      parentIndexCandidateCount target == count
    if targets.isEmpty then none else some (count, targets.length)

set_option linter.style.nativeDecide false in
set_option maxRecDepth 20000 in
theorem parentIndexCandidateCountHistogram_eq :
    parentIndexCandidateCountHistogram =
      [(1, 20), (2, 82), (3, 51), (4, 36), (5, 15),
        (7, 28), (8, 48), (24, 48), (40, 40)] := by
  native_decide

/-- Radius-zero parent-index recognition fails for the audited substitution. -/
def allTargetsHaveUniqueParentIndexBool : Bool :=
  Figure18Site.all.all fun target =>
    decide (parentIndexCandidateCount target = 1)

set_option linter.style.nativeDecide false in
set_option maxRecDepth 20000 in
theorem allTargetsHaveUniqueParentIndexBool_eq_false :
    allTargetsHaveUniqueParentIndexBool = false := by
  native_decide

/-- Despite the ambiguity, every child site has at least one parent index. -/
def allTargetsHaveParentIndexBool : Bool :=
  Figure18Site.all.all fun target =>
    !(parentIndexCandidates target).isEmpty

set_option linter.style.nativeDecide false in
set_option maxRecDepth 20000 in
theorem allTargetsHaveParentIndexBool_eq_true :
    allTargetsHaveParentIndexBool = true := by
  native_decide

theorem parentIndexCandidates_ne_nil (target : Figure18Site) :
    parentIndexCandidates target ≠ [] := by
  have htarget := List.all_eq_true.1 allTargetsHaveParentIndexBool_eq_true
    target (Figure18Site.mem_all target)
  intro hnil
  simp [hnil] at htarget

/-- Does a pair of L2 summand symbols overlay to the requested thick component? -/
def thickOverlayBool
    (first second : Figure16.Symbol) (target : Figure16.Thick) : Bool :=
  match first, second with
  | .blank, .thick component => decide (component = target)
  | .thick component, .blank => decide (component = target)
  | .line firstLine, .line secondLine =>
      match target.lineSum? with
      | none => false
      | some sum =>
          decide ((sum.first = firstLine ∧ sum.second = secondLine) ∨
            (sum.first = secondLine ∧ sum.second = firstLine))
  | _, _ => false

/-- A complete thin/thick/black component triple for one displayed tile. -/
abbrev ComponentTriple := Figure16.Thin × Figure16.Thick × Figure16.Black

/-- All 400 component triples before imposing the Figure 13 tile-list restriction. -/
def allComponentTriples : List ComponentTriple :=
  Figure16.Thin.all.flatMap fun thin =>
    Figure16.Thick.all.flatMap fun thick =>
      Figure16.Black.all.map fun black => (thin, thick, black)

/-- Component triple transcribed at a Figure 13 tile index. -/
def componentTripleAt (index : Fin 92) : ComponentTriple :=
  (thinComponentAt index, thickComponentAt index, blackComponentAt index)

/-- Does `child` equal the component triple produced at one parent quadrant? -/
def componentTripleChildMatchesBool
    (parent : ComponentTriple) (quadrant : Quadrant) (child : ComponentTriple) : Bool :=
  decide (Figure16.Symbol.thin child.1 =
    Figure16.phiL1Star.entry (quadrantColumn quadrant) (quadrantRow quadrant)) &&
  thickOverlayBool
    ((Figure16.phiL2Component1 parent.1).entry
      (quadrantColumn quadrant) (quadrantRow quadrant))
    ((Figure16.phiL2Component2 parent.2.1).entry
      (quadrantColumn quadrant) (quadrantRow quadrant))
    child.2.1 &&
  decide (Figure16.Symbol.black child.2.2 =
    (Figure16.phiL3 parent.2.2).entry
      (quadrantColumn quadrant) (quadrantRow quadrant))

/-- Figure 13-indexed specialization of `componentTripleChildMatchesBool`. -/
def childComponentMatchesBool
    (parent : Fin 92) (quadrant : Quadrant) (child : ComponentTriple) : Bool :=
  componentTripleChildMatchesBool (componentTripleAt parent) quadrant child

/-- Does an existing Figure 13 tile have the produced child component triple? -/
def childMatchesBool (parent : Fin 92) (quadrant : Quadrant) (child : Fin 92) : Bool :=
  childComponentMatchesBool parent quadrant (componentTripleAt child)

/-- Child tile indices produced at one quadrant of an audited parent expansion. -/
def childIndexCandidates (parent : Fin 92) (quadrant : Quadrant) : List (Fin 92) :=
  (List.finRange 92).filter fun child => childMatchesBool parent quadrant child

theorem mem_childIndexCandidates_iff
    {parent child : Fin 92} {quadrant : Quadrant} :
    child ∈ childIndexCandidates parent quadrant ↔
      childMatchesBool parent quadrant child = true := by
  simp [childIndexCandidates]

/-- Histogram of child-candidate counts over all 92 parents and four quadrants. -/
def childIndexCandidateCountHistogram : List (Nat × Nat) :=
  (List.range 93).filterMap fun count =>
    let cases := (List.finRange 92).flatMap fun parent =>
      Quadrant.all.filter fun quadrant =>
        (childIndexCandidates parent quadrant).length == count
    if cases.isEmpty then none else some (count, cases.length)

set_option linter.style.nativeDecide false in
set_option maxRecDepth 20000 in
theorem childIndexCandidateCountHistogram_eq :
    childIndexCandidateCountHistogram = [(0, 12), (1, 356)] := by
  native_decide

/-- Parent/quadrant pairs whose produced component triple is absent from Figure 13. -/
def missingChildParentQuadrants : List (Nat × Quadrant) :=
  (List.finRange 92).flatMap fun parent =>
    (Quadrant.all.filter fun quadrant =>
      (childIndexCandidates parent quadrant).isEmpty).map fun quadrant =>
        (parent.val, quadrant)

set_option linter.style.nativeDecide false in
set_option maxRecDepth 20000 in
theorem missingChildParentQuadrants_eq :
    missingChildParentQuadrants =
      [(68, .southwest), (69, .southwest), (70, .southwest),
        (71, .southwest), (72, .southwest), (73, .southwest),
        (74, .southwest), (75, .southwest), (76, .southwest),
        (77, .southwest), (78, .southwest), (79, .southwest)] := by
  native_decide

/-- Distinct component triples in the human Figure 13 table. -/
def currentComponentTriples : List ComponentTriple :=
  ((List.finRange 92).map componentTripleAt).eraseDups

/-- Distinct component triples produced by one substitution step. -/
def substitutionImageComponentTriples : List ComponentTriple :=
  ((List.finRange 92).flatMap fun parent =>
    Quadrant.all.flatMap fun quadrant =>
      allComponentTriples.filter fun child =>
        childComponentMatchesBool parent quadrant child).eraseDups

/-- Current triples together with all triples produced in one substitution step. -/
def oneStepClosedComponentTriples : List ComponentTriple :=
  (currentComponentTriples ++ substitutionImageComponentTriples).eraseDups

/-- Substitution image of an arbitrary finite component-triple alphabet. -/
def substitutionImageOf (parents : List ComponentTriple) : List ComponentTriple :=
  (parents.flatMap fun parent =>
    Quadrant.all.flatMap fun quadrant =>
      allComponentTriples.filter fun child =>
        componentTripleChildMatchesBool parent quadrant child).eraseDups

/-- Every cell of the 104-triple alphabet has a unique child in that alphabet. -/
def oneStepClosedUniqueChildrenBool : Bool :=
  oneStepClosedComponentTriples.all fun parent =>
    Quadrant.all.all fun quadrant =>
      decide (((oneStepClosedComponentTriples.filter fun child =>
        componentTripleChildMatchesBool parent quadrant child).length) = 1)

set_option linter.style.nativeDecide false in
set_option maxRecDepth 20000 in
theorem oneStepClosedUniqueChildrenBool_eq_true :
    oneStepClosedUniqueChildrenBool = true := by
  native_decide

/-- The substitution image of the 104-triple alphabet stays inside it. -/
def oneStepClosedUnderSubstitutionBool : Bool :=
  (substitutionImageOf oneStepClosedComponentTriples).all fun child =>
    decide (child ∈ oneStepClosedComponentTriples)

set_option linter.style.nativeDecide false in
set_option maxRecDepth 20000 in
theorem oneStepClosedUnderSubstitutionBool_eq_true :
    oneStepClosedUnderSubstitutionBool = true := by
  native_decide

set_option linter.style.nativeDecide false in
set_option maxRecDepth 20000 in
theorem componentTripleCounts_eq :
    (currentComponentTriples.length,
      substitutionImageComponentTriples.length,
      oneStepClosedComponentTriples.length,
      (substitutionImageOf oneStepClosedComponentTriples).length) =
        (92, 103, 104, 103) := by
  native_decide

/-- One quadrant-aligned `2 x 2` block of child Figure 18 sites. -/
structure AlignedChildBlock where
  southwest : Figure18Site
  southeast : Figure18Site
  northwest : Figure18Site
  northeast : Figure18Site
deriving DecidableEq, Repr

namespace AlignedChildBlock

/-- The four child sites have the expected substitution offsets. -/
def QuadrantsMatch (block : AlignedChildBlock) : Prop :=
  block.southwest.quadrant = .southwest ∧
    block.southeast.quadrant = .southeast ∧
    block.northwest.quadrant = .northwest ∧
    block.northeast.quadrant = .northeast

/-- All four internal Figure 18 site edges of the child block match. -/
def Compatible (block : AlignedChildBlock) : Prop :=
  Figure18Site.hCompatible block.southwest block.southeast = true ∧
    Figure18Site.hCompatible block.northwest block.northeast = true ∧
    Figure18Site.vCompatible block.southwest block.northwest = true ∧
    Figure18Site.vCompatible block.southeast block.northeast = true

instance (block : AlignedChildBlock) : Decidable block.QuadrantsMatch := by
  unfold QuadrantsMatch
  infer_instance

instance (block : AlignedChildBlock) : Decidable block.Compatible := by
  unfold Compatible
  infer_instance

end AlignedChildBlock

def sitesInQuadrant (quadrant : Quadrant) : List Figure18Site :=
  Figure18Site.all.filter fun site => decide (site.quadrant = quadrant)

/-- All locally compatible, quadrant-aligned `2 x 2` child blocks. -/
def alignedCompatibleChildBlocks : List AlignedChildBlock :=
  (sitesInQuadrant .southwest).flatMap fun southwest =>
    ((sitesInQuadrant .southeast).filter fun southeast =>
      Figure18Site.hCompatible southwest southeast).flatMap fun southeast =>
      ((sitesInQuadrant .northwest).filter fun northwest =>
        Figure18Site.vCompatible southwest northwest).flatMap fun northwest =>
        ((sitesInQuadrant .northeast).filter fun northeast =>
          Figure18Site.hCompatible northwest northeast &&
            Figure18Site.vCompatible southeast northeast).map fun northeast =>
          { southwest, southeast, northwest, northeast }

theorem mem_alignedCompatibleChildBlocks_iff (block : AlignedChildBlock) :
    block ∈ alignedCompatibleChildBlocks ↔
      block.QuadrantsMatch ∧ block.Compatible := by
  rcases block with ⟨southwest, southeast, northwest, northeast⟩
  simp [alignedCompatibleChildBlocks, sitesInQuadrant,
    AlignedChildBlock.QuadrantsMatch, AlignedChildBlock.Compatible,
    Figure18Site.mem_all, Bool.and_eq_true, and_assoc, and_left_comm, and_comm]

/-- Parent tile indices consistent with all four sites of an aligned child block. -/
def commonParentIndexCandidates (block : AlignedChildBlock) : List (Fin 92) :=
  (List.finRange 92).filter fun index =>
    parentIndexExpandsToBool index block.southwest &&
      parentIndexExpandsToBool index block.southeast &&
      parentIndexExpandsToBool index block.northwest &&
      parentIndexExpandsToBool index block.northeast

def commonParentIndexCandidateCount (block : AlignedChildBlock) : Nat :=
  (commonParentIndexCandidates block).length

/-- Finite radius-one recognizability test on all aligned compatible child blocks. -/
def allAlignedCompatibleBlocksHaveUniqueParentBool : Bool :=
  alignedCompatibleChildBlocks.all fun block =>
    decide (commonParentIndexCandidateCount block = 1)

/-- Number of quadrant-aligned blocks admitted by the current raw edge transcription. -/
def alignedCompatibleChildBlockCount : Nat :=
  alignedCompatibleChildBlocks.length

set_option linter.style.nativeDecide false in
set_option maxRecDepth 20000 in
theorem alignedCompatibleChildBlockCount_eq :
    alignedCompatibleChildBlockCount = 92 := by
  native_decide

/--
Do all currently admitted aligned blocks consist of the four quarters of one
raw Figure 13 tile? This diagnostic distinguishes internal subdivision seams
from genuine adjacency between different Figure 13 tiles.
-/
def allAlignedCompatibleBlocksHaveSameIndexBool : Bool :=
  alignedCompatibleChildBlocks.all fun block =>
    decide (block.southwest.index = block.southeast.index ∧
      block.southwest.index = block.northwest.index ∧
      block.southwest.index = block.northeast.index)

set_option linter.style.nativeDecide false in
set_option maxRecDepth 20000 in
theorem allAlignedCompatibleBlocksHaveSameIndexBool_eq_true :
    allAlignedCompatibleBlocksHaveSameIndexBool = true := by
  native_decide

set_option linter.style.nativeDecide false in
set_option maxRecDepth 20000 in
theorem allAlignedCompatibleBlocksHaveUniqueParentBool_eq_true :
    allAlignedCompatibleBlocksHaveUniqueParentBool = true := by
  native_decide

theorem commonParentIndexCandidateCount_eq_one
    {block : AlignedChildBlock}
    (hquadrants : block.QuadrantsMatch) (hcompatible : block.Compatible) :
    commonParentIndexCandidateCount block = 1 := by
  have hmem : block ∈ alignedCompatibleChildBlocks :=
    (mem_alignedCompatibleChildBlocks_iff block).2 ⟨hquadrants, hcompatible⟩
  have hblock := List.all_eq_true.1
    allAlignedCompatibleBlocksHaveUniqueParentBool_eq_true block hmem
  exact of_decide_eq_true hblock

theorem mem_commonParentIndexCandidates_iff
    {index : Fin 92} {block : AlignedChildBlock} :
    index ∈ commonParentIndexCandidates block ↔
      parentIndexExpandsToBool index block.southwest = true ∧
      parentIndexExpandsToBool index block.southeast = true ∧
      parentIndexExpandsToBool index block.northwest = true ∧
      parentIndexExpandsToBool index block.northeast = true := by
  simp [commonParentIndexCandidates, Bool.and_eq_true, and_assoc]

/-- Executable parent decoder for an aligned child block. -/
def blockParentIndex (block : AlignedChildBlock) : Fin 92 :=
  (commonParentIndexCandidates block).headD block.southwest.index

theorem commonParentIndexCandidates_eq_singleton
    {block : AlignedChildBlock}
    (hquadrants : block.QuadrantsMatch) (hcompatible : block.Compatible) :
    commonParentIndexCandidates block = [blockParentIndex block] := by
  have hlength := commonParentIndexCandidateCount_eq_one hquadrants hcompatible
  unfold commonParentIndexCandidateCount at hlength
  cases h : commonParentIndexCandidates block with
  | nil =>
      simp [h] at hlength
  | cons index tail =>
      cases tail with
      | nil =>
          simp [blockParentIndex, h]
      | cons other tail =>
          simp [h] at hlength

theorem blockParentIndex_expandsTo
    {block : AlignedChildBlock}
    (hquadrants : block.QuadrantsMatch) (hcompatible : block.Compatible) :
    parentIndexExpandsToBool (blockParentIndex block) block.southwest = true ∧
      parentIndexExpandsToBool (blockParentIndex block) block.southeast = true ∧
      parentIndexExpandsToBool (blockParentIndex block) block.northwest = true ∧
      parentIndexExpandsToBool (blockParentIndex block) block.northeast = true := by
  rw [← mem_commonParentIndexCandidates_iff]
  simp [commonParentIndexCandidates_eq_singleton hquadrants hcompatible]

theorem eq_blockParentIndex_of_expandsTo
    {index : Fin 92} {block : AlignedChildBlock}
    (hquadrants : block.QuadrantsMatch) (hcompatible : block.Compatible)
    (hindex :
      parentIndexExpandsToBool index block.southwest = true ∧
      parentIndexExpandsToBool index block.southeast = true ∧
      parentIndexExpandsToBool index block.northwest = true ∧
      parentIndexExpandsToBool index block.northeast = true) :
    index = blockParentIndex block := by
  have hmem : index ∈ commonParentIndexCandidates block :=
    mem_commonParentIndexCandidates_iff.2 hindex
  simpa [commonParentIndexCandidates_eq_singleton hquadrants hcompatible] using hmem

/-- Proposition-level local recognizability of the audited Figure 16 substitution. -/
theorem existsUnique_blockParentIndex
    (block : AlignedChildBlock)
    (hquadrants : block.QuadrantsMatch) (hcompatible : block.Compatible) :
    ∃! index : Fin 92,
      parentIndexExpandsToBool index block.southwest = true ∧
      parentIndexExpandsToBool index block.southeast = true ∧
      parentIndexExpandsToBool index block.northwest = true ∧
      parentIndexExpandsToBool index block.northeast = true := by
  refine ⟨blockParentIndex block,
    blockParentIndex_expandsTo hquadrants hcompatible, ?_⟩
  intro index hindex
  exact eq_blockParentIndex_of_expandsTo hquadrants hcompatible hindex

end ConcreteData
end LayeredFigure18ScaffoldData
end Figure13Layers
end OllingerRobinson
end LeanWang
