/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Kari.AffineTransducer
import LeanWang.Kari.TransducerHalfPlane

/-!
# Finite systems of rational affine branches

Kari's piecewise-affine simulation uses a finite union of transducers, one for
each affine branch.  The horizontal carry colors of `AffineTransducer.lean`
contain a branch tag.  If the tags in the finite system are unique, horizontal
matching therefore forces an entire bi-infinite row to use one branch.

This file packages that finite union and proves the row-uniformity statement.
It deliberately stops at local affine equations: extracting an affine orbit
from a bi-infinite digit row additionally requires the limiting argument for
balanced representations.
-/

namespace LeanWang
namespace Kari

/-- An affine branch together with the finite alphabets and carry bound used to
compile its local equations. -/
structure CompiledAffineBranch where
  branch : IntegerAffineBranch
  inputs : List IntVector3
  outputs : List IntVector3
  carryBound : Nat
deriving Repr

namespace CompiledAffineBranch

/-- Compile one finite affine branch to its letter-to-letter transducer. -/
def transducer (compiled : CompiledAffineBranch) : Transducer :=
  compiled.branch.transducer compiled.inputs compiled.outputs compiled.carryBound

/-- Both horizontal colors emitted by a compiled branch carry its tag. -/
theorem horizontal_tags_of_mem_transducer (compiled : CompiledAffineBranch)
    (t : Transition) (ht : t ∈ compiled.transducer) :
    t.left.unpair.1 = compiled.branch.tag ∧
      t.right.unpair.1 = compiled.branch.tag := by
  exact compiled.branch.horizontal_tags_of_mem_transducer
    compiled.inputs compiled.outputs compiled.carryBound t ht

/-- Every emitted transition satisfies the rational affine map represented by
the compiled branch. -/
theorem satisfiesAffine_of_mem_transducer (compiled : CompiledAffineBranch)
    (t : Transition) (ht : t ∈ compiled.transducer) :
    t.SatisfiesAffine compiled.branch.rationalMap
      IntegerAffineBranch.digitValue compiled.branch.carryValue := by
  exact compiled.branch.satisfiesAffine_of_mem_transducer
    compiled.inputs compiled.outputs compiled.carryBound t ht

end CompiledAffineBranch

/-- Within a list of compiled branches, the horizontal tag determines the
whole compiled branch (including its alphabets and carry bound). -/
def AffineBranchTagsUnique (branches : List CompiledAffineBranch) : Prop :=
  ∀ ⦃a b : CompiledAffineBranch⦄, a ∈ branches → b ∈ branches →
    a.branch.tag = b.branch.tag → a = b

/-- A finite piecewise-affine system.  Unique tags are exactly the condition
needed to turn horizontal carry matching into branch equality. -/
structure AffineSystem where
  branches : List CompiledAffineBranch
  tagsUnique : AffineBranchTagsUnique branches

namespace AffineSystem

/-- The system transducer is the finite union of all compiled branch
transducers. -/
def transducer (system : AffineSystem) : Transducer :=
  system.branches.flatMap CompiledAffineBranch.transducer

/-- Membership in the system transducer exposes a source compiled branch. -/
theorem mem_transducer_iff (system : AffineSystem) (t : Transition) :
    t ∈ system.transducer ↔
      ∃ compiled ∈ system.branches, t ∈ compiled.transducer := by
  simp [transducer]

/-- Equal tags of two branches in a system imply equality of the compiled
branches. -/
theorem eq_of_tag_eq (system : AffineSystem)
    {a b : CompiledAffineBranch} (ha : a ∈ system.branches)
    (hb : b ∈ system.branches) (htag : a.branch.tag = b.branch.tag) :
    a = b :=
  system.tagsUnique ha hb htag

/-- The four labels of a transition agree with one cell of an upper-half-plane
diagram. -/
def TransitionMatchesCell (t : Transition)
    (digits carries : Int × Nat → Nat) (p : Int × Nat) : Prop :=
  t.input = digits p ∧
    t.output = digits (p.1, p.2 + 1) ∧
    t.left = carries p ∧
    t.right = carries (p.1 + 1, p.2)

/-- A particular cell of a system diagram uses a particular compiled branch. -/
def UsesBranchAt (system : AffineSystem)
    (digits carries : Int × Nat → Nat) (p : Int × Nat)
    (compiled : CompiledAffineBranch) : Prop :=
  compiled ∈ system.branches ∧
    ∃ t ∈ compiled.transducer, TransitionMatchesCell t digits carries p

/-- Every cell of a system diagram comes from one of its compiled branches. -/
theorem exists_usesBranchAt (system : AffineSystem)
    {digits carries : Int × Nat → Nat}
    (hdiagram : system.transducer.IsUpperHalfDiagram digits carries)
    (p : Int × Nat) :
    ∃ compiled, system.UsesBranchAt digits carries p compiled := by
  rcases hdiagram p with
    ⟨t, ht, hinput, houtput, hleft, hright⟩
  rcases (system.mem_transducer_iff t).1 ht with
    ⟨compiled, hcompiled, htcompiled⟩
  exact ⟨compiled, hcompiled, t, htcompiled,
    hinput, houtput, hleft, hright⟩

/-- Neighboring cells in one row have the same branch tag, because the right
carry color of the first cell is the left carry color of the second. -/
theorem tag_eq_of_usesBranchAt_succ (system : AffineSystem)
    {digits carries : Int × Nat → Nat} {x : Int} {y : Nat}
    {a b : CompiledAffineBranch}
    (ha : system.UsesBranchAt digits carries (x, y) a)
    (hb : system.UsesBranchAt digits carries (x + 1, y) b) :
    a.branch.tag = b.branch.tag := by
  rcases ha.2 with ⟨ta, hta, hma⟩
  rcases hb.2 with ⟨tb, htb, hmb⟩
  have htagsA := a.horizontal_tags_of_mem_transducer ta hta
  have htagsB := b.horizontal_tags_of_mem_transducer tb htb
  calc
    a.branch.tag = ta.right.unpair.1 := htagsA.2.symm
    _ = (carries (x + 1, y)).unpair.1 :=
      congrArg (fun color : Nat => color.unpair.1) hma.2.2.2
    _ = tb.left.unpair.1 := by
      apply congrArg (fun color : Nat => color.unpair.1)
      simpa only using hmb.2.2.1.symm
    _ = b.branch.tag := htagsB.1

/-- Two branch witnesses for the same cell necessarily have the same tag. -/
theorem tag_eq_of_usesBranchAt_same_cell (system : AffineSystem)
    {digits carries : Int × Nat → Nat} {p : Int × Nat}
    {a b : CompiledAffineBranch}
    (ha : system.UsesBranchAt digits carries p a)
    (hb : system.UsesBranchAt digits carries p b) :
    a.branch.tag = b.branch.tag := by
  rcases ha.2 with ⟨ta, hta, hma⟩
  rcases hb.2 with ⟨tb, htb, hmb⟩
  have htagsA := a.horizontal_tags_of_mem_transducer ta hta
  have htagsB := b.horizontal_tags_of_mem_transducer tb htb
  calc
    a.branch.tag = ta.left.unpair.1 := htagsA.1.symm
    _ = (carries p).unpair.1 :=
      congrArg (fun color : Nat => color.unpair.1) hma.2.2.1
    _ = tb.left.unpair.1 :=
      congrArg (fun color : Nat => color.unpair.1) hmb.2.2.1.symm
    _ = b.branch.tag := htagsB.1

/-- A function on the integer line that agrees at every pair of successors is
constant. -/
private theorem int_constant_of_eq_succ {A : Type*} (f : Int → A)
    (hstep : ∀ x, f x = f (x + 1)) (x : Int) : f x = f 0 := by
  cases x with
  | ofNat n =>
      induction n with
      | zero => rfl
      | succ n ih =>
          calc
            f (Int.ofNat (n + 1)) = f (Int.ofNat n + 1) := by
              apply congrArg f
              simp only [Int.ofNat_eq_natCast, Int.natCast_add,
                Nat.cast_one]
            _ = f (Int.ofNat n) := (hstep (Int.ofNat n)).symm
            _ = f 0 := ih
  | negSucc n =>
      induction n with
      | zero =>
          calc
            f (Int.negSucc 0) = f (Int.negSucc 0 + 1) :=
              hstep (Int.negSucc 0)
            _ = f 0 := by
              apply congrArg f
              omega
      | succ n ih =>
          calc
            f (Int.negSucc (n + 1)) = f (Int.negSucc (n + 1) + 1) :=
              hstep (Int.negSucc (n + 1))
            _ = f (Int.negSucc n) := by
              apply congrArg f
              omega
            _ = f 0 := ih

/-- One row uses one compiled branch at every horizontal position.  Each local
transition is retained explicitly and is certified both as a diagram cell and
as a solution of that branch's rational affine carry equation. -/
theorem exists_branch_for_row (system : AffineSystem)
    {digits carries : Int × Nat → Nat}
    (hdiagram : system.transducer.IsUpperHalfDiagram digits carries)
    (y : Nat) :
    ∃ compiled ∈ system.branches, ∀ x : Int,
      ∃ t ∈ compiled.transducer,
        TransitionMatchesCell t digits carries (x, y) ∧
          t.SatisfiesAffine compiled.branch.rationalMap
            IntegerAffineBranch.digitValue compiled.branch.carryValue := by
  classical
  let branchAt : Int → CompiledAffineBranch := fun x =>
    Classical.choose (system.exists_usesBranchAt hdiagram (x, y))
  have hbranchAt (x : Int) :
      system.UsesBranchAt digits carries (x, y) (branchAt x) :=
    Classical.choose_spec (system.exists_usesBranchAt hdiagram (x, y))
  have hstep (x : Int) : branchAt x = branchAt (x + 1) := by
    apply system.eq_of_tag_eq (hbranchAt x).1 (hbranchAt (x + 1)).1
    exact system.tag_eq_of_usesBranchAt_succ (hbranchAt x) (hbranchAt (x + 1))
  have hconstant (x : Int) : branchAt x = branchAt 0 :=
    int_constant_of_eq_succ branchAt hstep x
  refine ⟨branchAt 0, (hbranchAt 0).1, ?_⟩
  intro x
  have huse := hbranchAt x
  rw [hconstant x] at huse
  rcases huse.2 with ⟨t, ht, hmatches⟩
  exact ⟨t, ht, hmatches,
    (branchAt 0).satisfiesAffine_of_mem_transducer t ht⟩

/-- The affine carry equations telescope across every finite interval of one
upper-half-plane row.  Unlike `IsPlaneDiagram.affine_telescope`, this theorem
first uses the tagged horizontal colors to select the single affine branch
used by the row; transitions belonging to other branches in the union are
irrelevant. -/
theorem exists_affine_telescope_for_row (system : AffineSystem)
    {digits carries : Int × Nat → Nat}
    (hdiagram : system.transducer.IsUpperHalfDiagram digits carries)
    (y : Nat) :
    ∃ compiled ∈ system.branches, ∀ (x : Int) (n : Nat),
      compiled.branch.carryValue (carries (x, y)) +
          (compiled.branch.rationalMap.linear
              (∑ i ∈ Finset.range n,
                IntegerAffineBranch.digitValue
                  (digits (x + (i : Int), y))) +
            (n : ℚ) • compiled.branch.rationalMap.offset) =
        (∑ i ∈ Finset.range n,
            IntegerAffineBranch.digitValue
              (digits (x + (i : Int), y + 1))) +
          compiled.branch.carryValue (carries (x + (n : Int), y)) := by
  rcases system.exists_branch_for_row hdiagram y with
    ⟨compiled, hcompiled, hrow⟩
  refine ⟨compiled, hcompiled, ?_⟩
  intro x n
  let input : Nat → Fin 3 → ℚ := fun i =>
    IntegerAffineBranch.digitValue (digits (x + (i : Int), y))
  let output : Nat → Fin 3 → ℚ := fun i =>
    IntegerAffineBranch.digitValue (digits (x + (i : Int), y + 1))
  let carry : Nat → Fin 3 → ℚ := fun i =>
    compiled.branch.carryValue (carries (x + (i : Int), y))
  have hlocal : ∀ i < n,
      carry i + compiled.branch.rationalMap (input i) =
        output i + carry (i + 1) := by
    intro i hi
    rcases hrow (x + (i : Int)) with ⟨t, ht, hmatches, hsatisfies⟩
    rw [Transition.SatisfiesAffine] at hsatisfies
    rcases hmatches with ⟨hinput, houtput, hleft, hright⟩
    rw [hinput, houtput, hleft, hright] at hsatisfies
    simpa [input, output, carry, Nat.cast_succ, Int.add_assoc] using hsatisfies
  simpa [input, output, carry] using
    compiled.branch.rationalMap.telescope input output carry n hlocal

/-- Equivalently, every row of an upper-half diagram carries one horizontally
constant branch tag.  The quantified branch witness makes the statement
independent of any particular choice of transition at a cell. -/
theorem exists_constant_branch_tag_for_row (system : AffineSystem)
    {digits carries : Int × Nat → Nat}
    (hdiagram : system.transducer.IsUpperHalfDiagram digits carries)
    (y : Nat) :
    ∃ tag : Nat, ∀ (x : Int) (compiled : CompiledAffineBranch),
      system.UsesBranchAt digits carries (x, y) compiled →
        compiled.branch.tag = tag := by
  rcases system.exists_branch_for_row hdiagram y with
    ⟨rowBranch, hrowBranch, hrow⟩
  refine ⟨rowBranch.branch.tag, ?_⟩
  intro x compiled hcompiled
  rcases hrow x with ⟨t, ht, hmatches, _⟩
  have hrowUses :
      system.UsesBranchAt digits carries (x, y) rowBranch :=
    ⟨hrowBranch, t, ht, hmatches⟩
  exact system.tag_eq_of_usesBranchAt_same_cell hcompiled hrowUses

end AffineSystem

end Kari
end LeanWang
