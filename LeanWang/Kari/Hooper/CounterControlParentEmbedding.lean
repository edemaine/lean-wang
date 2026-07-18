/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlPrefixResume

/-!
# Embedding a resumed caller in its parent counter core

Prefix cleanup resumes the suspended caller with gap `limit - 1`.  That
identity alone does not give a monotone sequence: before unnesting the next
level, the resumed caller must be shown to lie strictly inside that level's
reconstructed counter core.

This file states that caller-side obligation without pretending that generic
global-frontier normalization preserves tape geometry.  A structured resumed
caller has two relevant outcomes.

* Its command and finite direct continuation reach a bounded logical core,
  and the old gap is strictly smaller than that core's `layoutEnd`.
* The caller was already one of the finite cleanup commands, and completing
  that cleanup directly reaches a strictly larger resumed search.

In the first case, finite-prefix totality supplies exact cleanup of the
containing core.  Its resumed gap is at least the core end, so the strict
inside inequality gives the desired strict unnesting step.  Thus the only
remaining theorem is the finite-control/tape-coordinate classification
`ResumedParentEmbeddingLaw` below.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlParentEmbedding

open Turing CounterMachine
open BoundedMarkerProgram FramedMarkerTape
open CounterControlPlan CounterControlSearchSystem
open CounterControlPrefixInstructionResolution
open CounterControlPrefixResume CounterControlGlobalUnnesting

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-! ## Exact bounded logical cores -/

/-- A represented finite target prefix at bounded logical control.  Unlike a
generic `Frontier.logical`, this retains the exact core tape, the first
obstruction, and the centering used by prefix totality. -/
structure LogicalCore (base : Nat) (c : Nat.Partrec.Code) where
  growth : Turing.Dir
  source : Nat
  source_lt : source < logicalSpan
  registers : Registers
  tape : FullTM0.Tape (Symbol numTags)
  limit : Nat
  target : Target numTags
  represented : CoreTargetRepresents registers growth limit target tape

namespace LogicalCore

/-- Stable finite envelope of a reconstructed logical core. -/
def frame {base : Nat} {c : Nat.Partrec.Code}
    (core : LogicalCore base c) : PrefixEnvelope :=
  ⟨core.growth, core.limit, core.target⟩

/-- Abstract counter configuration represented by a logical core. -/
def abstract {base : Nat} {c : Nat.Partrec.Code}
    (core : LogicalCore base c) : CounterMachine.Cfg :=
  ⟨core.source, core.registers⟩

/-- Exact concrete bounded logical configuration. -/
def cfg {base : Nat} {c : Nat.Partrec.Code}
    (core : LogicalCore base c) :
    FullTM0.Cfg (Symbol numTags) FiniteTM0.State :=
  prefixLogicalCfg base c core.frame core.abstract core.tape

/-- The packaged data is immediately consumable by finite-prefix totality. -/
theorem prefixLogical {base : Nat} {c : Nat.Partrec.Code}
    (core : LogicalCore base c) :
    PrefixLogical base c core.frame core.abstract core.cfg := by
  exact .intro core.tape core.represented rfl core.source_lt

/-- An immortal represented logical core reaches an exact level-aware resume. -/
theorem reaches_resumed_of_immortal
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (core : LogicalCore base c)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) core.cfg) :
    Nonempty (PrefixResumedSearch base c core.frame core.cfg) := by
  exact prefixLogical_reaches_resumedSearch_of_immortal
    base c hmortal core.frame core.prefixLogical himmortal

/-- The core present at logical entry ends no farther out than the resumed
caller's gap.  This is the off-by-one-safe comparison: `layoutEnd < limit`
and the resumed distance is exactly `limit - 1`. -/
theorem layoutEnd_le_resumedDistance
    {base : Nat} {c : Nat.Partrec.Code}
    (core : LogicalCore base c)
    (resume : PrefixResumedSearch base c core.frame core.cfg) :
    layoutEnd core.registers ≤ resume.next.distance := by
  rw [resume.distance_eq]
  change layoutEnd core.registers ≤ core.limit - 1
  have hcore := core.represented.core_before_limit
  omega

end LogicalCore

/-! ## Caller embedding and its two possible outcomes -/

/-- A generated search reaches a reconstructed logical core which strictly
contains its gap.  The inequality is intentionally against the core present
at logical entry, not against the later collision-time core. -/
structure ReachesContainingLogicalCore
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GenuineSearch base c) : Type where
  core : LogicalCore base c
  reaches : FullTM0.Reaches (CounterControlNestingBridge.machine base c)
    current.cfg core.cfg
  strictly_inside : current.distance < layoutEnd core.registers

namespace ReachesContainingLogicalCore

/-- Prefix totality turns a containing logical core into one strict
unnesting step from the embedded search. -/
theorem clearedPrefixUnnests
    {base : Nat} {c : Nat.Partrec.Code}
    {current : GenuineSearch base c}
    (contained : ReachesContainingLogicalCore current)
    (resume : PrefixResumedSearch base c
      contained.core.frame contained.core.cfg) :
    ClearedPrefixUnnests current resume.next := by
  refine ⟨contained.reaches.trans resume.reaches, ?_⟩
  exact contained.strictly_inside.trans_le
    (contained.core.layoutEnd_le_resumedDistance resume)

end ReachesContainingLogicalCore

/-- Finite-control classification needed after a structured caller resumes.
The second branch is needed when the saved caller itself belongs to an
already-running cleanup chain and therefore need not visit logical control
before the next unnesting. -/
inductive ParentEmbeddingOutcome
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GenuineSearch base c) : Type where
  | logical (contained : ReachesContainingLogicalCore current)
  | resumed (next : GenuineSearch base c)
      (unnests : ClearedPrefixUnnests current next)

/-- The exact remaining caller-side operational law.

Proving this requires preserving the selected raw command and its absolute
head displacement while resolving the command continuation.  The existing
generic `Frontier` API is deliberately insufficient: it forgets both pieces
of geometry. -/
def ResumedParentEmbeddingLaw (base : Nat) (c : Nat.Partrec.Code) : Prop :=
  ∀ {frame : PrefixEnvelope}
      {start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
      (resumed : PrefixResumedSearch base c frame start),
    FullTM0.ImmortalFrom (CounterControlNestingBridge.machine base c)
      resumed.next.cfg →
      Nonempty (ParentEmbeddingOutcome resumed.next)

/-- The parent-embedding classification, together with finite-prefix
totality, is sufficient for one strict global-unnesting step. -/
theorem exists_clearedPrefixUnnests_of_parentEmbedding
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    {frame : PrefixEnvelope}
    {start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (resumed : PrefixResumedSearch base c frame start)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) resumed.next.cfg)
    (hembedding : Nonempty (ParentEmbeddingOutcome resumed.next)) :
    ∃ next : GenuineSearch base c,
      ClearedPrefixUnnests resumed.next next := by
  rcases hembedding with ⟨outcome⟩
  cases outcome with
  | resumed next hunnests => exact ⟨next, hunnests⟩
  | logical contained =>
      have himmortalCore : FullTM0.ImmortalFrom
          (CounterControlNestingBridge.machine base c)
          contained.core.cfg :=
        FullTM0.ImmortalFrom.of_reaches himmortal contained.reaches
      rcases contained.core.reaches_resumed_of_immortal
          base c hmortal himmortalCore with ⟨next⟩
      exact ⟨next.next, contained.clearedPrefixUnnests next⟩

/-- Consumer-facing consequence of the remaining law. -/
theorem exists_clearedPrefixUnnests
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (hlaw : ResumedParentEmbeddingLaw base c)
    {frame : PrefixEnvelope}
    {start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (resumed : PrefixResumedSearch base c frame start)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) resumed.next.cfg) :
    ∃ next : GenuineSearch base c,
      ClearedPrefixUnnests resumed.next next :=
  exists_clearedPrefixUnnests_of_parentEmbedding
    base c hmortal resumed himmortal (hlaw resumed himmortal)

end

end CounterControlParentEmbedding
end Hooper
end Kari
end LeanWang
