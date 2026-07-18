/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlPrefixResume
import LeanWang.Kari.Hooper.CounterControlRecoveredFrame

/-!
# Exact backing carried by a resumed prefix caller

`PrefixResumedSearch` remembers the tag, cleaned tape, and one-cell-shifted
gap produced by finite-prefix cleanup.  This file repackages those fields as
the exact suspended parent command selected by the tag.

In particular, the selected raw command has the prefix's first obstruction
as its target, its original unshifted gap has length `frame.limit`, and the
resumed search is exactly the same gap after its first blank cell.  These are
the tape-coordinate facts needed to classify the command's successful
continuation without reopening the shared-return proof.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlPrefixResume
namespace PrefixResumedSearch

open Turing CounterMachine
open BoundedMarkerProgram FramedMarkerTape FramedCounterGeometry
open CounterControlPlan CounterControlSearchSystem
open CounterControlFrameBacking CounterControlCleanupSemantics
open CounterControlPrefixInstructionResolution
open CounterControlPrefixResume CounterControlRecoveredFrame

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

variable {base : Nat} {c : Nat.Partrec.Code}
variable {frame : PrefixEnvelope}
variable {start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}

/-- The raw generated command selected by the recovered physical tag. -/
def selectedRaw (resumed : PrefixResumedSearch base c frame start) :
    RawCommand :=
  rawCommands.get resumed.next.search

/-- The selected raw command really belongs to the global command list. -/
theorem selectedRaw_mem
    (resumed : PrefixResumedSearch base c frame start) :
    resumed.selectedRaw ∈ rawCommands :=
  List.get_mem rawCommands resumed.next.search

/-- Re-enumerating the selected raw command recovers the exact saved tag. -/
@[simp] theorem rawTag_selectedRaw
    (resumed : PrefixResumedSearch base c frame start) :
    CounterControlCommandAt.rawTag resumed.selectedRaw resumed.selectedRaw_mem =
      resumed.next.search := by
  apply CounterControlCommandAt.rawTag_eq_of_get_eq
  rfl

/-- Command-oriented compilation of the selected raw command agrees with
the search-indexed command stored by `GenuineSearch`. -/
@[simp] theorem compileRawCommand_selectedRaw
    (resumed : PrefixResumedSearch base c frame start) :
    CounterControlCommandAt.compileRawCommand base c resumed.selectedRaw
        resumed.selectedRaw_mem =
      command base c resumed.next.search := by
  unfold CounterControlCommandAt.compileRawCommand command
  rw [rawTag_selectedRaw]

/-- Genuine recovered specification of the represented collision-time
prefix, using the resumed search itself as the return tag. -/
def parentSpec (resumed : PrefixResumedSearch base c frame start) :
    Spec numTags :=
  recoveredSpec resumed.next.search resumed.registers frame.growth
    frame.limit frame.target resumed.represented.core_before_limit

/-- The original unshifted search frame suspended around the finite prefix. -/
def parentFrame (resumed : PrefixResumedSearch base c frame start) :
    Frame (Symbol numTags) Search :=
  recoveredFrame resumed.next.search resumed.registers frame.growth
    frame.limit frame.target resumed.represented.core_before_limit
    resumed.tape

/-- The represented prefix is installed in the exact cleaned parent tape. -/
theorem parent_backedBy
    (resumed : PrefixResumedSearch base c frame start) :
    BackedBy resumed.parentSpec resumed.tape resumed.parentFrame.outer := by
  simpa [parentSpec, parentFrame, recoveredFrame] using
    (backedBy_recoveredSpec resumed.next.search resumed.represented
      resumed.tag_eq)

/-- The resumed search starts after the first cell of the recovered parent
frame, exactly as the private return rule prescribes. -/
theorem next_outer_eq
    (resumed : PrefixResumedSearch base c frame start) :
    resumed.next.outer = resumed.parentFrame.outer.move frame.growth := by
  rw [resumed.outer_eq]
  have hspec :
      afterTag
          (prefixSpec resumed.registers frame.growth frame.limit frame.target
            resumed.represented.core_before_limit) resumed.tape =
        afterTag resumed.parentSpec resumed.tape := by
    rfl
  rw [hspec, CounterControlFrameBacking.afterTag_eq_outer
    resumed.parent_backedBy]

/-- The prefix limit is positive; the recovered core already contains all
five boundary cells strictly before it. -/
theorem limit_pos
    (resumed : PrefixResumedSearch base c frame start) :
    0 < frame.limit := by
  have hend : 0 < layoutEnd resumed.registers := by
    simp [layoutEnd]
  exact hend.trans resumed.represented.core_before_limit

/-- The selected command's shifted genuine gap can be restored to its
original length by prepending the one erased/resumed blank cell. -/
private theorem selected_gap_on_parent
    (resumed : PrefixResumedSearch base c frame start) :
    SearchGap (fun symbol => symbol = blankSymbol)
      (command base c resumed.next.search).target.Matches
      resumed.parentFrame.outer frame.growth frame.limit := by
  have htail : SearchGap (fun symbol => symbol = blankSymbol)
      (command base c resumed.next.search).target.Matches
      (resumed.parentFrame.outer.move frame.growth) frame.growth
      (frame.limit - 1) := by
    simpa [resumed.next_outer_eq, resumed.direction_eq,
      resumed.distance_eq] using resumed.next.gap
  have hmoveOne : resumed.parentFrame.outer.move frame.growth =
      resumed.parentFrame.outer.moveN frame.growth 1 := by
    simpa using
      (FullTM0.Tape.move_moveN resumed.parentFrame.outer frame.growth 0)
  have htail' : SearchGap (fun symbol => symbol = blankSymbol)
      (command base c resumed.next.search).target.Matches
      (resumed.parentFrame.outer.moveN frame.growth 1) frame.growth
      (frame.limit - 1) := by
    rw [← hmoveOne]
    exact htail
  have hprefix : ∀ i < 1,
      resumed.parentFrame.outer (FullTM0.Tape.offset frame.growth i) =
        blankSymbol := by
    intro i hi
    have hiZero : i = 0 := by omega
    subst i
    exact resumed.parent_backedBy.searchGap.blank resumed.limit_pos
  have hfull := CounterControlArbitrarySearch.SearchGap.prepend_moveN
    hprefix htail'
  have hlength : 1 + (frame.limit - 1) = frame.limit := by
    have hpositive := resumed.limit_pos
    omega
  simpa [hlength] using hfull

/-- The physical first obstruction determines the selected command target
uniquely. -/
theorem selected_target_eq
    (resumed : PrefixResumedSearch base c frame start) :
    (command base c resumed.next.search).target = frame.target := by
  apply CounterControlTargetUniqueness.target_eq_of_matches
    resumed.selected_gap_on_parent.marked
    resumed.parent_backedBy.searchGap.marked

/-- The selected raw command recognizes precisely the prefix obstruction. -/
theorem selectedRaw_target_eq
    (resumed : PrefixResumedSearch base c frame start) :
    (CounterControlCommandAt.compileRawCommand base c resumed.selectedRaw
      resumed.selectedRaw_mem).target = frame.target := by
  rw [compileRawCommand_selectedRaw]
  exact resumed.selected_target_eq

/-- The selected raw command searches in the prefix's physical growth
direction. -/
theorem selectedRaw_direction_eq
    (resumed : PrefixResumedSearch base c frame start) :
    (CounterControlCommandAt.compileRawCommand base c resumed.selectedRaw
      resumed.selectedRaw_mem).searchDirection = frame.growth := by
  rw [compileRawCommand_selectedRaw]
  exact resumed.direction_eq

/-- Consumer-facing exact original gap of the recovered raw caller. -/
theorem selectedRaw_originalGap
    (resumed : PrefixResumedSearch base c frame start) :
    SearchGap (fun symbol => symbol = blankSymbol)
      (CounterControlCommandAt.compileRawCommand base c resumed.selectedRaw
        resumed.selectedRaw_mem).target.Matches
      resumed.parentFrame.outer frame.growth frame.limit := by
  rw [compileRawCommand_selectedRaw]
  exact resumed.selected_gap_on_parent

/-- The resumed configuration is the generated selected raw command on the
one-cell-shifted exact parent backing. -/
theorem next_cfg_eq
    (resumed : PrefixResumedSearch base c frame start) :
    resumed.next.cfg =
      ⟨searchState base c resumed.selectedRaw.address,
        resumed.parentFrame.outer.move frame.growth⟩ := by
  change (searchSystem base c).startCfg resumed.next.search
      resumed.next.outer = _
  rw [resumed.next_outer_eq]
  change (⟨searchState base c
      (rawCommands.get resumed.next.search).address,
      resumed.parentFrame.outer.move frame.growth⟩ :
        FullTM0.Cfg (Symbol numTags) FiniteTM0.State) = _
  rfl

end

end PrefixResumedSearch
end CounterControlPrefixResume
end Hooper
end Kari
end LeanWang
