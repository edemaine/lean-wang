/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.UniversalTM0TableauSemantics

/-!
# Correctness of the direct folded local rule
-/

noncomputable section

namespace LeanWang
namespace UniversalTM0Tableau

open UniversalTM0Semantic

theorem incomingFromLeft_cellAt_of_write
    (config : Config) (q' : Label) (symbol : Symbol)
    (hstep : tm0 config.source.q config.source.Tape.head =
      some (q', .write symbol)) (position : Nat) :
    incomingFromLeft? (config.cellAt position) = none := by
  by_cases hposition : position = config.head
  · subst position
    simp only [incomingFromLeft?, cellAt_head]
    rw [cellAt_activeSymbol, hstep]
  · simp [incomingFromLeft?, Config.cellAt, hposition]

theorem incomingFromRight_cellAt_of_write
    (config : Config) (q' : Label) (symbol : Symbol)
    (hstep : tm0 config.source.q config.source.Tape.head =
      some (q', .write symbol)) (position : Nat) :
    incomingFromRight? (config.cellAt position) = none := by
  by_cases hposition : position = config.head
  · subst position
    simp only [incomingFromRight?, cellAt_head]
    rw [cellAt_activeSymbol, hstep]
  · simp [incomingFromRight?, Config.cellAt, hposition]

theorem localNextCell_write
    (config : Config) (q' : Label) (symbol : Symbol)
    (hstep : tm0 config.source.q config.source.Tape.head =
      some (q', .write symbol)) (position : Nat) :
    localNextCell? (decide (position = 0))
        (config.cellAtLeft position) (config.cellAt position)
        (config.cellAt (position + 1)) =
      some ((config.afterWrite q' symbol).cellAt position) := by
  by_cases hposition : position = config.head
  · subst position
    rw [Config.cellAt_afterWrite]
    simp only [if_pos]
    simp only [localNextCell?, cellAt_head, updateHeadCell?]
    rw [cellAt_activeSymbol, hstep]
  · rw [Config.cellAt_afterWrite]
    simp only [if_neg hposition]
    have hclear := cellAt_withHead_none_of_ne hposition
    have hleft : incomingFromLeft? (config.cellAtLeft position) = none := by
      cases position with
      | zero => simp [Config.cellAtLeft, blankCell, incomingFromLeft?]
      | succ position =>
          exact incomingFromLeft_cellAt_of_write config q' symbol hstep position
    have hright := incomingFromRight_cellAt_of_write config q' symbol hstep (position + 1)
    simp only [localNextCell?, cellAt_head_eq_none hposition, incoming?, hleft]
    rw [hright, hclear]

theorem incomingFromLeft_cellAt_of_move
    (config : Config) (q' : Label) (dir : Turing.Dir)
    (hstep : tm0 config.source.q config.source.Tape.head =
      some (q', .move dir)) (position : Nat) :
    incomingFromLeft? (config.cellAt position) =
      if position = config.head then
        if config.side.isOutward dir then some (config.side, q') else none
      else none := by
  by_cases hposition : position = config.head
  · subst position
    simp only [incomingFromLeft?, cellAt_head]
    rw [cellAt_activeSymbol, hstep]
    simp only [if_true]
  · simp [incomingFromLeft?, Config.cellAt, hposition]

theorem incomingFromRight_cellAt_of_move
    (config : Config) (q' : Label) (dir : Turing.Dir)
    (hstep : tm0 config.source.q config.source.Tape.head =
      some (q', .move dir)) (position : Nat) :
    incomingFromRight? (config.cellAt position) =
      if position = config.head then
        if config.side.isInward dir then some (config.side, q') else none
      else none := by
  by_cases hposition : position = config.head
  · subst position
    simp only [incomingFromRight?, cellAt_head]
    rw [cellAt_activeSymbol, hstep]
    simp only [if_true]
  · simp [incomingFromRight?, Config.cellAt, hposition]

theorem incoming_move_zero (side : Side) (dir : Turing.Dir)
    (head : Nat) (q' : Label) (hhead : head ≠ 0) :
    (if 1 = head then
      if side.isInward dir then some (side, q') else none
    else none) =
      if 0 = moveHead side (decide (head = 0)) head dir then
        some (nextSide side (decide (head = 0)) dir, q')
      else none := by
  cases side <;> cases dir <;>
    by_cases hzero : head = 0 <;>
    by_cases hOne : 1 = head
  all_goals simp [moveHead, nextSide, Side.isInward, Side.isOutward,
    hhead, hOne, hzero] <;> omega

theorem incoming_move_succ (side : Side) (dir : Turing.Dir)
    (head position : Nat) (q' : Label) (_hcenter : position + 1 ≠ head) :
    (match (if position = head then
        if side.isOutward dir then some (side, q') else none
      else none) with
    | some incoming => some incoming
    | none =>
        if position + 1 + 1 = head then
          if side.isInward dir then some (side, q') else none
        else none) =
      if position + 1 = moveHead side (decide (head = 0)) head dir then
        some (nextSide side (decide (head = 0)) dir, q')
      else none := by
  cases side <;> cases dir <;>
    by_cases hzero : head = 0 <;>
    by_cases hLeft : position = head <;>
    by_cases hRight : position + 1 + 1 = head
  all_goals simp [moveHead, nextSide, Side.isInward, Side.isOutward,
    hLeft, hRight, hzero]
  all_goals by_cases hPositionZero : position = 0
  all_goals by_cases hSelf : head + 1 + 1 = head
  all_goals by_cases hPredSelf : head + 1 = head - 1
  all_goals try simp [hPositionZero, hSelf, hPredSelf]
  all_goals omega

set_option maxRecDepth 2000 in
theorem localNextCell_move
    (config : Config) (q' : Label) (dir : Turing.Dir)
    (hstep : tm0 config.source.q config.source.Tape.head =
      some (q', .move dir)) (position : Nat) :
    localNextCell? (decide (position = 0))
        (config.cellAtLeft position) (config.cellAt position)
        (config.cellAt (position + 1)) =
      some ((config.afterMove q' dir).cellAt position) := by
  rw [Config.cellAt_afterMove]
  by_cases hcenter : position = config.head
  · subst position
    simp only [localNextCell?, cellAt_head, updateHeadCell?]
    rw [cellAt_activeSymbol, hstep]
    cases config.side <;> cases dir <;> by_cases hzero : config.head = 0
    all_goals simp [moveHead, nextSide, Side.isInward, Side.isOutward,
      Side.opposite, hzero, Nat.pred_eq_sub_one]
    all_goals have hpred : config.head ≠ config.head - 1 := by omega
    all_goals simp [hpred]
  · simp only [localNextCell?, cellAt_head_eq_none hcenter]
    cases position with
    | zero =>
        simp only [Config.cellAtLeft, incoming?, blankCell, incomingFromLeft?]
        rw [incomingFromRight_cellAt_of_move config q' dir hstep 1]
        rw [incoming_move_zero config.side dir config.head q' (Ne.symm hcenter)]
    | succ position =>
        simp only [Config.cellAtLeft, incoming?]
        rw [incomingFromLeft_cellAt_of_move config q' dir hstep position]
        rw [incomingFromRight_cellAt_of_move config q' dir hstep (position + 1 + 1)]
        exact congrArg (fun head => some ((config.cellAt (position + 1)).withHead head))
          (incoming_move_succ config.side dir config.head position q' hcenter)

theorem localNextCell_of_step {config next : Config}
    (hstep : config.step = some next) (position : Nat) :
    localNextCell? (decide (position = 0))
        (config.cellAtLeft position) (config.cellAt position)
        (config.cellAt (position + 1)) = some (next.cellAt position) := by
  unfold Config.step at hstep
  cases hm : tm0 config.source.q config.source.Tape.head with
  | none => simp [hm] at hstep
  | some result =>
      rcases result with ⟨q', stmt⟩
      cases stmt with
      | write symbol =>
          simp [hm] at hstep
          cases hstep
          exact localNextCell_write config q' symbol hm position
      | move dir =>
          simp [hm] at hstep
          cases hstep
          exact localNextCell_move config q' dir hm position

end UniversalTM0Tableau
end LeanWang
