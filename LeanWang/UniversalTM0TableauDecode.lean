/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.UniversalTM0TableauInitial

/-!
# Decoding direct TM0 tableau tilings

The position colors force the finite bottom row from the seed.  Row colors
then force every positive row to consist of valid typed history tiles.
-/

noncomputable section

namespace LeanWang
namespace UniversalTM0Tableau

open UniversalTM0Semantic

theorem mem_tiles_iff (input : List Symbol) (tile : WangTile) :
    tile ∈ tiles input ↔
      (∃ position, position < tailPosition input ∧
        MachineInputTiles.toWangTile position (position + 1)
          initialRowTag normalRowTag
          (runHistoryTile input 0 position).toMachineHistoryTile = tile) ∨
      tile = MachineInputTiles.toWangTile (tailPosition input) (tailPosition input)
          initialRowTag normalRowTag
          (runHistoryTile input 0 (tailPosition input)).toMachineHistoryTile ∨
      ∃ history : HistoryTile, history.Valid ∧
        MachineInputTiles.toWangTile 0 0 normalRowTag normalRowTag
          history.toMachineHistoryTile = tile := by
  simp [tiles, initialTiles, normalTiles, List.mem_map, mem_historyTiles_iff]

theorem next_initialWangTile_of_hMatches_mem
    (input : List Symbol) (position : Nat) {right : WangTile}
    (hmatch : WangTile.HMatches (initialWangTile input position) right)
    (hmem : right ∈ tiles input) :
    right = initialWangTile input (position + 1) := by
  rcases (mem_tiles_iff input right).1 hmem with
    ⟨next, hnext, hright⟩ | hright | ⟨history, _hhistory, hright⟩
  · rw [initialWangTile] at hmatch ⊢
    split at hmatch <;> rename_i hposition
    · rw [← hright] at hmatch
      have htags := (MachineInputTiles.hMatches_toWangTile_iff
        _ _ _ _ _ _ _ _ _ _).1 hmatch
      have heq : next = position + 1 := htags.1.symm
      subst next
      rw [if_pos hnext]
      exact hright.symm
    · rw [← hright] at hmatch
      have htags := (MachineInputTiles.hMatches_toWangTile_iff
        _ _ _ _ _ _ _ _ _ _).1 hmatch
      omega
  · rw [initialWangTile] at hmatch ⊢
    split at hmatch <;> rename_i hposition
    · rw [hright] at hmatch
      have htags := (MachineInputTiles.hMatches_toWangTile_iff
        _ _ _ _ _ _ _ _ _ _).1 hmatch
      have heq : position + 1 = tailPosition input := htags.1
      rw [if_neg (by omega)]
      exact hright
    · rw [if_neg (by omega)]
      exact hright
  · rw [initialWangTile] at hmatch
    split at hmatch <;> rw [← hright] at hmatch
    all_goals
      exact False.elim (initialRowTag_ne_normalRowTag
        ((MachineInputTiles.hMatches_toWangTile_iff
          _ _ _ _ _ _ _ _ _ _).1 hmatch).2.1)

theorem seeded_tiling_row_zero_eq
    {input : List Symbol} {plane : Nat × Nat → TileIn (tiles input)}
    (valid : ValidQuarterTiling (tiles input) plane)
    (seeded : (plane (0, 0)).1 = seed input) :
    ∀ position, (plane (position, 0)).1 = initialWangTile input position := by
  intro position
  induction position with
  | zero => exact seeded
  | succ position ih =>
      apply next_initialWangTile_of_hMatches_mem input position
      · simpa [ih] using valid.1 (position, 0)
      · exact (plane (position + 1, 0)).2

theorem normal_of_vMatches
    (input : List Symbol) {lower upper : WangTile}
    (lowerMem : lower ∈ tiles input) (upperMem : upper ∈ tiles input)
    (hmatches : WangTile.VMatches lower upper) :
    ∃ history : HistoryTile, history.Valid ∧
      MachineInputTiles.toWangTile 0 0 normalRowTag normalRowTag
        history.toMachineHistoryTile = upper := by
  rcases (mem_tiles_iff input upper).1 upperMem with
    ⟨upperPosition, _hupperPosition, hupper⟩ | hupper |
      ⟨upperHistory, hupperHistory, hupper⟩
  · rcases (mem_tiles_iff input lower).1 lowerMem with
      ⟨lowerPosition, _hlowerPosition, hlower⟩ | hlower |
        ⟨lowerHistory, _hlowerHistory, hlower⟩
    · rw [← hlower, ← hupper] at hmatches
      exact False.elim (initialRowTag_ne_normalRowTag
        ((MachineInputTiles.vMatches_toWangTile_iff
          _ _ _ _ _ _ _ _ _ _).1 hmatches).1.symm)
    · rw [hlower, ← hupper] at hmatches
      exact False.elim (initialRowTag_ne_normalRowTag
        ((MachineInputTiles.vMatches_toWangTile_iff
          _ _ _ _ _ _ _ _ _ _).1 hmatches).1.symm)
    · rw [← hlower, ← hupper] at hmatches
      exact False.elim (initialRowTag_ne_normalRowTag
        ((MachineInputTiles.vMatches_toWangTile_iff
          _ _ _ _ _ _ _ _ _ _).1 hmatches).1.symm)
  · rcases (mem_tiles_iff input lower).1 lowerMem with
      ⟨lowerPosition, _hlowerPosition, hlower⟩ | hlower |
        ⟨lowerHistory, _hlowerHistory, hlower⟩
    · rw [← hlower, hupper] at hmatches
      exact False.elim (initialRowTag_ne_normalRowTag
        ((MachineInputTiles.vMatches_toWangTile_iff
          _ _ _ _ _ _ _ _ _ _).1 hmatches).1.symm)
    · rw [hlower, hupper] at hmatches
      exact False.elim (initialRowTag_ne_normalRowTag
        ((MachineInputTiles.vMatches_toWangTile_iff
          _ _ _ _ _ _ _ _ _ _).1 hmatches).1.symm)
    · rw [← hlower, hupper] at hmatches
      exact False.elim (initialRowTag_ne_normalRowTag
        ((MachineInputTiles.vMatches_toWangTile_iff
          _ _ _ _ _ _ _ _ _ _).1 hmatches).1.symm)
  · exact ⟨upperHistory, hupperHistory, hupper⟩

theorem positive_row_decode
    {input : List Symbol} {plane : Nat × Nat → TileIn (tiles input)}
    (valid : ValidQuarterTiling (tiles input) plane)
    (time position : Nat) :
    ∃ history : HistoryTile, history.Valid ∧
      MachineInputTiles.toWangTile 0 0 normalRowTag normalRowTag
          history.toMachineHistoryTile = (plane (position, time + 1)).1 := by
  exact normal_of_vMatches input
    (plane (position, time)).2 (plane (position, time + 1)).2
    (valid.2 (position, time))

def decodedTile {input : List Symbol}
    {plane : Nat × Nat → TileIn (tiles input)}
    (valid : ValidQuarterTiling (tiles input) plane)
    (time position : Nat) : HistoryTile :=
  (positive_row_decode valid time position).choose

theorem decodedTile_valid {input : List Symbol}
    {plane : Nat × Nat → TileIn (tiles input)}
    (valid : ValidQuarterTiling (tiles input) plane) (time position : Nat) :
    (decodedTile valid time position).Valid :=
  (positive_row_decode valid time position).choose_spec.1

theorem decodedTile_eq_plane {input : List Symbol}
    {plane : Nat × Nat → TileIn (tiles input)}
    (valid : ValidQuarterTiling (tiles input) plane) (time position : Nat) :
    MachineInputTiles.toWangTile 0 0 normalRowTag normalRowTag
        (decodedTile valid time position).toMachineHistoryTile =
      (plane (position, time + 1)).1 :=
  (positive_row_decode valid time position).choose_spec.2

theorem decodedTile_hMatches {input : List Symbol}
    {plane : Nat × Nat → TileIn (tiles input)}
    (valid : ValidQuarterTiling (tiles input) plane) (time position : Nat) :
    WangTile.HMatches
      (MachineInputTiles.toWangTile 0 0 normalRowTag normalRowTag
        (decodedTile valid time position).toMachineHistoryTile)
      (MachineInputTiles.toWangTile 0 0 normalRowTag normalRowTag
        (decodedTile valid time (position + 1)).toMachineHistoryTile) := by
  simpa [decodedTile_eq_plane valid time position,
    decodedTile_eq_plane valid time (position + 1)] using
      valid.1 (position, time + 1)

theorem decodedTile_atOrigin_succ {input : List Symbol}
    {plane : Nat × Nat → TileIn (tiles input)}
    (valid : ValidQuarterTiling (tiles input) plane) (time position : Nat) :
    (decodedTile valid time (position + 1)).atOrigin = false := by
  have hcells := (MachineInputTiles.hMatches_toWangTile_iff
    0 0 0 0 normalRowTag normalRowTag normalRowTag normalRowTag
    (decodedTile valid time position).toMachineHistoryTile
    (decodedTile valid time (position + 1)).toMachineHistoryTile).1
      (decodedTile_hMatches valid time position)
  have hplain := hcells.2.2.1
  cases horigin : (decodedTile valid time (position + 1)).atOrigin
  · rfl
  · simp [HistoryTile.toMachineHistoryTile, HistoryTile.leftMachineCell,
      horigin, Cell.toMachineCell] at hplain

theorem decodedTile_atOrigin_zero {input : List Symbol}
    {plane : Nat × Nat → TileIn (tiles input)}
    (valid : ValidQuarterTiling (tiles input) plane)
    (seeded : (plane (0, 0)).1 = seed input) :
    ∀ time, (decodedTile valid time 0).atOrigin = true := by
  intro time
  induction time with
  | zero =>
      have hbottom := seeded_tiling_row_zero_eq valid seeded 0
      have hvertical : WangTile.VMatches
          (initialWangTile input 0)
          (MachineInputTiles.toWangTile 0 0 normalRowTag normalRowTag
            (decodedTile valid 0 0).toMachineHistoryTile) := by
        simpa [hbottom, decodedTile_eq_plane valid 0 0] using valid.2 (0, 0)
      rw [initialWangTile_history, if_pos (by simp [tailPosition])] at hvertical
      have hcells := (MachineInputTiles.vMatches_toWangTile_iff
        0 1 0 0 initialRowTag normalRowTag normalRowTag normalRowTag
        (runHistoryTile input 0 0).toMachineHistoryTile
        (decodedTile valid 0 0).toMachineHistoryTile).1 hvertical
      have hleft := hcells.2.1
      cases horigin : (decodedTile valid 0 0).atOrigin
      · simp [HistoryTile.toMachineHistoryTile, HistoryTile.leftMachineCell,
          runHistoryTile, horigin, Cell.toMachineCell] at hleft
      · rfl
  | succ time ih =>
      have hvertical : WangTile.VMatches
          (MachineInputTiles.toWangTile 0 0 normalRowTag normalRowTag
            (decodedTile valid time 0).toMachineHistoryTile)
          (MachineInputTiles.toWangTile 0 0 normalRowTag normalRowTag
            (decodedTile valid (time + 1) 0).toMachineHistoryTile) := by
        simpa [decodedTile_eq_plane valid time 0,
          decodedTile_eq_plane valid (time + 1) 0] using
            valid.2 (0, time + 1)
      have hcells := (MachineInputTiles.vMatches_toWangTile_iff
        0 0 0 0 normalRowTag normalRowTag normalRowTag normalRowTag
        (decodedTile valid time 0).toMachineHistoryTile
        (decodedTile valid (time + 1) 0).toMachineHistoryTile).1 hvertical
      have hleft := hcells.2.1
      cases horigin : (decodedTile valid (time + 1) 0).atOrigin
      · simp [HistoryTile.toMachineHistoryTile, HistoryTile.leftMachineCell,
          ih, horigin, Cell.toMachineCell] at hleft
      · rfl

theorem decodedTile_atOrigin_eq {input : List Symbol}
    {plane : Nat × Nat → TileIn (tiles input)}
    (valid : ValidQuarterTiling (tiles input) plane)
    (seeded : (plane (0, 0)).1 = seed input) (time position : Nat) :
    (decodedTile valid time position).atOrigin = decide (position = 0) := by
  cases position with
  | zero => simpa using decodedTile_atOrigin_zero valid seeded time
  | succ position => simp [decodedTile_atOrigin_succ valid time position]

theorem decodedTile_prevLeft_succ {input : List Symbol}
    {plane : Nat × Nat → TileIn (tiles input)}
    (valid : ValidQuarterTiling (tiles input) plane) (time position : Nat) :
    (decodedTile valid time (position + 1)).prevLeft =
      (decodedTile valid time position).prevCenter := by
  have hcells := (MachineInputTiles.hMatches_toWangTile_iff
    0 0 0 0 normalRowTag normalRowTag normalRowTag normalRowTag
    (decodedTile valid time position).toMachineHistoryTile
    (decodedTile valid time (position + 1)).toMachineHistoryTile).1
      (decodedTile_hMatches valid time position)
  have hmachine := hcells.2.2.1
  rw [HistoryTile.toMachineHistoryTile, HistoryTile.toMachineHistoryTile,
    HistoryTile.leftMachineCell,
    decodedTile_atOrigin_succ valid time position] at hmachine
  exact Cell.toMachineCell_injective_on_mem
    (decodedTile_valid valid time (position + 1)).1
    (decodedTile_valid valid time position).2.1 hmachine.symm

theorem decodedTile_prevRight {input : List Symbol}
    {plane : Nat × Nat → TileIn (tiles input)}
    (valid : ValidQuarterTiling (tiles input) plane) (time position : Nat) :
    (decodedTile valid time position).prevRight =
      (decodedTile valid time (position + 1)).prevCenter := by
  have hcells := (MachineInputTiles.hMatches_toWangTile_iff
    0 0 0 0 normalRowTag normalRowTag normalRowTag normalRowTag
    (decodedTile valid time position).toMachineHistoryTile
    (decodedTile valid time (position + 1)).toMachineHistoryTile).1
      (decodedTile_hMatches valid time position)
  exact Cell.toMachineCell_injective_on_mem
    (decodedTile_valid valid time position).2.2.1
    (decodedTile_valid valid time (position + 1)).2.1 hcells.2.2.2.1

theorem decodedTile_nextCenter_eq_upper_prevCenter {input : List Symbol}
    {plane : Nat × Nat → TileIn (tiles input)}
    (valid : ValidQuarterTiling (tiles input) plane) (time position : Nat) :
    (decodedTile valid time position).nextCenter =
      (decodedTile valid (time + 1) position).prevCenter := by
  have hvertical : WangTile.VMatches
      (MachineInputTiles.toWangTile 0 0 normalRowTag normalRowTag
        (decodedTile valid time position).toMachineHistoryTile)
      (MachineInputTiles.toWangTile 0 0 normalRowTag normalRowTag
        (decodedTile valid (time + 1) position).toMachineHistoryTile) := by
    simpa [decodedTile_eq_plane valid time position,
      decodedTile_eq_plane valid (time + 1) position] using
        valid.2 (position, time + 1)
  have hcells := (MachineInputTiles.vMatches_toWangTile_iff
    0 0 0 0 normalRowTag normalRowTag normalRowTag normalRowTag
    (decodedTile valid time position).toMachineHistoryTile
    (decodedTile valid (time + 1) position).toMachineHistoryTile).1 hvertical
  exact Cell.toMachineCell_injective_on_mem
    (decodedTile_valid valid time position).2.2.2.2.1
    (decodedTile_valid valid (time + 1) position).2.1 hcells.2.2.1

theorem Config.step_some_of_localNextCell_at_head_some
    {config : Config} {cell : Cell}
    (hlocal : localNextCell? (decide (config.head = 0))
      (config.cellAtLeft config.head) (config.cellAt config.head)
      (config.cellAt (config.head + 1)) = some cell) :
    ∃ next, config.step = some next := by
  unfold localNextCell? updateHeadCell? at hlocal
  simp only [cellAt_head] at hlocal
  rw [cellAt_activeSymbol] at hlocal
  cases hstep : tm0 config.source.q config.source.Tape.head with
  | none => simp [hstep] at hlocal
  | some result =>
      rcases result with ⟨q', stmt⟩
      cases stmt with
      | write symbol => exact ⟨config.afterWrite q' symbol, by simp [Config.step, hstep]⟩
      | move dir => exact ⟨config.afterMove q' dir, by simp [Config.step, hstep]⟩

theorem decodedTile_zero_prevCenter_eq_run_one {input : List Symbol}
    {plane : Nat × Nat → TileIn (tiles input)}
    (valid : ValidQuarterTiling (tiles input) plane)
    (seeded : (plane (0, 0)).1 = seed input) (position : Nat) :
    (decodedTile valid 0 position).prevCenter =
      (Config.run input 1).cellAt position := by
  have hbottom := seeded_tiling_row_zero_eq valid seeded position
  have hvertical : WangTile.VMatches
      (initialWangTile input position)
      (MachineInputTiles.toWangTile 0 0 normalRowTag normalRowTag
        (decodedTile valid 0 position).toMachineHistoryTile) := by
    simpa [hbottom, decodedTile_eq_plane valid 0 position] using
      valid.2 (position, 0)
  rw [initialWangTile_history] at hvertical
  split at hvertical <;> rename_i hposition
  all_goals
    have hcells := (MachineInputTiles.vMatches_toWangTile_iff
      _ _ 0 0 initialRowTag normalRowTag normalRowTag normalRowTag
      (runHistoryTile input 0 position).toMachineHistoryTile
      (decodedTile valid 0 position).toMachineHistoryTile).1 hvertical
    have htyped := Cell.toMachineCell_injective_on_mem
      (Config.cellAt_mem (Config.run_mem input 1) position)
      (decodedTile_valid valid 0 position).2.1 hcells.2.2.1
    simpa [runHistoryTile] using htyped.symm

theorem decodedTile_prevCenter_eq_run {input : List Symbol}
    {plane : Nat × Nat → TileIn (tiles input)}
    (valid : ValidQuarterTiling (tiles input) plane)
    (seeded : (plane (0, 0)).1 = seed input) :
    ∀ time position, (decodedTile valid time position).prevCenter =
      (Config.run input (time + 1)).cellAt position := by
  intro time
  induction time with
  | zero => exact decodedTile_zero_prevCenter_eq_run_one valid seeded
  | succ time ih =>
      let config := Config.run input (time + 1)
      have hlocal (position : Nat) :
          localNextCell? (decide (position = 0))
              (config.cellAtLeft position) (config.cellAt position)
              (config.cellAt (position + 1)) =
            some (decodedTile valid time position).nextCenter := by
        have hvalid := decodedTile_valid valid time position
        have hleft : (decodedTile valid time position).prevLeft =
            config.cellAtLeft position := by
          cases position with
          | zero =>
              have horigin := decodedTile_atOrigin_zero valid seeded time
              simpa [config, Config.cellAtLeft] using
                (hvalid.2.2.2.2.2.2.1 horigin).1
          | succ position =>
              rw [decodedTile_prevLeft_succ valid time position]
              change (decodedTile valid time position).prevCenter =
                config.cellAt position
              simpa [config] using ih position
        have hcenter : (decodedTile valid time position).prevCenter =
            config.cellAt position := by
          simpa [config] using ih position
        have hright : (decodedTile valid time position).prevRight =
            config.cellAt (position + 1) := by
          rw [decodedTile_prevRight valid time position]
          simpa [config] using ih (position + 1)
        rw [← hleft, ← hcenter, ← hright,
          ← decodedTile_atOrigin_eq valid seeded time position]
        exact hvalid.2.2.2.2.2.2.2
      rcases Config.step_some_of_localNextCell_at_head_some
          (hlocal config.head) with ⟨next, hstep⟩
      intro position
      have hactual := localNextCell_of_step hstep position
      have hnextCenter : (decodedTile valid time position).nextCenter =
          next.cellAt position :=
        Option.some.inj ((hlocal position).symm.trans hactual)
      rw [← decodedTile_nextCenter_eq_upper_prevCenter valid time position]
      rw [hnextCenter]
      rw [show time + 1 + 1 = (time + 1) + 1 by omega, Config.run_succ]
      simp [Config.next, config, hstep]

theorem Config.step_run_succ_some_of_tiling {input : List Symbol}
    {plane : Nat × Nat → TileIn (tiles input)}
    (valid : ValidQuarterTiling (tiles input) plane)
    (seeded : (plane (0, 0)).1 = seed input) (time : Nat) :
    ∃ next, (Config.run input (time + 1)).step = some next := by
  let config := Config.run input (time + 1)
  have hrow := decodedTile_prevCenter_eq_run valid seeded time
  have hlocal (position : Nat) :
      localNextCell? (decide (position = 0))
          (config.cellAtLeft position) (config.cellAt position)
          (config.cellAt (position + 1)) =
        some (decodedTile valid time position).nextCenter := by
    have hvalid := decodedTile_valid valid time position
    have hleft : (decodedTile valid time position).prevLeft =
        config.cellAtLeft position := by
      cases position with
      | zero =>
          have horigin := decodedTile_atOrigin_zero valid seeded time
          simpa [config, Config.cellAtLeft] using
            (hvalid.2.2.2.2.2.2.1 horigin).1
      | succ position =>
          rw [decodedTile_prevLeft_succ valid time position]
          change (decodedTile valid time position).prevCenter =
            config.cellAt position
          simpa [config] using hrow position
    have hcenter : (decodedTile valid time position).prevCenter =
        config.cellAt position := by
      simpa [config] using hrow position
    have hright : (decodedTile valid time position).prevRight =
        config.cellAt (position + 1) := by
      rw [decodedTile_prevRight valid time position]
      simpa [config] using hrow (position + 1)
    rw [← hleft, ← hcenter, ← hright,
      ← decodedTile_atOrigin_eq valid seeded time position]
    exact hvalid.2.2.2.2.2.2.2
  exact Config.step_some_of_localNextCell_at_head_some (hlocal config.head)

theorem Config.step_run_some_of_tiling {input : List Symbol}
    {plane : Nat × Nat → TileIn (tiles input)}
    (valid : ValidQuarterTiling (tiles input) plane)
    (seeded : (plane (0, 0)).1 = seed input) (time : Nat) :
    ∃ next, (Config.run input time).step = some next := by
  cases time with
  | zero =>
      rcases Config.step_run_succ_some_of_tiling valid seeded 0 with ⟨next, hnext⟩
      cases hstep : (Config.run input 0).step with
      | some first => exact ⟨first, rfl⟩
      | none =>
          have hrun : Config.run input 1 = Config.run input 0 := by
            rw [show 1 = 0 + 1 by omega, Config.run_succ]
            change (Config.run input 0).step.getD (Config.run input 0) =
              Config.run input 0
            rw [hstep]
            rfl
          rw [hrun, hstep] at hnext
          cases hnext
  | succ time =>
      exact Config.step_run_succ_some_of_tiling valid seeded time

theorem source_reaches_eq_run_source {input : List Symbol}
    {source : Turing.TM0.Cfg Symbol Label}
    (hreach : StateTransition.Reaches (Turing.TM0.step tm0)
      (Config.initial input).source source) :
    ∃ time, source = (Config.run input time).source := by
  induction hreach with
  | refl => exact ⟨0, rfl⟩
  | tail hreach hstep ih =>
      rcases ih with ⟨time, rfl⟩
      cases hconfig : (Config.run input time).step with
      | none =>
          have hsourceNone := (Config.step_eq_none_iff _).1 hconfig
          rw [hsourceNone] at hstep
          cases hstep
      | some next =>
          have hsourceStep := Config.step_source hconfig
          have hsource : _ = next.source :=
            Option.mem_unique hstep (by rw [hsourceStep]; rfl)
          refine ⟨time + 1, ?_⟩
          rw [Config.run_succ]
          simp [Config.next, hconfig, hsource]

private theorem part_dom_map_iff' {alpha beta : Type} (f : alpha → beta) (p : Part alpha) :
    (f <$> p).Dom ↔ p.Dom := by
  rw [Part.map_eq_map]
  rfl

theorem not_dom_of_tilesQuarterWithSeed {input : List Symbol} :
    TilesQuarterWithSeed (tiles input) (seed input) →
      ¬ (Turing.TM0.eval tm0 input).Dom := by
  rintro ⟨plane, valid, seeded⟩ hdom
  have hdomState :
      (StateTransition.eval (Turing.TM0.step tm0)
        (Turing.TM0.init input)).Dom := by
    rw [Turing.TM0.eval] at hdom
    exact (part_dom_map_iff' (fun c => c.Tape.right₀)
      (StateTransition.eval (Turing.TM0.step tm0)
        (Turing.TM0.init input))).1 hdom
  let haltSource := (StateTransition.eval (Turing.TM0.step tm0)
    (Turing.TM0.init input)).get hdomState
  have hmem : haltSource ∈ StateTransition.eval (Turing.TM0.step tm0)
      (Turing.TM0.init input) := Part.get_mem hdomState
  rcases StateTransition.mem_eval.1 hmem with ⟨hreach, hterminal⟩
  have hreach' : StateTransition.Reaches (Turing.TM0.step tm0)
      (Config.initial input).source haltSource := by
    simpa [Config.initial] using hreach
  rcases source_reaches_eq_run_source hreach' with ⟨time, htime⟩
  rcases Config.step_run_some_of_tiling valid seeded time with ⟨next, hnext⟩
  have hsourceNext := Config.step_source hnext
  rw [← htime, hterminal] at hsourceNext
  cases hsourceNext

theorem tilesQuarterWithSeed_iff_not_dom (input : List Symbol) :
    TilesQuarterWithSeed (tiles input) (seed input) ↔
      ¬ (Turing.TM0.eval tm0 input).Dom :=
  ⟨not_dom_of_tilesQuarterWithSeed, tilesQuarterWithSeed_of_not_dom⟩
end UniversalTM0Tableau
end LeanWang
