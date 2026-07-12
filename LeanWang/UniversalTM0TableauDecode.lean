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

end UniversalTM0Tableau
end LeanWang
