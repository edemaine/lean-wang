/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104ShadedFreeLineTranslation

/-!
Ordered finite grids of free rows and columns inside shaded Robinson boards.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace ShadedFreeGrid

open OrientedRedCycles RedShadeCycles RefinementTranslation
  ShadedFreeLineTranslation ShadedPlaneSignalGrid

set_option maxRecDepth 20000

structure FreeGrid (indexGrid : Nat → Nat → Index)
    (shadeGrid : Nat → Nat → RedShades.State)
    (west east south north size : Nat) where
  columnAt : Fin size → Nat
  rowAt : Fin size → Nat
  column_strictMono : ∀ {i j}, i < j → columnAt i < columnAt j
  row_strictMono : ∀ {i j}, i < j → rowAt i < rowAt j
  column_west : ∀ i, quarterWest west < columnAt i
  column_east : ∀ i, columnAt i < quarterEast east
  row_south : ∀ i, quarterSouth south < rowAt i
  row_north : ∀ i, rowAt i < quarterNorth north
  freeColumn : ∀ i, IsFreeColumn indexGrid shadeGrid south north (columnAt i)
  freeRow : ∀ i, IsFreeRow indexGrid shadeGrid west east (rowAt i)

theorem FreeGrid.signal_clear
    {indexGrid : Nat → Nat → Index}
    {shadeGrid : Nat → Nat → RedShades.State}
    {signalGrid : Nat → Nat → Signals.State}
    {west east south north size : Nat}
    (freeGrid : FreeGrid indexGrid shadeGrid west east south north size)
    (cycle : CycleOn indexGrid west east south north)
    (shaded : CycleShade shadeGrid west east south north .light)
    (valid : ValidGrid indexGrid shadeGrid signalGrid)
    (column row : Fin size) :
    signalGrid (freeGrid.columnAt column) (freeGrid.rowAt row) =
      Signals.clearState := by
  exact CycleShade.clear_at_free_crossing shaded cycle valid
    (freeGrid.column_west column) (freeGrid.column_east column)
    (freeGrid.row_south row) (freeGrid.row_north row)
    (freeGrid.freeRow row) (freeGrid.freeColumn column)

def singleton
    {indexGrid : Nat → Nat → Index}
    {shadeGrid : Nat → Nat → RedShades.State}
    {west east south north column row : Nat}
    (hwest : quarterWest west < column)
    (heast : column < quarterEast east)
    (hsouth : quarterSouth south < row)
    (hnorth : row < quarterNorth north)
    (freeColumn : IsFreeColumn indexGrid shadeGrid south north column)
    (freeRow : IsFreeRow indexGrid shadeGrid west east row) :
    FreeGrid indexGrid shadeGrid west east south north 1 where
  columnAt := fun _ => column
  rowAt := fun _ => row
  column_strictMono := by
    intro i j hij
    omega
  row_strictMono := by
    intro i j hij
    omega
  column_west := fun _ => hwest
  column_east := fun _ => heast
  row_south := fun _ => hsouth
  row_north := fun _ => hnorth
  freeColumn := fun _ => freeColumn
  freeRow := fun _ => freeRow

def FreeGrid.translate
    {depth : Nat} {grid : Nat → Nat → Index}
    {shadeGrid : Nat → Nat → RedShades.State}
    {blockX blockY west east south north size : Nat}
    (freeGrid : FreeGrid
      (RedCycles.iterateRefine depth (shiftGrid grid blockX blockY))
      (shiftQuarterGrid shadeGrid
        (2 ^ (depth + 1) * blockX) (2 ^ (depth + 1) * blockY))
      west east south north size) :
    FreeGrid (RedCycles.iterateRefine depth grid) shadeGrid
      (2 ^ depth * blockX + west) (2 ^ depth * blockX + east)
      (2 ^ depth * blockY + south) (2 ^ depth * blockY + north) size where
  columnAt := fun i => 2 ^ (depth + 1) * blockX + freeGrid.columnAt i
  rowAt := fun i => 2 ^ (depth + 1) * blockY + freeGrid.rowAt i
  column_strictMono := by
    intro i j hij
    exact Nat.add_lt_add_left (freeGrid.column_strictMono hij) _
  row_strictMono := by
    intro i j hij
    exact Nat.add_lt_add_left (freeGrid.row_strictMono hij) _
  column_west := by
    intro i
    have hoffset : 2 ^ (depth + 1) * blockX =
        2 * (2 ^ depth * blockX) := by
      rw [pow_succ]
      ac_rfl
    have hboundary : quarterWest (2 ^ depth * blockX + west) =
        2 ^ (depth + 1) * blockX + quarterWest west := by
      simp [quarterWest, hoffset]
      omega
    rw [hboundary]
    exact Nat.add_lt_add_left (freeGrid.column_west i) _
  column_east := by
    intro i
    have hoffset : 2 ^ (depth + 1) * blockX =
        2 * (2 ^ depth * blockX) := by
      rw [pow_succ]
      ac_rfl
    have hboundary : quarterEast (2 ^ depth * blockX + east) =
        2 ^ (depth + 1) * blockX + quarterEast east := by
      simp [quarterEast, hoffset]
      omega
    rw [hboundary]
    exact Nat.add_lt_add_left (freeGrid.column_east i) _
  row_south := by
    intro i
    have hoffset : 2 ^ (depth + 1) * blockY =
        2 * (2 ^ depth * blockY) := by
      rw [pow_succ]
      ac_rfl
    have hboundary : quarterSouth (2 ^ depth * blockY + south) =
        2 ^ (depth + 1) * blockY + quarterSouth south := by
      simp [quarterSouth, hoffset]
      omega
    rw [hboundary]
    exact Nat.add_lt_add_left (freeGrid.row_south i) _
  row_north := by
    intro i
    have hoffset : 2 ^ (depth + 1) * blockY =
        2 * (2 ^ depth * blockY) := by
      rw [pow_succ]
      ac_rfl
    have hboundary : quarterNorth (2 ^ depth * blockY + north) =
        2 ^ (depth + 1) * blockY + quarterNorth north := by
      simp [quarterNorth, hoffset]
      omega
    rw [hboundary]
    exact Nat.add_lt_add_left (freeGrid.row_north i) _
  freeColumn := by
    intro i
    exact (isFreeColumn_shift_iff depth grid shadeGrid
      blockX blockY south north (freeGrid.columnAt i)).1
        (freeGrid.freeColumn i)
  freeRow := by
    intro i
    exact (isFreeRow_shift_iff depth grid shadeGrid
      blockX blockY west east (freeGrid.rowAt i)).1
        (freeGrid.freeRow i)

end ShadedFreeGrid
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
