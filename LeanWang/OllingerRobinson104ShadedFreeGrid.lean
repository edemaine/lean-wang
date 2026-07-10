/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104ShadedFreeLineSeed
import LeanWang.OllingerRobinson104ShadedFreeLineTranslation

/-!
Ordered finite grids of free rows and columns inside shaded Robinson boards.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace ShadedFreeGrid

open OrientedRedCycles RedShadeCycles ShadedPlaneSignalGrid

set_option maxRecDepth 20000

structure FreeGrid (indexGrid : Nat → Nat → Index)
    (shadeGrid : Nat → Nat → RedShades.State)
    (west east south north size : Nat) : Prop where
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

theorem center_at (grid : Nat → Nat → Index)
    (shadeGrid : Nat → Nat → RedShades.State) (blockX blockY : Nat) :
    FreeGrid (RedCycles.iterateRefine 4 grid) shadeGrid
      (16 * blockX + 4) (16 * blockX + 12)
      (16 * blockY + 4) (16 * blockY + 12) 1 := by
  apply singleton
  · simp [quarterWest]
  · simp [quarterEast]
  · simp [quarterSouth]
  · simp [quarterNorth]
  · exact ShadedFreeLineSeed.centerColumn_free_at
      grid shadeGrid blockX blockY
  · exact ShadedFreeLineSeed.centerRow_free_at
      grid shadeGrid blockX blockY

end ShadedFreeGrid
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
