/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.RedShadeGraph
import LeanWang.Robinson.Closed104.RedShadeCycles

/-!
Semantic endpoints for parity paths starting on uniformly shaded boards.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace RedShadeGraphBoards

open OrientedRedCycles RedShadeCycles RedShadeGraph RedShadePaths

/-- A strict-interior edge port on one of an oriented board's four sides. -/
inductive OnCycle (west east south north : Nat) : Port → Prop where
  | southWest (qx : Nat)
      (hwest : quarterWest west < qx) (heast : qx < quarterEast east) :
      OnCycle west east south north ⟨qx, quarterSouth south, .west⟩
  | southEast (qx : Nat)
      (hwest : quarterWest west < qx) (heast : qx < quarterEast east) :
      OnCycle west east south north ⟨qx, quarterSouth south, .east⟩
  | northWest (qx : Nat)
      (hwest : quarterWest west < qx) (heast : qx < quarterEast east) :
      OnCycle west east south north ⟨qx, quarterNorth north, .west⟩
  | northEast (qx : Nat)
      (hwest : quarterWest west < qx) (heast : qx < quarterEast east) :
      OnCycle west east south north ⟨qx, quarterNorth north, .east⟩
  | westSouth (qy : Nat)
      (hsouth : quarterSouth south < qy) (hnorth : qy < quarterNorth north) :
      OnCycle west east south north ⟨quarterWest west, qy, .south⟩
  | westNorth (qy : Nat)
      (hsouth : quarterSouth south < qy) (hnorth : qy < quarterNorth north) :
      OnCycle west east south north ⟨quarterWest west, qy, .north⟩
  | eastSouth (qy : Nat)
      (hsouth : quarterSouth south < qy) (hnorth : qy < quarterNorth north) :
      OnCycle west east south north ⟨quarterEast east, qy, .south⟩
  | eastNorth (qy : Nat)
      (hsouth : quarterSouth south < qy) (hnorth : qy < quarterNorth north) :
      OnCycle west east south north ⟨quarterEast east, qy, .north⟩

theorem OnCycle.value_eq
    {grid : Nat → Nat → Index}
    {stateGrid : Nat → Nat → RedShades.State}
    {west east south north : Nat} {shade : RedShades.Shade} {port : Port}
    (onCycle : OnCycle west east south north port)
    (cycle : CycleOn grid west east south north)
    (shaded : CycleShade stateGrid west east south north shade)
    (valid : ValidShadeGrid grid stateGrid) :
    value stateGrid port = some shade := by
  cases onCycle with
  | southWest qx hwest heast => exact (shaded.south_at cycle valid hwest heast).1
  | southEast qx hwest heast => exact (shaded.south_at cycle valid hwest heast).2
  | northWest qx hwest heast => exact (shaded.north_at cycle valid hwest heast).1
  | northEast qx hwest heast => exact (shaded.north_at cycle valid hwest heast).2
  | westSouth qy hsouth hnorth => exact (shaded.west_at cycle valid hsouth hnorth).1
  | westNorth qy hsouth hnorth => exact (shaded.west_at cycle valid hsouth hnorth).2
  | eastSouth qy hsouth hnorth => exact (shaded.east_at cycle valid hsouth hnorth).1
  | eastNorth qy hsouth hnorth => exact (shaded.east_at cycle valid hsouth hnorth).2

theorem end_eq_opposite_of_odd_path
    {grid : Nat → Nat → Index}
    {stateGrid : Nat → Nat → RedShades.State}
    {start finish : Port} {shade : RedShades.Shade}
    (valid : ValidShadeGrid grid stateGrid)
    (path : Path grid start finish true)
    (hstart : value stateGrid start = some shade) :
    value stateGrid finish = some shade.opposite := by
  rcases path.sound valid with ⟨pathShade, hpathStart, hpathFinish⟩
  have hshade : pathShade = shade :=
    Option.some.inj (hpathStart.symm.trans hstart)
  subst pathShade
  exact hpathFinish

/-- An odd path from a light board side ends on a dark red edge. -/
theorem dark_at_end_of_light_cycle
    {grid : Nat → Nat → Index}
    {stateGrid : Nat → Nat → RedShades.State}
    {west east south north : Nat} {start finish : Port}
    (valid : ValidShadeGrid grid stateGrid)
    (cycle : CycleOn grid west east south north)
    (shaded : CycleShade stateGrid west east south north .light)
    (onCycle : OnCycle west east south north start)
    (path : Path grid start finish true) :
    value stateGrid finish = some .dark := by
  exact end_eq_opposite_of_odd_path valid path
    (onCycle.value_eq cycle shaded valid)

end RedShadeGraphBoards
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
