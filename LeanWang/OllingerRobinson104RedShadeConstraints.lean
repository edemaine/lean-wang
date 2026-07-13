/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104RedShadeGraphWeightedSearch

/-!
# Signed red-shade constraints

A weighted start records the shade expected at a red port: parity `false`
means light and parity `true` means dark.  A weighted graph flood is
inconsistent when it reaches any constrained port with the opposite total
parity.  This module proves that such an executable certificate contradicts a
valid shade grid.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace RedShadeConstraints

open RedShadeGraph RedShadeGraphSearch RedShadeGraphWeightedSearch RedShadePaths

def expectedValue (parity : Bool) : Option RedShades.Shade :=
  if parity then some .dark else some .light

def Holds (stateGrid : Nat → Nat → RedShades.State)
    (constraint : WeightedStart) : Prop :=
  value stateGrid constraint.port = expectedValue constraint.parity

def contradicts (constraints : List WeightedStart) (node : ReachNode) : Bool :=
  constraints.any fun constraint =>
    decide (node.current = constraint.port) &&
      decide (node.parity ≠ constraint.parity)

theorem related_expectedValue_iff {pathParity firstParity secondParity : Bool} :
    Related pathParity (expectedValue firstParity) (expectedValue secondParity) ↔
      pathParity = Bool.xor firstParity secondParity := by
  cases pathParity <;> cases firstParity <;> cases secondParity <;>
    simp [Related, expectedValue, RedShades.Shade.opposite]

theorem false_of_soundReach_contradicts
    {grid : Nat → Nat → Index}
    {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid grid stateGrid)
    {constraints : List WeightedStart} {node : ReachNode}
    (holds : ∀ constraint ∈ constraints, Holds stateGrid constraint)
    (sound : SoundReachFromWeighted grid constraints node)
    (conflict : contradicts constraints node = true) : False := by
  rcases sound with ⟨start, startMem, path⟩
  simp only [contradicts, List.any_eq_true, Bool.and_eq_true,
    decide_eq_true_eq] at conflict
  rcases conflict with ⟨target, targetMem, currentEq, parityNe⟩
  have related := path.sound valid
  rw [holds start startMem, currentEq, holds target targetMem] at related
  have parityEq := related_expectedValue_iff.mp related
  cases start.parity <;> cases node.parity <;> cases target.parity <;>
    simp_all

theorem false_of_exploreFastWeightedReach_contradicts
    {grid : Nat → Nat → Index}
    {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid grid stateGrid)
    {width height fuel : Nat} {constraints : List WeightedStart}
    {node : ReachNode}
    (holds : ∀ constraint ∈ constraints, Holds stateGrid constraint)
    (nodeMem : node ∈ exploreFastWeightedReach
      grid width height fuel constraints)
    (conflict : contradicts constraints node = true) : False := by
  exact false_of_soundReach_contradicts valid holds
    (exploreFastWeightedReach_sound nodeMem) conflict

end RedShadeConstraints
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
