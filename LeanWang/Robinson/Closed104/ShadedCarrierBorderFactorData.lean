/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.ShadedSignalRectangle
import LeanWang.Robinson.Closed104.ShadedSubstitutionData

/-!
# Finite selected-border factor of the shaded substitution

Only the selected horizontal and vertical border orientations affect the
canonical obstruction signals.  Partition refinement reduces the 312
reachable decorated substitution states to a stable 16-state Moore factor.
The definitions here are executable; the native certificate and proof-facing
projection lemmas are kept in a separate module.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace ShadedCarrierBorderFactor

open ShadedSubstitution Signals.FreeCellLocal

/-- The four row-border and four column-border observations in one `2 x 2`
quarter block, in row-major order. -/
abbrev BorderPatch := List (Option Bool)

def emptyPatch : BorderPatch := List.replicate 8 none

def patchData (data : DecoratedData) : BorderPatch :=
  let indexGrid : Nat → Nat → Index := fun _ _ => data.parent
  let shadeGrid : Nat → Nat → RedShades.State := fun x y =>
    data.block.at (x % 2) (y % 2)
  let rows := (List.range 2).flatMap fun y => (List.range 2).map fun x =>
    ShadedSignalRectangle.horizontalInteriorCode <|
      ShadedSignals.selectedVerticalFor
        (componentAt indexGrid x y) (quadrantAt x y) (shadeGrid x y)
  let columns := (List.range 2).flatMap fun y => (List.range 2).map fun x =>
    ShadedSignalRectangle.verticalInteriorCode <|
      ShadedSignals.selectedHorizontalFor
        (componentAt indexGrid x y) (quadrantAt x y) (shadeGrid x y)
  rows ++ columns

def patch (node : Nat) : Option BorderPatch :=
  (modelData node).map patchData

def patches : List BorderPatch :=
  (reachable.filterMap patch).eraseDups

def patchIndex (node : Nat) : Nat :=
  ((patch node).bind fun nodePatch =>
    patches.findIdx? fun candidate => candidate = nodePatch).getD 0

/-- Every encoded context/state pair lies below this bound. -/
def nodeBound : Nat := 2 * stateInfos.length

abbrev ClassMap := Array Nat

/-- Initial Moore partition by the visible `2 x 2` border patch. -/
def patchClasses : ClassMap :=
  reachable.foldl (fun classes node =>
    classes.set! node (patchIndex node)) (Array.replicate nodeBound 0)

/-- One refinement signature: current output followed by the classes of all
sixteen children. -/
def signature (classes : ClassMap) (node : Nat) : List Nat :=
  patchIndex node :: (List.range 16).map fun position =>
    classes[((childNode node position).getD 0)]!

/-- One Moore partition-refinement step. -/
def refineClasses (classes : ClassMap) : ClassMap :=
  let entries := reachable.map fun node => (node, signature classes node)
  let signatures := (entries.map Prod.snd).eraseDups
  entries.foldl (fun result entry =>
    result.set! entry.1
      ((signatures.findIdx? fun candidate => candidate = entry.2).getD 0))
    (Array.replicate nodeBound 0)

/-- Stable 16-state selected-border class of every reachable node. -/
def classes : ClassMap := refineClasses patchClasses

def classOf (node : Nat) : Nat := classes[node]!

def classCount : Nat :=
  (reachable.map classOf).eraseDups.length

def representative (classId : Nat) : Nat :=
  (reachable.find? fun node => classOf node = classId).getD 0

def classPatch (classId : Nat) : BorderPatch :=
  (patch (representative classId)).getD emptyPatch

def childClass (classId position : Nat) : Nat :=
  classOf ((childNode (representative classId) position).getD 0)

def nodeClassValid (node : Nat) : Bool :=
  node < nodeBound && classOf node < 16

def nodePatchValid (node : Nat) : Bool :=
  decide (patch node = some (classPatch (classOf node)))

def nodeChildrenValid (node : Nat) : Bool :=
  (List.range 16).all fun position =>
    match childNode node position with
    | none => false
    | some child => classOf child = childClass (classOf node) position

def nodeFactorValid (node : Nat) : Bool :=
  nodeClassValid node && nodePatchValid node && nodeChildrenValid node

/-- Executable closure certificate for the minimized factor. -/
def factorValid : Bool :=
  decide (patches.length = 9) && decide (classCount = 16) &&
    reachable.all nodeFactorValid

end ShadedCarrierBorderFactor
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
