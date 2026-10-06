/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5/5.6
-/
import LeanWang.Robinson.Closed104.ShadedSubstitutionData

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104.ShadedSubstitution.LocalCertificates

def closedAt (node : Nat) : Bool :=
  modelNodeValid node && (children node).all fun child => decide (child ∈ reachable)

def pairsAt (first : Nat) : Bool :=
  reachable.all fun second =>
    match modelData first, modelData second with
    | some firstData, some secondData =>
        decoratedHCompatible firstData secondData && decoratedVCompatible firstData secondData
    | _, _ => false

def structureAt (node : Nat) : Bool :=
  match modelData node with
  | none => false
  | some data =>
      decide (data.block ∈ validShadeBlocks data.parent) && expansionInternallyValid data &&
        (List.range 16).all fun position => modelChildValid node position

end LeanWang.OllingerRobinson.Figure13Layers.Closed104.ShadedSubstitution.LocalCertificates
