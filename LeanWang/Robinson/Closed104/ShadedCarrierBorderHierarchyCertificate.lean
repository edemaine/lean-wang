/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5/5.6
-/
import LeanWang.Robinson.Closed104.ShadedCarrierBorderHierarchyCertificates.Group0
import LeanWang.Robinson.Closed104.ShadedCarrierBorderHierarchyCertificates.Group1
import LeanWang.Robinson.Closed104.ShadedCarrierBorderHierarchyCertificates.Group2
import LeanWang.Robinson.Closed104.ShadedCarrierBorderHierarchyCertificates.Group3
import LeanWang.Robinson.Closed104.ShadedCarrierBorderHierarchyCertificates.Group4
import LeanWang.Robinson.Closed104.ShadedCarrierBorderHierarchyCertificates.Group5
import LeanWang.Robinson.Closed104.ShadedCarrierBorderHierarchyCertificates.Group6
import LeanWang.Robinson.Closed104.ShadedCarrierBorderHierarchyCertificates.Group7
import LeanWang.Robinson.Closed104.ShadedCarrierBorderHierarchyCertificates.Group8
import LeanWang.Robinson.Closed104.ShadedCarrierBorderHierarchyCertificates.Group9
import LeanWang.Robinson.Closed104.ShadedCarrierBorderHierarchyCertificates.Group10
import LeanWang.Robinson.Closed104.ShadedCarrierBorderHierarchyCertificates.Group11
import LeanWang.Robinson.Closed104.ShadedCarrierBorderHierarchyCertificates.Group12
import LeanWang.Robinson.Closed104.ShadedCarrierBorderHierarchyCertificates.Group13
import LeanWang.Robinson.Closed104.ShadedCarrierBorderHierarchyCertificates.Group14
import LeanWang.Robinson.Closed104.ShadedCarrierBorderHierarchyCertificates.Group15

/-! Kernel certificates for the stored finite border invariant. -/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace ShadedCarrierBorderHierarchy

theorem statesValid_eq_true : statesValid = true := by
  simp only [statesValid, states, List.all_append,
    statesValid_group0, statesValid_group1, statesValid_group2,
    statesValid_group3, statesValid_group4, statesValid_group5,
    statesValid_group6, statesValid_group7, statesValid_group8,
    statesValid_group9, statesValid_group10, statesValid_group11,
    statesValid_group12, statesValid_group13, statesValid_group14,
    statesValid_group15, Bool.and_self]

theorem closedValid_eq_true : closedValid = true := by
  unfold closedValid
  change ((stateGroup0 ++
    stateGroup1 ++
    stateGroup2 ++
    stateGroup3 ++
    stateGroup4 ++
    stateGroup5 ++
    stateGroup6 ++
    stateGroup7 ++
    stateGroup8 ++
    stateGroup9 ++
    stateGroup10 ++
    stateGroup11 ++
    stateGroup12 ++
    stateGroup13 ++
    stateGroup14 ++
    stateGroup15).all fun candidate =>
    (stateChildren candidate).all fun child => child ∈ states) = true
  simp only [List.all_append,
    closedValid_group0, closedValid_group1, closedValid_group2,
    closedValid_group3, closedValid_group4, closedValid_group5,
    closedValid_group6, closedValid_group7, closedValid_group8,
    closedValid_group9, closedValid_group10, closedValid_group11,
    closedValid_group12, closedValid_group13, closedValid_group14,
    closedValid_group15, Bool.and_self]


theorem cornerTransitionsValid_eq_true : cornerTransitionsValid = true := by
  simp only [cornerTransitionsValid, states, List.all_append,
    cornerTransitionsValid_group0, cornerTransitionsValid_group1, cornerTransitionsValid_group2,
    cornerTransitionsValid_group3, cornerTransitionsValid_group4, cornerTransitionsValid_group5,
    cornerTransitionsValid_group6, cornerTransitionsValid_group7, cornerTransitionsValid_group8,
    cornerTransitionsValid_group9, cornerTransitionsValid_group10, cornerTransitionsValid_group11,
    cornerTransitionsValid_group12, cornerTransitionsValid_group13, cornerTransitionsValid_group14,
    cornerTransitionsValid_group15, Bool.and_self]

theorem initialState_mem : state 0 0 0 ∈ states := by
  decide +kernel

end ShadedCarrierBorderHierarchy
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
