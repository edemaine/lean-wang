/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5/5.6
-/
import LeanWang.Robinson.Closed104.Hierarchy
import Mathlib.Tactic.FinCases

/-!
Finite primitivity certificate for the corrected Ollinger substitution.

After five substitutions, the descendants of every parent contain all 104 tile
types. This supplies the uniform recurrence needed to find board patterns in an
arbitrary desubstitution hierarchy, independently of its chosen coarse tiles.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace Primitivity

/-- Four immediate substitution children, in southwest-first order. -/
def childrenAt (parent : Index) : List Index :=
  [childBlock parent ⟨0, by decide⟩ ⟨0, by decide⟩,
    childBlock parent ⟨1, by decide⟩ ⟨0, by decide⟩,
    childBlock parent ⟨0, by decide⟩ ⟨1, by decide⟩,
    childBlock parent ⟨1, by decide⟩ ⟨1, by decide⟩]

/-- The cached transition table, checked below against the substitution. -/
def childrenTable : List (List Index) :=
  ([[0, 22, 57, 4], [1, 20, 63, 4], [2, 26, 69, 4], [3, 24, 75, 4], [0, 17, 61, 7], [1, 16, 67, 7], [2, 19, 73, 7], [3, 18, 79, 7], [32, 8, 76, 5], [33, 9, 76, 5], [34, 10, 76, 5], [35, 11, 76, 5], [36, 29, 58, 5], [37, 31, 58, 5], [38, 9, 58, 5], [39, 11, 58, 5], [40, 28, 64, 5], [41, 30, 64, 5], [42, 8, 64, 5], [43, 10, 64, 5], [44, 28, 70, 5], [45, 29, 70, 5], [46, 30, 70, 5], [47, 31, 70, 5], [48, 8, 70, 5], [49, 9, 70, 5], [50, 10, 70, 5], [51, 11, 70, 5], [52, 28, 76, 5], [53, 29, 76, 5], [54, 30, 76, 5], [55, 31, 76, 5], [32, 24, 74, 4], [33, 25, 74, 4], [34, 26, 74, 4], [35, 27, 74, 4], [36, 21, 56, 4], [37, 23, 56, 4], [38, 25, 56, 4], [39, 27, 56, 4], [40, 20, 62, 4], [41, 22, 62, 4], [42, 24, 62, 4], [43, 26, 62, 4], [44, 20, 68, 4], [45, 21, 68, 4], [46, 22, 68, 4], [47, 23, 68, 4], [48, 24, 68, 4], [49, 25, 68, 4], [50, 26, 68, 4], [51, 27, 68, 4], [52, 20, 74, 4], [53, 21, 74, 4], [54, 22, 74, 4], [55, 23, 74, 4], [80, 12, 59, 6], [81, 12, 60, 6], [82, 13, 59, 6], [83, 14, 59, 6], [84, 14, 60, 6], [85, 15, 60, 6], [86, 12, 65, 6], [87, 12, 66, 6], [88, 13, 65, 6], [89, 14, 65, 6], [90, 14, 66, 6], [91, 15, 66, 6], [92, 12, 71, 6], [93, 12, 72, 6], [94, 13, 71, 6], [95, 14, 71, 6], [96, 14, 72, 6], [97, 15, 72, 6], [98, 12, 77, 6], [99, 12, 78, 6], [100, 13, 77, 6], [101, 14, 77, 6], [102, 14, 78, 6], [103, 15, 78, 6], [80, 21, 56, 4], [81, 21, 57, 4], [82, 23, 56, 4], [83, 25, 56, 4], [84, 25, 57, 4], [85, 27, 57, 4], [86, 21, 62, 4], [87, 21, 63, 4], [88, 23, 62, 4], [89, 25, 62, 4], [90, 25, 63, 4], [91, 27, 63, 4], [92, 21, 68, 4], [93, 21, 69, 4], [94, 23, 68, 4], [95, 25, 68, 4], [96, 25, 69, 4], [97, 27, 69, 4], [98, 21, 74, 4], [99, 21, 75, 4], [100, 23, 74, 4], [101, 25, 74, 4], [102, 25, 75, 4], [103, 27, 75, 4]] : List (List Nat)).map (fun row =>
    row.map (fun n => (⟨n % 104, Nat.mod_lt _ (by decide)⟩ : Index)))

def children (parent : Index) : List Index :=
  childrenTable.getD parent.val []

set_option maxRecDepth 20000 in
private theorem allChildrenTableCorrect :
    ∀ parent : Index, children parent = childrenAt parent := by
  intro parent
  fin_cases parent <;> decide +kernel

theorem children_eq_childrenAt (parent : Index) :
    children parent = childrenAt parent :=
  allChildrenTableCorrect parent

/-- Set-like list of tile types reached after exactly `level` substitutions. -/
def descendants : Nat → Index → List Index
  | 0, parent => [parent]
  | level + 1, parent =>
      ((descendants level parent).flatMap children).eraseDups

@[simp]
theorem mem_descendants_zero {parent target : Index} :
    target ∈ descendants 0 parent ↔ target = parent := by
  simp [descendants]

theorem mem_descendants_succ {level : Nat} {parent target : Index} :
    target ∈ descendants (level + 1) parent ↔
      ∃ middle ∈ descendants level parent, target ∈ children middle := by
  simp [descendants]

set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

private theorem reachAllAtFive_0 :
    (descendants 5 0).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_1 :
    (descendants 5 1).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_2 :
    (descendants 5 2).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_3 :
    (descendants 5 3).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_4 :
    (descendants 5 4).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_5 :
    (descendants 5 5).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_6 :
    (descendants 5 6).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_7 :
    (descendants 5 7).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_8 :
    (descendants 5 8).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_9 :
    (descendants 5 9).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_10 :
    (descendants 5 10).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_11 :
    (descendants 5 11).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_12 :
    (descendants 5 12).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_13 :
    (descendants 5 13).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_14 :
    (descendants 5 14).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_15 :
    (descendants 5 15).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_16 :
    (descendants 5 16).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_17 :
    (descendants 5 17).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_18 :
    (descendants 5 18).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_19 :
    (descendants 5 19).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_20 :
    (descendants 5 20).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_21 :
    (descendants 5 21).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_22 :
    (descendants 5 22).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_23 :
    (descendants 5 23).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_24 :
    (descendants 5 24).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_25 :
    (descendants 5 25).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_26 :
    (descendants 5 26).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_27 :
    (descendants 5 27).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_28 :
    (descendants 5 28).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_29 :
    (descendants 5 29).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_30 :
    (descendants 5 30).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_31 :
    (descendants 5 31).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_32 :
    (descendants 5 32).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_33 :
    (descendants 5 33).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_34 :
    (descendants 5 34).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_35 :
    (descendants 5 35).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_36 :
    (descendants 5 36).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_37 :
    (descendants 5 37).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_38 :
    (descendants 5 38).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_39 :
    (descendants 5 39).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_40 :
    (descendants 5 40).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_41 :
    (descendants 5 41).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_42 :
    (descendants 5 42).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_43 :
    (descendants 5 43).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_44 :
    (descendants 5 44).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_45 :
    (descendants 5 45).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_46 :
    (descendants 5 46).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_47 :
    (descendants 5 47).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_48 :
    (descendants 5 48).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_49 :
    (descendants 5 49).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_50 :
    (descendants 5 50).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_51 :
    (descendants 5 51).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_52 :
    (descendants 5 52).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_53 :
    (descendants 5 53).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_54 :
    (descendants 5 54).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_55 :
    (descendants 5 55).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_56 :
    (descendants 5 56).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_57 :
    (descendants 5 57).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_58 :
    (descendants 5 58).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_59 :
    (descendants 5 59).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_60 :
    (descendants 5 60).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_61 :
    (descendants 5 61).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_62 :
    (descendants 5 62).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_63 :
    (descendants 5 63).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_64 :
    (descendants 5 64).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_65 :
    (descendants 5 65).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_66 :
    (descendants 5 66).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_67 :
    (descendants 5 67).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_68 :
    (descendants 5 68).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_69 :
    (descendants 5 69).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_70 :
    (descendants 5 70).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_71 :
    (descendants 5 71).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_72 :
    (descendants 5 72).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_73 :
    (descendants 5 73).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_74 :
    (descendants 5 74).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_75 :
    (descendants 5 75).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_76 :
    (descendants 5 76).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_77 :
    (descendants 5 77).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_78 :
    (descendants 5 78).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_79 :
    (descendants 5 79).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_80 :
    (descendants 5 80).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_81 :
    (descendants 5 81).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_82 :
    (descendants 5 82).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_83 :
    (descendants 5 83).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_84 :
    (descendants 5 84).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_85 :
    (descendants 5 85).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_86 :
    (descendants 5 86).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_87 :
    (descendants 5 87).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_88 :
    (descendants 5 88).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_89 :
    (descendants 5 89).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_90 :
    (descendants 5 90).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_91 :
    (descendants 5 91).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_92 :
    (descendants 5 92).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_93 :
    (descendants 5 93).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_94 :
    (descendants 5 94).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_95 :
    (descendants 5 95).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_96 :
    (descendants 5 96).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_97 :
    (descendants 5 97).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_98 :
    (descendants 5 98).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_99 :
    (descendants 5 99).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_100 :
    (descendants 5 100).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_101 :
    (descendants 5 101).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_102 :
    (descendants 5 102).toFinset = Finset.univ := by
  decide +kernel

private theorem reachAllAtFive_103 :
    (descendants 5 103).toFinset = Finset.univ := by
  decide +kernel

private theorem allReachAllAtFive :
    ∀ parent : Index, (descendants 5 parent).toFinset = Finset.univ := by
  intro parent
  fin_cases parent
  · exact reachAllAtFive_0
  · exact reachAllAtFive_1
  · exact reachAllAtFive_2
  · exact reachAllAtFive_3
  · exact reachAllAtFive_4
  · exact reachAllAtFive_5
  · exact reachAllAtFive_6
  · exact reachAllAtFive_7
  · exact reachAllAtFive_8
  · exact reachAllAtFive_9
  · exact reachAllAtFive_10
  · exact reachAllAtFive_11
  · exact reachAllAtFive_12
  · exact reachAllAtFive_13
  · exact reachAllAtFive_14
  · exact reachAllAtFive_15
  · exact reachAllAtFive_16
  · exact reachAllAtFive_17
  · exact reachAllAtFive_18
  · exact reachAllAtFive_19
  · exact reachAllAtFive_20
  · exact reachAllAtFive_21
  · exact reachAllAtFive_22
  · exact reachAllAtFive_23
  · exact reachAllAtFive_24
  · exact reachAllAtFive_25
  · exact reachAllAtFive_26
  · exact reachAllAtFive_27
  · exact reachAllAtFive_28
  · exact reachAllAtFive_29
  · exact reachAllAtFive_30
  · exact reachAllAtFive_31
  · exact reachAllAtFive_32
  · exact reachAllAtFive_33
  · exact reachAllAtFive_34
  · exact reachAllAtFive_35
  · exact reachAllAtFive_36
  · exact reachAllAtFive_37
  · exact reachAllAtFive_38
  · exact reachAllAtFive_39
  · exact reachAllAtFive_40
  · exact reachAllAtFive_41
  · exact reachAllAtFive_42
  · exact reachAllAtFive_43
  · exact reachAllAtFive_44
  · exact reachAllAtFive_45
  · exact reachAllAtFive_46
  · exact reachAllAtFive_47
  · exact reachAllAtFive_48
  · exact reachAllAtFive_49
  · exact reachAllAtFive_50
  · exact reachAllAtFive_51
  · exact reachAllAtFive_52
  · exact reachAllAtFive_53
  · exact reachAllAtFive_54
  · exact reachAllAtFive_55
  · exact reachAllAtFive_56
  · exact reachAllAtFive_57
  · exact reachAllAtFive_58
  · exact reachAllAtFive_59
  · exact reachAllAtFive_60
  · exact reachAllAtFive_61
  · exact reachAllAtFive_62
  · exact reachAllAtFive_63
  · exact reachAllAtFive_64
  · exact reachAllAtFive_65
  · exact reachAllAtFive_66
  · exact reachAllAtFive_67
  · exact reachAllAtFive_68
  · exact reachAllAtFive_69
  · exact reachAllAtFive_70
  · exact reachAllAtFive_71
  · exact reachAllAtFive_72
  · exact reachAllAtFive_73
  · exact reachAllAtFive_74
  · exact reachAllAtFive_75
  · exact reachAllAtFive_76
  · exact reachAllAtFive_77
  · exact reachAllAtFive_78
  · exact reachAllAtFive_79
  · exact reachAllAtFive_80
  · exact reachAllAtFive_81
  · exact reachAllAtFive_82
  · exact reachAllAtFive_83
  · exact reachAllAtFive_84
  · exact reachAllAtFive_85
  · exact reachAllAtFive_86
  · exact reachAllAtFive_87
  · exact reachAllAtFive_88
  · exact reachAllAtFive_89
  · exact reachAllAtFive_90
  · exact reachAllAtFive_91
  · exact reachAllAtFive_92
  · exact reachAllAtFive_93
  · exact reachAllAtFive_94
  · exact reachAllAtFive_95
  · exact reachAllAtFive_96
  · exact reachAllAtFive_97
  · exact reachAllAtFive_98
  · exact reachAllAtFive_99
  · exact reachAllAtFive_100
  · exact reachAllAtFive_101
  · exact reachAllAtFive_102
  · exact reachAllAtFive_103

/-- Every tile type occurs below every parent after five substitutions. -/
theorem mem_descendants_five (parent target : Index) :
    target ∈ descendants 5 parent := by
  have hall := allReachAllAtFive parent
  have htarget : target ∈ (descendants 5 parent).toFinset := by
    rw [hall]
    exact Finset.mem_univ target
  simpa using htarget

/-- In particular, the fifth descendant set is the full corrected alphabet. -/
theorem descendants_five_toFinset (parent : Index) :
    (descendants 5 parent).toFinset = Finset.univ := by
  ext target
  simp only [List.mem_toFinset, Finset.mem_univ, iff_true]
  exact mem_descendants_five parent target

end Primitivity
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
