/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5/5.6
-/
import LeanWang.Robinson.Closed104.RedShadeGraphRefinementAudit
import Mathlib.Tactic.FinCases

/-! Kernel validation of the static connector forests. -/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace RedShadeGraphRefinement

set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

private theorem completeFor_eq_true_case0 : completeFor 0 = true := by
  decide +kernel

private theorem completeFor_eq_true_case1 : completeFor 1 = true := by
  decide +kernel

private theorem completeFor_eq_true_case2 : completeFor 2 = true := by
  decide +kernel

private theorem completeFor_eq_true_case3 : completeFor 3 = true := by
  decide +kernel

private theorem completeFor_eq_true_case4 : completeFor 4 = true := by
  decide +kernel

private theorem completeFor_eq_true_case5 : completeFor 5 = true := by
  decide +kernel

private theorem completeFor_eq_true_case6 : completeFor 6 = true := by
  decide +kernel

private theorem completeFor_eq_true_case7 : completeFor 7 = true := by
  decide +kernel

private theorem completeFor_eq_true_case8 : completeFor 8 = true := by
  decide +kernel

private theorem completeFor_eq_true_case9 : completeFor 9 = true := by
  decide +kernel

private theorem completeFor_eq_true_case10 : completeFor 10 = true := by
  decide +kernel

private theorem completeFor_eq_true_case11 : completeFor 11 = true := by
  decide +kernel

private theorem completeFor_eq_true_case12 : completeFor 12 = true := by
  decide +kernel

private theorem completeFor_eq_true_case13 : completeFor 13 = true := by
  decide +kernel

private theorem completeFor_eq_true_case14 : completeFor 14 = true := by
  decide +kernel

private theorem completeFor_eq_true_case15 : completeFor 15 = true := by
  decide +kernel

private theorem completeFor_eq_true_case16 : completeFor 16 = true := by
  decide +kernel

private theorem completeFor_eq_true_case17 : completeFor 17 = true := by
  decide +kernel

private theorem completeFor_eq_true_case18 : completeFor 18 = true := by
  decide +kernel

private theorem completeFor_eq_true_case19 : completeFor 19 = true := by
  decide +kernel

private theorem completeFor_eq_true_case20 : completeFor 20 = true := by
  decide +kernel

private theorem completeFor_eq_true_case21 : completeFor 21 = true := by
  decide +kernel

private theorem completeFor_eq_true_case22 : completeFor 22 = true := by
  decide +kernel

private theorem completeFor_eq_true_case23 : completeFor 23 = true := by
  decide +kernel

private theorem completeFor_eq_true_case24 : completeFor 24 = true := by
  decide +kernel

private theorem completeFor_eq_true_case25 : completeFor 25 = true := by
  decide +kernel

private theorem completeFor_eq_true_case26 : completeFor 26 = true := by
  decide +kernel

private theorem completeFor_eq_true_case27 : completeFor 27 = true := by
  decide +kernel

private theorem completeFor_eq_true_case28 : completeFor 28 = true := by
  decide +kernel

private theorem completeFor_eq_true_case29 : completeFor 29 = true := by
  decide +kernel

private theorem completeFor_eq_true_case30 : completeFor 30 = true := by
  decide +kernel

private theorem completeFor_eq_true_case31 : completeFor 31 = true := by
  decide +kernel

private theorem completeFor_eq_true_case32 : completeFor 32 = true := by
  decide +kernel

private theorem completeFor_eq_true_case33 : completeFor 33 = true := by
  decide +kernel

private theorem completeFor_eq_true_case34 : completeFor 34 = true := by
  decide +kernel

private theorem completeFor_eq_true_case35 : completeFor 35 = true := by
  decide +kernel

private theorem completeFor_eq_true_case36 : completeFor 36 = true := by
  decide +kernel

private theorem completeFor_eq_true_case37 : completeFor 37 = true := by
  decide +kernel

private theorem completeFor_eq_true_case38 : completeFor 38 = true := by
  decide +kernel

private theorem completeFor_eq_true_case39 : completeFor 39 = true := by
  decide +kernel

private theorem completeFor_eq_true_case40 : completeFor 40 = true := by
  decide +kernel

private theorem completeFor_eq_true_case41 : completeFor 41 = true := by
  decide +kernel

private theorem completeFor_eq_true_case42 : completeFor 42 = true := by
  decide +kernel

private theorem completeFor_eq_true_case43 : completeFor 43 = true := by
  decide +kernel

private theorem completeFor_eq_true_case44 : completeFor 44 = true := by
  decide +kernel

private theorem completeFor_eq_true_case45 : completeFor 45 = true := by
  decide +kernel

private theorem completeFor_eq_true_case46 : completeFor 46 = true := by
  decide +kernel

private theorem completeFor_eq_true_case47 : completeFor 47 = true := by
  decide +kernel

private theorem completeFor_eq_true_case48 : completeFor 48 = true := by
  decide +kernel

private theorem completeFor_eq_true_case49 : completeFor 49 = true := by
  decide +kernel

private theorem completeFor_eq_true_case50 : completeFor 50 = true := by
  decide +kernel

private theorem completeFor_eq_true_case51 : completeFor 51 = true := by
  decide +kernel

private theorem completeFor_eq_true_case52 : completeFor 52 = true := by
  decide +kernel

private theorem completeFor_eq_true_case53 : completeFor 53 = true := by
  decide +kernel

private theorem completeFor_eq_true_case54 : completeFor 54 = true := by
  decide +kernel

private theorem completeFor_eq_true_case55 : completeFor 55 = true := by
  decide +kernel

private theorem completeFor_eq_true_case56 : completeFor 56 = true := by
  decide +kernel

private theorem completeFor_eq_true_case57 : completeFor 57 = true := by
  decide +kernel

private theorem completeFor_eq_true_case58 : completeFor 58 = true := by
  decide +kernel

private theorem completeFor_eq_true_case59 : completeFor 59 = true := by
  decide +kernel

private theorem completeFor_eq_true_case60 : completeFor 60 = true := by
  decide +kernel

private theorem completeFor_eq_true_case61 : completeFor 61 = true := by
  decide +kernel

private theorem completeFor_eq_true_case62 : completeFor 62 = true := by
  decide +kernel

private theorem completeFor_eq_true_case63 : completeFor 63 = true := by
  decide +kernel

private theorem completeFor_eq_true_case64 : completeFor 64 = true := by
  decide +kernel

private theorem completeFor_eq_true_case65 : completeFor 65 = true := by
  decide +kernel

private theorem completeFor_eq_true_case66 : completeFor 66 = true := by
  decide +kernel

private theorem completeFor_eq_true_case67 : completeFor 67 = true := by
  decide +kernel

private theorem completeFor_eq_true_case68 : completeFor 68 = true := by
  decide +kernel

private theorem completeFor_eq_true_case69 : completeFor 69 = true := by
  decide +kernel

private theorem completeFor_eq_true_case70 : completeFor 70 = true := by
  decide +kernel

private theorem completeFor_eq_true_case71 : completeFor 71 = true := by
  decide +kernel

private theorem completeFor_eq_true_case72 : completeFor 72 = true := by
  decide +kernel

private theorem completeFor_eq_true_case73 : completeFor 73 = true := by
  decide +kernel

private theorem completeFor_eq_true_case74 : completeFor 74 = true := by
  decide +kernel

private theorem completeFor_eq_true_case75 : completeFor 75 = true := by
  decide +kernel

private theorem completeFor_eq_true_case76 : completeFor 76 = true := by
  decide +kernel

private theorem completeFor_eq_true_case77 : completeFor 77 = true := by
  decide +kernel

private theorem completeFor_eq_true_case78 : completeFor 78 = true := by
  decide +kernel

private theorem completeFor_eq_true_case79 : completeFor 79 = true := by
  decide +kernel

private theorem completeFor_eq_true_case80 : completeFor 80 = true := by
  decide +kernel

private theorem completeFor_eq_true_case81 : completeFor 81 = true := by
  decide +kernel

private theorem completeFor_eq_true_case82 : completeFor 82 = true := by
  decide +kernel

private theorem completeFor_eq_true_case83 : completeFor 83 = true := by
  decide +kernel

private theorem completeFor_eq_true_case84 : completeFor 84 = true := by
  decide +kernel

private theorem completeFor_eq_true_case85 : completeFor 85 = true := by
  decide +kernel

private theorem completeFor_eq_true_case86 : completeFor 86 = true := by
  decide +kernel

private theorem completeFor_eq_true_case87 : completeFor 87 = true := by
  decide +kernel

private theorem completeFor_eq_true_case88 : completeFor 88 = true := by
  decide +kernel

private theorem completeFor_eq_true_case89 : completeFor 89 = true := by
  decide +kernel

private theorem completeFor_eq_true_case90 : completeFor 90 = true := by
  decide +kernel

private theorem completeFor_eq_true_case91 : completeFor 91 = true := by
  decide +kernel

private theorem completeFor_eq_true_case92 : completeFor 92 = true := by
  decide +kernel

private theorem completeFor_eq_true_case93 : completeFor 93 = true := by
  decide +kernel

private theorem completeFor_eq_true_case94 : completeFor 94 = true := by
  decide +kernel

private theorem completeFor_eq_true_case95 : completeFor 95 = true := by
  decide +kernel

private theorem completeFor_eq_true_case96 : completeFor 96 = true := by
  decide +kernel

private theorem completeFor_eq_true_case97 : completeFor 97 = true := by
  decide +kernel

private theorem completeFor_eq_true_case98 : completeFor 98 = true := by
  decide +kernel

private theorem completeFor_eq_true_case99 : completeFor 99 = true := by
  decide +kernel

private theorem completeFor_eq_true_case100 : completeFor 100 = true := by
  decide +kernel

private theorem completeFor_eq_true_case101 : completeFor 101 = true := by
  decide +kernel

private theorem completeFor_eq_true_case102 : completeFor 102 = true := by
  decide +kernel

private theorem completeFor_eq_true_case103 : completeFor 103 = true := by
  decide +kernel

private theorem completeFor_eq_true (parent : Index) : completeFor parent = true := by
  fin_cases parent
  · exact completeFor_eq_true_case0
  · exact completeFor_eq_true_case1
  · exact completeFor_eq_true_case2
  · exact completeFor_eq_true_case3
  · exact completeFor_eq_true_case4
  · exact completeFor_eq_true_case5
  · exact completeFor_eq_true_case6
  · exact completeFor_eq_true_case7
  · exact completeFor_eq_true_case8
  · exact completeFor_eq_true_case9
  · exact completeFor_eq_true_case10
  · exact completeFor_eq_true_case11
  · exact completeFor_eq_true_case12
  · exact completeFor_eq_true_case13
  · exact completeFor_eq_true_case14
  · exact completeFor_eq_true_case15
  · exact completeFor_eq_true_case16
  · exact completeFor_eq_true_case17
  · exact completeFor_eq_true_case18
  · exact completeFor_eq_true_case19
  · exact completeFor_eq_true_case20
  · exact completeFor_eq_true_case21
  · exact completeFor_eq_true_case22
  · exact completeFor_eq_true_case23
  · exact completeFor_eq_true_case24
  · exact completeFor_eq_true_case25
  · exact completeFor_eq_true_case26
  · exact completeFor_eq_true_case27
  · exact completeFor_eq_true_case28
  · exact completeFor_eq_true_case29
  · exact completeFor_eq_true_case30
  · exact completeFor_eq_true_case31
  · exact completeFor_eq_true_case32
  · exact completeFor_eq_true_case33
  · exact completeFor_eq_true_case34
  · exact completeFor_eq_true_case35
  · exact completeFor_eq_true_case36
  · exact completeFor_eq_true_case37
  · exact completeFor_eq_true_case38
  · exact completeFor_eq_true_case39
  · exact completeFor_eq_true_case40
  · exact completeFor_eq_true_case41
  · exact completeFor_eq_true_case42
  · exact completeFor_eq_true_case43
  · exact completeFor_eq_true_case44
  · exact completeFor_eq_true_case45
  · exact completeFor_eq_true_case46
  · exact completeFor_eq_true_case47
  · exact completeFor_eq_true_case48
  · exact completeFor_eq_true_case49
  · exact completeFor_eq_true_case50
  · exact completeFor_eq_true_case51
  · exact completeFor_eq_true_case52
  · exact completeFor_eq_true_case53
  · exact completeFor_eq_true_case54
  · exact completeFor_eq_true_case55
  · exact completeFor_eq_true_case56
  · exact completeFor_eq_true_case57
  · exact completeFor_eq_true_case58
  · exact completeFor_eq_true_case59
  · exact completeFor_eq_true_case60
  · exact completeFor_eq_true_case61
  · exact completeFor_eq_true_case62
  · exact completeFor_eq_true_case63
  · exact completeFor_eq_true_case64
  · exact completeFor_eq_true_case65
  · exact completeFor_eq_true_case66
  · exact completeFor_eq_true_case67
  · exact completeFor_eq_true_case68
  · exact completeFor_eq_true_case69
  · exact completeFor_eq_true_case70
  · exact completeFor_eq_true_case71
  · exact completeFor_eq_true_case72
  · exact completeFor_eq_true_case73
  · exact completeFor_eq_true_case74
  · exact completeFor_eq_true_case75
  · exact completeFor_eq_true_case76
  · exact completeFor_eq_true_case77
  · exact completeFor_eq_true_case78
  · exact completeFor_eq_true_case79
  · exact completeFor_eq_true_case80
  · exact completeFor_eq_true_case81
  · exact completeFor_eq_true_case82
  · exact completeFor_eq_true_case83
  · exact completeFor_eq_true_case84
  · exact completeFor_eq_true_case85
  · exact completeFor_eq_true_case86
  · exact completeFor_eq_true_case87
  · exact completeFor_eq_true_case88
  · exact completeFor_eq_true_case89
  · exact completeFor_eq_true_case90
  · exact completeFor_eq_true_case91
  · exact completeFor_eq_true_case92
  · exact completeFor_eq_true_case93
  · exact completeFor_eq_true_case94
  · exact completeFor_eq_true_case95
  · exact completeFor_eq_true_case96
  · exact completeFor_eq_true_case97
  · exact completeFor_eq_true_case98
  · exact completeFor_eq_true_case99
  · exact completeFor_eq_true_case100
  · exact completeFor_eq_true_case101
  · exact completeFor_eq_true_case102
  · exact completeFor_eq_true_case103

theorem complete_eq_true : complete = true := by
  apply List.all_eq_true.mpr
  intro parent _
  exact completeFor_eq_true parent

theorem boundedComplete_eq_true : boundedComplete = true :=
  complete_eq_true

end RedShadeGraphRefinement
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
