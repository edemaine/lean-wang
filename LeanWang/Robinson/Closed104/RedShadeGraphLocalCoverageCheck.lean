/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5/5.6
-/
import LeanWang.Robinson.Closed104.RedShadeGraphLocalCoverageCertificates.Group0
import LeanWang.Robinson.Closed104.RedShadeGraphLocalCoverageCertificates.Group1
import LeanWang.Robinson.Closed104.RedShadeGraphLocalCoverageCertificates.Group2
import LeanWang.Robinson.Closed104.RedShadeGraphLocalCoverageCertificates.Group3
import Mathlib.Tactic.FinCases

/-! Kernel validation of the static local red-graph forests. -/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace RedShadeGraphLocalCoverage

set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

private theorem parentCovered_eq_true (parent : Index) : parentCovered parent = true := by
  fin_cases parent
  · exact parentCovered_eq_true_case0
  · exact parentCovered_eq_true_case1
  · exact parentCovered_eq_true_case2
  · exact parentCovered_eq_true_case3
  · exact parentCovered_eq_true_case4
  · exact parentCovered_eq_true_case5
  · exact parentCovered_eq_true_case6
  · exact parentCovered_eq_true_case7
  · exact parentCovered_eq_true_case8
  · exact parentCovered_eq_true_case9
  · exact parentCovered_eq_true_case10
  · exact parentCovered_eq_true_case11
  · exact parentCovered_eq_true_case12
  · exact parentCovered_eq_true_case13
  · exact parentCovered_eq_true_case14
  · exact parentCovered_eq_true_case15
  · exact parentCovered_eq_true_case16
  · exact parentCovered_eq_true_case17
  · exact parentCovered_eq_true_case18
  · exact parentCovered_eq_true_case19
  · exact parentCovered_eq_true_case20
  · exact parentCovered_eq_true_case21
  · exact parentCovered_eq_true_case22
  · exact parentCovered_eq_true_case23
  · exact parentCovered_eq_true_case24
  · exact parentCovered_eq_true_case25
  · exact parentCovered_eq_true_case26
  · exact parentCovered_eq_true_case27
  · exact parentCovered_eq_true_case28
  · exact parentCovered_eq_true_case29
  · exact parentCovered_eq_true_case30
  · exact parentCovered_eq_true_case31
  · exact parentCovered_eq_true_case32
  · exact parentCovered_eq_true_case33
  · exact parentCovered_eq_true_case34
  · exact parentCovered_eq_true_case35
  · exact parentCovered_eq_true_case36
  · exact parentCovered_eq_true_case37
  · exact parentCovered_eq_true_case38
  · exact parentCovered_eq_true_case39
  · exact parentCovered_eq_true_case40
  · exact parentCovered_eq_true_case41
  · exact parentCovered_eq_true_case42
  · exact parentCovered_eq_true_case43
  · exact parentCovered_eq_true_case44
  · exact parentCovered_eq_true_case45
  · exact parentCovered_eq_true_case46
  · exact parentCovered_eq_true_case47
  · exact parentCovered_eq_true_case48
  · exact parentCovered_eq_true_case49
  · exact parentCovered_eq_true_case50
  · exact parentCovered_eq_true_case51
  · exact parentCovered_eq_true_case52
  · exact parentCovered_eq_true_case53
  · exact parentCovered_eq_true_case54
  · exact parentCovered_eq_true_case55
  · exact parentCovered_eq_true_case56
  · exact parentCovered_eq_true_case57
  · exact parentCovered_eq_true_case58
  · exact parentCovered_eq_true_case59
  · exact parentCovered_eq_true_case60
  · exact parentCovered_eq_true_case61
  · exact parentCovered_eq_true_case62
  · exact parentCovered_eq_true_case63
  · exact parentCovered_eq_true_case64
  · exact parentCovered_eq_true_case65
  · exact parentCovered_eq_true_case66
  · exact parentCovered_eq_true_case67
  · exact parentCovered_eq_true_case68
  · exact parentCovered_eq_true_case69
  · exact parentCovered_eq_true_case70
  · exact parentCovered_eq_true_case71
  · exact parentCovered_eq_true_case72
  · exact parentCovered_eq_true_case73
  · exact parentCovered_eq_true_case74
  · exact parentCovered_eq_true_case75
  · exact parentCovered_eq_true_case76
  · exact parentCovered_eq_true_case77
  · exact parentCovered_eq_true_case78
  · exact parentCovered_eq_true_case79
  · exact parentCovered_eq_true_case80
  · exact parentCovered_eq_true_case81
  · exact parentCovered_eq_true_case82
  · exact parentCovered_eq_true_case83
  · exact parentCovered_eq_true_case84
  · exact parentCovered_eq_true_case85
  · exact parentCovered_eq_true_case86
  · exact parentCovered_eq_true_case87
  · exact parentCovered_eq_true_case88
  · exact parentCovered_eq_true_case89
  · exact parentCovered_eq_true_case90
  · exact parentCovered_eq_true_case91
  · exact parentCovered_eq_true_case92
  · exact parentCovered_eq_true_case93
  · exact parentCovered_eq_true_case94
  · exact parentCovered_eq_true_case95
  · exact parentCovered_eq_true_case96
  · exact parentCovered_eq_true_case97
  · exact parentCovered_eq_true_case98
  · exact parentCovered_eq_true_case99
  · exact parentCovered_eq_true_case100
  · exact parentCovered_eq_true_case101
  · exact parentCovered_eq_true_case102
  · exact parentCovered_eq_true_case103

theorem allParentsCovered_eq_true : allParentsCovered = true := by
  apply List.all_eq_true.mpr
  intro parent _
  exact parentCovered_eq_true parent

theorem baseCovered_eq_true : baseCovered = true := by
  decide +kernel

end RedShadeGraphLocalCoverage
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
