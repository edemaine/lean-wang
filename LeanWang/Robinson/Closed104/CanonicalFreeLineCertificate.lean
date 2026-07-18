/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.CanonicalFreeLineChecks

/-! Proof-facing projections of the canonical free-line local audit. -/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace CanonicalFreeLine

open ShadedSubstitution

set_option maxRecDepth 20000

theorem evenLocalValid_of_mem {node : Nat} (hnode : node ∈ reachable) :
    evenLocalValid node = true := by
  exact List.all_eq_true.1 evenLocalComplete_eq_true node hnode

private theorem evenLocalCheck_of_mem {node : Nat} (hnode : node ∈ reachable)
    {check : Bool} (hcheck : check ∈ evenLocalChecks node) : check = true := by
  have checked := evenLocalValid_of_mem hnode
  exact List.all_eq_true.1 checked check hcheck

theorem row_zero_refines {node : Nat} (hnode : node ∈ reachable)
    (clear : rowClear node 0 = true) : fineRowClear node 0 = true := by
  have checked := evenLocalCheck_of_mem hnode (check :=
    !rowClear node 0 || fineRowClear node 0) (by simp [evenLocalChecks])
  simpa [clear] using checked

theorem row_one_refines {node : Nat} (hnode : node ∈ reachable)
    (clear : rowClear node 1 = true) :
    fineRowClear node 1 = true ∧ fineRowClear node 2 = true := by
  have checked := evenLocalCheck_of_mem hnode (check :=
    !rowClear node 1 ||
      (fineRowClear node 1 && fineRowClear node 2)) (by
        simp [evenLocalChecks])
  simpa [clear, Bool.and_eq_true] using checked

theorem column_zero_refines {node : Nat} (hnode : node ∈ reachable)
    (clear : columnClear node 0 = true) : fineColumnClear node 0 = true := by
  have checked := evenLocalCheck_of_mem hnode (check :=
    !columnClear node 0 || fineColumnClear node 0) (by
      simp [evenLocalChecks])
  simpa [clear] using checked

theorem column_one_refines {node : Nat} (hnode : node ∈ reachable)
    (clear : columnClear node 1 = true) :
    fineColumnClear node 1 = true ∧ fineColumnClear node 2 = true := by
  have checked := evenLocalCheck_of_mem hnode (check :=
    !columnClear node 1 ||
      (fineColumnClear node 1 && fineColumnClear node 2)) (by
        simp [evenLocalChecks])
  simpa [clear, Bool.and_eq_true] using checked

theorem west_strips_clear {node : Nat} (hnode : node ∈ reachable) :
    westStripClear node 0 = true ∧ westStripClear node 1 = true ∧
      westStripClear node 2 = true := by
  exact ⟨evenLocalCheck_of_mem hnode (by simp [evenLocalChecks]),
    evenLocalCheck_of_mem hnode (by simp [evenLocalChecks]),
    evenLocalCheck_of_mem hnode (by simp [evenLocalChecks])⟩

theorem south_strips_clear {node : Nat} (hnode : node ∈ reachable) :
    southStripClear node 0 = true ∧ southStripClear node 1 = true ∧
      southStripClear node 2 = true := by
  exact ⟨evenLocalCheck_of_mem hnode (by simp [evenLocalChecks]),
    evenLocalCheck_of_mem hnode (by simp [evenLocalChecks]),
    evenLocalCheck_of_mem hnode (by simp [evenLocalChecks])⟩

theorem cycleSourceShade_eq_dark {node : Nat} (hnode : node ∈ reachable) :
    cycleSourceShade? node = some .dark := by
  have checked := evenLocalCheck_of_mem hnode (check :=
    decide (cycleSourceShade? node = some .dark)) (by
      simp [evenLocalChecks])
  exact of_decide_eq_true checked

theorem evenBaseRowClear_eq_true : rowClear evenBaseNodeId 1 = true := by
  have checked := evenBaseValid_eq_true
  simp only [evenBaseValid, Bool.and_eq_true] at checked
  exact checked.1

theorem evenBaseColumnClear_eq_true : columnClear evenBaseNodeId 1 = true := by
  have checked := evenBaseValid_eq_true
  simp only [evenBaseValid, Bool.and_eq_true] at checked
  exact checked.2

end CanonicalFreeLine
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
