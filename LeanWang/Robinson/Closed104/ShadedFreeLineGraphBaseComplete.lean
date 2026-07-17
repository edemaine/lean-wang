/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.ShadedFreeLineGraphBaseAudit

/-!
Project the cached all-parent native audit to one arbitrary parent.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace ShadedFreeLineGraphBase

set_option maxRecDepth 100000

set_option maxHeartbeats 2000000 in
-- Projecting through the cached table compares large explicit path lists.
theorem completeFor_eq_true (parent : Index) :
    completeFor parent (nodes parent) = true := by
  have hcomplete := complete_eq_true
  unfold complete at hcomplete
  have hall : ∀ data ∈ allData, completeFor data.1 data.2 = true :=
    List.all_eq_true.mp hcomplete
  apply hall (parent, nodes parent)
  exact List.mem_map.2 ⟨parent, List.mem_finRange parent, rfl⟩

end ShadedFreeLineGraphBase
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
