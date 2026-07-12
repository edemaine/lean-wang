/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104SparseFreeLineOddMarkerBaseAudit

/-! Project the cached odd-marker audit to one parent. -/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace SparseFreeLineOddMarkerBaseAudit

set_option maxHeartbeats 2000000 in
-- Projecting the cached finite table unfolds explicit route lists.
theorem completeFor_eq_true (parent : Index) : completeFor parent = true := by
  have hcomplete := complete_eq_true
  unfold complete at hcomplete
  have hall := List.all_eq_true.mp hcomplete
  exact hall parent (List.mem_finRange parent)

end SparseFreeLineOddMarkerBaseAudit
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
