/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedCompiler.CorrectnessHalting

/-!
Projection lemmas for the folded-configuration invariant.
-/

namespace LeanWang

namespace TM0FoldedCompiler

theorem FoldedConfigRel_state_some {tc : Turing.ToPartrec.Code}
    {cfg : Turing.TM0.Cfg SourceSymbol (SourceLabel tc)} {id : PostID}
    (hrel : FoldedConfigRel tc cfg id) :
    ∃ side : FoldSide,
      id.state = some (foldedSimStateCode tc side cfg.q) := by
  rcases hrel with ⟨side, _hq, hstate, _htape⟩
  exact ⟨side, hstate⟩

theorem FoldedConfigRel_label_mem {tc : Turing.ToPartrec.Code}
    {cfg : Turing.TM0.Cfg SourceSymbol (SourceLabel tc)} {id : PostID}
    (hrel : FoldedConfigRel tc cfg id) :
    cfg.q ∈ TM0Route.partrecStartedTM0LabelList tc := by
  rcases hrel with ⟨_side, hq, _hstate, _htape⟩
  exact hq

theorem FoldedConfigRel_read_head {tc : Turing.ToPartrec.Code}
    {cfg : Turing.TM0.Cfg SourceSymbol (SourceLabel tc)} {id : PostID}
    (hrel : FoldedConfigRel tc cfg id) :
    ∃ side : FoldSide,
      id.state = some (foldedSimStateCode tc side cfg.q) ∧
        id.tape id.head =
          foldedCellOfTapeAt cfg.Tape side id.head id.head ∧
        foldedRead side
          (cfg.Tape.nth (sourceOffset side id.head (leftAbs id.head)))
          (cfg.Tape.nth (sourceOffset side id.head (rightAbs id.head))) =
            cfg.Tape.head := by
  rcases hrel with ⟨side, _hq, hstate, htape⟩
  exact ⟨side, hstate, htape id.head, foldedRead_active_cell cfg.Tape side id.head⟩

end TM0FoldedCompiler

end LeanWang
