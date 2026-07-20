/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Scaffold.Routed.PointedPlane
import LeanWang.Robinson.Machine.UniversalTM0.MachineData
import LeanWang.DominoProblem

/-!
# Fixed-universal-machine Wang reduction

The two-sided universal TM0 evaluator is simulated by one fixed one-sided
machine.  The generic `MachineInputTiles` construction then turns that machine
and a finite input into Wang tiles.  The simulation control and all normal
rows are constants; a source code changes only the bottom-row input data.

Compared with the old source-program route, no theorem here needs to decode a
dependent `Turing.ToPartrec.Code` statement or prove that such a decoder is
uniformly primitive recursive. Compared with the generated-initializer route,
the executable reduction also avoids compiling input-specific machine states.
-/

noncomputable section

namespace LeanWang

namespace UniversalTM0Reduction

open Nat.Partrec (Code)

/-- Fixed-corner Wang instance with the source input forced on its bottom row. -/
def fixedDominoReduction (c : Code) : TileSet × WangTile :=
  UniversalTM0Machine.fixedDominoData (UniversalTM0Semantic.input c)

theorem fixedDominoReduction_computable : Computable fixedDominoReduction := by
  exact UniversalTM0Machine.fixedDominoData_computable.comp
    UniversalTM0Semantic.input_computable

theorem fixedDominoReduction_correct (c : Code) :
    TilesQuarterWithSeed (fixedDominoReduction c).1
        (fixedDominoReduction c).2 ↔
      ¬ (Nat.Partrec.Code.eval c 0).Dom := by
  change TilesQuarterWithSeed
      (MachineInputTiles.tiles UniversalTM0Machine.machine
        (UniversalTM0Machine.input (UniversalTM0Semantic.input c)))
      (MachineInputTiles.seed UniversalTM0Machine.machine
        (UniversalTM0Machine.input (UniversalTM0Semantic.input c))) ↔ _
  exact (MachineInputTiles.tilesQuarterWithSeed_iff_not_halts
    (UniversalTM0Machine.input_supported
      (UniversalTM0Semantic.input c))).trans
    (not_congr ((UniversalTM0Machine.halts_iff_tm0_eval_dom
      (UniversalTM0Semantic.input c)).trans
        (UniversalTM0Semantic.tm0_eval_dom_iff c)))

/-- Pointed full-plane form of the fixed universal TM0 instance. -/
def pointedFixedDominoReduction (c : Code) : TileSet × WangTile :=
  PointedExtension.data (fixedDominoReduction c)

theorem pointedFixedDominoReduction_computable :
    Computable pointedFixedDominoReduction := by
  exact PointedExtension.data_computable.comp fixedDominoReduction_computable

/-- Plane-tiling instance after applying a channel-aware routed scaffold to
the pointed full-plane payload. -/
def routedDominoReduction (S : RoutedScaffold) (c : Code) : TileSet :=
  combineWithRoutedScaffold S (pointedFixedDominoReduction c).1
    (pointedFixedDominoReduction c).2

theorem routedDominoReduction_computable (S : RoutedScaffold) :
    Computable (routedDominoReduction S) := by
  exact (combineWithRoutedScaffold_computable S).comp
    pointedFixedDominoReduction_computable

theorem routedDominoReduction_correct
    {S : RoutedScaffold}
    (realizes : RealizesRoutedPointedPlanes S)
    (forces : ForcesRoutedFixedCornerSquares S) (c : Code) :
    TilesPlane (routedDominoReduction S c) ↔
      ¬ (Nat.Partrec.Code.eval c 0).Dom := by
  rw [routedDominoReduction, pointedFixedDominoReduction,
    PointedExtension.data]
  exact (routedPointedExtension_reduction_correct realizes forces
    (fixedDominoReduction c).1 (fixedDominoReduction c).2).trans
      (fixedDominoReduction_correct c)

/-- The proof-neutral reduction certificate supplied by a routed scaffold. -/
def routedReduction
    (S : RoutedScaffold)
    (realizes : RealizesRoutedPointedPlanes S)
    (forces : ForcesRoutedFixedCornerSquares S) :
    DominoProblem.Reduction where
  tiles := routedDominoReduction S
  tiles_computable := routedDominoReduction_computable S
  correct := routedDominoReduction_correct realizes forces

end UniversalTM0Reduction

end LeanWang
