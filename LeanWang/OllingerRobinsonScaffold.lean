/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Theorems

/-!
Ollinger/Robinson scaffold interface.

The paper's scaffold step has two genuinely Wang-tile-specific parts:

* every plane tiling of the scaffold contains arbitrarily large recognizable
  active squares with a marked lower-left corner;
* whenever arbitrarily large fixed-corner squares are available for a payload
  tileset, the scaffold can realize them in the plane.

This file names that certificate in a form close to the figures in the paper,
then connects it to the abstract `IsScaffold` interface used by the final
reduction. The concrete finite Ollinger/Robinson tileset and its mechanical
local checks should instantiate this certificate.
-/

noncomputable section

namespace LeanWang
namespace OllingerRobinson

/--
A decoded active square window in a scaffold tiling.

The `baseRect` is the scaffold layer of the free square. The final `product`
field records that this square is actually the base layer of the combined
scaffold/payload tiling at the translated positions.
-/
structure ActiveCornerWindow (S : Scaffold) {T : TileSet} {seed : WangTile}
    (x : Int × Int → TileIn (combineWithScaffold S T seed))
    (n : Nat) (hn : 0 < n) where
  origin : Int × Int
  baseRect : Rectangle n n
  active : ∀ i : Fin n, ∀ j : Fin n, S.active (baseRect i j) = true
  corner : baseRect ⟨0, hn⟩ ⟨0, hn⟩ = S.corner
  product : ∀ i : Fin n, ∀ j : Fin n, ∃ payload : WangTile,
    WangTile.product (baseRect i j) payload =
      (x (origin.1 + Int.ofNat i.val, origin.2 + Int.ofNat j.val)).1

/--
The local recognizability/free-square fact expected from the
Ollinger/Robinson scaffold.

In the paper, this is the statement that the noncrossing square grid, after
crossing out obstructed rows and columns, leaves arbitrarily large free
sub-squares with a recognizable lower-left corner.
-/
def HasRecognizableFreeSquares (S : Scaffold) : Prop :=
  ∀ {T : TileSet} {seed : WangTile}
    (x : Int × Int → TileIn (combineWithScaffold S T seed)),
    ValidPlaneTiling (combineWithScaffold S T seed) x →
      ∀ n : Nat, ∀ hn : 0 < n, Nonempty (ActiveCornerWindow S x n hn)

theorem planeTilingHasActiveCornerBaseWindows_of_hasRecognizableFreeSquares
    {S : Scaffold} (hS : HasRecognizableFreeSquares S) :
    PlaneTilingHasActiveCornerBaseWindows S := by
  intro T seed x hx n hn
  rcases hS x hx n hn with ⟨window⟩
  exact ⟨window.origin, window.baseRect, window.active, window.corner, window.product⟩

/--
The two scaffold facts needed from a concrete Ollinger/Robinson tile list.

`recognizable` is the hard local square-extraction theorem. `realizes` is the
extension theorem saying that compatible payload square data can be threaded
through the free cells and obstruction channels of the scaffold.
-/
structure Certificate (S : Scaffold) : Prop where
  recognizable : HasRecognizableFreeSquares S
  realizes : RealizesActiveCornerSquares S

/-- A certified scaffold satisfies the abstract scaffold interface. -/
theorem isScaffold_of_certificate {S : Scaffold} (hS : Certificate S) :
    IsScaffold S := by
  exact isScaffold_of_realizesActiveCornerSquares_of_forcesActiveCornerSquares
    hS.realizes
    (forcesActiveCornerSquares_of_planeTilingForcesActiveCornerWindows
      (planeTilingForcesActiveCornerWindows_of_hasActiveCornerBaseWindows
        (planeTilingHasActiveCornerBaseWindows_of_hasRecognizableFreeSquares
          hS.recognizable)))

/-- Package for the eventual concrete Ollinger/Robinson scaffold instance. -/
structure Instance where
  scaffold : Scaffold
  certificate : Certificate scaffold

/-- The packaged concrete scaffold provides the abstract reduction hypothesis. -/
theorem Instance.isScaffold (I : Instance) :
    IsScaffold I.scaffold :=
  isScaffold_of_certificate I.certificate

end OllingerRobinson
end LeanWang

end
