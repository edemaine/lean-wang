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

/-- Role of a scaffold tile in the payload overlay. -/
inductive CellRole where
  | inactive
  | channel
  | active
  | corner
deriving DecidableEq, Repr

namespace CellRole

def toBits : CellRole → Bool × Bool
  | inactive => (false, false)
  | channel => (false, true)
  | active => (true, false)
  | corner => (true, true)

def ofBits : Bool × Bool → CellRole
  | (false, false) => inactive
  | (false, true) => channel
  | (true, false) => active
  | (true, true) => corner

def equivBits : CellRole ≃ Bool × Bool where
  toFun := toBits
  invFun := ofBits
  left_inv := by
    intro r
    cases r <;> rfl
  right_inv := by
    intro bits
    rcases bits with ⟨a, b⟩
    cases a <;> cases b <;> rfl

instance instPrimcodable : Primcodable CellRole :=
  Primcodable.ofEquiv (Bool × Bool) equivBits

def isActive : CellRole → Bool
  | inactive => false
  | channel => false
  | active => true
  | corner => true

def isCorner : CellRole → Bool
  | inactive => false
  | channel => false
  | active => false
  | corner => true

theorem toBits_primrec : Primrec toBits := by
  simpa [equivBits] using
    (Primrec.of_equiv (e := equivBits) : Primrec equivBits)

theorem isActive_primrec : Primrec isActive := by
  exact (Primrec.fst.comp toBits_primrec).of_eq fun r => by
    cases r <;> rfl

theorem isCorner_primrec : Primrec isCorner := by
  exact ((Primrec.and.comp (Primrec.fst.comp toBits_primrec)
    (Primrec.snd.comp toBits_primrec))).of_eq fun r => by
      cases r <;> rfl

@[simp]
theorem isActive_corner : isActive corner = true :=
  rfl

@[simp]
theorem isCorner_corner : isCorner corner = true :=
  rfl

end CellRole

/--
Typed finite data for a scaffold candidate.

The concrete Ollinger/Robinson tile list should instantiate this structure with
ordinary Wang tiles plus a primitive-recursive role decoder. Keeping the role
decoder separate from edge colors avoids committing to a particular natural-color
packing before the finite tile data is transcribed.
-/
structure ScaffoldPresentation where
  tiles : TileSet
  role : WangTile → CellRole
  cornerTile : WangTile
  role_primrec : Primrec role
  corner_role : role cornerTile = CellRole.corner

namespace ScaffoldPresentation

def toScaffold (P : ScaffoldPresentation) : Scaffold where
  tiles := P.tiles
  active := fun tile => CellRole.isActive (P.role tile)
  corner := P.cornerTile
  active_primrec := CellRole.isActive_primrec.comp P.role_primrec

@[simp]
theorem toScaffold_tiles (P : ScaffoldPresentation) :
    P.toScaffold.tiles = P.tiles :=
  rfl

@[simp]
theorem toScaffold_corner (P : ScaffoldPresentation) :
    P.toScaffold.corner = P.cornerTile :=
  rfl

@[simp]
theorem toScaffold_active (P : ScaffoldPresentation) (tile : WangTile) :
    P.toScaffold.active tile = CellRole.isActive (P.role tile) :=
  rfl

theorem toScaffold_corner_active (P : ScaffoldPresentation) :
    P.toScaffold.active P.toScaffold.corner = true := by
  simp [P.corner_role]

end ScaffoldPresentation

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
