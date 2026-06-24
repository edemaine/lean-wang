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

theorem isActive_eq_true_iff (r : CellRole) :
    isActive r = true ↔ r = active ∨ r = corner := by
  cases r <;> simp [isActive]

theorem isCorner_eq_true_iff (r : CellRole) :
    isCorner r = true ↔ r = corner := by
  cases r <;> simp [isCorner]

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

/-- Finite check that the declared corner tile occurs in the scaffold tile list. -/
def cornerMemBool (P : ScaffoldPresentation) : Bool :=
  decide (P.cornerTile ∈ P.tiles)

theorem corner_mem_of_cornerMemBool {P : ScaffoldPresentation}
    (hcheck : P.cornerMemBool = true) :
    P.cornerTile ∈ P.tiles := by
  exact of_decide_eq_true hcheck

/--
Finite check that the distinguished corner role occurs only on `cornerTile`
inside the scaffold tile list.
-/
def cornerUniqueBool (P : ScaffoldPresentation) : Bool :=
  P.tiles.all fun tile =>
    decide (P.role tile = CellRole.corner) == decide (tile = P.cornerTile)

private theorem cornerUniqueBool_mem_eq {P : ScaffoldPresentation} {tile : WangTile}
    (hcheck : P.cornerUniqueBool = true) (htile : tile ∈ P.tiles) :
    decide (P.role tile = CellRole.corner) = decide (tile = P.cornerTile) := by
  unfold cornerUniqueBool at hcheck
  have hall := List.all_eq_true.1 hcheck tile htile
  cases hleft : decide (P.role tile = CellRole.corner) <;>
    cases hright : decide (tile = P.cornerTile) <;>
      simp [hleft, hright] at hall ⊢

theorem cornerUnique_of_cornerUniqueBool {P : ScaffoldPresentation}
    (hcheck : P.cornerUniqueBool = true) :
    ∀ tile : WangTile, tile ∈ P.tiles →
      P.role tile = CellRole.corner → tile = P.cornerTile := by
  intro tile htile hcorner
  have heq := cornerUniqueBool_mem_eq (P := P) (tile := tile) hcheck htile
  have hleft : decide (P.role tile = CellRole.corner) = true := by
    exact decide_eq_true hcorner
  have hright : decide (tile = P.cornerTile) = true := by
    simpa [hleft] using heq.symm
  exact of_decide_eq_true hright

/-- Basic finite sanity conditions for a scaffold presentation. -/
structure Sanity (P : ScaffoldPresentation) : Prop where
  corner_mem : P.cornerTile ∈ P.tiles
  corner_unique : ∀ tile : WangTile, tile ∈ P.tiles →
    P.role tile = CellRole.corner → tile = P.cornerTile

/-- Boolean version of `Sanity`, intended for concrete finite scaffold data. -/
def sanityBool (P : ScaffoldPresentation) : Bool :=
  P.cornerMemBool && P.cornerUniqueBool

theorem sanity_of_sanityBool {P : ScaffoldPresentation}
    (hcheck : P.sanityBool = true) :
    Sanity P := by
  unfold sanityBool at hcheck
  cases hmem : P.cornerMemBool <;> cases hunique : P.cornerUniqueBool <;>
    simp [hmem, hunique] at hcheck
  exact ⟨corner_mem_of_cornerMemBool hmem,
    cornerUnique_of_cornerUniqueBool hunique⟩

theorem toScaffold_corner_mem_of_sanity {P : ScaffoldPresentation}
    (hP : P.Sanity) :
    P.toScaffold.corner ∈ P.toScaffold.tiles := by
  simpa using hP.corner_mem

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
Role-level active square window for a presented scaffold.

Finite verification over a concrete tile list should prove this form: active
cells and the distinguished corner are recognized by the presentation's role
decoder. It converts directly to `ActiveCornerWindow P.toScaffold`.
-/
structure PresentedActiveCornerWindow (P : ScaffoldPresentation)
    {T : TileSet} {seed : WangTile}
    (x : Int × Int → TileIn (combineWithScaffold P.toScaffold T seed))
    (n : Nat) (hn : 0 < n) where
  origin : Int × Int
  baseRect : Rectangle n n
  mem : ∀ i : Fin n, ∀ j : Fin n, baseRect i j ∈ P.tiles
  active : ∀ i : Fin n, ∀ j : Fin n,
    CellRole.isActive (P.role (baseRect i j)) = true
  corner : P.role (baseRect ⟨0, hn⟩ ⟨0, hn⟩) = CellRole.corner
  product : ∀ i : Fin n, ∀ j : Fin n, ∃ payload : WangTile,
    WangTile.product (baseRect i j) payload =
      (x (origin.1 + Int.ofNat i.val, origin.2 + Int.ofNat j.val)).1

def activeCornerWindowOfPresentedActiveCornerWindow
    {P : ScaffoldPresentation} {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold P.toScaffold T seed)}
    {n : Nat} {hn : 0 < n}
    (hwindow : PresentedActiveCornerWindow P x n hn)
    (hcorner_unique : ∀ tile : WangTile, tile ∈ P.tiles →
      P.role tile = CellRole.corner → tile = P.cornerTile) :
    ActiveCornerWindow P.toScaffold x n hn where
  origin := hwindow.origin
  baseRect := hwindow.baseRect
  active := hwindow.active
  corner := hcorner_unique (hwindow.baseRect ⟨0, hn⟩ ⟨0, hn⟩)
    (hwindow.mem ⟨0, hn⟩ ⟨0, hn⟩) hwindow.corner
  product := hwindow.product

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

/--
Role-level recognizability for a presented scaffold.

The extra uniqueness premise in `PresentedCertificate` states that the only
tile in `P.tiles` with role `corner` is `P.cornerTile`, so role-level corner
recognition matches the abstract scaffold corner field.
-/
def HasPresentedRecognizableFreeSquares (P : ScaffoldPresentation) : Prop :=
  ∀ {T : TileSet} {seed : WangTile}
    (x : Int × Int → TileIn (combineWithScaffold P.toScaffold T seed)),
    ValidPlaneTiling (combineWithScaffold P.toScaffold T seed) x →
      ∀ n : Nat, ∀ hn : 0 < n,
        Nonempty (PresentedActiveCornerWindow P x n hn)

theorem hasRecognizableFreeSquares_of_presented
    {P : ScaffoldPresentation}
    (hS : HasPresentedRecognizableFreeSquares P)
    (hcorner_unique : ∀ tile : WangTile, tile ∈ P.tiles →
      P.role tile = CellRole.corner → tile = P.cornerTile) :
    HasRecognizableFreeSquares P.toScaffold := by
  intro T seed x hx n hn
  rcases hS x hx n hn with ⟨window⟩
  exact ⟨activeCornerWindowOfPresentedActiveCornerWindow window hcorner_unique⟩

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

/-- Certificate stated against a typed scaffold presentation. -/
structure PresentedCertificate (P : ScaffoldPresentation) : Prop where
  recognizable : HasPresentedRecognizableFreeSquares P
  corner_unique : ∀ tile : WangTile, tile ∈ P.tiles →
    P.role tile = CellRole.corner → tile = P.cornerTile
  realizes : RealizesActiveCornerSquares P.toScaffold

theorem certificate_of_presentedCertificate
    {P : ScaffoldPresentation} (hP : PresentedCertificate P) :
    Certificate P.toScaffold where
  recognizable := hasRecognizableFreeSquares_of_presented
    hP.recognizable hP.corner_unique
  realizes := hP.realizes

theorem presentedCertificate_of_sanity
    {P : ScaffoldPresentation} (hP : P.Sanity)
    (hrecognizable : HasPresentedRecognizableFreeSquares P)
    (hrealizes : RealizesActiveCornerSquares P.toScaffold) :
    PresentedCertificate P where
  recognizable := hrecognizable
  corner_unique := hP.corner_unique
  realizes := hrealizes

theorem presentedCertificate_of_sanityBool
    {P : ScaffoldPresentation} (hcheck : P.sanityBool = true)
    (hrecognizable : HasPresentedRecognizableFreeSquares P)
    (hrealizes : RealizesActiveCornerSquares P.toScaffold) :
    PresentedCertificate P :=
  presentedCertificate_of_sanity
    (ScaffoldPresentation.sanity_of_sanityBool hcheck)
    hrecognizable hrealizes

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

/-- Package for a concrete scaffold given by typed finite tile data. -/
structure PresentedInstance where
  presentation : ScaffoldPresentation
  certificate : PresentedCertificate presentation

/--
Package for a concrete scaffold whose finite sanity obligations are discharged
by `ScaffoldPresentation.sanityBool`.
-/
structure CheckedPresentedInstance where
  presentation : ScaffoldPresentation
  sanity : presentation.sanityBool = true
  recognizable : HasPresentedRecognizableFreeSquares presentation
  realizes : RealizesActiveCornerSquares presentation.toScaffold

/-- The packaged concrete scaffold provides the abstract reduction hypothesis. -/
theorem Instance.isScaffold (I : Instance) :
    IsScaffold I.scaffold :=
  isScaffold_of_certificate I.certificate

/-- The packaged presented scaffold provides the abstract reduction hypothesis. -/
theorem PresentedInstance.isScaffold (I : PresentedInstance) :
    IsScaffold I.presentation.toScaffold :=
  isScaffold_of_certificate (certificate_of_presentedCertificate I.certificate)

def CheckedPresentedInstance.toPresentedInstance (I : CheckedPresentedInstance) :
    PresentedInstance where
  presentation := I.presentation
  certificate := presentedCertificate_of_sanityBool
    I.sanity I.recognizable I.realizes

/--
The checked finite-data package provides the abstract scaffold reduction
hypothesis.
-/
theorem CheckedPresentedInstance.isScaffold (I : CheckedPresentedInstance) :
    IsScaffold I.presentation.toScaffold :=
  I.toPresentedInstance.isScaffold

end OllingerRobinson
end LeanWang

end
