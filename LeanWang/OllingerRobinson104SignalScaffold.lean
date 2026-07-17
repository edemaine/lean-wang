/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104SignalCorridors
import LeanWang.Theorems

/-!
The concrete scaffold carried by the corrected quarter tiles and Robinson
obstruction signals.

A site is active exactly when all four signal edges are clear. The test reads
the signal component directly from the paired Wang colors, so it is primitive
recursive and does not search the finite tileset.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace Signals

set_option maxRecDepth 20000

/-- Signal-layer component of a paired Wang edge color. -/
def edgeFlowCode (color : Nat) : Nat := color.unpair.2

/-- Whether an encoded scaffold tile carries no obstruction signal. -/
def isClear (wang : WangTile) : Bool :=
  edgeFlowCode wang.n == 0 &&
    edgeFlowCode wang.s == 0 &&
    edgeFlowCode wang.e == 0 &&
    edgeFlowCode wang.w == 0

theorem isClear_primrec : Primrec isClear := by
  have hn : Primrec (fun wang : WangTile => edgeFlowCode wang.n) :=
    Primrec.snd.comp (Primrec.unpair.comp WangTile.n_primrec)
  have hs : Primrec (fun wang : WangTile => edgeFlowCode wang.s) :=
    Primrec.snd.comp (Primrec.unpair.comp WangTile.s_primrec)
  have he : Primrec (fun wang : WangTile => edgeFlowCode wang.e) :=
    Primrec.snd.comp (Primrec.unpair.comp WangTile.e_primrec)
  have hw : Primrec (fun wang : WangTile => edgeFlowCode wang.w) :=
    Primrec.snd.comp (Primrec.unpair.comp WangTile.w_primrec)
  have hn0 : Primrec (fun wang : WangTile => edgeFlowCode wang.n == 0) :=
    Primrec.beq.comp hn (Primrec.const 0)
  have hs0 : Primrec (fun wang : WangTile => edgeFlowCode wang.s == 0) :=
    Primrec.beq.comp hs (Primrec.const 0)
  have he0 : Primrec (fun wang : WangTile => edgeFlowCode wang.e == 0) :=
    Primrec.beq.comp he (Primrec.const 0)
  have hw0 : Primrec (fun wang : WangTile => edgeFlowCode wang.w == 0) :=
    Primrec.beq.comp hw (Primrec.const 0)
  exact Primrec.and.comp
    (Primrec.and.comp (Primrec.and.comp hn0 hs0) he0) hw0

def clearState : State := ⟨.none, .none, .none, .none⟩

theorem isClear_tile_eq_true_iff (site : Site) :
    isClear (tile site) = true ↔ site.2 = clearState := by
  rcases site with ⟨quarter, state⟩
  rcases state with ⟨west, east, south, north⟩
  cases west <;> cases east <;> cases south <;> cases north <;>
    simp [isClear, edgeFlowCode, tile, State.tile, Flow.code, clearState,
      WangTile.product]

def cornerQuarter : Quarters.QuarterIndex :=
  (⟨0, by decide⟩, .southwest)

def cornerSite : Site := (cornerQuarter, clearState)

set_option linter.style.nativeDecide false in
theorem cornerSite_allowed :
    locallyAllowed cornerSite.1 cornerSite.2 = true := by
  native_decide

def cornerTile : WangTile := tile cornerSite

theorem cornerTile_mem : cornerTile ∈ tileSet :=
  tile_mem cornerSite cornerSite_allowed

@[simp] theorem isClear_cornerTile : isClear cornerTile = true :=
  (isClear_tile_eq_true_iff cornerSite).2 rfl

/-- Concrete corrected-Ollinger/Robinson signal scaffold. -/
@[irreducible] def scaffold : Scaffold where
  tiles := tileSet
  active := isClear
  corner := cornerTile
  active_primrec := isClear_primrec

@[simp] theorem scaffold_tiles : scaffold.tiles = tileSet := by
  unfold scaffold
  rfl

@[simp] theorem scaffold_active : scaffold.active = isClear := by
  unfold scaffold
  rfl

@[simp] theorem scaffold_corner : scaffold.corner = cornerTile := by
  unfold scaffold
  rfl

theorem scaffold_corner_mem : scaffold.corner ∈ scaffold.tiles :=
  by simpa only [scaffold_corner, scaffold_tiles] using cornerTile_mem

@[simp] theorem scaffold_corner_active :
    scaffold.active scaffold.corner = true :=
  by simpa only [scaffold_active, scaffold_corner] using isClear_cornerTile

end Signals
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
