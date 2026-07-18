/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Kari.AffineOrbitDiagram
import LeanWang.Kari.AffineTMStacks
import LeanWang.Kari.AffineTMSeries
import LeanWang.Kari.AffineTMSystem

/-!
# Affine immortality and finite TM0 immortality

This file joins the generic affine limit theorem to the local finite-machine
compiler.  In the soundness direction, every orbit branch is inverted to a
source table rule; the coordinate-envelope invariant recovers its separated
input region, and `AffineTMStacks` decodes the real side stacks to a genuine
unrestricted tape.  Thus an affine diagram cannot introduce a spurious
immortal computation.
-/

namespace LeanWang
namespace Kari
namespace AffineTMImmortality

open Hooper
open Hooper.FiniteTM0
open AffineTM
open AffineLimit

noncomputable section

variable {numSymbols : Nat}

/-- Tape effect of an explicit finite-table action. -/
def actionTape (action : Action numSymbols)
    (tape : FullTM0.Tape (Symbol numSymbols)) :
    FullTM0.Tape (Symbol numSymbols) :=
  match action with
  | .write a => tape.write a
  | .moveLeft => tape.move .left
  | .moveRight => tape.move .right

/-- Expose the explicit table rule and tape effect behind one successful
full-machine step. -/
theorem exists_rule_of_step {table : Table numSymbols}
    {cfg next : FullTM0.Cfg (Symbol numSymbols) State}
    (hstep : FullTM0.step (FiniteTM0.machine table) cfg = some next) :
    ∃ target action,
      Rule.mk cfg.q cfg.tape.read target action ∈ table ∧
        next = ⟨target, actionTape action cfg.tape⟩ := by
  unfold FullTM0.step at hstep
  cases hlookup : lookupAction table cfg.q cfg.tape.read with
  | none =>
      rw [FiniteTM0.machine_apply, hlookup] at hstep
      simp at hstep
  | some result =>
      rcases result with ⟨target, action⟩
      rw [FiniteTM0.machine_apply, hlookup] at hstep
      simp only [Option.map_some] at hstep
      refine ⟨target, action, rule_mem_of_lookupAction_eq_some hlookup, ?_⟩
      have hcfg := Option.some.inj hstep
      cases action <;> simpa [actionTape] using hcfg.symm

/-- A concrete immortal run yields a canonical digit-admissible affine orbit
of the table compiler. -/
theorem exists_digitAdmissible_forwardOrbit {table : Table numSymbols}
    {start : FullTM0.Cfg (Symbol numSymbols) State}
    (himmortal : FullTM0.ImmortalFrom (FiniteTM0.machine table) start) :
    ∃ orbit : ForwardOrbit (AffineTMSystem.system table),
      DigitAdmissible orbit := by
  let cfgAt : Nat → FullTM0.Cfg (Symbol numSymbols) State := fun n =>
    Classical.choose (himmortal n)
  have hcfgAt (n : Nat) :
      Dynamics.iterate (FullTM0.step (FiniteTM0.machine table)) n start =
        some (cfgAt n) :=
    Classical.choose_spec (himmortal n)
  have hcfgStep (n : Nat) :
      FullTM0.step (FiniteTM0.machine table) (cfgAt n) =
        some (cfgAt (n + 1)) := by
    have hnext := hcfgAt (n + 1)
    rw [Dynamics.iterate_succ, hcfgAt n, Option.bind_some] at hnext
    exact hnext
  have hresultExists (n : Nat) :
      ∃ result : State × Action numSymbols,
        Rule.mk (cfgAt n).q (cfgAt n).tape.read result.1 result.2 ∈ table ∧
          cfgAt (n + 1) = ⟨result.1, actionTape result.2 (cfgAt n).tape⟩ := by
    rcases exists_rule_of_step (hcfgStep n) with
      ⟨target, action, hrule, hnext⟩
    exact ⟨(target, action), hrule, hnext⟩
  let resultAt : Nat → State × Action numSymbols := fun n =>
    Classical.choose (hresultExists n)
  have hresultAt (n : Nat) :
      Rule.mk (cfgAt n).q (cfgAt n).tape.read
          (resultAt n).1 (resultAt n).2 ∈ table ∧
        cfgAt (n + 1) =
          ⟨(resultAt n).1, actionTape (resultAt n).2 (cfgAt n).tape⟩ :=
    Classical.choose_spec (hresultExists n)
  let specAt : Nat → LocalRule numSymbols := fun n =>
    specFor (cfgAt n) (resultAt n).1 (resultAt n).2
  have hspecRule (n : Nat) : (specAt n).rule ∈ table := by
    exact (hresultAt n).1
  have hspecRegion (n : Nat) :
      (specAt n).InInputRegion (encodeCfg (cfgAt n)) := by
    exact specFor_inInputRegion (cfgAt n) (resultAt n).1 (resultAt n).2
  have hencodeStep (n : Nat) :
      encodeCfg (cfgAt (n + 1)) =
        (specAt n).realStep (encodeCfg (cfgAt n)) := by
    change encodeCfg (cfgAt (n + 1)) =
      (specFor (cfgAt n) (resultAt n).1 (resultAt n).2).realStep
        (encodeCfg (cfgAt n))
    rw [(hresultAt n).2]
    unfold actionTape
    exact encodeCfg_action (cfgAt n) (resultAt n).1 (resultAt n).2
  let orbit : ForwardOrbit (AffineTMSystem.system table) :=
    { state := fun n => encodeCfg (cfgAt n)
      branch := fun n => (specAt n).compiled
      branch_mem := fun n => by
        simpa only [AffineTMSystem.system_branches] using
          AffineTMSystem.compiled_mem_branches table (hspecRule n)
            (specAt n).leftTop (specAt n).rightTop
      in_input_envelope := fun n =>
        (specAt n).inInputEnvelope_of_inInputRegion
          (encodeCfg (cfgAt n)) (hspecRegion n)
      realizes := fun n => by
        rw [hencodeStep n]
        exact (specAt n).realizes_realStep (encodeCfg (cfgAt n)) }
  have hadmissible : DigitAdmissible orbit := by
    refine
      { canonical_bound := fun _ => rfl
        input_mem := ?_
        output_mem := ?_ }
    · intro y x
      exact (specAt y).digitVector_mem_inputs (encodeCfg (cfgAt y))
        (hspecRegion y) x
    · intro y x
      have houtputRegion :
          (specAt y).InOutputRegion (encodeCfg (cfgAt (y + 1))) := by
        change (specFor (cfgAt y) (resultAt y).1 (resultAt y).2).InOutputRegion
          (encodeCfg (cfgAt (y + 1)))
        rw [(hresultAt y).2]
        unfold actionTape
        exact specFor_action_inOutputRegion (cfgAt y)
          (resultAt y).1 (resultAt y).2
      exact (specAt y).digitVector_mem_outputs
        (encodeCfg (cfgAt (y + 1))) houtputRegion x
  exact ⟨orbit, hadmissible⟩

/-- Arbitrary full-tape immortality produces an upper-half transducer diagram
of the compiled table. -/
theorem hasUpperHalfDiagram_of_immortal {table : Table numSymbols}
    (himmortal : FullTM0.Immortal (FiniteTM0.machine table)) :
    (AffineTMSystem.transducer table).HasUpperHalfDiagram := by
  rcases himmortal with ⟨start, hstart⟩
  rcases exists_digitAdmissible_forwardOrbit hstart with
    ⟨orbit, hadmissible⟩
  exact hasUpperHalfDiagram_of_digitAdmissible orbit hadmissible

/-- Completeness of the affine compiler: an arbitrary immortal configuration
tiles the plane. -/
theorem tilesPlane_of_immortal {table : Table numSymbols}
    (himmortal : FullTM0.Immortal (FiniteTM0.machine table)) :
    TilesPlane (AffineTMSystem.tiles table) := by
  exact (Transducer.tilesPlane_iff_hasUpperHalfDiagram
    (AffineTMSystem.transducer table)).2
      (hasUpperHalfDiagram_of_immortal himmortal)

/-- An admissible forward orbit of the system compiled from a deterministic
finite table decodes to an immortal arbitrary full-tape configuration. -/
theorem immortal_of_forwardOrbit {table : Table numSymbols}
    (hdeterministic : Deterministic table)
    (fallback : Symbol numSymbols)
    (orbit : ForwardOrbit (AffineTMSystem.system table)) :
    FullTM0.Immortal (FiniteTM0.machine table) := by
  let specAt : Nat → LocalRule numSymbols := fun y =>
    Classical.choose ((AffineTMSystem.mem_branches_iff table
      (orbit.branch y)).1 (by
        simpa only [AffineTMSystem.system_branches] using orbit.branch_mem y))
  have hspecAt (y : Nat) :
      (specAt y).rule ∈ table ∧ (specAt y).compiled = orbit.branch y :=
    Classical.choose_spec ((AffineTMSystem.mem_branches_iff table
      (orbit.branch y)).1 (by
        simpa only [AffineTMSystem.system_branches] using orbit.branch_mem y))
  have hregion (y : Nat) :
      (specAt y).InInputRegion (orbit.state y) := by
    apply (specAt y).inInputRegion_of_inInputEnvelope
    rw [hspecAt y |>.2]
    exact orbit.in_input_envelope y
  have hstep (y : Nat) :
      FullTM0.step (FiniteTM0.machine table)
          (realCfg fallback (specAt y) (orbit.state y)) =
        some (realCfg fallback (specAt (y + 1)) (orbit.state (y + 1))) := by
    have hrealizes := orbit.realizes y
    rw [← (hspecAt y).2] at hrealizes
    exact step_realCfg hdeterministic fallback (specAt y) (specAt (y + 1))
      (hspecAt y).1 (orbit.state y) (orbit.state (y + 1))
      (hregion y) (hregion (y + 1)) hrealizes
  refine ⟨realCfg fallback (specAt 0) (orbit.state 0), ?_⟩
  intro n
  refine ⟨realCfg fallback (specAt n) (orbit.state n), ?_⟩
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [Dynamics.iterate_succ, ih, Option.bind_some]
      exact hstep n

/-- Any upper-half affine diagram of a deterministic compiled table therefore
implies arbitrary-configuration immortality of that table. -/
theorem immortal_of_hasUpperHalfDiagram {table : Table numSymbols}
    (hdeterministic : Deterministic table)
    (fallback : Symbol numSymbols)
    (hdiagram : (AffineTMSystem.transducer table).HasUpperHalfDiagram) :
    FullTM0.Immortal (FiniteTM0.machine table) := by
  have horbit : HasForwardOrbit (AffineTMSystem.system table) := by
    exact AffineLimit.hasForwardOrbit_of_hasUpperHalfDiagram
      (AffineTMSystem.system table) hdiagram
  exact horbit.elim (immortal_of_forwardOrbit hdeterministic fallback)

/-- Plane tilability of the compiled Wang set is sound for arbitrary-tape
immortality. -/
theorem immortal_of_tilesPlane {table : Table numSymbols}
    (hdeterministic : Deterministic table)
    (fallback : Symbol numSymbols)
    (htiles : TilesPlane (AffineTMSystem.tiles table)) :
    FullTM0.Immortal (FiniteTM0.machine table) := by
  apply immortal_of_hasUpperHalfDiagram hdeterministic fallback
  exact (Transducer.tilesPlane_iff_hasUpperHalfDiagram
    (AffineTMSystem.transducer table)).1 htiles

/-- Exact finite-table endpoint of Kari's affine construction. -/
theorem tilesPlane_iff_immortal {table : Table numSymbols}
    (hdeterministic : Deterministic table)
    (fallback : Symbol numSymbols) :
    TilesPlane (AffineTMSystem.tiles table) ↔
      FullTM0.Immortal (FiniteTM0.machine table) :=
  ⟨immortal_of_tilesPlane hdeterministic fallback,
    tilesPlane_of_immortal⟩

end

end AffineTMImmortality
end Kari
end LeanWang
