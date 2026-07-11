/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104RedShadeGraph

/-!
Executable certificates for finite red-shade graph paths.

The Boolean checker is intended for native finite geometry searches. Its
soundness theorem turns accepted move records into the proposition-valued
`RedShadeGraph.Link` relation used by shade propagation proofs.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace RedShadeGraphCertificate

open RedCycles Signals.FreeCellLocal RedShadeGraph

inductive Kind where
  | horizontalMatch
  | verticalMatch
  | horizontal
  | vertical
  | westNorth
  | westSouth
  | eastNorth
  | eastSouth
  | crossing
deriving DecidableEq, Repr

/-- One directed, executable local move. -/
structure Move where
  x : Nat
  y : Nat
  kind : Kind
  reverse : Bool := false
deriving DecidableEq, Repr

def Move.baseFirst (move : Move) : Port :=
  match move.kind with
  | .horizontalMatch => ⟨move.x, move.y, .east⟩
  | .verticalMatch => ⟨move.x, move.y, .north⟩
  | .horizontal => ⟨move.x, move.y, .west⟩
  | .vertical => ⟨move.x, move.y, .south⟩
  | .westNorth => ⟨move.x, move.y, .west⟩
  | .westSouth => ⟨move.x, move.y, .west⟩
  | .eastNorth => ⟨move.x, move.y, .east⟩
  | .eastSouth => ⟨move.x, move.y, .east⟩
  | .crossing => ⟨move.x, move.y, .west⟩

def Move.baseSecond (move : Move) : Port :=
  match move.kind with
  | .horizontalMatch => ⟨move.x + 1, move.y, .west⟩
  | .verticalMatch => ⟨move.x, move.y + 1, .south⟩
  | .horizontal => ⟨move.x, move.y, .east⟩
  | .vertical => ⟨move.x, move.y, .north⟩
  | .westNorth => ⟨move.x, move.y, .north⟩
  | .westSouth => ⟨move.x, move.y, .south⟩
  | .eastNorth => ⟨move.x, move.y, .north⟩
  | .eastSouth => ⟨move.x, move.y, .south⟩
  | .crossing => ⟨move.x, move.y, .south⟩

def Move.first (move : Move) : Port :=
  if move.reverse then move.baseSecond else move.baseFirst

def Move.second (move : Move) : Port :=
  if move.reverse then move.baseFirst else move.baseSecond

def Move.parity (move : Move) : Bool :=
  move.kind == .crossing

def Move.valid (indexGrid : Nat → Nat → Index) (move : Move) : Bool :=
  let component := componentAt indexGrid move.x move.y
  let quadrant := quadrantAt move.x move.y
  match move.kind with
  | .horizontalMatch | .verticalMatch => true
  | .horizontal => RedShades.hasHorizontal component quadrant
  | .vertical => RedShades.hasVertical component quadrant
  | .westNorth =>
      RedShades.cornerWest component quadrant &&
        RedShades.cornerNorth component quadrant
  | .westSouth =>
      RedShades.cornerWest component quadrant &&
        RedShades.cornerSouth component quadrant
  | .eastNorth =>
      RedShades.cornerEast component quadrant &&
        RedShades.cornerNorth component quadrant
  | .eastSouth =>
      RedShades.cornerEast component quadrant &&
        RedShades.cornerSouth component quadrant
  | .crossing =>
      RedShades.hasHorizontal component quadrant &&
        RedShades.hasVertical component quadrant

theorem Move.link_of_valid {indexGrid : Nat → Nat → Index}
    (move : Move) (valid : move.valid indexGrid = true) :
    Link indexGrid move.first move.second move.parity := by
  rcases move with ⟨x, y, kind, reverse⟩
  cases kind <;> cases reverse <;>
    simp only [Move.valid, Move.first, Move.second, Move.baseFirst,
      Move.baseSecond, Move.parity, Bool.false_eq_true,
      Bool.and_eq_true, beq_self_eq_true] at valid ⊢
  · exact Link.horizontalMatch x y
  · exact Link.symm (Link.horizontalMatch x y)
  · exact Link.verticalMatch x y
  · exact Link.symm (Link.verticalMatch x y)
  · exact Link.horizontal x y valid
  · exact Link.symm (Link.horizontal x y valid)
  · exact Link.vertical x y valid
  · exact Link.symm (Link.vertical x y valid)
  · exact Link.westNorth x y valid.1 valid.2
  · exact Link.symm (Link.westNorth x y valid.1 valid.2)
  · exact Link.westSouth x y valid.1 valid.2
  · exact Link.symm (Link.westSouth x y valid.1 valid.2)
  · exact Link.eastNorth x y valid.1 valid.2
  · exact Link.symm (Link.eastNorth x y valid.1 valid.2)
  · exact Link.eastSouth x y valid.1 valid.2
  · exact Link.symm (Link.eastSouth x y valid.1 valid.2)
  · exact Link.crossing x y valid.1 valid.2
  · exact Link.symm (Link.crossing x y valid.1 valid.2)

/-- Follow checked moves and return the final port and crossing parity. -/
def endpoint (indexGrid : Nat → Nat → Index) :
    Port → List Move → Option (Port × Bool)
  | start, [] => some (start, false)
  | start, move :: moves =>
      if move.first = start ∧ move.valid indexGrid = true then
        match endpoint indexGrid move.second moves with
        | none => none
        | some (finish, parity) => some (finish, Bool.xor move.parity parity)
      else none

theorem path_of_endpoint {indexGrid : Nat → Nat → Index} :
    ∀ {moves : List Move} {start finish : Port} {parity : Bool},
      endpoint indexGrid start moves = some (finish, parity) →
        Path indexGrid start finish parity := by
  intro moves
  induction moves with
  | nil =>
      intro start finish parity hend
      simp only [endpoint, Option.some.injEq, Prod.mk.injEq] at hend
      rcases hend with ⟨rfl, rfl⟩
      exact Path.refl start
  | cons move moves ih =>
      intro start finish parity hend
      rw [endpoint] at hend
      by_cases hvalid : move.first = start ∧ move.valid indexGrid = true
      · rw [if_pos hvalid] at hend
        cases htail : endpoint indexGrid move.second moves with
        | none => simp [htail] at hend
        | some result =>
            rcases result with ⟨tailFinish, tailParity⟩
            rw [htail] at hend
            simp only [Option.some.injEq, Prod.mk.injEq] at hend
            rcases hend with ⟨rfl, rfl⟩
            rw [← hvalid.1]
            exact Path.trans
              (Path.ofLink (move.link_of_valid hvalid.2))
              (ih htail)
      · rw [if_neg hvalid] at hend
        contradiction

end RedShadeGraphCertificate
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
