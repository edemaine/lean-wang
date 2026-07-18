/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.RedShadeGraphBoundedPath

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

open RedCycles Signals.FreeCellLocal RedShadeGraph RedShadeGraphBoundedPath

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

/-- Follow checked moves while also verifying that every visited port remains
inside one finite search box. -/
def portInBounds (port : Port) (width height : Nat) : Bool :=
  port.x < width && port.y < height

theorem portInBounds_eq_true {port : Port} {width height : Nat}
    (bounded : portInBounds port width height = true) :
    PortInBounds port width height := by
  simpa [portInBounds, PortInBounds, Bool.and_eq_true] using bounded

def boundedEndpoint (indexGrid : Nat → Nat → Index)
    (width height : Nat) : Port → List Move → Option (Port × Bool)
  | start, [] =>
      if portInBounds start width height then some (start, false) else none
  | start, move :: moves =>
      if move.first = start ∧ move.valid indexGrid = true ∧
          portInBounds start width height = true ∧
          portInBounds move.second width height = true then
        match boundedEndpoint indexGrid width height move.second moves with
        | none => none
        | some (finish, parity) => some (finish, Bool.xor move.parity parity)
      else none

/-- A successful bounded move-list check is a genuine path all of whose ports
stay inside the checked box. -/
theorem boundedPath_of_boundedEndpoint
    {indexGrid : Nat → Nat → Index} {width height : Nat} :
    ∀ {moves : List Move} {start finish : Port} {parity : Bool},
      boundedEndpoint indexGrid width height start moves =
          some (finish, parity) →
        BoundedPath indexGrid width height start finish parity := by
  intro moves
  induction moves with
  | nil =>
      intro start finish parity checked
      rw [boundedEndpoint] at checked
      split at checked
      · rename_i inBounds
        simp only [Option.some.injEq, Prod.mk.injEq] at checked
        rcases checked with ⟨rfl, rfl⟩
        exact BoundedPath.refl start (portInBounds_eq_true inBounds)
      · contradiction
  | cons move moves inductionHypothesis =>
      intro start finish parity checked
      rw [boundedEndpoint] at checked
      by_cases valid : move.first = start ∧ move.valid indexGrid = true ∧
          portInBounds start width height = true ∧
          portInBounds move.second width height = true
      · rw [if_pos valid] at checked
        cases tail : boundedEndpoint indexGrid width height move.second moves with
        | none => simp [tail] at checked
        | some result =>
            rcases result with ⟨tailFinish, tailParity⟩
            rw [tail] at checked
            simp only [Option.some.injEq, Prod.mk.injEq] at checked
            rcases checked with ⟨rfl, rfl⟩
            have firstBounds : PortInBounds move.first width height := by
              rw [valid.1]
              exact portInBounds_eq_true valid.2.2.1
            rw [← valid.1]
            exact BoundedPath.trans
              (BoundedPath.ofLink (move.link_of_valid valid.2.1)
                firstBounds
                (portInBounds_eq_true valid.2.2.2))
              (inductionHypothesis tail)
      · rw [if_neg valid] at checked
        contradiction

end RedShadeGraphCertificate
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
