/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.RedShadeGraphCertificate

/-!
Untrusted finite path search for red-shade geometry certificates.

Search results are explicit move lists. Proofs consume them only after the
sound Boolean `endpoint` checker accepts them.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace RedShadeGraphSearch

open RedShadeGraph RedShadeGraphCertificate

abbrev CertificateKind := RedShadeGraphCertificate.Kind
abbrev CertificateMove := RedShadeGraphCertificate.Move

def kinds : List CertificateKind :=
  [.horizontalMatch, .verticalMatch, .horizontal, .vertical,
    .westNorth, .westSouth, .eastNorth, .eastSouth, .crossing]

def movesAt (x y : Nat) : List CertificateMove :=
  kinds.flatMap fun kind =>
    [⟨x, y, kind, false⟩, ⟨x, y, kind, true⟩]

/-- Candidate moves incident to a port, before validity and endpoint checks. -/
def candidateMoves (port : Port) : List CertificateMove :=
  movesAt port.x port.y ++
    (if port.x = 0 then []
      else [⟨port.x - 1, port.y, .horizontalMatch, true⟩]) ++
    (if port.y = 0 then []
      else [⟨port.x, port.y - 1, .verticalMatch, true⟩])

structure Node where
  origin : Port
  current : Port
  parity : Bool
  reverseMoves : List CertificateMove
deriving Repr

def Node.state (node : Node) : Port × Bool :=
  (node.current, node.parity)

def inBounds (port : Port) (width height : Nat) : Bool :=
  port.x < width && port.y < height

def advance (indexGrid : Nat → Nat → Index)
    (width height : Nat) (node : Node) (move : CertificateMove) : Option Node :=
  if RedShadeGraphCertificate.Move.first move = node.current &&
      RedShadeGraphCertificate.Move.valid indexGrid move &&
      inBounds (RedShadeGraphCertificate.Move.second move) width height then
    some {
      origin := node.origin
      current := RedShadeGraphCertificate.Move.second move
      parity := Bool.xor node.parity
        (RedShadeGraphCertificate.Move.parity move)
      reverseMoves := move :: node.reverseMoves
    }
  else none

def nextNodes (indexGrid : Nat → Nat → Index)
    (width height : Nat) (node : Node) : List Node :=
  (candidateMoves node.current).filterMap (advance indexGrid width height node)

def freshNodes (visited : List (Port × Bool)) (nodes : List Node) : List Node :=
  nodes.filter fun node => decide (node.state ∉ visited)

def searchAux (indexGrid : Nat → Nat → Index)
    (width height : Nat) (accept : Port → Bool → Bool) :
    Nat → List Node → List (Port × Bool) → Option Node
  | 0, _, _ => none
  | _ + 1, [], _ => none
  | fuel + 1, node :: queue, visited =>
      if accept node.current node.parity then some node
      else
        let fresh := freshNodes visited (nextNodes indexGrid width height node)
        searchAux indexGrid width height accept fuel
          (queue ++ fresh) (visited ++ fresh.map Node.state)

/-- Flood a bounded component from several initial ports, retaining paths. -/
def exploreAux (indexGrid : Nat → Nat → Index)
    (width height : Nat) :
    Nat → List Node → List (Port × Bool) → List Node → List Node
  | 0, _, _, found => found
  | _ + 1, [], _, found => found
  | fuel + 1, node :: stack, visited, found =>
      let fresh := freshNodes visited (nextNodes indexGrid width height node)
      exploreAux indexGrid width height fuel
        (fresh ++ stack) (visited ++ fresh.map Node.state) (node :: found)

def explore (indexGrid : Nat → Nat → Index)
    (width height fuel : Nat) (starts : List Port) : List Node :=
  let nodes := starts.map fun start => ⟨start, start, false, []⟩
  exploreAux indexGrid width height fuel nodes (nodes.map Node.state) []

def sideCode : Side → Nat
  | .west => 0
  | .east => 1
  | .south => 2
  | .north => 3

def stateCode (width : Nat) (state : Port × Bool) : Nat :=
  2 * (4 * (width * state.1.y + state.1.x) + sideCode state.1.side) +
    if state.2 then 1 else 0

def markFresh (width : Nat) :
    List Node × Array Bool → Node → List Node × Array Bool
  | (fresh, visited), node =>
      let code := stateCode width node.state
      match visited[code]? with
      | some true => (fresh, visited)
      | _ => (node :: fresh, visited.setIfInBounds code true)

def markFreshList (width : Nat) (visited : Array Bool) (nodes : List Node) :
    List Node × Array Bool :=
  nodes.foldl (markFresh width) ([], visited)

def exploreFastAux (indexGrid : Nat → Nat → Index)
    (width height : Nat) :
    Nat → List Node → Array Bool → List Node → List Node
  | 0, _, _, found => found
  | _ + 1, [], _, found => found
  | fuel + 1, node :: stack, visited, found =>
      let marked := markFreshList width visited
        (nextNodes indexGrid width height node)
      exploreFastAux indexGrid width height fuel
        (marked.1 ++ stack) marked.2 (node :: found)

/-- Array-backed variant used by exhaustive native geometry checks. -/
def exploreFast (indexGrid : Nat → Nat → Index)
    (width height fuel : Nat) (starts : List Port) : List Node :=
  let nodes := starts.map fun start => ⟨start, start, false, []⟩
  let emptyVisited := Array.replicate (width * height * 8) false
  let marked := markFreshList width emptyVisited nodes
  exploreFastAux indexGrid width height fuel marked.1 marked.2 []

structure ReachNode where
  current : Port
  parity : Bool

def ReachNode.state (node : ReachNode) : Port × Bool :=
  (node.current, node.parity)

def advanceReach (indexGrid : Nat → Nat → Index)
    (width height : Nat) (node : ReachNode)
    (move : CertificateMove) : Option ReachNode :=
  if RedShadeGraphCertificate.Move.first move = node.current &&
      RedShadeGraphCertificate.Move.valid indexGrid move &&
      inBounds (RedShadeGraphCertificate.Move.second move) width height then
    some {
      current := RedShadeGraphCertificate.Move.second move
      parity := Bool.xor node.parity
        (RedShadeGraphCertificate.Move.parity move)
    }
  else none

def nextReachNodes (indexGrid : Nat → Nat → Index)
    (width height : Nat) (node : ReachNode) : List ReachNode :=
  (candidateMoves node.current).filterMap
    (advanceReach indexGrid width height node)

def markFreshReach (width : Nat) :
    List ReachNode × Array Bool → ReachNode → List ReachNode × Array Bool
  | (fresh, visited), node =>
      let code := stateCode width node.state
      match visited[code]? with
      | some true => (fresh, visited)
      | _ => (node :: fresh, visited.setIfInBounds code true)

def markFreshReachList (width : Nat) (visited : Array Bool)
    (nodes : List ReachNode) : List ReachNode × Array Bool :=
  nodes.foldl (markFreshReach width) ([], visited)

def reachableAux (indexGrid : Nat → Nat → Index)
    (width height : Nat) :
    Nat → List ReachNode → Array Bool → Array Bool
  | 0, _, visited => visited
  | _ + 1, [], visited => visited
  | fuel + 1, node :: stack, visited =>
      let marked := markFreshReachList width visited
        (nextReachNodes indexGrid width height node)
      reachableAux indexGrid width height fuel (marked.1 ++ stack) marked.2

/-- Compact multi-source reachability, without retaining path witnesses. -/
def reachable (indexGrid : Nat → Nat → Index)
    (width height fuel : Nat) (starts : List Port) : Array Bool :=
  let nodes := starts.map fun start => ⟨start, false⟩
  let emptyVisited := Array.replicate (width * height * 8) false
  let marked := markFreshReachList width emptyVisited nodes
  reachableAux indexGrid width height fuel marked.1 marked.2

def isReachable (width : Nat) (visited : Array Bool)
    (port : Port) (parity : Bool) : Bool :=
  visited[stateCode width (port, parity)]?.getD false

/-- Search a bounded port graph and return a checked-path candidate. -/
def search (indexGrid : Nat → Nat → Index)
    (width height fuel : Nat) (start : Port)
    (accept : Port → Bool → Bool) :
    Option (Port × Bool × List CertificateMove) :=
  if inBounds start width height then
    (searchAux indexGrid width height accept fuel
      [⟨start, start, false, []⟩] [(start, false)]).map fun (node : Node) =>
        (node.current, node.parity, node.reverseMoves.reverse)
  else none

end RedShadeGraphSearch
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
