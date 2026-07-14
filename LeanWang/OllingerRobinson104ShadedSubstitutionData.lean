/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104RedShadeGraphRefinement
import LeanWang.OllingerRobinson104Tiles

/-!
# Finite-state substitution for the red-shade layer

A corrected tile carries a `2 x 2` block of quarter shade states.  There are at
most two such blocks for each of the 104 corrected tile types.  Two
substitutions replace one decorated tile by a `4 x 4` block of decorated tiles.

The shade selected for a newly created board also needs one hierarchy-context
bit.  `modelChoiceTrue` and `modelTransitionTrue` are a finite strategy found
by an exhaustive SAT check.  The executable definitions below reconstruct the
chosen decorated substitution and its closed reachable state set; the separate
certificate module audits all local and boundary conditions with
`native_decide`.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace ShadedSubstitution

open RedShadeGraph RedShadeGraphRefinement Signals.FreeCellLocal

set_option maxRecDepth 20000

/-- Four quarter shade states decorating one corrected tile. -/
structure ShadeBlock where
  southwest : RedShades.State
  southeast : RedShades.State
  northwest : RedShades.State
  northeast : RedShades.State
deriving DecidableEq, Repr

def ShadeBlock.at (block : ShadeBlock) (x y : Nat) : RedShades.State :=
  if x = 0 then if y = 0 then block.southwest else block.northwest
  else if y = 0 then block.southeast else block.northeast

def allowedStates (parent : Index) (x y : Nat) : List RedShades.State :=
  RedShades.State.all.filter fun state =>
    RedShades.locallyAllowed (parent, quadrantAt x y) state

def shadeBlocks (parent : Index) : List ShadeBlock :=
  (allowedStates parent 0 0).flatMap fun southwest =>
    (allowedStates parent 1 0).flatMap fun southeast =>
      (allowedStates parent 0 1).flatMap fun northwest =>
        (allowedStates parent 1 1).map fun northeast =>
          { southwest, southeast, northwest, northeast }

def ShadeBlock.valid (block : ShadeBlock) : Bool :=
  decide (block.southwest.east = block.southeast.west) &&
    decide (block.northwest.east = block.northeast.west) &&
    decide (block.southwest.north = block.northwest.south) &&
    decide (block.southeast.north = block.northeast.south)

def validShadeBlocks (parent : Index) : List ShadeBlock :=
  (shadeBlocks parent).filter ShadeBlock.valid

def ShadeBlock.hMatches (left right : ShadeBlock) : Bool :=
  decide ((left.at 1 0).east = (right.at 0 0).west) &&
    decide ((left.at 1 1).east = (right.at 0 1).west)

def ShadeBlock.vMatches (lower upper : ShadeBlock) : Bool :=
  decide ((lower.at 0 1).north = (upper.at 0 0).south) &&
    decide ((lower.at 1 1).north = (upper.at 1 0).south)

def compatiblePlacement (position : Nat) (placedRev : List ShadeBlock)
    (candidate : ShadeBlock) : Bool :=
  let horizontal :=
    if position % 4 = 0 then true
    else match placedRev.head? with
      | none => false
      | some left => left.hMatches candidate
  let vertical :=
    if position < 4 then true
    else match placedRev[3]? with
      | none => false
      | some lower => lower.vMatches candidate
  horizontal && vertical

/-- Enumerate valid `4 x 4` decorated expansions, fixing the southwest
decorated child to the sparse copy of the parent shade block. -/
def expansionsAux (parent : Index) (parentBlock : ShadeBlock) :
    Nat → List ShadeBlock → List (List ShadeBlock)
  | 0, placedRev =>
      if placedRev.length = 16 then [placedRev.reverse] else []
  | fuel + 1, placedRev =>
      let position := placedRev.length
      if position = 16 then [placedRev.reverse]
      else
        let candidates :=
          if position = 0 then [parentBlock]
          else validShadeBlocks
            (fineGrid parent (position % 4) (position / 4))
        candidates.flatMap fun candidate =>
          if compatiblePlacement position placedRev candidate then
            expansionsAux parent parentBlock fuel (candidate :: placedRev)
          else []

def expansions (parent : Index) (parentBlock : ShadeBlock) :
    List (List ShadeBlock) :=
  expansionsAux parent parentBlock 16 []

structure StateInfo where
  parent : Index
  block : ShadeBlock
  choices : List (List ShadeBlock)
deriving Repr

/-- The 176 corrected-tile/shade-block states. -/
def stateInfos : List StateInfo :=
  (List.finRange 104).flatMap fun parent =>
    (validShadeBlocks parent).map fun block =>
      { parent, block, choices := expansions parent block }

def stateIndex (parent : Index) (block : ShadeBlock) : Option Nat :=
  stateInfos.findIdx? fun info => info.parent == parent && info.block == block

structure DecoratedData where
  parent : Index
  block : ShadeBlock
  expansion : List ShadeBlock
deriving Repr

def choiceData (info : StateInfo) (choice : Nat) : Option DecoratedData :=
  info.choices[choice]?.map fun expansion =>
    { parent := info.parent, block := info.block, expansion }

def expansionHMatches (left right : List ShadeBlock) : Bool :=
  (List.range 4).all fun y =>
    match left[3 + 4 * y]?, right[4 * y]? with
    | some leftBlock, some rightBlock => leftBlock.hMatches rightBlock
    | _, _ => false

def expansionVMatches (lower upper : List ShadeBlock) : Bool :=
  (List.range 4).all fun x =>
    match lower[x + 12]?, upper[x]? with
    | some lowerBlock, some upperBlock => lowerBlock.vMatches upperBlock
    | _, _ => false

def decoratedHCompatible (left right : DecoratedData) : Bool :=
  if WangTile.HMatches (tile (components left.parent))
      (tile (components right.parent)) && left.block.hMatches right.block then
    expansionHMatches left.expansion right.expansion
  else true

def decoratedVCompatible (lower upper : DecoratedData) : Bool :=
  if WangTile.VMatches (tile (components lower.parent))
      (tile (components upper.parent)) && lower.block.vMatches upper.block then
    expansionVMatches lower.expansion upper.expansion
  else true

/-- SAT-selected expansion-choice bits for the two hierarchy contexts. -/
def modelChoiceTrue : List Nat :=
  [0,1,2,3,4,5,6,7,16,17,18,19,20,21,38,39,40,41,42,43,44,45,46,47,
   48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,
   70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,
   92,93,94,95,136,137,138,139,140,141,142,143,144,145,146,147,148,149,
   150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,
   167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,
   192,193,194,195,196,197,214,215,216,217,218,219,220,221,222,223,224,
   225,226,227,228,229,230,231,232,233,234,235,236,237,238,239,240,241,
   242,243,244,245,246,247,248,249,250,251,252,253,254,255,256,257,258,
   259,260,261,262,263,264,265,266,267,268,269,270,271,312,313,314,315,
   316,317,318,319,320,321,322,323,324,325,326,327,328,329,330,331,332,
   333,334,335,336,337,338,339,340,341,342,343,344,345,346,347,348,349,
   350,351]

/-- Positions whose child hierarchy context differs from the parent context. -/
def modelTransitionTrue : List Nat :=
  [0,1,2,4,6,7,8,9,10,11,12,14,15]

def strategyVariable (context : Bool) (state : Nat) : Nat :=
  state + if context then stateInfos.length else 0

def modelChoice (context : Bool) (state : Nat) : Nat :=
  if strategyVariable context state ∈ modelChoiceTrue then 1 else 0

def modelTransition (position : Nat) : Bool :=
  decide (position ∈ modelTransitionTrue)

/-- Encoded decorated state: context in the high half, state index in the low
half. -/
def encodeNode (context : Bool) (state : Nat) : Nat :=
  strategyVariable context state

def nodeContext (node : Nat) : Bool := decide (stateInfos.length ≤ node)

def nodeState (node : Nat) : Nat := node % stateInfos.length

def modelData (node : Nat) : Option DecoratedData :=
  match stateInfos[nodeState node]? with
  | none => none
  | some info => choiceData info (modelChoice (nodeContext node) (nodeState node))

def childNode (node position : Nat) : Option Nat :=
  match modelData node with
  | none => none
  | some data =>
      match data.expansion[position]? with
      | none => none
      | some block =>
          match stateIndex
              (fineGrid data.parent (position % 4) (position / 4)) block with
          | none => none
          | some state => some (encodeNode
              (Bool.xor (nodeContext node) (modelTransition position)) state)

def children (node : Nat) : List Nat :=
  (List.range 16).filterMap (childNode node)

def closureAux : Nat → List Nat → List Nat → List Nat
  | 0, _, visited => visited
  | _ + 1, [], visited => visited
  | fuel + 1, node :: queue, visited =>
      if node ∈ visited then closureAux fuel queue visited
      else closureAux fuel (queue ++ children node) (node :: visited)

/-- Closed decorated subsystem reachable from one concrete seed state. -/
def reachable : List Nat :=
  closureAux 10000 [encodeNode false 0] []

def modelBoundariesValid (node : Nat) : Bool :=
  let childAt (position : Nat) : Option DecoratedData :=
    match childNode node position with
    | none => none
    | some child => modelData child
  let horizontal :=
    (List.range 3).all fun x => (List.range 4).all fun y =>
      match childAt (x + 4 * y), childAt (x + 1 + 4 * y) with
      | some left, some right => decoratedHCompatible left right
      | _, _ => false
  let vertical :=
    (List.range 4).all fun x => (List.range 3).all fun y =>
      match childAt (x + 4 * y), childAt (x + 4 * (y + 1)) with
      | some lower, some upper => decoratedVCompatible lower upper
      | _, _ => false
  horizontal && vertical

def modelNodeValid (node : Nat) : Bool :=
  (modelData node).isSome && decide ((children node).length = 16) &&
    modelBoundariesValid node

/-- Executable closure and compatibility audit. -/
def reachableClosed : Bool :=
  reachable.all fun node =>
    modelNodeValid node && (children node).all fun child => child ∈ reachable

end ShadedSubstitution
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
