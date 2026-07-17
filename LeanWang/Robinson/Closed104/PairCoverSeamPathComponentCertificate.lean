import Mathlib.Tactic.FinCases
import LeanWang.Robinson.Closed104.PairCoverSeamPathSemantics

/-!
# Connected-component certificates for the seam-path bases

The old base audit launched a fresh graph search from every active seam port.
Here two committed roots identify the relevant connected components. Each
component is flooded once, and array-backed source and target witnesses are
checked against the resulting bounded paths.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace PairCoverSeamPathComponentCertificate

open RedCycles RedShadeCycles RedShadeGraph RedShadeGraphSearch
  RedShadeGraphSearchSoundness RedShadeGraphWeightedSearch
  RedShadeGraphWeightedReachBounded PairCoverSeamShadePaths
  PairCoverSeamPathSearch PairCoverSeamPathBaseAudit
  PairCoverSeamPathBoundedBase ShadedFreeLineRecurrence
  PairCoverSeamArithmetic Signals.FreeCellLocal

set_option maxRecDepth 20000

@[noinline] def gridTable (grid : Nat → Nat → Index) (width height : Nat) :
    Array (Array Index) :=
  Array.ofFn fun (y : Fin height) =>
    Array.ofFn fun (x : Fin width) => grid x y

@[noinline] def cachedGridFromTable (grid : Nat → Nat → Index)
    (table : Array (Array Index)) : Nat → Nat → Index :=
  fun x y =>
    match table[y]? with
    | none => grid x y
    | some row =>
        match row[x]? with
        | none => grid x y
        | some index => index

@[simp] theorem cachedGridFromTable_gridTable_eq
    (grid : Nat → Nat → Index) (width height : Nat) :
    cachedGridFromTable grid (gridTable grid width height) = grid := by
  funext x y
  by_cases hy : y < height
  · by_cases hx : x < width
    · simp [cachedGridFromTable, gridTable, hy, hx]
    · simp [cachedGridFromTable, gridTable, hy, hx]
  · simp [cachedGridFromTable, gridTable, hy]

def firstSome : List (Option Nat) → Option Nat
  | [] => none
  | some value :: _ => some value
  | none :: values => firstSome values

def strictPreviousAux (previous : Option Nat) :
    List (Option Nat) → List (Option Nat)
  | [] => []
  | current :: values =>
      previous :: strictPreviousAux
        (match current with
        | some value => some value
        | none => previous) values

def strictPrevious (values : List (Option Nat)) : List (Option Nat) :=
  strictPreviousAux none values

def strictNext (values : List (Option Nat)) : List (Option Nat) :=
  (strictPrevious values.reverse).reverse

def stateIndexTable (width height : Nat) (nodes : List ReachNode) :
    Array (Option Nat) :=
  nodes.zipIdx.foldl (fun table entry =>
    table.setIfInBounds (stateCode width entry.1.state) (some entry.2))
    (Array.replicate (width * height * 8) none)

def indexOfState (table : Array (Option Nat)) (width : Nat)
    (port : Port) (parity : Bool) : Option Nat :=
  match table[stateCode width (port, parity)]? with
  | some result => result
  | none => none

def horizontalCandidate (grid : Nat → Nat → Index)
    (table : Array (Option Nat)) (size column y : Nat) : Option Nat :=
  if (Signals.horizontalInterior?
      (componentAt grid column y) (quadrantAt column y)).isSome then
    indexOfState table size (horizontalPort grid column y) false
  else none

def verticalCandidate (grid : Nat → Nat → Index)
    (table : Array (Option Nat)) (size x row : Nat) : Option Nat :=
  if (Signals.verticalInterior?
      (componentAt grid x row) (quadrantAt x row)).isSome then
    indexOfState table size (verticalPort grid x row) false
  else none

def verticalDirectIndices (grid : Nat → Nat → Index)
    (table : Array (Option Nat)) (size west east : Nat) :
    Array (Option Nat) :=
  ((List.range size).map fun row =>
    firstSome ((List.range size).map fun x =>
      let port := verticalPort grid x row
      if verticalTarget grid west east row port then
        indexOfState table size port false
      else none)).toArray

def horizontalDirectIndices (grid : Nat → Nat → Index)
    (table : Array (Option Nat)) (size south north : Nat) :
    Array (Option Nat) :=
  ((List.range size).map fun column =>
    firstSome ((List.range size).map fun y =>
      let port := horizontalPort grid column y
      if horizontalTarget grid south north column port then
        indexOfState table size port false
      else none)).toArray

def horizontalPreviousIndices (grid : Nat → Nat → Index)
    (table : Array (Option Nat)) (size : Nat) : Array (Option Nat) :=
  ((List.range size).flatMap fun column =>
    strictPrevious ((List.range size).map fun y =>
      horizontalCandidate grid table size column y)).toArray

def horizontalNextIndices (grid : Nat → Nat → Index)
    (table : Array (Option Nat)) (size : Nat) : Array (Option Nat) :=
  ((List.range size).flatMap fun column =>
    strictNext ((List.range size).map fun y =>
      horizontalCandidate grid table size column y)).toArray

def verticalPreviousIndices (grid : Nat → Nat → Index)
    (table : Array (Option Nat)) (size : Nat) : Array (Option Nat) :=
  ((List.range size).flatMap fun row =>
    strictPrevious ((List.range size).map fun x =>
      verticalCandidate grid table size x row)).toArray

def verticalNextIndices (grid : Nat → Nat → Index)
    (table : Array (Option Nat)) (size : Nat) : Array (Option Nat) :=
  ((List.range size).flatMap fun row =>
    strictNext ((List.range size).map fun x =>
      verticalCandidate grid table size x row)).toArray

structure Component (grid : Nat → Nat → Index) (size : Nat) where
  root : Port
  nodes : Array ReachNode
  stateIndices : Array (Option Nat)
  verticalDirect : Array (Option Nat)
  horizontalDirect : Array (Option Nat)
  horizontalPrevious : Array (Option Nat)
  horizontalNext : Array (Option Nat)
  verticalPrevious : Array (Option Nat)
  verticalNext : Array (Option Nat)
  sound :
    ∀ {index : Nat} {node : ReachNode}, nodes[index]? = some node →
      PortInBounds root size size →
      BoundedPath grid size size root node.current node.parity

def Component.make (grid : Nat → Nat → Index) (size west east : Nat)
    (root : Port) : Component grid size :=
  let flood := exploreFastWeightedReach grid size size
    (size * size * 8 + 1) [⟨root, false⟩]
  let nodes := flood.toArray
  let table := stateIndexTable size size flood
  {
    root := root
    nodes := nodes
    stateIndices := table
    verticalDirect := verticalDirectIndices grid table size west east
    horizontalDirect := horizontalDirectIndices grid table size west east
    horizontalPrevious := horizontalPreviousIndices grid table size
    horizontalNext := horizontalNextIndices grid table size
    verticalPrevious := verticalPreviousIndices grid table size
    verticalNext := verticalNextIndices grid table size
    sound := by
      intro index node hnode hroot
      rw [Array.getElem?_eq_some_iff] at hnode
      rcases hnode with ⟨hindex, hvalue⟩
      have nodeMem : node ∈ flood := by
        have arrayMem : nodes[index] ∈ nodes :=
          Array.getElem_mem hindex
        simpa [nodes, hvalue] using arrayMem
      have bounded := exploreFastWeightedReach_bounded_sound
        (starts := [⟨root, false⟩])
        (by
          intro start hstart
          simp only [List.mem_singleton] at hstart
          subst start
          exact hroot)
        nodeMem
      rcases bounded with ⟨start, hstart, path⟩
      simp only [List.mem_singleton] at hstart
      subst start
      simpa using path
  }

def Component.makeCachedWithTable (grid : Nat → Nat → Index)
    (size west east : Nat) (table : Array (Array Index))
    (same : cachedGridFromTable grid table = grid)
    (root : Port) : Component grid size :=
  let cached := cachedGridFromTable grid table
  let component := Component.make cached size west east root
  {
    root := root
    nodes := component.nodes
    stateIndices := component.stateIndices
    verticalDirect := component.verticalDirect
    horizontalDirect := component.horizontalDirect
    horizontalPrevious := component.horizontalPrevious
    horizontalNext := component.horizontalNext
    verticalPrevious := component.verticalPrevious
    verticalNext := component.verticalNext
    sound := by
      intro index node hnode hroot
      have path := component.sound hnode hroot
      change BoundedPath (cachedGridFromTable grid table) size size
        root node.current node.parity at path
      simpa only [same] using path
  }

def Component.makeCached (grid : Nat → Nat → Index)
    (size west east : Nat) (root : Port) : Component grid size :=
  Component.makeCachedWithTable grid size west east
    (gridTable grid size size)
    (cachedGridFromTable_gridTable_eq grid size size) root
@[simp] theorem Component.makeCached_root
    (grid : Nat → Nat → Index) (size west east : Nat) (root : Port) :
    (Component.makeCached grid size west east root).root = root := rfl

@[noinline] def components (grid : Nat → Nat → Index) (size west east : Nat)
    (roots : List Port) : List (Component grid size) :=
  let table := gridTable grid size size
  let same := cachedGridFromTable_gridTable_eq grid size size
  roots.map (Component.makeCachedWithTable grid size west east table same)
def optionIndex (values : Array (Option Nat)) (index : Nat) : Option Nat :=
  match values[index]? with
  | some result => result
  | none => none

def Component.nodeAt {grid : Nat → Nat → Index} {size : Nat}
    (component : Component grid size) : Option Nat → Option ReachNode
  | none => none
  | some index => component.nodes[index]?

def Component.sourceIndex {grid : Nat → Nat → Index} {size : Nat}
    (component : Component grid size) (source : Port) : Option Nat :=
  indexOfState component.stateIndices size source false

def Component.verticalDirectIndex
    {grid : Nat → Nat → Index} {size : Nat}
    (component : Component grid size) (row : Nat) : Option Nat :=
  optionIndex component.verticalDirect row

def Component.horizontalDirectIndex
    {grid : Nat → Nat → Index} {size : Nat}
    (component : Component grid size) (column : Nat) : Option Nat :=
  optionIndex component.horizontalDirect column

def Component.verticalBetweenIndex
    {grid : Nat → Nat → Index} {size : Nat}
    (component : Component grid size) (column row boundary : Nat) : Option Nat :=
  if row < boundary then
    optionIndex component.horizontalNext (size * column + row)
  else if boundary < row then
    optionIndex component.horizontalPrevious (size * column + row)
  else none

def Component.horizontalBetweenIndex
    {grid : Nat → Nat → Index} {size : Nat}
    (component : Component grid size) (row column boundary : Nat) : Option Nat :=
  if column < boundary then
    optionIndex component.verticalNext (size * row + column)
  else if boundary < column then
    optionIndex component.verticalPrevious (size * row + column)
  else none

def checkNode (candidate : Option ReachNode)
    (accept : ReachNode → Bool) : Bool :=
  match candidate with
  | none => false
  | some node => accept node

theorem checkNode_sound {candidate : Option ReachNode}
    {accept : ReachNode → Bool} (checked : checkNode candidate accept = true) :
    ∃ node, candidate = some node ∧ accept node = true := by
  cases candidate with
  | none => simp [checkNode] at checked
  | some node => exact ⟨node, rfl, checked⟩

theorem Component.nodePath
    {grid : Nat → Nat → Index} {size : Nat}
    (component : Component grid size) {candidate : Option Nat}
    {node : ReachNode} (hnode : component.nodeAt candidate = some node)
    (hroot : PortInBounds component.root size size) :
    BoundedPath grid size size component.root node.current node.parity := by
  cases candidate with
  | none => simp [Component.nodeAt] at hnode
  | some index => exact component.sound hnode hroot

def sourceAccept (source : Port) (node : ReachNode) : Bool :=
  decide (node.current = source) && !node.parity

def targetAccept (target : Port → Bool) (node : ReachNode) : Bool :=
  !node.parity && target node.current

theorem boundedPath_symm
    {grid : Nat → Nat → Index} {width height : Nat}
    {first second : Port} {parity : Bool}
    (path : BoundedPath grid width height first second parity) :
    BoundedPath grid width height second first parity := by
  induction path with
  | refl port hport => exact BoundedPath.refl port hport
  | ofLink link hfirst hsecond =>
      exact BoundedPath.ofLink (Link.symm link) hsecond hfirst
  | trans firstPath secondPath firstIH secondIH =>
      simpa [Bool.xor_comm] using
        BoundedPath.trans secondIH firstIH

private theorem boundedPath_of_checks
    {grid : Nat → Nat → Index} {size : Nat}
    (component : Component grid size)
    (hroot : PortInBounds component.root size size)
    (source : Port) (target : Port → Bool)
    {sourceIndex targetIndex : Option Nat}
    (sourceChecked :
      checkNode (component.nodeAt sourceIndex) (sourceAccept source) = true)
    (targetChecked :
      checkNode (component.nodeAt targetIndex) (targetAccept target) = true) :
    ∃ finish, target finish = true ∧
      BoundedPath grid size size source finish false := by
  rcases checkNode_sound sourceChecked with
    ⟨sourceNode, hsourceNode, hsourceAccept⟩
  rcases checkNode_sound targetChecked with
    ⟨targetNode, htargetNode, htargetAccept⟩
  have sourcePath := component.nodePath hsourceNode hroot
  have targetPath := component.nodePath htargetNode hroot
  simp only [sourceAccept, Bool.and_eq_true,
    decide_eq_true_eq] at hsourceAccept
  simp only [targetAccept, Bool.and_eq_true] at htargetAccept
  have sourceParity : sourceNode.parity = false :=
    Bool.eq_false_of_not_eq_true' hsourceAccept.2
  have targetParity : targetNode.parity = false :=
    Bool.eq_false_of_not_eq_true' htargetAccept.1
  have sourcePathFalse :
      BoundedPath grid size size component.root source false := by
    simpa [hsourceAccept.1, sourceParity] using sourcePath
  have targetPathFalse :
      BoundedPath grid size size component.root targetNode.current false := by
    simpa [targetParity] using targetPath
  refine ⟨targetNode.current, htargetAccept.2, ?_⟩
  simpa using BoundedPath.trans
    (boundedPath_symm sourcePathFalse) targetPathFalse

def verticalComponentCheck
    {grid : Nat → Nat → Index} {size : Nat}
    (west east column row boundary : Nat)
    (component : Component grid size) : Bool :=
  let source := horizontalPort grid column boundary
  let target := verticalSeamTarget grid west east column row boundary
  checkNode (component.nodeAt (component.sourceIndex source))
      (sourceAccept source) &&
    (checkNode
        (component.nodeAt (component.verticalDirectIndex row))
        (targetAccept target) ||
      checkNode
        (component.nodeAt
          (component.verticalBetweenIndex column row boundary))
        (targetAccept target))

def horizontalComponentCheck
    {grid : Nat → Nat → Index} {size : Nat}
    (south north row column boundary : Nat)
    (component : Component grid size) : Bool :=
  let source := verticalPort grid boundary row
  let target := horizontalSeamTarget grid south north row column boundary
  checkNode (component.nodeAt (component.sourceIndex source))
      (sourceAccept source) &&
    (checkNode
        (component.nodeAt (component.horizontalDirectIndex column))
        (targetAccept target) ||
      checkNode
        (component.nodeAt
          (component.horizontalBetweenIndex row column boundary))
        (targetAccept target))

theorem verticalComponentCheck_sound
    {grid : Nat → Nat → Index} {size : Nat}
    {west east column row boundary : Nat}
    {component : Component grid size}
    (hroot : PortInBounds component.root size size)
    (checked : verticalComponentCheck west east column row boundary
      component = true) :
    BoundedVerticalSeamPath grid size west east column row boundary := by
  simp only [verticalComponentCheck, Bool.and_eq_true,
    Bool.or_eq_true] at checked
  rcases checked.2 with direct | between
  · rcases boundedPath_of_checks component hroot
      (horizontalPort grid column boundary)
      (verticalSeamTarget grid west east column row boundary)
      checked.1 direct with ⟨finish, target, path⟩
    exact boundedVerticalSeamPath_of_target path target
  · rcases boundedPath_of_checks component hroot
      (horizontalPort grid column boundary)
      (verticalSeamTarget grid west east column row boundary)
      checked.1 between with ⟨finish, target, path⟩
    exact boundedVerticalSeamPath_of_target path target

theorem horizontalComponentCheck_sound
    {grid : Nat → Nat → Index} {size : Nat}
    {south north row column boundary : Nat}
    {component : Component grid size}
    (hroot : PortInBounds component.root size size)
    (checked : horizontalComponentCheck south north row column boundary
      component = true) :
    BoundedHorizontalSeamPath grid size south north row column boundary := by
  simp only [horizontalComponentCheck, Bool.and_eq_true,
    Bool.or_eq_true] at checked
  rcases checked.2 with direct | between
  · rcases boundedPath_of_checks component hroot
      (verticalPort grid boundary row)
      (horizontalSeamTarget grid south north row column boundary)
      checked.1 direct with ⟨finish, target, path⟩
    exact boundedHorizontalSeamPath_of_target path target
  · rcases boundedPath_of_checks component hroot
      (verticalPort grid boundary row)
      (horizontalSeamTarget grid south north row column boundary)
      checked.1 between with ⟨finish, target, path⟩
    exact boundedHorizontalSeamPath_of_target path target

def verticalCheck (phase : Phase) (depth : Nat)
    (grid : Nat → Nat → Index) (coords : List Nat) (west east : Nat)
    {size : Nat} (certificate : List (Component grid size)) : Bool :=
  coords.all fun column => coords.all fun boundary =>
    (verticalQueries phase depth grid coords column boundary).all fun row =>
      certificate.any (verticalComponentCheck west east column row boundary)

def horizontalCheck (phase : Phase) (depth : Nat)
    (grid : Nat → Nat → Index) (coords : List Nat) (south north : Nat)
    {size : Nat} (certificate : List (Component grid size)) : Bool :=
  coords.all fun boundary => coords.all fun row =>
    (horizontalQueries phase depth grid coords row boundary).all fun column =>
      certificate.any (horizontalComponentCheck south north row column boundary)

@[noinline] def checkParent (phase : Phase) (depth : Nat) (roots : List Port)
    (parent : Index) : Bool :=
  let grid := fineGrid phase depth (fun _ _ => parent)
  let coords := coordinates phase depth
  let size := searchSize phase depth
  let west := successorWest phase depth 0
  let east := successorEast phase depth 0
  let certificate := components grid size west east roots
  verticalCheck phase depth grid coords west east certificate &&
    horizontalCheck phase depth grid coords west east certificate

@[noinline] def checkChunk (phase : Phase) (depth : Nat) (roots : List Port)
    (chunk : Chunk) : Bool :=
  (parentChunk chunk).all (checkParent phase depth roots)

def chunkParent (chunk : Chunk) (offset : Fin 4) : Index :=
  ((parentChunk chunk)[offset.val]?).getD 0

set_option linter.style.nativeDecide false in
theorem parentChunk_eq_map_chunkParent (chunk : Chunk) :
    parentChunk chunk = (List.finRange 4).map (chunkParent chunk) := by
  fin_cases chunk <;> native_decide

def checkChunkParent (phase : Phase) (depth : Nat) (roots : List Port)
    (chunk : Chunk) (offset : Fin 4) : Bool :=
  checkParent phase depth roots (chunkParent chunk offset)

opaque checkChunkParentNative (phase : Phase) (depth : Nat)
    (roots : List Port) (chunk : Chunk) (offset : Fin 4) : Bool :=
  checkChunkParent phase depth roots chunk offset

@[implemented_by checkChunkParentNative]
def compiledCheckChunkParent (phase : Phase) (depth : Nat)
    (roots : List Port) (chunk : Chunk) (offset : Fin 4) : Bool :=
  checkChunkParent phase depth roots chunk offset

theorem compiledCheckChunkParent_eq_checkChunkParent
    (phase : Phase) (depth : Nat) (roots : List Port)
    (chunk : Chunk) (offset : Fin 4) :
    compiledCheckChunkParent phase depth roots chunk offset =
      checkChunkParent phase depth roots chunk offset := rfl

theorem checkChunk_of_parentChecks
    {phase : Phase} {depth : Nat} {roots : List Port} {chunk : Chunk}
    (checked : ∀ offset : Fin 4,
      checkChunkParent phase depth roots chunk offset = true) :
    checkChunk phase depth roots chunk = true := by
  simp only [checkChunk, List.all_eq_true]
  intro parent hparent
  rw [parentChunk_eq_map_chunkParent] at hparent
  simp only [List.mem_map] at hparent
  rcases hparent with ⟨offset, _, rfl⟩
  exact checked offset
def ChunkChecks (phase : Phase) (depth : Nat) (roots : List Port) : Prop :=
  ∀ chunk : Chunk, checkChunk phase depth roots chunk = true

theorem checkParent_sound
    {phase : Phase} {depth : Nat} {roots : List Port} {parent : Index}
    (rootBounds : ∀ root ∈ roots,
      PortInBounds root (searchSize phase depth) (searchSize phase depth))
    (checked : checkParent phase depth roots parent = true) :
    BoundedParentPaths phase depth parent := by
  simp only [checkParent, Bool.and_eq_true] at checked
  constructor
  · dsimp only
    intro column boundary row hcolumn hboundary hrow
    simp only [verticalCheck, List.all_eq_true] at checked
    have rowChecked := checked.1 column hcolumn boundary hboundary row hrow
    simp only [List.any_eq_true] at rowChecked
    rcases rowChecked with ⟨component, hcomponent, hchecked⟩
    rcases List.mem_map.1 hcomponent with ⟨root, hroot, hcomponent⟩
    have componentRoot : component.root = root := by
      rw [← hcomponent]
      exact Component.makeCached_root _ _ _ _ _
    apply verticalComponentCheck_sound
    · rw [componentRoot]
      exact rootBounds root hroot
    · exact hchecked
  · dsimp only
    intro boundary row column hboundary hrow hcolumn
    simp only [horizontalCheck, List.all_eq_true] at checked
    have columnChecked :=
      checked.2 boundary hboundary row hrow column hcolumn
    simp only [List.any_eq_true] at columnChecked
    rcases columnChecked with ⟨component, hcomponent, hchecked⟩
    rcases List.mem_map.1 hcomponent with ⟨root, hroot, hcomponent⟩
    have componentRoot : component.root = root := by
      rw [← hcomponent]
      exact Component.makeCached_root _ _ _ _ _
    apply horizontalComponentCheck_sound
    · rw [componentRoot]
      exact rootBounds root hroot
    · exact hchecked

theorem ChunkChecks.boundedPaths
    {phase : Phase} {depth : Nat} {roots : List Port}
    (rootBounds : ∀ root ∈ roots,
      PortInBounds root (searchSize phase depth) (searchSize phase depth))
    (checked : ChunkChecks phase depth roots) :
    BoundedPaths phase depth := by
  apply BoundedCanonicalPaths.paths
  intro parent hparent
  rw [canonicalParents_eq_chunks] at hparent
  simp only [List.mem_flatMap] at hparent
  rcases hparent with ⟨chunk, _, hparent⟩
  apply checkParent_sound rootBounds
  have chunkChecked := checked chunk
  simp only [checkChunk, List.all_eq_true] at chunkChecked
  exact chunkChecked parent hparent

theorem boundedParentPaths_to_parentPaths
    {phase : Phase} {depth : Nat} {parent : Index}
    (bounded : BoundedParentPaths phase depth parent) :
    ParentPaths phase depth parent := by
  constructor
  · dsimp only
    intro column boundary row hcolumn hboundary hrow
    rcases bounded.vertical hcolumn hboundary hrow with path | path
    · left
      rcases path with ⟨target, hwest, heast, hinterior, boundedPath⟩
      exact ⟨target, hwest, heast, hinterior, boundedPath.path⟩
    · right
      rcases path with ⟨target, hbetween, hinterior, boundedPath⟩
      exact ⟨target, hbetween, hinterior, boundedPath.path⟩
  · dsimp only
    intro boundary row column hboundary hrow hcolumn
    rcases bounded.horizontal hboundary hrow hcolumn with path | path
    · left
      rcases path with ⟨target, hsouth, hnorth, hinterior, boundedPath⟩
      exact ⟨target, hsouth, hnorth, hinterior, boundedPath.path⟩
    · right
      rcases path with ⟨target, hbetween, hinterior, boundedPath⟩
      exact ⟨target, hbetween, hinterior, boundedPath.path⟩

theorem BoundedPaths.paths
    {phase : Phase} {depth : Nat} (bounded : BoundedPaths phase depth) :
    Paths phase depth :=
  fun parent => boundedParentPaths_to_parentPaths (bounded parent)

def oddRoots : List Port :=
  [⟨21, 21, .east⟩, ⟨18, 24, .west⟩]

def evenRoots : List Port :=
  [⟨35, 35, .east⟩, ⟨34, 48, .west⟩]

theorem oddRoots_inBounds :
    ∀ root ∈ oddRoots,
      PortInBounds root (searchSize .odd 0) (searchSize .odd 0) := by
  intro root hroot
  simp only [oddRoots, List.mem_cons, List.not_mem_nil, or_false] at hroot
  rcases hroot with rfl | rfl <;>
    norm_num [PortInBounds, searchSize, refinementDepth, Phase.extra]

theorem evenRoots_inBounds :
    ∀ root ∈ evenRoots,
      PortInBounds root (searchSize .even 1) (searchSize .even 1) := by
  intro root hroot
  simp only [evenRoots, List.mem_cons, List.not_mem_nil, or_false] at hroot
  rcases hroot with rfl | rfl <;>
    norm_num [PortInBounds, searchSize, refinementDepth, Phase.extra]

end PairCoverSeamPathComponentCertificate
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
