/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Machine.InputHistory

/-!
# Wang histories with a finite input on the bottom row

Horizontal position tags force the finite input history from the distinguished
corner.  Beyond a computable bound, the bottom history is constant and uses
one self-looping tail tile.  Normal rows use the same finite local-history
language as the empty-input construction.

The theorem `tilesQuarterWithSeed_iff_not_halts` has two directions.  For a
nonhalting run, `runTile` places its actual two-row local histories in the
quarter plane.  Conversely, the seed and horizontal position tags force the
entire bottom row; row tags make every higher tile a normal history tile.
Vertical colors expose the lower triples of the next row, and horizontal
overlaps make those triples one coherent machine configuration.  Inductively,
every positive tiling row therefore decodes to the corresponding run row.  A
first halting configuration is impossible because the normal history palette
contains no tile whose relevant transition enters the halt state.

The position tags are needed only on the input-dependent bottom row.  Once the
finite input and one-step lookahead have become blank, a self-looping tag and a
single tail tile represent the infinite remainder, keeping the generated tile
set finite.
-/

namespace LeanWang
namespace MachineInputTiles

open MachineInput

/- A Wang color stores both the ordinary local-history overlap and a tag.  On
horizontal edges the tag is a bottom-row position; on vertical edges it says
whether the lower row is the distinguished input row or a normal row.  The two
matching lemmas below are the decoding interface for these packed colors. -/

def horizontalColor (positionTag rowTag : Nat)
    (prevLeft prevRight nextLeft nextRight : MachineCell) : Nat :=
  Nat.pair positionTag
    (taggedOverlapCellColor rowTag prevLeft prevRight nextLeft nextRight)

def toWangTile (westTag eastTag rowTag nextRowTag : Nat)
    (tile : MachineHistoryTile) : WangTile where
  n := taggedTripleCellColor nextRowTag
    tile.nextLeft tile.nextCenter tile.nextRight
  s := taggedTripleCellColor rowTag
    tile.prevLeft tile.prevCenter tile.prevRight
  e := horizontalColor eastTag rowTag
    tile.prevCenter tile.prevRight tile.nextCenter tile.nextRight
  w := horizontalColor westTag rowTag
    tile.prevLeft tile.prevCenter tile.nextLeft tile.nextCenter

theorem toWangTile_primrec :
    Primrec (fun p : Nat × Nat × Nat × Nat × MachineHistoryTile =>
      toWangTile p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  let tagged : Nat × Nat × Nat × Nat × MachineHistoryTile → WangTile :=
    fun p => p.2.2.2.2.toTaggedWangTile p.2.2.1 p.2.2.2.1
  have htagged : Primrec tagged :=
    MachineHistoryTile.toTaggedWangTile_primrec.comp
      (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.pair
          (Primrec.fst.comp (Primrec.snd.comp
            (Primrec.snd.comp Primrec.snd)))
          (Primrec.snd.comp (Primrec.snd.comp
            (Primrec.snd.comp Primrec.snd)))))
  have htuple : Primrec
      (fun p : Nat × Nat × Nat × Nat × MachineHistoryTile =>
        ((tagged p).n, (tagged p).s,
          Nat.pair p.2.1 (tagged p).e,
          Nat.pair p.1 (tagged p).w)) :=
    Primrec.pair (WangTile.n_primrec.comp htagged)
      (Primrec.pair (WangTile.s_primrec.comp htagged)
        (Primrec.pair
          (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.snd)
            (WangTile.e_primrec.comp htagged))
          (Primrec₂.natPair.comp Primrec.fst
            (WangTile.w_primrec.comp htagged))))
  exact (WangTile.ofTuple_primrec.comp htuple).of_eq fun p => by
    rcases p with ⟨westTag, eastTag, rowTag, nextRowTag, history⟩
    cases history
    rfl

theorem hMatches_toWangTile_iff
    (westTag eastTag westTag' eastTag' rowTag nextRowTag rowTag' nextRowTag' : Nat)
    (left right : MachineHistoryTile) :
    WangTile.HMatches
        (toWangTile westTag eastTag rowTag nextRowTag left)
        (toWangTile westTag' eastTag' rowTag' nextRowTag' right) ↔
      eastTag = westTag' ∧ rowTag = rowTag' ∧
        left.prevCenter = right.prevLeft ∧
        left.prevRight = right.prevCenter ∧
        left.nextCenter = right.nextLeft ∧
        left.nextRight = right.nextCenter := by
  simp [WangTile.HMatches, toWangTile, horizontalColor, Nat.pair_eq_pair,
    taggedOverlapCellColor_eq_iff]

theorem vMatches_toWangTile_iff
    (westTag eastTag westTag' eastTag' rowTag nextRowTag rowTag' nextRowTag' : Nat)
    (lower upper : MachineHistoryTile) :
    WangTile.VMatches
        (toWangTile westTag eastTag rowTag nextRowTag lower)
        (toWangTile westTag' eastTag' rowTag' nextRowTag' upper) ↔
      nextRowTag = rowTag' ∧
        lower.nextLeft = upper.prevLeft ∧
        lower.nextCenter = upper.prevCenter ∧
        lower.nextRight = upper.prevRight := by
  simp [WangTile.VMatches, toWangTile, taggedTripleCellColor_eq_iff]

/- The input-specific palette consists of a finite prefix followed by one
constant blank tile.  The `+ 3` margin covers both the width-three local window
and the possible one-cell head move in the first transition. -/

/-- Past this position, the time-zero local history is a constant blank tail. -/
def tailPosition (input : List Nat) : Nat :=
  input.length + 3

theorem run_zero_cell_eq_plain_blank
    (M : Machine) (input : List Nat) {position : Nat}
    (hlength : input.length ≤ position) (hpositive : 0 < position) :
    (run M input 0).cellAt position = MachineCell.plain M.blank := by
  simp [run_zero, initialID, ID.cellAt, tape,
    List.getElem?_eq_none_iff.mpr hlength, Nat.ne_of_gt hpositive]

theorem run_zero_cellLeft_eq_plain_blank
    (M : Machine) (input : List Nat) {position : Nat}
    (hlength : input.length < position) (htwo : 2 ≤ position) :
    (run M input 0).cellAtLeft position = MachineCell.plain M.blank := by
  obtain ⟨predecessor, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : position ≠ 0)
  simp only [ID.cellAtLeft_succ]
  exact run_zero_cell_eq_plain_blank M input (by omega) (by omega)

theorem run_one_cell_eq_plain_blank
    (M : Machine) (input : List Nat) {position : Nat}
    (hlength : input.length ≤ position) (htwo : 2 ≤ position) :
    (run M input 1).cellAt position = MachineCell.plain M.blank := by
  by_cases hhalt : M.start = M.halt
  · have hinitial : (initialID M input).state = M.halt := by
      simpa [initialID] using hhalt
    rw [show 1 = 0 + 1 by omega, run_succ, run_zero,
      Machine.nextID_of_halt M _ hinitial]
    exact run_zero_cell_eq_plain_blank M input hlength (by omega)
  · have hstate : (initialID M input).state ≠ M.halt := by
      simpa [initialID] using hhalt
    have hhead : (M.nextID (initialID M input)).head ≤ 1 := by
      rw [Machine.nextID_head_of_ne_halt hstate]
      rcases hstep : M.step M.start (tape M.blank input 0) with
        ⟨write, state, move⟩
      change (M.step M.start (tape M.blank input 0)).2.2.apply 0 ≤ 1
      rw [hstep]
      cases move <;> simp [Move.apply]
    rw [show 1 = 0 + 1 by omega, run_succ, run_zero]
    rw [ID.cellAt_of_ne (by omega : position ≠ (M.nextID (initialID M input)).head)]
    congr 1
    rw [Machine.nextID_tape_of_ne_head (by simp [initialID]; omega)]
    exact tape_eq_blank_of_length_le hlength

theorem run_one_cellLeft_eq_plain_blank
    (M : Machine) (input : List Nat) {position : Nat}
    (hlength : input.length + 1 < position) (hthree : 3 ≤ position) :
    (run M input 1).cellAtLeft position = MachineCell.plain M.blank := by
  obtain ⟨predecessor, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : position ≠ 0)
  simp only [ID.cellAtLeft_succ]
  exact run_one_cell_eq_plain_blank M input (by omega) (by omega)

def blankHistoryTile (M : Machine) : MachineHistoryTile where
  prevLeft := .plain M.blank
  prevCenter := .plain M.blank
  prevRight := .plain M.blank
  nextLeft := .plain M.blank
  nextCenter := .plain M.blank
  nextRight := .plain M.blank

theorem historyTile_zero_eq_blank_of_tailPosition_le
    (M : Machine) (input : List Nat) {position : Nat}
    (hposition : tailPosition input ≤ position) :
    historyTile M input 0 position = blankHistoryTile M := by
  have hp : input.length + 3 ≤ position := by
    simpa [tailPosition] using hposition
  unfold historyTile runCell runCellLeft blankHistoryTile
  simp only [Nat.zero_add]
  rw [run_zero_cellLeft_eq_plain_blank M input (by omega) (by omega)]
  rw [run_zero_cell_eq_plain_blank M input (by omega) (by omega)]
  rw [run_zero_cell_eq_plain_blank M input (by omega) (by omega)]
  rw [run_one_cellLeft_eq_plain_blank M input (by omega) (by omega)]
  rw [run_one_cell_eq_plain_blank M input (by omega) (by omega)]
  rw [run_one_cell_eq_plain_blank M input (by omega) (by omega)]

theorem historyTile_zero_eq_tail_of_tailPosition_le
    (M : Machine) (input : List Nat) {position : Nat}
    (hposition : tailPosition input ≤ position) :
    historyTile M input 0 position =
      historyTile M input 0 (tailPosition input) := by
  rw [historyTile_zero_eq_blank_of_tailPosition_le M input hposition]
  rw [historyTile_zero_eq_blank_of_tailPosition_le M input (le_refl _)]

def initialTile (M : Machine) (input : List Nat) (position : Nat) : WangTile :=
  let tail := tailPosition input
  if position < tail then
    toWangTile position (position + 1) initialRowTag normalRowTag
      (historyTile M input 0 position)
  else
    toWangTile tail tail initialRowTag normalRowTag
      (historyTile M input 0 tail)

def initialTiles (M : Machine) (input : List Nat) : TileSet :=
  ((List.range (tailPosition input)).map fun position =>
      toWangTile position (position + 1) initialRowTag normalRowTag
        (historyTile M input 0 position)) ++
    [toWangTile (tailPosition input) (tailPosition input)
      initialRowTag normalRowTag
      (historyTile M input 0 (tailPosition input))]

def normalTiles (M : Machine) : TileSet :=
  (machineHistoryTiles M).map
    (toWangTile 0 0 normalRowTag normalRowTag)

def tiles (M : Machine) (input : List Nat) : TileSet :=
  initialTiles M input ++ normalTiles M

def seed (M : Machine) (input : List Nat) : WangTile :=
  initialTile M input 0

theorem initialTile_mem (M : Machine) (input : List Nat) (position : Nat) :
    initialTile M input position ∈ initialTiles M input := by
  rw [initialTile]
  split_ifs with hposition
  · rw [initialTiles, List.mem_append]
    left
    rw [List.mem_map]
    exact ⟨position, by simp [hposition], rfl⟩
  · rw [initialTiles, List.mem_append]
    right
    simp

theorem initialTile_history (M : Machine) (input : List Nat) (position : Nat) :
    let tail := tailPosition input
    initialTile M input position =
      if position < tail then
        toWangTile position (position + 1) initialRowTag normalRowTag
          (historyTile M input 0 position)
      else
        toWangTile tail tail initialRowTag normalRowTag
          (historyTile M input 0 position) := by
  dsimp
  rw [initialTile]
  split_ifs with hposition
  · rfl
  · congr 1
    exact (historyTile_zero_eq_tail_of_tailPosition_le M input (by omega)).symm

set_option linter.flexible false in
theorem initialTile_hMatches (M : Machine) (input : List Nat) (position : Nat) :
    WangTile.HMatches (initialTile M input position)
      (initialTile M input (position + 1)) := by
  rw [initialTile_history, initialTile_history]
  by_cases hposition : position + 1 < tailPosition input
  · simp [hposition, show position < tailPosition input by omega,
      hMatches_toWangTile_iff]
    exact historyTile_hMatches M input 0 position
  · have htail : tailPosition input ≤ position + 1 := by omega
    by_cases hbefore : position < tailPosition input
    · have heq : position + 1 = tailPosition input := by omega
      simp [hbefore, heq, hMatches_toWangTile_iff]
      rw [← heq]
      exact historyTile_hMatches M input 0 position
    · simp [hbefore, hposition, hMatches_toWangTile_iff]
      rw [historyTile_zero_eq_tail_of_tailPosition_le M input (by omega :
        tailPosition input ≤ position)]
      rw [historyTile_zero_eq_tail_of_tailPosition_le M input htail]
      rw [historyTile_zero_eq_blank_of_tailPosition_le M input (le_refl _)]
      simp [blankHistoryTile]

/- Soundness: place the actual history tile at `(position, time)`.  Time zero
uses the tagged finite-input row, while all later rows use the fixed normal
palette.  Horizontal and vertical validity are then direct overlap facts. -/

def runTile (M : Machine) (input : List Nat) (time position : Nat) : WangTile :=
  if time = 0 then initialTile M input position
  else toWangTile 0 0 normalRowTag normalRowTag
    (historyTile M input time position)

theorem runTile_mem {M : Machine} {input : List Nat}
    (supported : Supported M input) (notHalts : ¬ Halts M input)
    (time position : Nat) :
    runTile M input time position ∈ tiles M input := by
  cases time with
  | zero => simp [runTile, tiles, initialTile_mem]
  | succ time =>
      rw [runTile, if_neg (by omega)]
      simp only [tiles, List.mem_append]
      right
      rw [normalTiles, List.mem_map]
      exact ⟨historyTile M input (time + 1) position,
        historyTile_mem_machineHistoryTiles supported notHalts
          (time + 1) position, rfl⟩

theorem runTile_hMatches (M : Machine) (input : List Nat)
    (time position : Nat) :
    WangTile.HMatches (runTile M input time position)
      (runTile M input time (position + 1)) := by
  cases time with
  | zero => simpa [runTile] using initialTile_hMatches M input position
  | succ time =>
      simp [runTile, hMatches_toWangTile_iff]
      exact historyTile_hMatches M input (time + 1) position

theorem runTile_vMatches (M : Machine) (input : List Nat)
    (time position : Nat) :
    WangTile.VMatches (runTile M input time position)
      (runTile M input (time + 1) position) := by
  cases time with
  | zero =>
      rw [runTile, if_pos rfl, runTile, if_neg (by omega)]
      rw [initialTile_history]
      split_ifs <;> simp [vMatches_toWangTile_iff, historyTile]
  | succ time =>
      simp [runTile, vMatches_toWangTile_iff, historyTile]

theorem tilesQuarterWithSeed_of_not_halts
    {M : Machine} {input : List Nat}
    (supported : Supported M input) (notHalts : ¬ Halts M input) :
    TilesQuarterWithSeed (tiles M input) (seed M input) := by
  let plane : Nat × Nat → TileIn (tiles M input) := fun point =>
    ⟨runTile M input point.2 point.1,
      runTile_mem supported notHalts point.2 point.1⟩
  refine ⟨plane, ?_, ?_⟩
  · constructor
    · intro point
      exact runTile_hMatches M input point.2 point.1
    · intro point
      exact runTile_vMatches M input point.2 point.1
  · rfl

/- Completeness starts by classifying every palette member.  The seed fixes
position zero, horizontal tags force its unique successor repeatedly, and the
self-looping tail handles all remaining positions.  Since every legal north
edge is tagged `normal`, vertical matching excludes another initial tile above
the bottom row. -/

theorem mem_tiles_iff (M : Machine) (input : List Nat) (tile : WangTile) :
    tile ∈ tiles M input ↔
      (∃ position, position < tailPosition input ∧
        toWangTile position (position + 1) initialRowTag normalRowTag
          (historyTile M input 0 position) = tile) ∨
      tile = toWangTile (tailPosition input) (tailPosition input)
          initialRowTag normalRowTag
          (historyTile M input 0 (tailPosition input)) ∨
      ∃ history, history ∈ machineHistoryTiles M ∧
        toWangTile 0 0 normalRowTag normalRowTag history = tile := by
  simp [tiles, initialTiles, normalTiles, List.mem_map]

/-- Every legal tile presents the normal-row tag on its north edge. -/
theorem northRowTag_eq_normal_of_mem
    {M : Machine} {input : List Nat} {tile : WangTile}
    (member : tile ∈ tiles M input) :
    tile.n.unpair.1 = normalRowTag := by
  rcases (mem_tiles_iff M input tile).1 member with
    ⟨position, _hposition, rfl⟩ | rfl | ⟨history, _hhistory, rfl⟩ <;>
    simp [toWangTile, taggedTripleCellColor]

set_option linter.flexible false in
theorem next_initialTile_of_hMatches_mem
    (M : Machine) (input : List Nat) (position : Nat) {right : WangTile}
    (hmatch : WangTile.HMatches (initialTile M input position) right)
    (hmem : right ∈ tiles M input) :
    right = initialTile M input (position + 1) := by
  rcases (mem_tiles_iff M input right).1 hmem with
    ⟨next, hnext, hright⟩ | hright | ⟨history, _hhistory, hright⟩
  · rw [initialTile] at hmatch ⊢
    split_ifs at hmatch with hposition
    · rw [← hright] at hmatch
      have htags := (hMatches_toWangTile_iff _ _ _ _ _ _ _ _ _ _).1 hmatch
      have heq : next = position + 1 := htags.1.symm
      subst next
      rw [if_pos hnext]
      exact hright.symm
    · rw [← hright] at hmatch
      have htags := (hMatches_toWangTile_iff _ _ _ _ _ _ _ _ _ _).1 hmatch
      omega
  · rw [initialTile] at hmatch ⊢
    split_ifs at hmatch with hposition
    · rw [hright] at hmatch
      have htags := (hMatches_toWangTile_iff _ _ _ _ _ _ _ _ _ _).1 hmatch
      have heq : position + 1 = tailPosition input := htags.1
      rw [if_neg (by omega)]
      exact hright
    · rw [if_neg (by omega)]
      exact hright
  · rw [initialTile] at hmatch
    split_ifs at hmatch <;> rw [← hright] at hmatch
    · exact False.elim (initialRowTag_ne_normalRowTag
        ((hMatches_toWangTile_iff _ _ _ _ _ _ _ _ _ _).1 hmatch).2.1)
    · exact False.elim (initialRowTag_ne_normalRowTag
        ((hMatches_toWangTile_iff _ _ _ _ _ _ _ _ _ _).1 hmatch).2.1)

theorem seeded_tiling_row_zero_eq
    {M : Machine} {input : List Nat}
    {plane : Nat × Nat → TileIn (tiles M input)}
    (valid : ValidQuarterTiling (tiles M input) plane)
    (seeded : (plane (0, 0)).1 = seed M input) :
    ∀ position, (plane (position, 0)).1 = initialTile M input position := by
  intro position
  induction position with
  | zero => exact seeded
  | succ position ih =>
      apply next_initialTile_of_hMatches_mem M input position
      · simpa [ih] using valid.1 (position, 0)
      · exact (plane (position + 1, 0)).2

theorem normal_of_vMatches
    (M : Machine) (input : List Nat) {lower upper : WangTile}
    (lowerMem : lower ∈ tiles M input) (upperMem : upper ∈ tiles M input)
    (hmatches : WangTile.VMatches lower upper) :
    ∃ history, history ∈ machineHistoryTiles M ∧
      toWangTile 0 0 normalRowTag normalRowTag history = upper := by
  have upperRowTag : upper.s.unpair.1 = normalRowTag := by
    rw [← hmatches]
    exact northRowTag_eq_normal_of_mem lowerMem
  rcases (mem_tiles_iff M input upper).1 upperMem with
    ⟨upperPosition, _hupperPosition, hupper⟩ | hupper |
      ⟨upperHistory, hupperHistory, hupper⟩
  · have tagEq : initialRowTag = normalRowTag := by
      simpa [← hupper, toWangTile, taggedTripleCellColor] using upperRowTag
    exact (initialRowTag_ne_normalRowTag tagEq).elim
  · have tagEq : initialRowTag = normalRowTag := by
      simpa [hupper, toWangTile, taggedTripleCellColor] using upperRowTag
    exact (initialRowTag_ne_normalRowTag tagEq).elim
  · exact ⟨upperHistory, hupperHistory, hupper⟩

theorem positive_row_decode
    {M : Machine} {input : List Nat}
    {plane : Nat × Nat → TileIn (tiles M input)}
    (valid : ValidQuarterTiling (tiles M input) plane)
    (time position : Nat) :
    ∃ history, history ∈ machineHistoryTiles M ∧
      toWangTile 0 0 normalRowTag normalRowTag history =
        (plane (position, time + 1)).1 := by
  exact normal_of_vMatches M input
    (plane (position, time)).2 (plane (position, time + 1)).2
    (valid.2 (position, time))

/-- A decoded positive row, represented by a coherent row of local history
tiles whose lower cells are the corresponding machine configuration. -/
structure IsDecodedHistoryRow (M : Machine) (input : List Nat)
    (plane : Nat × Nat → TileIn (tiles M input)) (time : Nat)
    (row : Nat → MachineHistoryTile) : Prop where
  mem (position : Nat) : row position ∈ machineHistoryTiles M
  encoded (position : Nat) :
    toWangTile 0 0 normalRowTag normalRowTag (row position) =
      (plane (position, time)).1
  prevCells (position : Nat) :
    (row position).prevLeft = (historyTile M input time position).prevLeft ∧
      (row position).prevCenter = (historyTile M input time position).prevCenter ∧
      (row position).prevRight = (historyTile M input time position).prevRight

def DecodedHistoryRow (M : Machine) (input : List Nat)
    (plane : Nat × Nat → TileIn (tiles M input)) (time : Nat) : Prop :=
  ∃ row, IsDecodedHistoryRow M input plane time row

/- A decoded row remembers more than tile membership: its lower triples equal
the true machine configuration at that time.  Local transition validity fixes
each upper center; overlap with neighboring tiles fixes the upper left and
right cells.  Vertical matching then transfers all three cells to the lower
triple of the next row. -/

theorem row_one_decoded
    {M : Machine} {input : List Nat}
    {plane : Nat × Nat → TileIn (tiles M input)}
    (valid : ValidQuarterTiling (tiles M input) plane)
    (seeded : (plane (0, 0)).1 = seed M input) :
    DecodedHistoryRow M input plane 1 := by
  choose row hrow using fun position => positive_row_decode valid 0 position
  refine ⟨row, ⟨fun position => (hrow position).1,
    fun position => (hrow position).2, ?_⟩⟩
  intro position
  have hbottom := seeded_tiling_row_zero_eq valid seeded position
  have hvertical : WangTile.VMatches
      (initialTile M input position)
      (toWangTile 0 0 normalRowTag normalRowTag (row position)) := by
    simpa [hbottom, (hrow position).2] using valid.2 (position, 0)
  rw [initialTile_history] at hvertical
  split_ifs at hvertical <;>
    have hcells := (vMatches_toWangTile_iff _ _ _ _ _ _ _ _ _ _).1 hvertical
  all_goals
    exact ⟨by simpa [historyTile] using hcells.2.1.symm,
      by simpa [historyTile] using hcells.2.2.1.symm,
      by simpa [historyTile] using hcells.2.2.2.symm⟩

theorem positive_row_hMatches_cells
    {M : Machine} {input : List Nat}
    {plane : Nat × Nat → TileIn (tiles M input)}
    (valid : ValidQuarterTiling (tiles M input) plane)
    {time position : Nat} {left right : MachineHistoryTile}
    (hleft : toWangTile 0 0 normalRowTag normalRowTag left =
      (plane (position, time + 1)).1)
    (hright : toWangTile 0 0 normalRowTag normalRowTag right =
      (plane (position + 1, time + 1)).1) :
    left.prevCenter = right.prevLeft ∧
      left.prevRight = right.prevCenter ∧
      left.nextCenter = right.nextLeft ∧
      left.nextRight = right.nextCenter := by
  have hhorizontal : WangTile.HMatches
      (toWangTile 0 0 normalRowTag normalRowTag left)
      (toWangTile 0 0 normalRowTag normalRowTag right) := by
    simpa [hleft, hright] using valid.1 (position, time + 1)
  exact (hMatches_toWangTile_iff _ _ _ _ _ _ _ _ _ _).1 hhorizontal |>.2.2

theorem nextCenter_eq_historyTile_nextCenter_of_prev_cells
    {M : Machine} {input : List Nat} {time position : Nat}
    {tile : MachineHistoryTile}
    (tileMem : tile ∈ machineHistoryTiles M)
    (hstate : (run M input time).state ≠ M.halt)
    (hnext : (run M input (time + 1)).state ≠ M.halt)
    (hprevLeft : tile.prevLeft = (historyTile M input time position).prevLeft)
    (hprevCenter : tile.prevCenter = (historyTile M input time position).prevCenter)
    (hprevRight : tile.prevRight = (historyTile M input time position).prevRight) :
    tile.nextCenter = (historyTile M input time position).nextCenter := by
  have hlocal := localNextCell?_of_mem_machineHistoryTiles tileMem
  rw [hprevLeft, hprevCenter, hprevRight] at hlocal
  have hrun := historyTile_local_of_state_ne_halt hstate hnext position
  rw [hrun] at hlocal
  exact Option.some.inj hlocal.symm

/-- Local transition validity and horizontal matching determine all three
upper cells of a decoded history row. -/
theorem next_cells_eq_historyTile_of_decoded_row
    {M : Machine} {input : List Nat}
    {plane : Nat × Nat → TileIn (tiles M input)}
    (valid : ValidQuarterTiling (tiles M input) plane)
    {time : Nat} {row : Nat → MachineHistoryTile}
    (decoded : IsDecodedHistoryRow M input plane (time + 1) row)
    (hstate : (run M input (time + 1)).state ≠ M.halt)
    (hnext : (run M input (time + 1 + 1)).state ≠ M.halt)
    (position : Nat) :
    (row position).nextLeft =
        (historyTile M input (time + 1 + 1) position).prevLeft ∧
      (row position).nextCenter =
        (historyTile M input (time + 1 + 1) position).prevCenter ∧
      (row position).nextRight =
        (historyTile M input (time + 1 + 1) position).prevRight := by
  have nextCenter (p : Nat) :
      (row p).nextCenter = (historyTile M input (time + 1) p).nextCenter :=
    nextCenter_eq_historyTile_nextCenter_of_prev_cells
      (decoded.mem p) hstate hnext
      (decoded.prevCells p).1 (decoded.prevCells p).2.1
      (decoded.prevCells p).2.2
  have nextLeft : (row position).nextLeft =
      (historyTile M input (time + 1 + 1) position).prevLeft := by
    cases position with
    | zero =>
        rw [nextLeft_boundary_of_mem_machineHistoryTiles (decoded.mem 0)
          (by simpa [historyTile, runCellLeft] using (decoded.prevCells 0).1)]
        simp [historyTile, runCellLeft]
    | succ predecessor =>
        have hmatches := positive_row_hMatches_cells valid
          (time := time) (position := predecessor)
          (decoded.encoded predecessor) (decoded.encoded (predecessor + 1))
        calc
          (row (Nat.succ predecessor)).nextLeft =
              (row predecessor).nextCenter := by
            simpa [Nat.succ_eq_add_one] using hmatches.2.2.1.symm
          _ = (historyTile M input (time + 1) predecessor).nextCenter :=
            nextCenter predecessor
          _ = (historyTile M input (time + 1 + 1)
              (Nat.succ predecessor)).prevLeft := by
            simp [historyTile, runCellLeft, runCell, Nat.succ_eq_add_one]
  have hmatches := positive_row_hMatches_cells valid
    (time := time) (position := position)
    (decoded.encoded position) (decoded.encoded (position + 1))
  exact ⟨nextLeft,
    by simpa [historyTile] using nextCenter position,
    calc
      (row position).nextRight = (row (position + 1)).nextCenter :=
        hmatches.2.2.2
      _ = (historyTile M input (time + 1) (position + 1)).nextCenter :=
        nextCenter (position + 1)
      _ = (historyTile M input (time + 1 + 1) position).prevRight := by
        simp [historyTile]⟩

theorem next_row_decoded
    {M : Machine} {input : List Nat}
    {plane : Nat × Nat → TileIn (tiles M input)}
    (valid : ValidQuarterTiling (tiles M input) plane)
    {time : Nat}
    (hrow : DecodedHistoryRow M input plane (time + 1))
    (hstate : (run M input (time + 1)).state ≠ M.halt)
    (hnext : (run M input (time + 1 + 1)).state ≠ M.halt) :
    DecodedHistoryRow M input plane (time + 1 + 1) := by
  rcases hrow with ⟨lower, decoded⟩
  choose upper hupper using fun position =>
    positive_row_decode valid (time + 1) position
  refine ⟨upper, ⟨fun position => (hupper position).1,
    fun position => (hupper position).2, ?_⟩⟩
  intro position
  have hvertical : WangTile.VMatches
      (toWangTile 0 0 normalRowTag normalRowTag (lower position))
      (toWangTile 0 0 normalRowTag normalRowTag (upper position)) := by
    simpa [decoded.encoded position, (hupper position).2] using
      valid.2 (position, time + 1)
  have cells := (vMatches_toWangTile_iff _ _ _ _ _ _ _ _ _ _).1 hvertical
  have nextCells := next_cells_eq_historyTile_of_decoded_row
    valid decoded hstate hnext position
  exact ⟨cells.2.1.symm.trans nextCells.1,
    cells.2.2.1.symm.trans nextCells.2.1,
    cells.2.2.2.symm.trans nextCells.2.2⟩

theorem decoded_row_of_nonhalting_prefix
    {M : Machine} {input : List Nat}
    {plane : Nat × Nat → TileIn (tiles M input)}
    (valid : ValidQuarterTiling (tiles M input) plane)
    (seeded : (plane (0, 0)).1 = seed M input) (time : Nat)
    (hprefix : ∀ step, 1 ≤ step → step ≤ time + 1 →
      (run M input step).state ≠ M.halt) :
    DecodedHistoryRow M input plane (time + 1) := by
  induction time with
  | zero => exact row_one_decoded valid seeded
  | succ time ih =>
      exact next_row_decoded valid
        (time := time)
        (ih fun step hstep hbound => hprefix step hstep (by omega))
        (hprefix (time + 1) (by omega) (by omega))
        (hprefix (time + 1 + 1) (by omega) (by omega))

/- At the first halting time, all preceding positive rows can be decoded.  If
halting occurs immediately, row one already contains a forbidden halt head.
Otherwise the tile at the next head position would have to realize a local
transition into `halt`, which the normal palette explicitly omits. -/

theorem false_of_run_one_halt
    {M : Machine} {input : List Nat}
    {plane : Nat × Nat → TileIn (tiles M input)}
    (valid : ValidQuarterTiling (tiles M input) plane)
    (seeded : (plane (0, 0)).1 = seed M input)
    (hhalt : (run M input 1).state = M.halt) : False := by
  let position := (run M input 1).head
  rcases row_one_decoded valid seeded with ⟨row, decoded⟩
  apply prevCenter_not_halt_of_mem_machineHistoryTiles
    (a := (run M input 1).tape (run M input 1).head) (decoded.mem position)
  rw [(decoded.prevCells position).2.1]
  change (run M input 1).cellAt position =
    MachineCell.head M.halt ((run M input 1).tape (run M input 1).head)
  dsimp only [position]
  rw [ID.cellAt_head, hhalt]

theorem false_of_next_halt_from_decoded_row
    {M : Machine} {input : List Nat}
    {plane : Nat × Nat → TileIn (tiles M input)}
    {time : Nat}
    (hrow : DecodedHistoryRow M input plane (time + 1))
    (hstate : (run M input (time + 1)).state ≠ M.halt)
    (hnext : (run M input (time + 1 + 1)).state = M.halt) : False := by
  let configuration := run M input (time + 1)
  let position :=
    (M.step configuration.state (configuration.tape configuration.head)).2.2.apply
      configuration.head
  rcases hrow with ⟨row, decoded⟩
  let tile := row position
  have tileMem := decoded.mem position
  have prevCells := decoded.prevCells position
  have hstate' : configuration.state ≠ M.halt := by
    simpa [configuration] using hstate
  have hnextState :
      (M.step configuration.state (configuration.tape configuration.head)).2.1 =
        M.halt := by
    rw [← Machine.nextID_state_of_ne_halt hstate']
    simpa [configuration, run_succ] using hnext
  have hlocal := localNextCell?_of_mem_machineHistoryTiles tileMem
  rw [prevCells.1, prevCells.2.1, prevCells.2.2] at hlocal
  have hnone := Machine.localNextCell?_at_next_halt_head
    (M := M) (c := configuration) hstate' hnextState
  have hnoneRun :
      localNextCell? M (historyTile M input (time + 1) position).prevLeft
          (historyTile M input (time + 1) position).prevCenter
          (historyTile M input (time + 1) position).prevRight = none := by
    simpa [historyTile, runCell, runCellLeft, configuration, position] using hnone
  rw [hnoneRun] at hlocal
  cases hlocal

theorem not_tilesQuarterWithSeed_of_halts
    {M : Machine} {input : List Nat} (halts : Halts M input) :
    ¬ TilesQuarterWithSeed (tiles M input) (seed M input) := by
  rcases exists_first_halting_time halts with ⟨step, hhalt, before⟩
  rintro ⟨plane, valid, seeded⟩
  cases step with
  | zero =>
      apply false_of_run_one_halt valid seeded
      have hinitial : (initialID M input).state = M.halt := by
        simpa [run_zero] using hhalt
      rw [show 1 = 0 + 1 by omega, run_succ, run_zero,
        Machine.nextID_of_halt M _ hinitial]
      exact hinitial
  | succ step =>
      cases step with
      | zero =>
          exact false_of_run_one_halt valid seeded (by simpa using hhalt)
      | succ time =>
          have hrow := decoded_row_of_nonhalting_prefix
            valid seeded time (fun k _positive bounded => before k (by omega))
          exact false_of_next_halt_from_decoded_row hrow
            (before (time + 1) (by omega)) (by simpa using hhalt)

theorem tilesQuarterWithSeed_iff_not_halts
    {M : Machine} {input : List Nat} (supported : Supported M input) :
    TilesQuarterWithSeed (tiles M input) (seed M input) ↔ ¬ Halts M input := by
  constructor
  · intro tiled halts
    exact not_tilesQuarterWithSeed_of_halts halts tiled
  · exact tilesQuarterWithSeed_of_not_halts supported

end MachineInputTiles
end LeanWang
