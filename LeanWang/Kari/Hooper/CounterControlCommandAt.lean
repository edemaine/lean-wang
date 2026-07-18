/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlPlan
import LeanWang.Kari.Hooper.CounterControlWellFormed

/-!
# Linking raw counter commands to compiled controller blocks

This module packages the global enumeration arguments from
`CounterControlWellFormed` behind a command-oriented interface.  A semantic
proof can name any `RawCommand`, prove that it belongs to `rawCommands`, and
then obtain both its compiled command and the `CommandAt` witness for its
uniform bounded-search block.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlCommandAt

open BoundedMarkerProgram CounterControlPlan
open CounterControlWellFormed

noncomputable section

/-! ## The unique physical tag of a raw command -/

/-- The return tag assigned to a generated raw command.  It is the position
of the command's unique symbolic address in the global address enumeration. -/
def rawTag (raw : RawCommand) (hraw : raw ∈ rawCommands) :
    Fin rawCommands.length :=
  ⟨searchIndex raw.address, command_searchIndex_lt_numTags hraw⟩

@[simp]
theorem rawTag_val (raw : RawCommand) (hraw : raw ∈ rawCommands) :
    (rawTag raw hraw).val = searchIndex raw.address := rfl

/-- Any enumeration index containing `raw` is its address-selected tag. -/
theorem rawTag_eq_of_get_eq (raw : RawCommand)
    (hraw : raw ∈ rawCommands) (tag : Fin rawCommands.length)
    (htag : rawCommands.get tag = raw) :
    rawTag raw hraw = tag := by
  apply Fin.ext
  change searchIndex raw.address = tag.val
  simpa only [htag] using searchIndex_get tag

/-- Looking up the address-selected tag recovers the exact raw command, not
merely a command with the same address. -/
@[simp]
theorem rawCommands_get_rawTag (raw : RawCommand)
    (hraw : raw ∈ rawCommands) :
    rawCommands.get (rawTag raw hraw) = raw := by
  rcases List.mem_iff_get.mp hraw with ⟨tag, htag⟩
  rw [rawTag_eq_of_get_eq raw hraw tag htag, htag]

/-- The tag is independent of the particular proof of list membership. -/
theorem rawTag_proof_irrel (raw : RawCommand)
    (hfirst hsecond : raw ∈ rawCommands) :
    rawTag raw hfirst = rawTag raw hsecond := by
  rfl

/-! ## Command-oriented compilation -/

/-- Constructor-by-constructor compilation of a raw command at an explicitly
chosen return tag.  This is the specification hidden by the enumeration-based
`compileCommand`. -/
def compileRawAtTag (base : Nat) (c : Nat.Partrec.Code)
    (tag : Fin rawCommands.length) : RawCommand → Command rawCommands.length
  | .boundaryNavigation address expected direction success action =>
      .boundaryNavigation expected (orient address.growth direction)
        (resolve base c success) tag
        (compileNavigationAction address.growth action)
  | .tagNavigation address direction success =>
      .tagNavigation (orient address.growth direction)
        (resolve base c success) tag
  | .markerShift address expected search shift success departure collision =>
      .markerShift
        ⟨expected, orient address.growth search,
          orient address.growth shift⟩
        (resolve base c success) tag
        (departure.map (orient address.growth))
        (collision.map (resolve base c))

/-- Compile a raw command using the unique return tag assigned to its
symbolic address. -/
def compileRawCommand (base : Nat) (c : Nat.Partrec.Code)
    (raw : RawCommand) (hraw : raw ∈ rawCommands) :
    Command rawCommands.length :=
  compileCommand base c (rawTag raw hraw)

/-- Explicit specification of command-oriented compilation. -/
theorem compileRawCommand_spec (base : Nat) (c : Nat.Partrec.Code)
    (raw : RawCommand) (hraw : raw ∈ rawCommands) :
    compileRawCommand base c raw hraw =
      compileRawAtTag base c (rawTag raw hraw) raw := by
  unfold compileRawCommand compileCommand compileRawAtTag
  rw [rawCommands_get_rawTag]
  cases raw <;> rfl

@[simp]
theorem compileRawCommand_returnTag (base : Nat) (c : Nat.Partrec.Code)
    (raw : RawCommand) (hraw : raw ∈ rawCommands) :
    (compileRawCommand base c raw hraw).returnTag = rawTag raw hraw := by
  simp only [compileRawCommand, compileCommand_returnTag]

@[simp]
theorem compileRawCommand_searchDirection (base : Nat)
    (c : Nat.Partrec.Code) (raw : RawCommand)
    (hraw : raw ∈ rawCommands) :
    (compileRawCommand base c raw hraw).searchDirection =
      raw.physicalSearchDirection := by
  simp only [compileRawCommand, compileCommand_searchDirection,
    rawCommands_get_rawTag]

/-! ## The compiled block selected by a raw command -/

/-- A generated raw command occupies the controller block named by its
symbolic search address. -/
theorem compileRawCommand_commandAt (base : Nat) (c : Nat.Partrec.Code)
    (raw : RawCommand) (hraw : raw ∈ rawCommands) :
    CommandAt (CanonicalInitializer.radius c) base
      (searchState base c raw.address)
      (compileRawCommand base c raw hraw) (commands base c) := by
  simpa only [compileRawCommand, rawCommands_get_rawTag] using
    compileCommand_commandAt base c (rawTag raw hraw)

/-- Namespace-form alias for downstream bounded-command semantics. -/
theorem CommandAt.compileRawCommand (base : Nat) (c : Nat.Partrec.Code)
    (raw : RawCommand) (hraw : raw ∈ rawCommands) :
    CommandAt (CanonicalInitializer.radius c) base
      (searchState base c raw.address)
      (compileRawCommand base c raw hraw) (commands base c) :=
  compileRawCommand_commandAt base c raw hraw

end

end CounterControlCommandAt
end Hooper
end Kari
end LeanWang
