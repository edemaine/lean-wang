/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlCommandAt

/-!
# Inverting compiled command locations

`CommandAt` is the inductive linker relation used by the bounded marker
controller.  Its forward constructors are convenient for selecting a known
command.  Arbitrary-entry arguments need the converse: a command known only
through `CommandAt` has an actual list index, and in the counter controller
that index selects an actual generated raw command.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlCommandAtConverse

open BoundedMarkerProgram CounterControlPlan CounterControlCommandAt
open CounterControlWellFormed

noncomputable section

/-- Every linked command location is the uniform block offset of an actual
index in the command list. -/
theorem exists_index_of_commandAt {numTags radius base offset : Nat}
    {command : Command numTags} {commands : List (Command numTags)}
    (hat : CommandAt radius base offset command commands) :
    ∃ index : Fin commands.length,
      commands.get index = command ∧
        offset = commandOffset base radius index.val := by
  induction hat with
  | head base command commands =>
      refine ⟨⟨0, by simp⟩, ?_, ?_⟩
      · rfl
      · simp [commandOffset]
  | tail base offset first command commands hat ih =>
      rcases ih with ⟨index, hcommand, hoffset⟩
      let next : Fin (first :: commands).length :=
        ⟨index.val + 1, by
          have hindex := index.isLt
          simp only [List.length_cons]
          omega⟩
      refine ⟨next, ?_, ?_⟩
      · simpa [next] using hcommand
      · rw [hoffset]
        simp [next, commandOffset, Nat.add_mul, Nat.add_assoc,
          Nat.add_comm]

/-- Every command linked into the compiled counter controller is the
compilation of an actual generated raw command, and its block offset is that
raw command's symbolic search state. -/
theorem exists_raw_of_commandAt
    (base : Nat) (c : Nat.Partrec.Code) {offset : Nat}
    {command : Command numTags}
    (hat : CommandAt (CanonicalInitializer.radius c) base offset command
      (commands base c)) :
    ∃ raw, ∃ hraw : raw ∈ rawCommands,
      command = compileRawCommand base c raw hraw ∧
        offset = searchState base c raw.address := by
  rcases exists_index_of_commandAt hat with
    ⟨index, hcommand, hoffset⟩
  let tag : Fin rawCommands.length :=
    ⟨index.val, by
      simpa only [commands_length, numTags] using index.isLt⟩
  let raw := rawCommands.get tag
  have hraw : raw ∈ rawCommands := by
    exact List.get_mem rawCommands tag
  refine ⟨raw, hraw, ?_, ?_⟩
  · have hcompiled : (commands base c).get index =
        compileCommand base c tag := by
      have hget := commands_get_eq_compileCommand base c tag
      simpa [tag] using hget
    have htag : rawTag raw hraw = tag :=
      rawTag_eq_of_get_eq raw hraw tag rfl
    rw [← hcommand, hcompiled]
    simp only [compileRawCommand]
    rw [htag]
  · rw [hoffset]
    have hstate := searchState_get base c tag
    simpa [tag, raw] using hstate.symm

end

end CounterControlCommandAtConverse
end Hooper
end Kari
end LeanWang
