/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedProgram.ProgramData

/-!
# Data-parameterized initialization for a fixed folded TM0 program

The original folded compiler closes over the input `[0]` and varies its source
program.  The universal-machine reduction needs the dual interface: simulation
rows are fixed once, while a finite source input word determines only the
initialization prelude.
-/

namespace LeanWang

namespace TM0FoldedCompiler

/-- Initialization states needed to write and rewind a particular input word. -/
def foldedInitStateListFor (input : List SourceSymbol) : List Nat :=
  [initWriteOriginState, initReturnState 0] ++
    (List.range input.length).flatMap fun i =>
      [initMoveRightState i, initWriteRightState i, initReturnState i]

/-- All states for fixed simulation control and a varying input prelude. -/
def foldedStateListForInput (stateCount : Nat) (input : List SourceSymbol) : List Nat :=
  foldedInitStateListFor input ++
    foldedSimStateListOfCodes (List.range stateCount)

def inputSymbolFor (input : List SourceSymbol) (i : Nat) : SourceSymbol :=
  input.getI i

def nextAfterOriginFor (input : List SourceSymbol) : Nat :=
  if input.length ≤ 1 then initReturnState 0 else initMoveRightState 0

def initWriteOriginRowFor (input : List SourceSymbol) : PostTransition :=
  mkRow initWriteOriginState foldedBlank (nextAfterOriginFor input)
    (PostStmt.write (foldedOriginSymbol (inputSymbolFor input 0)))

def initMoveRightRowsFor (input : List SourceSymbol) : List PostTransition :=
  (List.range (input.length - 1)).flatMap fun i =>
    foldedSymbolList.map fun read => initMoveRightRow i read

def nextAfterWriteRightFor (input : List SourceSymbol) (i : Nat) : Nat :=
  if i + 2 < input.length then initMoveRightState (i + 1)
  else initReturnState (i + 1)

def initWriteRightRowFor (input : List SourceSymbol) (i : Nat) : PostTransition :=
  mkRow (initWriteRightState i) foldedBlank (nextAfterWriteRightFor input i)
    (PostStmt.write
      (foldedSymbolCode false default (inputSymbolFor input (i + 1))))

def initWriteRightRowsFor (input : List SourceSymbol) : List PostTransition :=
  (List.range (input.length - 1)).map fun i => initWriteRightRowFor input i

def initReturnIndexListFor (input : List SourceSymbol) : List Nat :=
  0 :: List.range input.length

def initReturnRowsFor (input : List SourceSymbol) : List PostTransition :=
  (initReturnIndexListFor input).flatMap fun i =>
    foldedSymbolList.map fun read => initReturnRow default i read

/-- Complete finite prelude which writes `input` and returns to its origin. -/
def initRowsForInput (input : List SourceSymbol) : List PostTransition :=
  initWriteOriginRowFor input ::
    (initMoveRightRowsFor input ++
      (initWriteRightRowsFor input ++ initReturnRowsFor input))

/--
Folded program data with fixed numeric simulation rows and a varying source
input word.
-/
def positionProgramDataForInput
    (stateCount : Nat) (steps : List SimStepData) (input : List SourceSymbol) :
    FiniteTM0Program where
  symbols := foldedSymbolList
  states := foldedStateListForInput stateCount input
  blank := foldedBlank
  start := foldedStartState
  table := initRowsForInput input ++ simRowsOfStepData steps

/-- The position-coded folded simulation of `tc` on an arbitrary finite input. -/
def positionProgramDataOnInput
    (tc : Turing.ToPartrec.Code) (input : List SourceSymbol) : FiniteTM0Program :=
  positionProgramDataForInput
    (TM0Route.partrecStartedTM0StateCount tc)
    (simStepDataByLabelIndexWithPositionCode tc) input

@[simp]
theorem positionProgramDataOnInput_symbols
    (tc : Turing.ToPartrec.Code) (input : List SourceSymbol) :
    (positionProgramDataOnInput tc input).symbols = foldedSymbolList := rfl

@[simp]
theorem positionProgramDataOnInput_states
    (tc : Turing.ToPartrec.Code) (input : List SourceSymbol) :
    (positionProgramDataOnInput tc input).states =
      foldedStateListForInput (TM0Route.partrecStartedTM0StateCount tc) input := rfl

@[simp]
theorem positionProgramDataOnInput_blank
    (tc : Turing.ToPartrec.Code) (input : List SourceSymbol) :
    (positionProgramDataOnInput tc input).blank = foldedBlank := rfl

@[simp]
theorem positionProgramDataOnInput_start
    (tc : Turing.ToPartrec.Code) (input : List SourceSymbol) :
    (positionProgramDataOnInput tc input).start = foldedStartState := rfl

/-- The parameterized definitions conservatively extend the old input-`0` data. -/
theorem initRowsForInput_eq_initRowsData :
    initRowsForInput TM0Route.partrecStartedTM0Input = initRowsData := by
  rfl

theorem foldedInitStateListFor_eq_foldedInitStateList :
    foldedInitStateListFor TM0Route.partrecStartedTM0Input = foldedInitStateList := by
  rfl

/-- On the original input, the parameterized constructor is the proved program. -/
theorem positionProgramDataForInput_eq_positionProgramData
    (tc : Turing.ToPartrec.Code) :
    positionProgramDataOnInput tc TM0Route.partrecStartedTM0Input =
      positionProgramData tc := by
  rfl

end TM0FoldedCompiler

end LeanWang
