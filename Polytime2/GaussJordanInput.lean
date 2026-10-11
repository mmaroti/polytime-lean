/-
Copyright (c) 2026 Miklos Maroti <mmaroti@math.u-szeged.hu>
SPDX-License-Identifier: Apache-2.0

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Polytime2.GaussJordanMachine
import Polytime2.UnaryRead
import Polytime2.ScalarStreams

/-! # External tapes and dimension-header preparation for Gauss–Jordan

Only the input tape initially contains data: a complete unary row/column
header and the canonical binary matrix payload. Working and output tapes are
blank. Their number and alphabets are fixed independently of the dimensions.
-/

namespace Polytime2.GaussJordanInput

open MultiTape


variable {Scalar : Type} {rows columns width : ℕ}

abbrev TapeName := Sum Bool GaussJordanWorkspace.TapeName

abbrev Alphabet (Scalar : Type) : TapeName → Type
  | .inl _ => Binary.Symbol
  | .inr name => GaussJordanWorkspace.Alphabet Scalar name

instance (name : TapeName) : Inhabited (Alphabet Scalar name) :=
  match name with
  | .inl _ => inferInstanceAs (Inhabited Binary.Symbol)
  | .inr name => GaussJordanWorkspace.instInhabitedAlphabet name

instance [Fintype Scalar] (name : TapeName) : Fintype (Alphabet Scalar name) :=
  match name with
  | .inl _ => inferInstanceAs (Fintype Binary.Symbol)
  | .inr name => GaussJordanWorkspace.instFintypeAlphabet name

/-- External tape `false` is input; tape `true` receives the serialized output. -/
def frame (input output : Turing.Tape Binary.Symbol)
    (working : Tapes (GaussJordanWorkspace.Alphabet Scalar)) : Tapes (Alphabet Scalar)
  | .inl false => input
  | .inl true => output
  | .inr name => working name

def blank {Symbol : Type} [Inhabited Symbol] : Turing.Tape Symbol :=
  Turing.Tape.mk' (Turing.ListBlank.mk []) (Turing.ListBlank.mk [])

def optionalCounter (value : Option ℕ) : Turing.Tape Binary.Symbol :=
  match value with
  | none => blank
  | some count => MatrixAddress.counter 0 count

/-- During header parsing, only the two dimension tapes have been initialized. -/
def dimensions (rows columns : Option ℕ) : Tapes (GaussJordanWorkspace.Alphabet Scalar)
  | .inl (.inl (.inl .width)) => optionalCounter columns
  | .inr .rowCount => optionalCounter rows
  | .inl (.inl (.inl .row)) | .inl (.inl (.inl .column)) | .inl (.inl (.inl .output)) => blank
  | .inl (.inl (.inr _)) => blank
  | .inl (.inr (.inl _)) => blank
  | .inl (.inr (.inr _)) => blank
  | .inr .pivotRow | .inr .pivotColumn => blank

def header (rows columns : ℕ) : List Binary.Symbol :=
  List.replicate rows 2 ++ 3 :: (List.replicate columns 2 ++ [3])

def initial (rows columns : ℕ) (payload : List Binary.Symbol) : Tapes (Alphabet Scalar) :=
  frame (Binary.tape [3] (header rows columns ++ payload ++ [0]) ()) blank (dimensions none none)

/-- The read routine's second role is one of the two dimension counters. -/
def sizeWiring (readRows : Bool) : Bool ↪ TapeName where
  toFun
    | false => .inl false
    | true => if readRows then .inr (.inr .rowCount) else .inr (.inl (.inl (.inl .width)))
  inj' := by intro first second equal; cases readRows <;> cases first <;> cases second <;> simp_all

def sizeEquivalences (Scalar : Type) (readRows name : Bool) :
    Binary.Symbol ≃ Alphabet Scalar (sizeWiring readRows name) := by
  cases readRows <;> cases name <;> exact Equiv.refl _

theorem sizeBlanks (readRows name : Bool) : sizeEquivalences Scalar readRows name default = default := by
  cases readRows <;> cases name <;> rfl

noncomputable def readSize (readRows : Bool) : Machine (Alphabet Scalar) UnaryRead.State :=
  wire (sizeWiring readRows) (relabel (sizeEquivalences Scalar readRows) UnaryRead.machine)

private theorem readSize_steps (readRows : Bool) (count : ℕ) (other : Option ℕ)
    (left right : List Binary.Symbol) :
    Steps (readSize (Scalar := Scalar) readRows) (2 * count + 6)
      (UnaryRead.entry, frame (Binary.tape left (List.replicate count 2 ++ 3 :: right) ()) blank
        (dimensions (if readRows then none else other) (if readRows then other else none)))
      (UnaryRead.exit, frame (Binary.tape (3 :: (List.replicate count 2 ++ left)) right ()) blank
        (dimensions (if readRows then some count else other) (if readRows then other else some count))) := by
  have trace := (UnaryRead.steps count left right).relabel (sizeEquivalences Scalar readRows) (sizeBlanks readRows)
  apply wire_steps_of_eq (sizeWiring readRows) _ trace
  · intro name
    cases readRows <;> cases name
    all_goals change (_ : Turing.Tape Binary.Symbol) =
      Turing.Tape.map (⟨id, rfl⟩ : Turing.PointedMap Binary.Symbol Binary.Symbol) _
    all_goals rw [mapTape_identity]; rfl
  · intro name
    cases readRows <;> cases name
    all_goals change (_ : Turing.Tape Binary.Symbol) =
      Turing.Tape.map (⟨id, rfl⟩ : Turing.PointedMap Binary.Symbol Binary.Symbol) _
    all_goals rw [mapTape_identity]; rfl
  · intro name outside
    cases readRows <;> fin_cases name <;>
      first | rfl | exact False.elim (outside ⟨false, rfl⟩) | exact False.elim (outside ⟨true, rfl⟩)

theorem readSize_halt (readRows : Bool) (symbols : Symbols (Alphabet Scalar)) :
    readSize readRows UnaryRead.exit symbols = none := by
  simp [readSize, wire, relabel, UnaryRead.halt]

abbrev HeaderState := Sum UnaryRead.State UnaryRead.State

noncomputable def readHeader : Machine (Alphabet Scalar) HeaderState :=
  sequence (readSize true) (readSize false) UnaryRead.entry

def headerEntry : HeaderState := .inl UnaryRead.entry
def headerExit : HeaderState := .inr UnaryRead.exit

def consumedHeader (rows columns : ℕ) : List Binary.Symbol :=
  3 :: (List.replicate columns 2 ++ 3 :: (List.replicate rows 2 ++ [3]))

/-- Parse both dimensions into initially blank counter tapes, with all work charged. -/
theorem readHeader_steps (rows columns : ℕ) (payload : List Binary.Symbol) :
    Steps (readHeader (Scalar := Scalar)) (2 * rows + 2 * columns + 13)
      (headerEntry, initial rows columns payload)
      (headerExit, frame (Binary.tape (consumedHeader rows columns) (payload ++ [0]) ()) blank
        (dimensions (some rows) (some columns))) := by
  have first := readSize_steps (Scalar := Scalar) true rows none [3]
    (List.replicate columns 2 ++ 3 :: (payload ++ [0]))
  have second := readSize_steps (Scalar := Scalar) false columns (some rows)
    (3 :: (List.replicate rows 2 ++ [3])) (payload ++ [0])
  have complete := sequence_steps _ _ UnaryRead.entry first (readSize_halt true) second
  convert complete using 1 <;> first | rfl | omega |
    simp only [headerEntry, initial, header, ite_true, List.append_assoc, List.cons_append, List.nil_append]

theorem readHeader_halt (symbols : Symbols (Alphabet Scalar)) : readHeader headerExit symbols = none := by
  simp [readHeader, headerExit, MultiTape.sequence, readSize_halt]


/-- A ready workspace with an arbitrary dense scalar array and zeroed registers. -/
def working [Zero Scalar] (rows columns : ℕ) (values : List Scalar) : Tapes (GaussJordanWorkspace.Alphabet Scalar)
  | .inl (.inl (.inl name)) => MatrixAddress.ready 0 columns 0 0 name
  | .inl (.inl (.inr false)) => Turing.Tape.mk' (Turing.ListBlank.mk [some none])
      (Turing.ListBlank.mk (TableTraversal.word values ++ [none]))
  | .inl (.inl (.inr true)) => MatrixRows.scalarTape 0
  | .inl (.inr (.inl false)) => MatrixAddress.counter 0 0
  | .inl (.inr (.inl true)) => MatrixRows.flagTape false
  | .inl (.inr (.inr _)) => MatrixRows.scalarTape 0
  | .inr .pivotRow | .inr .pivotColumn => MatrixAddress.counter 0 0
  | .inr .rowCount => MatrixAddress.counter 0 rows

theorem working_matrix [Zero Scalar] (matrix : Matrix (Fin rows) (Fin columns) Scalar) :
    working rows columns (MatrixAccess.entries matrix) = GaussJordanWorkspace.frame matrix 0 0 0 0 0 0 0 false := by
  funext name
  fin_cases name <;> rfl

def markWorking (symbols : Symbols (GaussJordanWorkspace.Alphabet Scalar)) :
    Actions (GaussJordanWorkspace.Alphabet Scalar)
  | .inl (.inl (.inl .width)) => (symbols (.inl (.inl (.inl .width))), none)
  | .inl (.inl (.inl .row)) | .inl (.inl (.inl .column)) | .inl (.inl (.inl .output)) => ((3 : Binary.Symbol), some .right)
  | .inl (.inl (.inr _)) => (some none, some .right)
  | .inl (.inr (.inl _)) => ((3 : Binary.Symbol), some .right)
  | .inl (.inr (.inr _)) => (some none, some .right)
  | .inr .pivotRow | .inr .pivotColumn => ((3 : Binary.Symbol), some .right)
  | .inr .rowCount => (symbols (.inr .rowCount), none)

def fillWorking [Zero Scalar] (symbols : Symbols (GaussJordanWorkspace.Alphabet Scalar)) :
    Actions (GaussJordanWorkspace.Alphabet Scalar)
  | .inl (.inl (.inr true)) => (some (some 0), none)
  | .inl (.inr (.inr _)) => (some (some 0), none)
  | .inl (.inr (.inl true)) => (Binary.data false, none)
  | name => (symbols name, none)

def markAction (symbols : Symbols (Alphabet Scalar)) : Actions (Alphabet Scalar)
  | .inl false => (symbols (.inl false), none)
  | .inl true => ((3 : Binary.Symbol), some .right)
  | .inr name => markWorking (fun name => symbols (.inr name)) name

def fillAction [Zero Scalar] (symbols : Symbols (Alphabet Scalar)) : Actions (Alphabet Scalar)
  | .inl name => (symbols (.inl name), none)
  | .inr name => fillWorking (fun name => symbols (.inr name)) name

/-- Only fixed boundary symbols and zero registers are written during initialization. -/
def format [Zero Scalar] : Machine (Alphabet Scalar) (Fin 3) := fun state symbols =>
  if state = 0 then some (1, markAction symbols)
  else if state = 1 then some (2, fillAction symbols)
  else none

theorem format_steps [Zero Scalar] (rows columns : ℕ) (input : Turing.Tape Binary.Symbol) :
    Steps (format (Scalar := Scalar)) 2
      (0, frame input blank (dimensions (some rows) (some columns)))
      (2, frame input (Binary.tape [3] [0] ()) (working rows columns [])) := by
  let initial : Tapes (Alphabet Scalar) := frame input blank (dimensions (some rows) (some columns))
  let middle := act (markAction (MultiTape.read initial)) initial
  have first : step format (0, initial) = some (1, middle) := by simp [step, format, middle]
  have second : step format (1, middle) =
      some (2, frame input (Binary.tape [3] [0] ()) (working rows columns [])) := by
    simp only [step, format, show (1 : Fin 3) ≠ 0 by decide, ↓reduceIte, Option.map_some]
    congr 2
    funext name
    fin_cases name <;>
      simp [middle, initial, act, MultiTape.read, frame, markAction, fillAction, markWorking, fillWorking,
        dimensions, optionalCounter, blank, working, MatrixAddress.ready, MatrixAddress.counter,
        MatrixRows.scalarTape, MatrixRows.flagTape, TableTraversal.word, Binary.tape, Binary.data,
        Turing.Tape.write_mk', Turing.Tape.move_right_mk', Turing.ListBlank.cons_mk]
    all_goals rfl
  exact Steps.next first (Steps.next second (.zero _))

theorem format_halt [Zero Scalar] (symbols : Symbols (Alphabet Scalar)) : format 2 symbols = none := by
  simp [format]


/-- The matrix array tape is shared by preparation, elimination, and serialization. -/
def arrayName : GaussJordanWorkspace.TapeName := .inl (.inl (.inr false))

def streamWiring (output : Bool) : Bool ↪ TapeName where
  toFun
    | false => .inl output
    | true => .inr arrayName
  inj' := by intro first second equal; cases first <;> cases second <;> simp_all

def streamEquivalences (Scalar : Type) (output name : Bool) :
    ScalarCodec.Alphabet Scalar name ≃ Alphabet Scalar (streamWiring output name) := by
  cases name <;> exact Equiv.refl _

theorem streamBlanks (output name : Bool) : streamEquivalences Scalar output name default = default := by
  cases name <;> rfl

noncomputable def prepareArray [DecidableEq Scalar] (decode : BitVec width → Scalar) :
    Machine (Alphabet Scalar) (ScalarStreams.PrepareState width) :=
  wire (streamWiring false) (relabel (streamEquivalences Scalar false) (ScalarStreams.prepareMachine decode))

theorem prepareArray_steps [Zero Scalar] [DecidableEq Scalar]
    (encode : Scalar → BitVec width) (decode : BitVec width → Scalar)
    (roundtrip : ∀ value, decode (encode value) = value) (positive : 0 < width)
    (values : List Scalar) (rows columns : ℕ) (left : List Binary.Symbol) (output : Turing.Tape Binary.Symbol) :
    Steps (prepareArray decode) (values.length * (width + 4) + 4)
      (ScalarStreams.prepareEntry width,
        frame (Binary.tape left (ScalarStreams.word encode values ++ [0]) ()) output (working rows columns []))
      (ScalarStreams.prepareExit width,
        frame (Binary.tape ((ScalarStreams.word encode values).reverse ++ left) [0] ()) output (working rows columns values)) := by
  have trace := (ScalarStreams.prepare_steps encode decode roundtrip positive values left []).relabel
    (streamEquivalences Scalar false) (streamBlanks false)
  apply wire_steps_of_eq (streamWiring false) _ trace
  · intro name
    cases name
    all_goals first
      | change (_ : Turing.Tape Binary.Symbol) =
          Turing.Tape.map (⟨id, rfl⟩ : Turing.PointedMap Binary.Symbol Binary.Symbol) _
        rw [mapTape_identity]; rfl
      | change (_ : Turing.Tape (TableTraversal.Symbol Scalar)) =
          Turing.Tape.map (⟨id, rfl⟩ : Turing.PointedMap (TableTraversal.Symbol Scalar) (TableTraversal.Symbol Scalar)) _
        rw [mapTape_identity]; rfl
  · intro name
    cases name
    all_goals first
      | change (_ : Turing.Tape Binary.Symbol) =
          Turing.Tape.map (⟨id, rfl⟩ : Turing.PointedMap Binary.Symbol Binary.Symbol) _
        rw [mapTape_identity]; rfl
      | change (_ : Turing.Tape (TableTraversal.Symbol Scalar)) =
          Turing.Tape.map (⟨id, rfl⟩ : Turing.PointedMap (TableTraversal.Symbol Scalar) (TableTraversal.Symbol Scalar)) _
        rw [mapTape_identity]; rfl
  · intro name outside
    fin_cases name <;>
      first | rfl | exact False.elim (outside ⟨false, rfl⟩) | exact False.elim (outside ⟨true, rfl⟩)

theorem prepareArray_halt [DecidableEq Scalar] (decode : BitVec width → Scalar) (symbols : Symbols (Alphabet Scalar)) :
    prepareArray decode (ScalarStreams.prepareExit width) symbols = none := by
  simp [prepareArray, wire, relabel, ScalarStreams.prepare_halt]

abbrev PrepareState (width : ℕ) := Sum (Sum HeaderState (Fin 3)) (ScalarStreams.PrepareState width)

noncomputable def prepare [Zero Scalar] [DecidableEq Scalar] (decode : BitVec width → Scalar) :
    Machine (Alphabet Scalar) (PrepareState width) :=
  sequence (sequence readHeader format 0) (prepareArray decode) (ScalarStreams.prepareEntry width)

def prepareEntry (width : ℕ) : PrepareState width := .inl (.inl headerEntry)
def prepareExit (width : ℕ) : PrepareState width := .inr (ScalarStreams.prepareExit width)

/-- The complete external preparation starts with only a size header and matrix
bits. No working markers, dimension registers, or reserved matrix cells are supplied. -/
theorem prepare_steps [Zero Scalar] [DecidableEq Scalar]
    (encode : Scalar → BitVec width) (decode : BitVec width → Scalar)
    (roundtrip : ∀ value, decode (encode value) = value) (positive : 0 < width)
    (matrix : Matrix (Fin rows) (Fin columns) Scalar) :
    Steps (prepare decode) (2 * rows + 2 * columns + rows * columns * (width + 4) + 21)
      (prepareEntry width, initial rows columns (ScalarStreams.word encode (MatrixAccess.entries matrix)))
      (prepareExit width, frame
        (Binary.tape ((ScalarStreams.word encode (MatrixAccess.entries matrix)).reverse ++ consumedHeader rows columns) [0] ())
        (Binary.tape [3] [0] ()) (GaussJordanWorkspace.frame matrix 0 0 0 0 0 0 0 false)) := by
  have parsed := readHeader_steps (Scalar := Scalar) rows columns (ScalarStreams.word encode (MatrixAccess.entries matrix))
  have formatted := format_steps (Scalar := Scalar) rows columns
    (Binary.tape (consumedHeader rows columns) (ScalarStreams.word encode (MatrixAccess.entries matrix) ++ [0]) ())
  have decoded := prepareArray_steps encode decode roundtrip positive (MatrixAccess.entries matrix) rows columns
    (consumedHeader rows columns) (Binary.tape [3] [0] ())
  rw [working_matrix] at decoded
  have first := sequence_steps _ _ 0 parsed readHeader_halt formatted
  have complete := sequence_steps _ _ (ScalarStreams.prepareEntry width) first
    (by intro symbols; simp [MultiTape.sequence, format_halt]) decoded
  simp only [MatrixAccess.entries_length] at complete
  convert complete using 1 <;> first | rfl | omega

theorem prepare_halt [Zero Scalar] [DecidableEq Scalar]
    (decode : BitVec width → Scalar) (symbols : Symbols (Alphabet Scalar)) :
    prepare decode (prepareExit width) symbols = none := by
  simp [prepare, prepareExit, MultiTape.sequence, prepareArray_halt]

end Polytime2.GaussJordanInput
