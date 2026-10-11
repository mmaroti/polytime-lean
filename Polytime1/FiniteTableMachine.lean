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

import Polytime1.TupleMachine

/-! # Tape realization of fixed finite operation tables

Input and output widths, and the entire table, are specialization constants.
The controller reads a canonical bit tuple, returns a table value before the
unchanged input and suffix, and uses the existing universal tape alphabet.
-/

namespace Polytime1.FiniteTableMachine

open TupleMachine (Symbol data word)
variable {inputWidth outputWidth : ℕ}

/-- All stored bits are finite controller data because the widths are fixed. -/
inductive State (inputWidth outputWidth : ℕ)
  | read (position : Fin (inputWidth + 1)) (bits : Fin inputWidth → Bool)
  | rewind (remaining : Fin (inputWidth + 1)) (bits : Fin outputWidth → Bool)
  | emit (remaining : Fin (outputWidth + 1)) (bits : Fin outputWidth → Bool)
  | write (position : Fin outputWidth) (bits : Fin outputWidth → Bool)
  | halt
  deriving Fintype

instance : Inhabited (State inputWidth outputWidth) := ⟨.read 0 (fun _ => false)⟩

def machine (table : (Fin inputWidth → Bool) → (Fin outputWidth → Bool)) :
    Turing.TM0.Machine Symbol (State inputWidth outputWidth) := fun state symbol =>
  match state with
  | .read position bits =>
    if valid : position.val < inputWidth then
      some (.read ⟨position.val + 1, by omega⟩
        (BoolTuple.update bits ⟨position.val, valid⟩ (symbol = data true)), .move .right)
    else some (.rewind (Fin.last inputWidth) (table bits), .write symbol)
  | .rewind remaining bits =>
    if positive : remaining.val > 0 then
      some (.rewind ⟨remaining.val - 1, by omega⟩ bits, .move .left)
    else some (.emit (Fin.last outputWidth) bits, .write symbol)
  | .emit remaining bits =>
    if positive : remaining.val > 0 then
      some (.write ⟨remaining.val - 1, by omega⟩ bits, .move .left)
    else some (.halt, .write symbol)
  | .write position bits => some (.emit position.castSucc bits, .write (data (bits position)))
  | .halt => none

private def readPrefix (bits : Fin inputWidth → Bool) (count : ℕ) : Fin inputWidth → Bool :=
  fun position => if position.val < count then bits position else false

private theorem prefix_next (bits : Fin inputWidth → Bool) (position : Fin inputWidth) :
    BoolTuple.update (readPrefix bits position.val) position (bits position) =
      readPrefix bits (position.val + 1) := by
  funext other
  by_cases same : other = position
  · subst other; simp [BoolTuple.update, readPrefix]
  · have different : other.val ≠ position.val := Fin.ext_iff.not.mp same
    simp only [BoolTuple.update, ite_eq_right (show ¬other = position from same), readPrefix]
    by_cases earlier : other.val < position.val
    · simp [earlier, show other.val < position.val + 1 by omega]
    · simp [earlier, show ¬other.val < position.val + 1 by omega]

/-- Read the remaining fixed number of bits into finite controller states. -/
private theorem read_loop (table : (Fin inputWidth → Bool) → (Fin outputWidth → Bool))
    (bits : Fin inputWidth → Bool) (position : Fin (inputWidth + 1))
    (left tail : List Symbol) :
    Tape.Steps (machine table) (inputWidth - position.val)
      (Tape.configuration (.read position (readPrefix bits position.val)) left
        (word ((List.ofFn bits).drop position.val) ++ tail))
      (Tape.configuration (.read (Fin.last inputWidth) bits)
        ((word ((List.ofFn bits).drop position.val)).reverse ++ left) tail) := by
  generalize equality : inputWidth - position.val = remaining
  induction remaining generalizing position left with
  | zero =>
    have atEnd : position = Fin.last inputWidth := Fin.ext (by change position.val = inputWidth; omega)
    subst position
    have full : readPrefix bits inputWidth = bits := by
      funext index; simp [readPrefix, index.isLt]
    have empty : (List.ofFn bits).drop inputWidth = [] := by
      apply List.drop_eq_nil_of_le; simp
    simpa only [Fin.val_last, full, empty, word, List.map_nil, List.nil_append, List.reverse_nil] using
      Tape.Steps.zero (machine := machine table)
      (Tape.configuration (.read (Fin.last inputWidth) bits) left tail)
  | succ remaining hypothesis =>
    have valid : position.val < inputWidth := by omega
    let index : Fin inputWidth := ⟨position.val, valid⟩
    let next : Fin (inputWidth + 1) := ⟨position.val + 1, by omega⟩
    have split : (List.ofFn bits).drop position.val = bits index :: (List.ofFn bits).drop next.val := by
      have result := List.drop_eq_getElem_cons (l := List.ofFn bits) (i := position.val)
        (by simpa using valid)
      rw [List.getElem_ofFn] at result
      exact result
    have move := Tape.move_right (machine := machine table)
      (state := .read position (readPrefix bits position.val))
      (nextState := .read next (readPrefix bits next.val)) left
      (word ((List.ofFn bits).drop next.val) ++ tail) (data (bits index)) (by
        simp [machine, valid, data, next, index]
        exact prefix_next bits ⟨position.val, valid⟩)
    have rest := hypothesis next (data (bits index) :: left) (by dsimp [next]; omega)
    simpa [split, word, List.reverse_cons, List.append_assoc, next] using Tape.Steps.next move rest

private theorem rewind_loop (table : (Fin inputWidth → Bool) → (Fin outputWidth → Bool))
    (bits : Fin outputWidth → Bool) (symbols left right : List Symbol)
    (remaining : Fin (inputWidth + 1)) (length : remaining.val = symbols.length) :
    Tape.Steps (machine table) symbols.length
      (Tape.configuration (.rewind remaining bits) (symbols ++ left) right)
      (Tape.configuration (.rewind 0 bits) left (symbols.reverse ++ right)) := by
  induction symbols generalizing remaining right with
  | nil =>
    have zero : remaining = 0 := Fin.ext length
    subst remaining
    exact .zero _
  | cons symbol symbols hypothesis =>
    let next : Fin (inputWidth + 1) := ⟨remaining.val - 1, by omega⟩
    have move := Tape.move_left_list (machine := machine table)
      (state := .rewind remaining bits) (nextState := .rewind next bits)
      (symbols ++ left) right symbol (by intro current; simp [machine, next, show remaining.val > 0 by simp at length; omega])
    have rest := hypothesis (symbol :: right) next (by simp at length; simp [next]; omega)
    simpa [List.reverse_cons, List.append_assoc] using Tape.Steps.next move rest

/-- Emit into an assigned output window, preserving both surrounding contexts.
The window may contain results from an earlier call. -/
theorem emit_loop (table : (Fin inputWidth → Bool) → (Fin outputWidth → Bool))
    (bits : Fin outputWidth → Bool) (reserved left right : List Symbol)
    (remaining : Fin (outputWidth + 1)) (length : remaining.val = reserved.length) :
    Tape.Steps (machine table) (2 * remaining.val + 1)
      (Tape.configuration (.emit remaining bits) (reserved ++ left) right)
      (Tape.configuration .halt left (word ((List.ofFn bits).take remaining.val) ++ right)) := by
  induction reserved generalizing remaining right with
  | nil =>
    have zero : remaining = 0 := Fin.ext length
    subst remaining
    have stay := Tape.stay (machine := machine table) (state := .emit 0 bits) (nextState := .halt)
      left right (by intro symbol; simp [machine])
    simpa [word] using Tape.Steps.next stay (.zero _)
  | cons old reserved hypothesis =>
    let position : Fin outputWidth := ⟨remaining.val - 1, by simp at length; omega⟩
    have index : position.val = reserved.length := by simp at length; dsimp [position]; omega
    have positive : remaining.val > 0 := by simp at length; omega
    have previous : remaining.val = position.val + 1 := by dsimp [position]; omega
    have move := Tape.move_left_list (machine := machine table) (state := .emit remaining bits)
      (nextState := .write position bits) (reserved ++ left) right old
      (by intro symbol; simp [machine, positive, position])
    have write := Tape.write (machine := machine table) (state := .write position bits)
      (nextState := .emit position.castSucc bits) (reserved ++ left) right old (data (bits position)) (by rfl)
    have rest := hypothesis (data (bits position) :: right) position.castSucc index
    have split : (List.ofFn bits).take remaining.val =
        (List.ofFn bits).take position.val ++ [bits position] := by
      have result := List.take_succ_eq_append_getElem (l := List.ofFn bits) (i := position.val)
        (by simpa only [List.length_ofFn] using position.isLt)
      rw [List.getElem_ofFn] at result
      exact (congrArg (fun count => (List.ofFn bits).take count) previous).trans result
    convert Tape.Steps.next move (Tape.Steps.next write rest) using 1
    all_goals first | omega | simp [split, word, List.append_assoc]
    all_goals omega

/-- Read a fixed field into finite controller states, preserving the tape. -/
theorem reads (table : (Fin inputWidth → Bool) → (Fin outputWidth → Bool))
    (bits : Fin inputWidth → Bool) (left tail : List Symbol) :
    Tape.Steps (machine table) inputWidth
      (Tape.configuration (.read 0 (fun _ => false)) left (word (List.ofFn bits) ++ tail))
      (Tape.configuration (.read (Fin.last inputWidth) bits)
        ((word (List.ofFn bits)).reverse ++ left) tail) := by
  have read := read_loop table bits 0 left tail
  have empty : readPrefix bits 0 = fun _ => false := by funext index; simp [readPrefix]
  simpa only [Fin.val_zero, empty, Nat.sub_zero, List.drop_zero] using read

/-- A table call overwrites exactly its fixed output window and preserves its
input and both surrounding regions, ready for repeated prepared-frame calls. -/
theorem realizes_in_frame (table : (Fin inputWidth → Bool) → (Fin outputWidth → Bool))
    (bits : Fin inputWidth → Bool) (reserved left tail : List Symbol)
    (width : reserved.length = outputWidth) :
    Tape.Steps (machine table) (2 * inputWidth + 2 * outputWidth + 3)
      (Tape.configuration (.read 0 (fun _ => false)) (reserved ++ left) (word (List.ofFn bits) ++ tail))
      (Tape.configuration .halt left (word (List.ofFn (table bits)) ++ word (List.ofFn bits) ++ tail)) := by
  have read := read_loop table bits 0 (reserved ++ left) tail
  have emptyPrefix : readPrefix bits 0 = fun _ => false := by funext index; simp [readPrefix]
  rw [Fin.val_zero, emptyPrefix] at read
  simp only [Nat.sub_zero, List.drop_zero] at read
  have enter := Tape.stay (machine := machine table)
    (state := .read (Fin.last inputWidth) bits)
    (nextState := .rewind (Fin.last inputWidth) (table bits))
    ((word (List.ofFn bits)).reverse ++ (reserved ++ left)) tail
    (by intro symbol; simp [machine])
  have rewind := rewind_loop table (table bits) (word (List.ofFn bits)).reverse (reserved ++ left) tail
    (Fin.last inputWidth) (by simp [word])
  have wordLength : (word (List.ofFn bits)).length = inputWidth := by simp [word]
  simp only [List.reverse_reverse, List.length_reverse, wordLength] at rewind
  have prepare := Tape.stay (machine := machine table) (state := .rewind 0 (table bits))
    (nextState := .emit (Fin.last outputWidth) (table bits)) (reserved ++ left) (word (List.ofFn bits) ++ tail)
    (by intro symbol; simp [machine])
  have emit := emit_loop table (table bits) reserved left (word (List.ofFn bits) ++ tail)
    (Fin.last outputWidth) width.symm
  have full : (List.ofFn (table bits)).take outputWidth = List.ofFn (table bits) :=
    List.take_of_length_le (by simp)
  simp only [Fin.val_last, full] at emit
  have trace := read.trans (Tape.Steps.next enter (rewind.trans (Tape.Steps.next prepare emit)))
  convert trace using 1
  · omega
  · simp only [List.append_assoc]

/-- Every transition counted here is a TM0 move or write. Both input bits and
arbitrary trailing storage are preserved, including zero-width domains. -/
theorem realizes (table : (Fin inputWidth → Bool) → (Fin outputWidth → Bool))
    (bits : Fin inputWidth → Bool) (tail : List Symbol) :
    Tape.Steps (machine table) (2 * inputWidth + 2 * outputWidth + 3)
      (Tape.configuration (.read 0 (fun _ => false)) [] (word (List.ofFn bits) ++ tail))
      (Tape.configuration .halt [] (word (List.ofFn (table bits)) ++ word (List.ofFn bits) ++ tail)) := by
  have trace := realizes_in_frame table bits (List.replicate outputWidth 0) [] tail (by simp)
  have blanks : Turing.ListBlank.mk (List.replicate outputWidth (0 : Symbol)) =
      Turing.ListBlank.mk ([] : List Symbol) := by
    apply Quotient.sound
    exact Or.inr ⟨outputWidth, by simp⟩
  simpa only [List.append_nil, Tape.configuration, blanks] using trace

@[simp] theorem halt (table : (Fin inputWidth → Bool) → (Fin outputWidth → Bool))
    (left right : List Symbol) :
    Turing.TM0.step (machine table) (Tape.configuration .halt left right) = none := by
  simp [Turing.TM0.step, Tape.configuration, machine]

-- inputLevel and outputLevel: the mathematical carriers presented by the fixed codecs.
universe inputLevel outputLevel
variable {Input : Type inputLevel} {Output : Type outputLevel}

/-- Compile a mathematical operation on fixed presented domains into a bit table. -/
def encodedTable (inputCodec : BitCodec Input inputWidth) (outputCodec : BitCodec Output outputWidth)
    (operation : Input → Output) : (Fin inputWidth → Bool) → (Fin outputWidth → Bool) := fun bits =>
  BoolTuple.fromBits (match inputCodec.decode (BoolTuple.toBits bits) with
    | some value => outputCodec.encode (operation value)
    | none => 0)

/-- Canonical mathematical operations can reuse an assigned output slot. -/
theorem realizes_operation_in_frame (inputCodec : BitCodec Input inputWidth)
    (outputCodec : BitCodec Output outputWidth) (operation : Input → Output) (value : Input)
    (reserved left tail : List Symbol) (width : reserved.length = outputWidth) :
    Tape.Steps (machine (encodedTable inputCodec outputCodec operation))
      (2 * inputWidth + 2 * outputWidth + 3)
      (Tape.configuration (.read 0 (fun _ => false)) (reserved ++ left)
        (word (List.ofFn (BoolTuple.fromBits (inputCodec.encode value))) ++ tail))
      (Tape.configuration .halt left
        (word (List.ofFn (BoolTuple.fromBits (outputCodec.encode (operation value)))) ++
          word (List.ofFn (BoolTuple.fromBits (inputCodec.encode value))) ++ tail)) := by
  simpa only [encodedTable, BoolTuple.toBits_fromBits, inputCodec.decode_encode] using
    realizes_in_frame (encodedTable inputCodec outputCodec operation)
      (BoolTuple.fromBits (inputCodec.encode value)) reserved left tail width

/-- Valid canonical input realizes the mathematical operation, with a constant
number of tape transitions depending only on the fixed domain widths. -/
theorem realizes_operation (inputCodec : BitCodec Input inputWidth)
    (outputCodec : BitCodec Output outputWidth) (operation : Input → Output) (value : Input)
    (tail : List Symbol) :
    Tape.Steps (machine (encodedTable inputCodec outputCodec operation))
      (2 * inputWidth + 2 * outputWidth + 3)
      (Tape.configuration (.read 0 (fun _ => false)) []
        (word (List.ofFn (BoolTuple.fromBits (inputCodec.encode value))) ++ tail))
      (Tape.configuration .halt []
        (word (List.ofFn (BoolTuple.fromBits (outputCodec.encode (operation value)))) ++
          word (List.ofFn (BoolTuple.fromBits (inputCodec.encode value))) ++ tail)) := by
  simpa only [encodedTable, BoolTuple.toBits_fromBits, inputCodec.decode_encode] using
    realizes (encodedTable inputCodec outputCodec operation)
      (BoolTuple.fromBits (inputCodec.encode value)) tail

end Polytime1.FiniteTableMachine
