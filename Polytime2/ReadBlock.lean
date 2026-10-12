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

import Polytime2.UnaryRead

/-! # Runtime-width input transfer and zero-buffer initialization

A unary width controls the number of transferred bits. The input head advances
only when reading; initialization leaves it untouched. Width and destination
heads are restored. A fixed optional leading zero reserves a carry digit.
-/

namespace Polytime2.ReadBlock

open MultiTape
open Binary (Symbol data word)

@[simp] private theorem reconstruct (letters : List Symbol) :
    Turing.ListBlank.mk (letters.headI :: letters.tail) = Turing.ListBlank.mk letters := by
  cases letters with
  | nil => exact Turing.ListBlank.cons_head_tail (Turing.ListBlank.mk [])
  | cons => rfl

private theorem replicate_commute (count : ℕ) (symbol : Symbol) (tail : List Symbol) :
    List.replicate count symbol ++ symbol :: tail = symbol :: (List.replicate count symbol ++ tail) := by
  induction count with
  | zero => rfl
  | succ count hypothesis => simpa only [List.replicate_succ, List.cons_append] using congrArg (List.cons symbol) hypothesis

-- Tape 0 is input, tape 1 is the unary width, and tape 2 is the destination.
abbrev Alphabet := fun _ : Fin 3 => Symbol

def frame (source : Turing.Tape Symbol) (counterLeft counterRight targetLeft targetRight : List Symbol) :
    Tapes Alphabet := fun name => if name = 0 then source
      else if name = 1 then Binary.tape counterLeft counterRight ()
      else Binary.tape targetLeft targetRight ()

def source (fillZeros : Bool) (left : List Symbol) (bits : List Bool) (right : List Symbol) : Turing.Tape Symbol :=
  Binary.tape left ((if fillZeros then [] else word bits) ++ right) ()

def consumed (fillZeros : Bool) (left : List Symbol) (bits : List Bool) : List Symbol :=
  (if fillZeros then [] else (word bits).reverse) ++ left

def payload (fillZeros : Bool) (bits : List Bool) : List Bool :=
  if fillZeros then List.replicate bits.length false else bits

def format (extra : Bool) : Machine Alphabet (Fin 3) := fun state symbols =>
  if state = 0 then some (1, fun name => if name = 2 then (3, some .right) else (symbols name, none))
  else if state = 1 then some (2, fun name => if name = 2 ∧ extra then (1, some .right) else (symbols name, none))
  else none

def forward (fillZeros : Bool) : Machine Alphabet (Fin 2) := fun state symbols =>
  if state = 0 then
    if symbols 1 = 0 then some (1, fun name => if name = 2 then (0, none) else (symbols name, none))
    else some (0, fun name => if name = 0 then (symbols name, if fillZeros then none else some .right)
      else if name = 1 then (symbols name, some .right)
      else (if fillZeros then 1 else symbols 0, some .right))
  else none

noncomputable def returnCounter : Machine Alphabet (Fin 2) := wire (oneTape 1) BoundaryReturn.machine
noncomputable def returnTarget : Machine Alphabet (Fin 2) := wire (oneTape 2) BoundaryReturn.machine

abbrev State := Sum (Sum (Sum (Fin 3) (Fin 2)) (Fin 2)) (Fin 2)

noncomputable def machine (fillZeros extra : Bool) : Machine Alphabet State :=
  sequence (sequence (sequence (format extra) (forward fillZeros) 0) returnCounter 0) returnTarget 0

def entry : State := .inl (.inl (.inl 0))
def exit : State := .inr 1

private theorem forward_steps (fillZeros : Bool) (bits : List Bool)
    (left right counterLeft targetLeft : List Symbol) :
    Steps (forward fillZeros) (bits.length + 1)
      (0, frame (source fillZeros left bits right) counterLeft (List.replicate bits.length 2 ++ [0]) targetLeft [0])
      (1, frame (Binary.tape (consumed fillZeros left bits) right ())
        (List.replicate bits.length 2 ++ counterLeft) [0]
        ((word (payload fillZeros bits)).reverse ++ targetLeft) [0]) := by
  induction bits generalizing left counterLeft targetLeft with
  | nil =>
    refine .next ?_ (.zero _)
    cases fillZeros <;> simp [step, forward, MultiTape.read, frame, source, consumed, payload, word, Binary.tape]
    <;> funext name <;> fin_cases name <;>
      simp [act, frame, Binary.tape, Turing.Tape.write_mk']
  | cons bit bits hypothesis =>
    have first : step (forward fillZeros)
        (0, frame (source fillZeros left (bit :: bits) right) counterLeft
          (List.replicate (bit :: bits).length 2 ++ [0]) targetLeft [0]) =
        some (0, frame (source fillZeros (if fillZeros then left else data bit :: left) bits right)
          (2 :: counterLeft) (List.replicate bits.length 2 ++ [0])
          (data (if fillZeros then false else bit) :: targetLeft) [0]) := by
      cases fillZeros <;>
        simp [step, forward, MultiTape.read, frame, source, word, Binary.tape, List.replicate_succ] <;>
        funext name <;> fin_cases name <;>
        simp [act, frame, Binary.tape, data, Turing.Tape.write_mk',
          Turing.Tape.move_right_mk', Turing.ListBlank.cons_mk]
    have rest := hypothesis (if fillZeros then left else data bit :: left) (2 :: counterLeft)
      (data (if fillZeros then false else bit) :: targetLeft)
    cases fillZeros <;>
      simpa [consumed, payload, word, List.replicate_succ', List.reverse_cons, List.append_assoc,
        List.length_cons, Nat.add_assoc, replicate_commute] using Steps.next first rest

/-- Read exactly the supplied width, or fillZeros that many zeros, from blank
storage. No input-dependent controller or preallocated destination is used. -/
theorem steps (fillZeros extra : Bool) (bits : List Bool) (left right : List Symbol) :
    let output := (if extra then [false] else []) ++ payload fillZeros bits
    Steps (machine fillZeros extra) (3 * bits.length + extra.toNat + 10)
      (entry, frame (source fillZeros left bits right) [3] (List.replicate bits.length 2 ++ [0]) [] [0])
      (exit, frame (Binary.tape (consumed fillZeros left bits) right ())
        [3] (List.replicate bits.length 2 ++ [0]) [3] (word output ++ [0])) := by
  intro output
  let leading : List Bool := if extra then [false] else []
  have formatted : Steps (format extra) 2
      (0, frame (source fillZeros left bits right) [3] (List.replicate bits.length 2 ++ [0]) [] [0])
      (2, frame (source fillZeros left bits right) [3] (List.replicate bits.length 2 ++ [0])
        ((word leading).reverse ++ [3]) [0]) := by
    cases extra <;> refine Steps.next
      (middle := (1, frame (source fillZeros left bits right) [3] (List.replicate bits.length 2 ++ [0]) [3] [0]))
      ?_ (.next ?_ (.zero _)) <;>
      simp [step, format, MultiTape.read, frame, leading, word, data, Binary.tape] <;>
      funext name <;> fin_cases name <;>
      simp [act, frame, Binary.tape, Turing.Tape.write_self, Turing.Tape.write_mk',
        Turing.Tape.move_right_mk', Turing.ListBlank.cons_mk]
  have scanned := forward_steps fillZeros bits left right [3] ((word leading).reverse ++ [3])
  let finalSource := Binary.tape (consumed fillZeros left bits) right ()
  let targetLeft := (word (payload fillZeros bits)).reverse ++ ((word leading).reverse ++ [3])
  have counterTrace : Steps returnCounter (bits.length + 2)
      (0, frame finalSource (List.replicate bits.length 2 ++ [3]) [0] targetLeft [0])
      (1, frame finalSource [3] (List.replicate bits.length 2 ++ [0]) targetLeft [0]) := by
    have localTrace := BoundaryReturn.steps (List.replicate bits.length true) 0 (by decide) [] []
    simp only [List.length_replicate] at localTrace
    apply wire_steps_of_eq (oneTape 1) _ localTrace
    · intro name; cases name; simp [frame, Binary.tape, word, data]
    · intro name; cases name; simp [frame, Binary.tape, word, data]
    · intro name outside; fin_cases name <;> first | rfl | exact False.elim (outside ⟨(), rfl⟩)
  have outputLength : output.length = bits.length + extra.toNat := by
    cases extra <;> cases fillZeros <;> simp [output, payload]
  have targetTrace : Steps returnTarget (output.length + 2)
      (0, frame finalSource [3] (List.replicate bits.length 2 ++ [0]) targetLeft [0])
      (1, frame finalSource [3] (List.replicate bits.length 2 ++ [0]) [3] (word output ++ [0])) := by
    have localTrace := BoundaryReturn.steps output.reverse 0 (by decide) [] []
    simp only [List.length_reverse] at localTrace
    apply wire_steps_of_eq (oneTape 2) _ localTrace
    · intro name; cases name
      simp [frame, Binary.tape, targetLeft, output, leading, word, List.reverse_append, List.map_append]
    · intro name; cases name; simp [frame, word, List.map_reverse]
    · intro name outside; fin_cases name <;> first | rfl | exact False.elim (outside ⟨(), rfl⟩)
  have first := sequence_steps _ _ 0 formatted (by intro symbols; simp [format]) scanned
  have second := sequence_steps _ _ 0 first (by intro symbols; simp [MultiTape.sequence, forward]) counterTrace
  have complete := sequence_steps _ _ 0 second
    (by intro symbols; simp [MultiTape.sequence, returnCounter, wire, BoundaryReturn.machine]) targetTrace
  convert complete using 1 <;> first | rfl | (rw [outputLength]; omega)

theorem halt (fillZeros extra : Bool) (symbols : Symbols Alphabet) : machine fillZeros extra exit symbols = none := by
  simp [machine, exit, MultiTape.sequence, returnTarget, wire, BoundaryReturn.machine]

end Polytime2.ReadBlock
