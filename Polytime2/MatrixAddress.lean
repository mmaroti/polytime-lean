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

import Polytime2.UnaryAppend
import Polytime2.While
import Polytime2.Storage

/-! # Runtime row-major address construction

The three input counters are row index, column count, and column index.
Repeated unary addition computes `row * width + column`. All input counters
and heads are preserved; the initially blank output counter receives the
address. Neither the controller nor the tape set depends on runtime sizes.
-/

namespace Polytime2.MatrixAddress

open MultiTape
open Binary (Symbol tape)

inductive TapeName | row | width | column | output
  deriving DecidableEq

instance : Fintype TapeName :=
  ⟨{.row, .width, .column, .output}, by intro name; cases name <;> simp⟩

abbrev Alphabet (_name : TapeName) := Symbol

/-- A counter with the head after `processed` digits and before `remaining` digits. -/
def counter (processed remaining : ℕ) : Turing.Tape Symbol :=
  tape (List.replicate processed 2 ++ [3]) (List.replicate remaining 2 ++ [0]) ()

theorem counter_fits (processed remaining : ℕ) : Fits (processed + remaining + 2) (counter processed remaining) := by
  refine ⟨List.replicate processed 2 ++ [3], List.replicate remaining 2 ++ [0], rfl, ?_⟩
  simp
  omega

def frame (processed remaining width column written : ℕ) : Tapes Alphabet
  | .row => counter processed remaining
  | .width => counter 0 width
  | .column => counter 0 column
  | .output => counter written 0

def ready (row width column address : ℕ) : Tapes Alphabet
  | .row => counter 0 row
  | .width => counter 0 width
  | .column => counter 0 column
  | .output => counter 0 address

noncomputable def appendWidth : Machine Alphabet (Sum (Fin 2) (Fin 2)) :=
  wire (twoTapes TapeName.width .output (by decide)) UnaryAppend.machine

noncomputable def appendColumn : Machine Alphabet (Sum (Fin 2) (Fin 2)) :=
  wire (twoTapes TapeName.column .output (by decide)) UnaryAppend.machine

noncomputable def advanceRow : Machine Alphabet (Fin 2) :=
  wire (oneTape TapeName.row) (Move.machine 1 .right)

noncomputable def body : Machine Alphabet (Sum (Sum (Fin 2) (Fin 2)) (Fin 2)) :=
  sequence appendWidth advanceRow 1

def guard : Machine Alphabet Unit := fun _ _ => none

def result (symbols : Symbols Alphabet) : Bool := decide (symbols .row = 2)

noncomputable def loop : Machine Alphabet (Sum Unit (Sum (Sum (Fin 2) (Fin 2)) (Fin 2))) :=
  whileMachine guard body () (.inl (.inl 0)) result

abbrev RepeatState := Sum (Sum Unit (Sum (Sum (Fin 2) (Fin 2)) (Fin 2))) Unit

noncomputable def repeatWidth : Machine Alphabet RepeatState := withExit loop

noncomputable def returnRow : Machine Alphabet (Fin 2) :=
  wire (oneTape TapeName.row) BoundaryReturn.machine

noncomputable def returnOutput : Machine Alphabet (Fin 2) :=
  wire (oneTape TapeName.output) BoundaryReturn.machine

abbrev State := Sum (Sum (Sum RepeatState (Fin 2)) (Sum (Fin 2) (Fin 2))) (Fin 2)

noncomputable def machine : Machine Alphabet State :=
  sequence (sequence (sequence repeatWidth returnRow 0) appendColumn (.inl 0)) returnOutput 0

def entry : State := .inl (.inl (.inl (.inl (.inl ()))))
def exit : State := .inr 1

private theorem append_steps (selected : Bool) (processed remaining width column written : ℕ) :
    let amount := if selected then width else column
    Steps (if selected then appendWidth else appendColumn) (2 * amount + 4)
      (.inl 0, frame processed remaining width column written)
      (.inr 1, frame processed remaining width column (written + amount)) := by
  cases selected with
  | false =>
    let wiring := twoTapes TapeName.column .output (by decide)
    have trace := wire_steps wiring UnaryAppend.machine
      (UnaryAppend.steps column [] [] (List.replicate written 2 ++ [3]))
      (frame processed remaining width column written)
      (by intro name; cases name <;> rfl)
    have restored : install wiring
        (Copy.frame [3] (List.replicate column 2 ++ [0])
          (List.replicate column 2 ++ (List.replicate written 2 ++ [3])) [0])
        (frame processed remaining width column written) =
        frame processed remaining width column (written + column) := by
      funext name
      cases name <;> simp [wiring, frame, counter, Copy.frame, Binary.tape, Function.update,
        ← List.append_assoc, Nat.add_comm]
    simpa only [Bool.false_eq_true, ite_false, appendColumn, wiring, restored] using trace
  | true =>
    let wiring := twoTapes TapeName.width .output (by decide)
    have trace := wire_steps wiring UnaryAppend.machine
      (UnaryAppend.steps width [] [] (List.replicate written 2 ++ [3]))
      (frame processed remaining width column written)
      (by intro name; cases name <;> rfl)
    have restored : install wiring
        (Copy.frame [3] (List.replicate width 2 ++ [0])
          (List.replicate width 2 ++ (List.replicate written 2 ++ [3])) [0])
        (frame processed remaining width column written) =
        frame processed remaining width column (written + width) := by
      funext name
      cases name <;> simp [wiring, frame, counter, Copy.frame, Binary.tape, Function.update,
        ← List.append_assoc, Nat.add_comm]
    simpa only [Bool.true_eq, ite_true, appendWidth, wiring, restored] using trace

private theorem advance_steps (processed remaining width column written : ℕ) :
    Steps advanceRow 1
      (1, frame processed (remaining + 1) width column written)
      (0, frame (processed + 1) remaining width column written) := by
  have localTrace : Steps (Move.machine 1 .right) 1
      (1, tape (List.replicate processed 2 ++ [3]) (List.replicate (remaining + 1) 2 ++ [0]))
      (0, tape (List.replicate (processed + 1) 2 ++ [3]) (List.replicate remaining 2 ++ [0])) := by
    refine .next ?_ (.zero _)
    simp only [step, Move.machine, Fin.val_one, show (1 : ℕ) ≠ 0 by decide, ↓reduceDIte,
      Option.map_some]
    congr 2
  have trace := wire_steps (oneTape TapeName.row) (Move.machine 1 .right) localTrace
    (frame processed (remaining + 1) width column written) (by intro name; cases name; rfl)
  have restored : install (oneTape TapeName.row)
      (tape (List.replicate (processed + 1) 2 ++ [3]) (List.replicate remaining 2 ++ [0]))
      (frame processed (remaining + 1) width column written) =
      frame (processed + 1) remaining width column written := by
    funext name
    cases name <;> simp [frame, counter, Binary.tape, Function.update]
  simpa only [advanceRow, restored] using trace

private theorem body_steps (processed remaining width column written : ℕ) :
    Steps body (2 * width + 6)
      (.inl (.inl 0), frame processed (remaining + 1) width column written)
      (.inr 0, frame (processed + 1) remaining width column (written + width)) := by
  have appended := append_steps true processed (remaining + 1) width column written
  have advanced := advance_steps processed remaining width column (written + width)
  have trace := sequence_steps appendWidth advanceRow 1 appended
    (by intro symbols; simp [appendWidth, wire, UnaryAppend.machine, MultiTape.sequence,
      UnaryAppend.returnSource, BoundaryReturn.machine]) advanced
  exact trace

private theorem loop_steps (processed remaining width column written : ℕ) :
    Steps loop (remaining * (2 * width + 8))
      (.inl (), frame processed remaining width column written)
      (.inl (), frame (processed + remaining) 0 width column (written + remaining * width)) := by
  induction remaining generalizing processed written with
  | zero => simpa using Steps.zero (machine := loop) (.inl (), frame processed 0 width column written)
  | succ remaining hypothesis =>
    have choose : step loop (.inl (), frame processed (remaining + 1) width column written) =
        some (.inr (.inl (.inl 0)), frame processed (remaining + 1) width column written) := by
      simp [step, loop, whileMachine, guard, result, MultiTape.read, frame, counter, Binary.tape, List.replicate_succ]
    have advanced := (body_steps processed remaining width column written).rename Sum.inr (target := loop)
      (by intro state symbols next actions transition; simp [loop, whileMachine, transition])
    have handover : step loop (.inr (.inr 0), frame (processed + 1) remaining width column (written + width)) =
        some (.inl (), frame (processed + 1) remaining width column (written + width)) := by
      simp [step, loop, whileMachine, body, MultiTape.sequence, advanceRow, wire, Move.machine]
    have rest := hypothesis (processed + 1) (written + width)
    have trace := Steps.next choose (advanced.trans (Steps.next handover rest))
    convert trace using 1 <;> first | rfl | congr 2 <;> ring

theorem repeat_steps (row width column written : ℕ) :
    Steps repeatWidth (row * (2 * width + 8) + 1)
      (.inl (.inl ()), frame 0 row width column written)
      (.inr (), frame row 0 width column (written + row * width)) := by
  have trace := loop_steps 0 row width column written
  have halt : step loop (.inl (), frame row 0 width column (written + row * width)) = none := by
    simp [step, loop, whileMachine, guard, result, MultiTape.read, frame, counter, Binary.tape]
  simpa only [Nat.zero_add, repeatWidth] using withExit_steps loop trace halt

private theorem returnRow_steps (row width column written : ℕ) :
    Steps returnRow (row + 2)
      (0, frame row 0 width column written)
      (1, frame 0 row width column written) := by
  have localTrace : Steps BoundaryReturn.machine (row + 2)
      (0, tape (List.replicate row 2 ++ [3]) [0])
      (1, tape [3] (List.replicate row 2 ++ [0])) := by
    simpa [Binary.word, Binary.data] using
      BoundaryReturn.steps (List.replicate row true) 0 (by decide) [] []
  have trace := wire_steps (oneTape TapeName.row) BoundaryReturn.machine localTrace
    (frame row 0 width column written) (by intro name; cases name; rfl)
  have restored : install (oneTape TapeName.row)
      (tape [3] (List.replicate row 2 ++ [0])) (frame row 0 width column written) =
      frame 0 row width column written := by
    funext name
    cases name <;> simp [frame, counter, Binary.tape, Function.update]
  simpa only [returnRow, restored] using trace

private theorem returnOutput_steps (row width column written : ℕ) :
    Steps returnOutput (written + 2)
      (0, frame 0 row width column written)
      (1, ready row width column written) := by
  have localTrace : Steps BoundaryReturn.machine (written + 2)
      (0, tape (List.replicate written 2 ++ [3]) [0])
      (1, tape [3] (List.replicate written 2 ++ [0])) := by
    simpa [Binary.word, Binary.data] using
      BoundaryReturn.steps (List.replicate written true) 0 (by decide) [] []
  have trace := wire_steps (oneTape TapeName.output) BoundaryReturn.machine localTrace
    (frame 0 row width column written) (by intro name; cases name; rfl)
  have restored : install (oneTape TapeName.output)
      (tape [3] (List.replicate written 2 ++ [0])) (frame 0 row width column written) =
      ready row width column written := by
    funext name
    cases name <;> simp [frame, ready, counter, Binary.tape, Function.update]
  simpa only [returnOutput, restored] using trace

/-- Compute the row-major address, including every handover and head restoration. -/
theorem steps (row width column : ℕ) :
    Steps machine (3 * row * width + 9 * row + 3 * column + 12)
      (entry, ready row width column 0)
      (exit, ready row width column (row * width + column)) := by
  have repeated := repeat_steps row width column 0
  simp only [Nat.zero_add] at repeated
  have first := sequence_steps repeatWidth returnRow 0 repeated
    (by intro symbols; rfl) (returnRow_steps row width column (row * width))
  have second := sequence_steps (sequence repeatWidth returnRow 0) appendColumn (.inl 0) first
    (by intro symbols; simp [MultiTape.sequence, returnRow, wire, BoundaryReturn.machine])
    (append_steps false 0 row width column (row * width))
  have complete := sequence_steps _ returnOutput 0 second
    (by intro symbols; simp [MultiTape.sequence, appendColumn, wire, UnaryAppend.machine,
      UnaryAppend.returnSource, BoundaryReturn.machine])
    (returnOutput_steps row width column (row * width + column))
  simp only [Bool.false_eq_true, ite_false] at complete
  convert complete using 1 <;> first | rfl | ring

-- parameterLevel: the runtime size names bounding the three input counters.
universe parameterLevel

theorem realizes {Parameter : Type parameterLevel} [Fintype Parameter]
    (rowCapacity widthCapacity columnCapacity : MvPolynomial Parameter ℕ) :
    Realizes machine entry exit
      (fun assignment initial => ∃ (row width column : ℕ),
        row ≤ MvPolynomial.eval assignment rowCapacity ∧
        width ≤ MvPolynomial.eval assignment widthCapacity ∧
        column ≤ MvPolynomial.eval assignment columnCapacity ∧ initial = ready row width column 0)
      (fun _ initial final => ∃ (row width column : ℕ),
        initial = ready row width column 0 ∧ final = ready row width column (row * width + column)) := by
  refine ⟨?_, 3 * rowCapacity * widthCapacity + 9 * rowCapacity + 3 * columnCapacity + 12, ?_⟩
  · intro symbols
    simp [machine, exit, MultiTape.sequence, returnOutput, wire, BoundaryReturn.machine]
  · intro assignment initial valid
    obtain ⟨row, width, column, rowBound, widthBound, columnBound, rfl⟩ := valid
    refine ⟨3 * row * width + 9 * row + 3 * column + 12, _, ?_, steps row width column, row, width, column, rfl, rfl⟩
    have product := Nat.mul_le_mul rowBound widthBound
    simp only [map_add, map_mul, map_ofNat]
    nlinarith

end Polytime2.MatrixAddress
