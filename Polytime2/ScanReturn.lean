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

import Polytime2.CallingConvention

/-! # Shared return phases for synchronized scans -/

namespace Polytime2.ScanReturn

open MultiTape CallingConvention
open Binary (Symbol data word)

-- tapeLevel: named tape roles; stateLevel: the enclosing finite controller.
universe tapeLevel stateLevel
variable {TapeName : Type tapeLevel} {State : Type stateLevel}

/-- Selected heads move together; every symbol and unselected tape is preserved. -/
def move (moving : TapeName → Bool) (direction : Turing.Dir)
    (tapes : Tapes (CallingConvention.Alphabet TapeName)) : Tapes (CallingConvention.Alphabet TapeName) :=
  fun name => if moving name then Turing.Tape.move direction (tapes name) else tapes name

theorem act_move (moving : TapeName → Bool) (direction : Turing.Dir)
    (tapes : Tapes (CallingConvention.Alphabet TapeName)) :
    act (fun name => ((tapes name).head, if moving name then some direction else none)) tapes =
      move moving direction tapes := by
  funext name
  cases choice : moving name <;> simp [act, move, choice, Turing.Tape.write_self]

@[simp] theorem move_iterate (moving : TapeName → Bool) (direction : Turing.Dir)
    (count : ℕ) (tapes : Tapes (CallingConvention.Alphabet TapeName)) (name : TapeName) :
    (move moving direction)^[count] tapes name =
      if moving name then (Turing.Tape.move direction)^[count] (tapes name) else tapes name := by
  induction count with
  | zero => simp
  | succ count hypothesis =>
    rw [Function.iterate_succ_apply']
    simp only [move, hypothesis]
    cases moving name <;> simp [Function.iterate_succ_apply']

/-- Crossing a known word does not require inspecting its symbols. -/
theorem left_list (letters farLeft right : List Symbol) :
    (Turing.Tape.move .left)^[letters.length]
      (Turing.Tape.mk' (Turing.ListBlank.mk (letters ++ farLeft)) (Turing.ListBlank.mk right)) =
    Turing.Tape.mk' (Turing.ListBlank.mk farLeft) (Turing.ListBlank.mk (letters.reverse ++ right)) := by
  induction letters generalizing right with
  | nil => simp
  | cons letter letters hypothesis =>
    simpa [Function.iterate_succ_apply, Turing.Tape.move_left_mk',
      Turing.ListBlank.cons_mk, List.reverse_cons, List.append_assoc] using
      hypothesis (letter :: right)

/-- The final right step restores all selected heads after crossing a left blank. -/
theorem restore_tape (letters farLeft right : List Symbol) :
    Turing.Tape.move .right ((Turing.Tape.move .left)^[letters.length + 1]
      (Turing.Tape.mk' (Turing.ListBlank.mk (letters ++ 0 :: farLeft)) (Turing.ListBlank.mk right))) =
    Turing.Tape.mk' (Turing.ListBlank.mk (0 :: farLeft))
      (Turing.ListBlank.mk (letters.reverse ++ right)) := by
  have crossed := left_list (letters ++ [0]) farLeft right
  simp only [List.length_append, List.length_singleton, List.append_assoc, List.singleton_append,
    List.reverse_append, List.reverse_singleton] at crossed
  rw [crossed]
  simp [Turing.Tape.move_right_mk', Turing.ListBlank.cons_mk]

/-- A return phase follows the immutable source to its left blank. Other selected
heads follow even when their tapes contain blanks inside the data region. -/
theorem left_steps (machine : Machine (CallingConvention.Alphabet TapeName) State)
    (state : State) (cursor : TapeName) (moving : TapeName → Bool) (selected : moving cursor = true)
    (instruction : ∀ symbols, symbols cursor ≠ 0 → machine state symbols =
      some (state, fun name => (symbols name, if moving name then some .left else none)))
    (bits : List Bool) (current : Symbol) (nonblank : current ≠ 0)
    (farLeft right : List Symbol) (tapes : Tapes (CallingConvention.Alphabet TapeName))
    (source : tapes cursor = Turing.Tape.mk' (Turing.ListBlank.mk (word bits ++ 0 :: farLeft))
      (Turing.ListBlank.mk (current :: right))) :
    Steps machine (bits.length + 1) (state, tapes)
      (state, (move moving .left)^[bits.length + 1] tapes) := by
  have one (tapes : Tapes (CallingConvention.Alphabet TapeName))
      (head : (MultiTape.read tapes) cursor ≠ 0) :
      step machine (state, tapes) = some (state, move moving .left tapes) := by
    simp only [step, instruction (MultiTape.read tapes) head, Option.map_some]
    congr 2
    funext name
    cases choice : moving name <;> simp [act, move, choice, MultiTape.read, Turing.Tape.write_self]
  induction bits generalizing current right tapes with
  | nil =>
    have first := one tapes (by simpa [MultiTape.read, source] using nonblank)
    simpa using Steps.next first (Steps.zero _)
  | cons bit bits hypothesis =>
    have first := one tapes (by simpa [MultiTape.read, source] using nonblank)
    have changed : move moving .left tapes cursor =
        Turing.Tape.mk' (Turing.ListBlank.mk (word bits ++ 0 :: farLeft))
          (Turing.ListBlank.mk (data bit :: current :: right)) := by
      simp [move, selected, source, word, Turing.Tape.move_left_mk', Turing.ListBlank.cons_mk]
    have rest := hypothesis (data bit) (by cases bit <;> decide) (current :: right)
      (move moving .left tapes) changed
    simpa [Function.iterate_succ_apply] using Steps.next first rest

/-- The terminating instruction is supplied by the caller: it can restore
heads, write a finite-memory result, or hand control to another phase. -/
theorem steps (machine : Machine (CallingConvention.Alphabet TapeName) State)
    (state finalState : State) (cursor : TapeName) (moving : TapeName → Bool)
    (selected : moving cursor = true)
    (advance : ∀ symbols, symbols cursor ≠ 0 → machine state symbols =
      some (state, fun name => (symbols name, if moving name then some .left else none)))
    (finish : Symbols (CallingConvention.Alphabet TapeName) → Actions (CallingConvention.Alphabet TapeName))
    (terminal : ∀ symbols, symbols cursor = 0 → machine state symbols = some (finalState, finish symbols))
    (bits : List Bool) (current : Symbol) (nonblank : current ≠ 0)
    (farLeft right : List Symbol) (tapes : Tapes (CallingConvention.Alphabet TapeName))
    (source : tapes cursor = Turing.Tape.mk' (Turing.ListBlank.mk (word bits ++ 0 :: farLeft))
      (Turing.ListBlank.mk (current :: right))) :
    Steps machine (bits.length + 2) (state, tapes)
      (finalState, act (finish (read ((move moving .left)^[bits.length + 1] tapes)))
        ((move moving .left)^[bits.length + 1] tapes)) := by
  have trace := left_steps machine state cursor moving selected advance bits current nonblank farLeft right tapes source
  have blank : (read ((move moving .left)^[bits.length + 1] tapes)) cursor = 0 := by
    simp only [MultiTape.read, move_iterate, selected, ite_true, source]
    have crossed := left_list (word bits ++ [0]) farLeft (current :: right)
    simp only [List.length_append, List.length_map, word, List.length_singleton,
      List.append_assoc, List.singleton_append, List.reverse_append, List.reverse_singleton] at crossed
    simpa [word] using congrArg Turing.Tape.head crossed
  have last : Steps machine 1
      (state, (move moving .left)^[bits.length + 1] tapes)
      (finalState, act (finish (MultiTape.read ((move moving .left)^[bits.length + 1] tapes)))
        ((move moving .left)^[bits.length + 1] tapes)) :=
    Steps.next (by rw [step, terminal _ blank]; rfl) (Steps.zero _)
  simpa using trace.trans last

/-- A right-boundary handover also covers empty words. The caller chooses the
boundary writes and the final instruction; the shared rule performs the return. -/
theorem from_end (machine : Machine (CallingConvention.Alphabet TapeName) State)
    (start state finalState : State) (cursor : TapeName) (moving : TapeName → Bool)
    (selected : moving cursor = true)
    (advance : ∀ symbols, symbols cursor ≠ 0 → machine state symbols =
      some (state, fun name => (symbols name, if moving name then some .left else none)))
    (finish : Symbols (CallingConvention.Alphabet TapeName) → Actions (CallingConvention.Alphabet TapeName))
    (terminal : ∀ symbols, symbols cursor = 0 → machine state symbols = some (finalState, finish symbols))
    (bits : List Bool) (farLeft right : List Symbol)
    (initial prepared : Tapes (CallingConvention.Alphabet TapeName))
    (boundary : step machine (start, initial) = some (state, move moving .left prepared))
    (source : prepared cursor = Turing.Tape.mk' (Turing.ListBlank.mk (word bits ++ 0 :: farLeft))
      (Turing.ListBlank.mk (0 :: right))) :
    Steps machine (bits.length + 2) (start, initial)
      (finalState, act (finish (MultiTape.read ((move moving .left)^[bits.length + 1] prepared)))
        ((move moving .left)^[bits.length + 1] prepared)) := by
  cases bits with
  | nil =>
    have blank : (MultiTape.read (move moving .left prepared)) cursor = 0 := by
      simp [MultiTape.read, move, selected, source, word, Turing.Tape.move_left_mk',
        Turing.ListBlank.cons_mk]
    exact Steps.next boundary (Steps.next (by rw [step, terminal _ blank]; rfl) (Steps.zero _))
  | cons bit bits =>
    have changed : move moving .left prepared cursor =
        Turing.Tape.mk' (Turing.ListBlank.mk (word bits ++ 0 :: farLeft))
          (Turing.ListBlank.mk (data bit :: 0 :: right)) := by
      simp [move, selected, source, word, Turing.Tape.move_left_mk', Turing.ListBlank.cons_mk]
    have trace := steps machine state finalState cursor moving selected advance finish terminal
      bits (data bit) (by cases bit <;> decide) farLeft (0 :: right) (move moving .left prepared) changed
    simpa [Function.iterate_succ_apply, Nat.add_assoc] using Steps.next boundary trace

end Polytime2.ScanReturn
