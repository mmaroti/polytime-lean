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

import Polytime2.Wiring

/-! # Binary indices for array navigation

Symbols are blank (0), binary zero (1), binary one (2), and left boundary (3).
Digits are little endian, with a fixed reserved digit count. Decrement requires
a positive value; it preserves that count and returns to the first digit.
-/

namespace Polytime2.Binary

open MultiTape

abbrev Symbol := Fin 4

def data (bit : Bool) : Symbol := if bit then 2 else 1
def word (bits : List Bool) : List Symbol := bits.map data

def value : List Bool → ℕ
  | [] => 0
  | bit :: bits => bit.toNat + 2 * value bits

def decrement : List Bool → List Bool
  | [] => []
  | false :: bits => true :: decrement bits
  | true :: bits => false :: bits

@[simp] theorem decrement_length (bits : List Bool) : (decrement bits).length = bits.length := by
  induction bits with
  | nil => rfl
  | cons bit bits hypothesis => cases bit <;> simp [decrement, hypothesis]

theorem decrement_value (bits : List Bool) (positive : 0 < value bits) :
    value (decrement bits) + 1 = value bits := by
  induction bits with
  | nil => simp [value] at positive
  | cons bit bits hypothesis =>
    cases bit with
    | false =>
      have smaller : 0 < value bits := by simpa [value] using positive
      have equality := hypothesis smaller
      simp only [decrement, value, Bool.toNat_true, Bool.toNat_false]
      omega
    | true => simp [decrement, value, Nat.add_comm]

theorem eq_zero_digits (bits : List Bool) (zero : value bits = 0) :
    bits = List.replicate bits.length false := by
  induction bits with
  | nil => rfl
  | cons bit bits hypothesis =>
    cases bit with
    | false =>
      have tailZero : value bits = 0 := by simpa [value] using zero
      simpa [List.replicate_succ] using congrArg (List.cons false) (hypothesis tailZero)
    | true => simp [value] at zero

private theorem first_one (bits : List Bool) (positive : 0 < value bits) :
    ∃ zeros rest, bits = List.replicate zeros false ++ true :: rest := by
  induction bits with
  | nil => simp [value] at positive
  | cons bit bits hypothesis =>
    cases bit with
    | true => exact ⟨0, bits, rfl⟩
    | false =>
      have smaller : 0 < value bits := by simpa [value] using positive
      obtain ⟨zeros, rest, rfl⟩ := hypothesis smaller
      exact ⟨zeros + 1, rest, by simp [List.replicate_succ]⟩

@[simp] theorem decrement_first_one (zeros : ℕ) (rest : List Bool) :
    decrement (List.replicate zeros false ++ true :: rest) =
      List.replicate zeros true ++ false :: rest := by
  induction zeros with
  | zero => rfl
  | succ zeros hypothesis => simp [List.replicate_succ, decrement, hypothesis]

def tape (left right : List Symbol) : Tapes (fun _ : Unit => Symbol) :=
  fun _ => Turing.Tape.mk' (Turing.ListBlank.mk left) (Turing.ListBlank.mk right)

def machine : Machine (fun _ : Unit => Symbol) (Fin 3) := fun state symbols =>
  match state.val with
  | 0 => if symbols () = 1 then some (0, fun _ => (2, some .right))
    else if symbols () = 2 then some (1, fun _ => (1, none)) else none
  | 1 => if symbols () = 3 then some (2, fun _ => (3, some .right))
    else some (1, fun _ => (symbols (), some .left))
  | _ => none

private theorem carry (zeros : ℕ) (left right : List Symbol) :
    Steps machine zeros
      (0, tape left (List.replicate zeros 1 ++ 2 :: right))
      (0, tape (List.replicate zeros 2 ++ left) (2 :: right)) := by
  induction zeros generalizing left with
  | zero => simpa using Steps.zero (machine := machine) (0, tape left (2 :: right))
  | succ zeros hypothesis =>
    have first : step machine (0, tape left (List.replicate (zeros + 1) 1 ++ 2 :: right)) =
        some (0, tape (2 :: left) (List.replicate zeros 1 ++ 2 :: right)) := by
      simp only [step, machine, MultiTape.read, tape, List.replicate_succ, List.cons_append,
        Turing.Tape.mk'_head, Turing.ListBlank.head_mk, List.headI_cons, ↓reduceIte]
      congr 2
    have rest := hypothesis (2 :: left)
    simpa [List.replicate_succ', List.append_assoc] using Steps.next first rest

private theorem return_head (zeros : ℕ) (current : Symbol) (notBoundary : current ≠ 3)
    (left right : List Symbol) :
    Steps machine (zeros + 2)
      (1, tape (List.replicate zeros 2 ++ 3 :: left) (current :: right))
      (2, tape (3 :: left) (List.replicate zeros 2 ++ current :: right)) := by
  induction zeros generalizing current right with
  | zero =>
    have first : step machine (1, tape (3 :: left) (current :: right)) =
        some (1, tape left (3 :: current :: right)) := by
      simp only [step, machine, MultiTape.read, tape, Turing.Tape.mk'_head,
        Turing.ListBlank.head_mk, List.headI_cons, notBoundary, ↓reduceIte]
      congr 2
    have second : step machine (1, tape left (3 :: current :: right)) =
        some (2, tape (3 :: left) (current :: right)) := by
      simp only [step, machine, MultiTape.read, tape, Turing.Tape.mk'_head,
        Turing.ListBlank.head_mk, List.headI_cons, ↓reduceIte]
      congr 2
    simpa using Steps.next first (Steps.next second (.zero _))
  | succ zeros hypothesis =>
    have first : step machine
        (1, tape (List.replicate (zeros + 1) 2 ++ 3 :: left) (current :: right)) =
        some (1, tape (List.replicate zeros 2 ++ 3 :: left) (2 :: current :: right)) := by
      simp only [step, machine, MultiTape.read, tape, List.replicate_succ, List.cons_append,
        Turing.Tape.mk'_head, Turing.ListBlank.head_mk, List.headI_cons,
        notBoundary, ↓reduceIte]
      congr 2
    have rest := hypothesis 2 (by decide) (current :: right)
    simpa [List.replicate_succ', List.append_assoc, Nat.add_assoc] using Steps.next first rest

/-- Binary decrement has linear digit cost and preserves both neighboring regions. -/
theorem steps (bits : List Bool) (positive : 0 < value bits) (left right : List Symbol) :
    ∃ ticks, ticks ≤ 2 * bits.length + 3 ∧ Steps machine ticks
      (0, tape (3 :: left) (word bits ++ right))
      (2, tape (3 :: left) (word (decrement bits) ++ right)) := by
  obtain ⟨zeros, rest, rfl⟩ := first_one bits positive
  have carried := carry zeros (3 :: left) (word rest ++ right)
  have pivot : step machine
      (0, tape (List.replicate zeros 2 ++ 3 :: left) (2 :: (word rest ++ right))) =
      some (1, tape (List.replicate zeros 2 ++ 3 :: left) (1 :: (word rest ++ right))) := by
    simp only [step, machine, MultiTape.read, tape, Turing.Tape.mk'_head,
      Turing.ListBlank.head_mk, List.headI_cons, ↓reduceIte]
    congr 2
  have returned := return_head zeros 1 (by decide) left (word rest ++ right)
  refine ⟨zeros + (zeros + 2 + 1), ?_, ?_⟩
  · simp only [List.length_append, List.length_replicate, List.length_cons]; omega
  · simpa [word, data, List.map_append, List.map_replicate, List.append_assoc] using
      carried.trans (Steps.next pivot returned)

-- parameterLevel: names of size parameters bounding the index digit count.
universe parameterLevel

/-- One fixed three-state machine decrements every positive binary index.
The capacity bounds digits, not the possibly exponential numeric value. -/
theorem realizes {Parameter : Type parameterLevel} [Fintype Parameter]
    (capacity : MvPolynomial Parameter ℕ) :
    Realizes machine 0 2
      (fun assignment initial => ∃ bits left right,
        0 < value bits ∧ bits.length ≤ MvPolynomial.eval assignment capacity ∧
          initial = tape (3 :: left) (word bits ++ right))
      (fun _ initial final => ∃ bits updated left right,
        value updated + 1 = value bits ∧ updated.length = bits.length ∧
          initial = tape (3 :: left) (word bits ++ right) ∧
          final = tape (3 :: left) (word updated ++ right)) := by
  refine ⟨by intro symbols; rfl, 2 * capacity + 3, ?_⟩
  intro assignment initial valid
  obtain ⟨bits, left, right, positive, fits, rfl⟩ := valid
  obtain ⟨ticks, cost, trace⟩ := steps bits positive left right
  refine ⟨ticks, tape (3 :: left) (word (decrement bits) ++ right), ?_, trace,
    bits, decrement bits, left, right, decrement_value bits positive,
    decrement_length bits, rfl, rfl⟩
  simp only [map_add, map_mul, map_ofNat]
  omega

end Polytime2.Binary
