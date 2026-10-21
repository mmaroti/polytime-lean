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

import Polytime2.Machine.Wiring

/-! # Binary encoding and arithmetic facts

Binary zero and one use nonblank symbols 1 and 2. Digits are little endian,
with a fixed reserved count. Decrement preserves that count for positive words.
-/

namespace Polytime2.Binary

open MultiTape

/-- Blank, binary zero, and binary one are the entire source alphabet. -/
abbrev Symbol := Fin 3

def data (bit : Bool) : Symbol := if bit then 2 else 1
def word (bits : List Bool) : List Symbol := bits.map data

/-- Appending an explicit blank does not change an eventually blank tape. -/
theorem mk_append_blank (payload : List Symbol) :
    Turing.ListBlank.mk (payload ++ [0]) = Turing.ListBlank.mk payload :=
  Quotient.sound (Or.inr ⟨1, by simp⟩)

def value : List Bool → ℕ
  | [] => 0
  | bit :: bits => bit.toNat + 2 * value bits

/-- Concatenating little-endian words shifts the second word by the first width. -/
theorem value_append (low high : List Bool) :
    value (low ++ high) = value low + 2 ^ low.length * value high := by
  induction low with
  | nil => simp [value]
  | cons bit bits hypothesis =>
    simp only [List.cons_append, value, List.length_cons, pow_succ, hypothesis]
    ring

/-- A padded binary word fits its declared digit capacity. -/
theorem value_lt_pow_length (bits : List Bool) : value bits < 2 ^ bits.length := by
  induction bits with
  | nil => simp [value]
  | cons bit bits hypothesis =>
    cases bit <;> simp only [value, Bool.toNat_false, Bool.toNat_true, List.length_cons, pow_succ] <;>
      nlinarith

@[simp] theorem value_replicate_false (length : ℕ) : value (List.replicate length false) = 0 := by
  induction length with
  | zero => rfl
  | succ length hypothesis => simp [List.replicate_succ, value, hypothesis]

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

def tape (left right : List Symbol) : Tapes (fun _ : Unit => Symbol) :=
  fun _ => Turing.Tape.mk' (Turing.ListBlank.mk left) (Turing.ListBlank.mk right)

end Polytime2.Binary
