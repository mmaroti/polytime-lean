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

import Polytime.Tuple

/-! # Binary counter facts used by tuple routing

Lists enumerate bits from least to most significant. Borrow propagation below
is proof notation for the writes performed by the tape machine.
-/

namespace Polytime.Binary

def value : List Bool → ℕ
  | [] => 0
  | bit :: rest => bit.toNat + 2 * value rest

def decrement : List Bool → List Bool
  | [] => []
  | false :: rest => true :: decrement rest
  | true :: rest => false :: rest

@[simp] theorem decrement_length (bits : List Bool) : (decrement bits).length = bits.length := by
  induction bits with
  | nil => rfl
  | cons bit rest hypothesis => cases bit <;> simp [decrement, hypothesis]

theorem decrement_value (bits : List Bool) (positive : 0 < value bits) :
    value (decrement bits) + 1 = value bits := by
  induction bits with
  | nil => simp [value] at positive
  | cons bit rest hypothesis =>
    cases bit with
    | false =>
      have restPositive : 0 < value rest := by simpa [value] using positive
      have equality := hypothesis restPositive
      simp only [decrement, value, Bool.toNat_true, Bool.toNat_false]
      omega
    | true => simp [decrement, value, Nat.add_comm]

theorem value_eq_bits (bits : List Bool) : value bits = (BitVec.ofBoolListLE bits).toNat := by
  induction bits with
  | nil => rfl
  | cons bit rest hypothesis => simp [value, BitVec.ofBoolListLE, hypothesis, Nat.add_comm,
      Nat.mul_comm]

def digits (width value : ℕ) : List Bool :=
  List.ofFn (BoolTuple.fromBits (BitVec.ofNat width value))

@[simp] theorem digits_length (width value : ℕ) : (digits width value).length = width := by
  simp [digits]

@[simp] theorem digits_value (width number : ℕ) :
    value (digits width number) = number % 2 ^ width := by
  rw [value_eq_bits]
  have equality := congrArg BitVec.toNat (BoolTuple.toBits_fromBits (BitVec.ofNat width number))
  simpa [digits, BoolTuple.toBits] using equality

theorem positive_split (bits : List Bool) (positive : 0 < value bits) :
    ∃ zeros rest, bits = List.replicate zeros false ++ true :: rest := by
  induction bits with
  | nil => simp [value] at positive
  | cons bit rest hypothesis =>
    cases bit with
    | false =>
      have restPositive : 0 < value rest := by simpa [value] using positive
      obtain ⟨zeros, tail, equality⟩ := hypothesis restPositive
      exact ⟨zeros + 1, tail, by simp [List.replicate_succ, equality]⟩
    | true => exact ⟨0, rest, rfl⟩

theorem decrement_split (zeros : ℕ) (rest : List Bool) :
    decrement (List.replicate zeros false ++ true :: rest) =
      List.replicate zeros true ++ false :: rest := by
  induction zeros with
  | zero => rfl
  | succ zeros hypothesis => simp [List.replicate_succ, decrement, hypothesis]

theorem zero_bits (bits : List Bool) (zero : value bits = 0) :
    bits = List.replicate bits.length false := by
  induction bits with
  | nil => rfl
  | cons bit rest hypothesis =>
    cases bit with
    | false =>
      have restZero : value rest = 0 := by simpa [value] using zero
      simpa only [List.length_cons, List.replicate_succ] using
        congrArg (List.cons false) (hypothesis restZero)
    | true => simp [value] at zero

end Polytime.Binary
