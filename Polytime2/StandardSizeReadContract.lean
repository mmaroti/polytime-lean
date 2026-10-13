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

import Polytime2.StandardSizeRead

/-! # Encoded-domain contract for unary size reading -/

namespace Polytime2.StandardSizeRead

open MultiTape CallingConvention
open Binary (word)

def domains : Sum Bool Bool → EncodedDomain Bool
  | .inl parameter => EncodedDomain.unary parameter
  | .inr _ => EncodedDomain.binaryNaturals true

def argumentReadOnly : Sum Bool Bool → Bool
  | .inl _ => true
  | .inr _ => false

def sizeTapes : Bool ↪ Sum Bool Bool :=
  ⟨Sum.inl, by intro first second equal; cases equal; rfl⟩

def wiring : Fin 4 ↪ Sum Bool Bool :=
  ⟨(fun name => match name.val with
    | 0 => .inl false | 1 => .inl true | 2 => .inr false | _ => .inr true), by
    intro first second equal
    fin_cases first <;> fin_cases second <;> simp_all⟩

noncomputable def algorithm : Machine (CallingConvention.Alphabet (Sum Bool Bool)) State :=
  MultiTape.wire wiring machine

/-- A size can be read as an ordinary natural whenever it fits the declared
binary capacity. Both unary sizes remain unchanged and scratch is canonical. -/
theorem contract : CallingConvention.Realizes domains argumentReadOnly sizeTapes algorithm entry exit
    (fun assignment _ => assignment false < 2 ^ assignment true)
    (fun assignment _ output => (output ⟨.inr false, rfl⟩).val = assignment false) := by
  refine ⟨(by intro parameter; rfl), (by intro symbols; simp [algorithm, MultiTape.wire]),
    4 * MvPolynomial.X true + MvPolynomial.X false * (4 * MvPolynomial.X true + 8) + 11, ?_⟩
  intro assignment input initial valid represented sizes
  obtain ⟨oldResult, resultLength, resultEq⟩ := represented.2 (.inr false) rfl
  obtain ⟨oldScratch, scratchLength, scratchEq⟩ := represented.2 (.inr true) rfl
  obtain ⟨finalScratch, finalLength, localTrace⟩ := runs (assignment false) (assignment true)
    oldResult oldScratch resultLength scratchLength
  let result := advanceBits (assignment false) (List.replicate (assignment true) false)
  have resultLength : result.length = assignment true := by simp [result]
  have resultValue : Binary.value result = assignment false := by
    simp [result, advanceBits_value, Nat.mod_eq_of_lt valid]
  have resultBound : Binary.value result < 2 ^ assignment true :=
    resultValue.symm ▸ valid
  let resultNatural : Fin (2 ^ assignment true) := ⟨Binary.value result, resultBound⟩
  let scratchNatural : Fin (2 ^ assignment true) :=
    ⟨Binary.value finalScratch, by simpa [finalLength] using Binary.value_lt_pow_length finalScratch⟩
  let localFinal := entryFrame (assignment false) (assignment true) (word result) (word finalScratch)
  have trace := localTrace.wire wiring
    (fun name => (domains name).width assignment) argumentReadOnly
    (by intro name; fin_cases name <;> rfl)
    (by intro name premise; fin_cases name <;> exact premise) initial (fun _ => 0)
  have initialMatches : (fun name => initial (wiring name)) =
      entryFrame (assignment false) (assignment true) oldResult oldScratch := by
    funext name
    fin_cases name
    · exact sizes false
    · exact sizes true
    · exact resultEq
    · exact scratchEq
  have start : install wiring (entryFrame (assignment false) (assignment true) oldResult oldScratch) initial = initial := by
    rw [← initialMatches, install_self]
  have positions : install wiring (fun _ : Fin 4 => (0 : ℤ)) (fun _ : Sum Bool Bool => (0 : ℤ)) =
      fun _ => 0 := install_self _ _
  rw [start, positions] at trace
  let output : Outputs domains argumentReadOnly assignment := fun name => by
    rcases name with ⟨name, writable⟩
    cases name with
    | inl parameter => contradiction
    | inr name => cases name with
      | false => exact resultNatural
      | true => exact scratchNatural
  refine ⟨_, output, _, ?_, trace, resultValue, ?_⟩
  · simp
  · intro name writable
    cases name with
    | inl parameter => contradiction
    | inr name => cases name with
      | false =>
        change install wiring _ initial (wiring 2) = _
        rw [install_at]
        exact (encoded_binaryNaturals true assignment result resultLength).symm
      | true =>
        change install wiring _ initial (wiring 3) = _
        rw [install_at]
        exact (encoded_binaryNaturals true assignment finalScratch finalLength).symm

end Polytime2.StandardSizeRead
