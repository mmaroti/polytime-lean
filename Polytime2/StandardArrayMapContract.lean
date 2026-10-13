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

import Polytime2.StandardArrayMap
import Polytime2.EncodedArray

/-! # Mathematical contract for binary array maps -/

namespace Polytime2.StandardArrayMap

open MultiTape CallingConvention
open Binary (Symbol word)

-- parameterLevel: immutable unary size arguments.
universe parameterLevel
variable {Parameter : Type parameterLevel} [Fintype Parameter]

def domains (parameterDomain elementDomain : EncodedDomain Empty)
    (length : MvPolynomial Parameter ℕ) : Sum Parameter (Fin 3) → EncodedDomain Parameter
  | .inl parameter => EncodedDomain.unary parameter
  | .inr 0 => parameterDomain.constant
  | .inr 1 | .inr 2 => elementDomain.constant.arrayOfLength length

def argumentReadOnly : Sum Parameter (Fin 3) → Bool
  | .inl _ => true
  | .inr name => readOnly name

def sizeTapes : Parameter ↪ Sum Parameter (Fin 3) :=
  ⟨Sum.inl, by intro first second equal; cases equal; rfl⟩

def dataTapes : Fin 3 ↪ Sum Parameter (Fin 3) :=
  ⟨Sum.inr, by intro first second equal; cases equal; rfl⟩

noncomputable def algorithm (parameterDomain elementDomain : EncodedDomain Empty)
    (operation : ∀ assignment, parameterDomain.Carrier assignment →
      elementDomain.Carrier assignment → elementDomain.Carrier assignment) :
    Machine (CallingConvention.Alphabet (Sum Parameter (Fin 3)))
      (State (parameterDomain.width Empty.elim) (elementDomain.width Empty.elim)) :=
  MultiTape.wire dataTapes
    (machine (StandardFiniteTable.encodedTable parameterDomain elementDomain elementDomain operation))

private theorem arrayBits (elementDomain : EncodedDomain Empty)
    (length : MvPolynomial Parameter ℕ) (assignment : Parameter → ℕ)
    (array : Fin (MvPolynomial.eval assignment length) → elementDomain.Carrier Empty.elim) :
    encoded (elementDomain.constant.arrayOfLength length) assignment array =
      buffer (word (bits (List.ofFn (fun index (bit : Fin (elementDomain.width Empty.elim)) =>
        (elementDomain.encode Empty.elim (array index)).getLsbD bit.val)))) := by
  change tape (EncodedDomain.ArrayEncoding.bits (EncodedDomain.ArrayEncoding.encode
    (elementDomain.encode Empty.elim) _ array)) = _
  rw [EncodedDomain.ArrayEncoding.bits_encode]
  congr 2
  simp only [List.map_ofFn, EncodedDomain.ArrayEncoding.bits]
  rfl

set_option maxHeartbeats 600000 in
/-- A finite scalar operation maps every array entry. No prepared output or
scratch is required; the unary size inputs and both mathematical arguments stay
unchanged, and the output has the same array length. -/
theorem contract (parameterDomain elementDomain : EncodedDomain Empty)
    (length : MvPolynomial Parameter ℕ)
    (operation : ∀ assignment, parameterDomain.Carrier assignment →
      elementDomain.Carrier assignment → elementDomain.Carrier assignment) :
    CallingConvention.Realizes (domains parameterDomain elementDomain length)
      argumentReadOnly sizeTapes (algorithm parameterDomain elementDomain operation)
      entry exit (fun _ _ => True)
      (fun _ input output => output ⟨.inr 2, rfl⟩ =
        fun index => operation Empty.elim (input ⟨.inr 0, rfl⟩) (input ⟨.inr 1, rfl⟩ index)) := by
  let parameterWidth := parameterDomain.width Empty.elim
  let elementWidth := elementDomain.width Empty.elim
  refine ⟨(by intro parameter; rfl), (by intro symbols; simp [algorithm, MultiTape.wire]),
    length * MvPolynomial.C (2 * (parameterWidth + elementWidth + elementWidth) +
      elementWidth + 9 + 2 * elementWidth) + 9, ?_⟩
  intro assignment input initial valid represented sizes
  let parameter := input ⟨.inr 0, rfl⟩
  let array := input ⟨.inr 1, rfl⟩
  let parameterRegister : Register parameterWidth :=
    fun index => (parameterDomain.encode Empty.elim parameter).getLsbD index.val
  let registers : List (Register elementWidth) := List.ofFn (fun index bit =>
    (elementDomain.encode Empty.elim (array index)).getLsbD bit.val)
  let table := StandardFiniteTable.encodedTable parameterDomain elementDomain elementDomain operation
  let result := fun index => operation Empty.elim parameter (array index)
  have tableCorrect (value : elementDomain.Carrier Empty.elim) :
      table parameterRegister (fun bit => (elementDomain.encode Empty.elim value).getLsbD bit.val) =
        elementDomain.encode Empty.elim (operation Empty.elim parameter value) := by
    dsimp only [table, parameterRegister, parameterWidth]
    simp only [StandardFiniteTable.encodedTable, Binary.value_bits,
      BitVec.ofNat_toNat, BitVec.setWidth_eq, elementDomain.decode_encode]
    rw [parameterDomain.decode_encode Empty.elim parameter]
  have mappedCorrect : mapped table parameterRegister registers = List.ofFn (fun index bit =>
      (elementDomain.encode Empty.elim (result index)).getLsbD bit.val) := by
    simp only [mapped, registers, List.map_ofFn]
    congr 1
    funext index bit
    exact congrArg (fun code : BitVec elementWidth => code.getLsbD bit.val) (tableCorrect (array index))
  have parameterEq : initial (.inr 0) = buffer (word (List.ofFn parameterRegister)) :=
    represented.1 (.inr 0) rfl
  have arrayEq : initial (.inr 1) = buffer (word (bits registers)) :=
    (represented.1 (.inr 1) rfl).trans (arrayBits elementDomain length assignment array)
  obtain ⟨old, oldLength, oldEq⟩ := represented.2 (.inr 2) rfl
  have count : registers.length = MvPolynomial.eval assignment length := by simp [registers]
  have oldWidth : old.length = (bits registers).length := by
    change old.length = MvPolynomial.eval assignment length * elementWidth at oldLength
    simpa [count] using oldLength
  obtain ⟨ticks, cost, localTrace⟩ := runs table parameterRegister registers old oldWidth
  have initialLocal : (fun name => initial (dataTapes name)) =
      frame parameterRegister [] (bits registers) [] old := by
    funext name
    fin_cases name
    · exact parameterEq
    · change initial (.inr 1) = Turing.Tape.mk' (Turing.ListBlank.mk [0])
        (Turing.ListBlank.mk (word (bits registers) ++ [0]))
      rw [arrayEq]
      exact (buffer_padding _).symm
    · change initial (.inr 2) = Turing.Tape.mk' (Turing.ListBlank.mk [0])
        (Turing.ListBlank.mk (old ++ [0]))
      rw [oldEq]
      exact (buffer_padding _).symm
  have trace := localTrace.wire dataTapes
    (fun name => (domains parameterDomain elementDomain length name).width assignment) argumentReadOnly
    (by
      intro name
      change (domains parameterDomain elementDomain length (.inr name)).width assignment = _
      fin_cases name
      · rfl
      · change MvPolynomial.eval assignment length * elementWidth = (bits registers).length
        simp [count]
      · change MvPolynomial.eval assignment length * elementWidth = (bits registers).length
        simp [count])
    (by intro name premise; exact premise) initial (fun _ => 0)
  have start : install dataTapes (frame parameterRegister [] (bits registers) [] old) initial = initial := by
    rw [← initialLocal, install_self]
  have positions : install dataTapes (fun _ : Fin 3 => (0 : ℤ))
      (fun _ : Sum Parameter (Fin 3) => (0 : ℤ)) = fun _ => 0 := install_self _ _
  rw [start, positions] at trace
  let output : Outputs (domains parameterDomain elementDomain length) argumentReadOnly assignment := fun name => by
    rcases name with ⟨name, writable⟩
    cases name with
    | inl parameter => contradiction
    | inr name =>
      have isResult : name = 2 := by fin_cases name <;> first | rfl | contradiction
      subst name
      exact result
  refine ⟨ticks, output, _, ?_, trace, rfl, ?_⟩
  · simp only [map_add, map_mul, MvPolynomial.eval_C, map_ofNat]
    simp only [bits_length, count] at cost
    exact cost.trans_eq (by ring)
  · intro name writable
    cases name with
    | inl parameter => contradiction
    | inr name =>
      fin_cases name
      · contradiction
      · contradiction
      · change install dataTapes _ initial (dataTapes 2) = _
        rw [install_at]
        change buffer (word (bits (mapped table parameterRegister registers))) = _
        rw [mappedCorrect]
        exact (arrayBits elementDomain length assignment result).symm

end Polytime2.StandardArrayMap
