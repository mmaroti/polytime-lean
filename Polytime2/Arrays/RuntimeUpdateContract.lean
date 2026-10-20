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

import Polytime2.Encoding.Records

import Polytime2.Arrays.RuntimeUpdate
import Polytime2.Computation.Width

/-! # Polynomial-width encoded array update with a prepared unary header -/

namespace Polytime2.RuntimeArrayUpdate

open MultiTape CallingConvention
open Binary (Symbol word data value)

universe parameterLevel
variable {Parameter : Type parameterLevel} [Fintype Parameter]

/-- Index, array, replacement, result, counters, guard, and unary width. -/
noncomputable def domainsSized (element : EncodedDomain.{parameterLevel, 0} Parameter)
    (indexDomain : EncodedDomain.{parameterLevel, 0} Parameter) (length : MvPolynomial Parameter ℕ) :
    Parameter ⊕ Fin 8 → EncodedDomain.{parameterLevel, 0} Parameter
  | .inl parameter => EncodedDomain.unary parameter
  | .inr name => if name = 0 then indexDomain else if name = 1 ∨ name = 3 then element.arrayOfLength length
      else if name = 2 then element
      else if name = 6 then EncodedDomain.booleans
      else if name = 7 then EncodedDomain.unaryOfLength element.widthPolynomial
      else EncodedDomain.bitVectors indexDomain.widthPolynomial

def argumentReadOnly : Parameter ⊕ Fin 8 → Bool
  | .inl _ => true
  | .inr name => readOnly name

def sizeTapes : Parameter ↪ Parameter ⊕ Fin 8 := Function.Embedding.inl

def dataTapes : Fin 8 ↪ Parameter ⊕ Fin 8 := Function.Embedding.inr

def outputTapes : Unit ↪ Parameter ⊕ Fin 8 := oneTape (.inr 3)

noncomputable def algorithmSized : Machine (CallingConvention.Alphabet (Parameter ⊕ Fin 8)) State :=
  MultiTape.wire dataTapes machine

/-- An in-range update returns a separate array with one coordinate replaced. -/
theorem contractSized (element : EncodedDomain.{parameterLevel, 0} Parameter)
    (indexDomain : EncodedDomain.{parameterLevel, 0} Parameter) (length : MvPolynomial Parameter ℕ) (toNat : ∀ sizes, indexDomain.Carrier sizes → ℕ)
    (value_encode : ∀ sizes index, value (EncodedDomain.ArrayEncoding.bits (indexDomain.encode sizes index)) = toNat sizes index) :
    CallingConvention.Realizes (domainsSized element indexDomain length)
      argumentReadOnly sizeTapes outputTapes algorithmSized entry exit
      (fun sizes input =>
        toNat sizes (input ⟨.inr 0, rfl⟩) < MvPolynomial.eval sizes length)
      (fun sizes input output => ∃ within : toNat sizes (input ⟨.inr 0, rfl⟩) < MvPolynomial.eval sizes length,
        output () = Function.update (input ⟨.inr 1, rfl⟩)
          ⟨toNat sizes (input ⟨.inr 0, rfl⟩), within⟩ (input ⟨.inr 2, rfl⟩)) := by
  refine ⟨(by intro parameter; rfl), (by intro name; rfl),
    (by intro symbols; simp [algorithmSized, MultiTape.wire]),
    length * (6 * indexDomain.widthPolynomial + 5 * element.widthPolynomial + 16) +
      6 * indexDomain.widthPolynomial + 3 * element.widthPolynomial + 20, ?_⟩
  intro sizes input initial valid represented headers
  let indexValue : indexDomain.Carrier sizes := input ⟨.inr 0, rfl⟩
  let index := EncodedDomain.ArrayEncoding.bits (indexDomain.encode sizes indexValue)
  let array : (element.arrayOfLength length).Carrier sizes := input ⟨.inr 1, rfl⟩
  let replacement : element.Carrier sizes := input ⟨.inr 2, rfl⟩
  have indexLength : index.length = indexDomain.width sizes := List.length_ofFn
  have indexValueEq : value index = toNat sizes indexValue := value_encode sizes indexValue
  have within : value index < MvPolynomial.eval sizes length := by rw [indexValueEq]; exact valid
  obtain ⟨oldOutput, outputLength, outputEq⟩ := represented.2 (.inr 3) rfl
  obtain ⟨oldCounter, counterLength, counterEq⟩ := represented.2 (.inr 4) rfl
  obtain ⟨scratch, scratchLength, scratchEq⟩ := represented.2 (.inr 5) rfl
  obtain ⟨flags, flagLength, flagEq⟩ := represented.2 (.inr 6) rfl
  norm_num [domainsSized, EncodedDomain.booleans, EncodedDomain.fixed, EncodedDomain.ofCodec] at flagLength
  obtain ⟨flag, rfl⟩ := List.length_eq_one_iff.mp flagLength
  change oldOutput.length = (element.arrayOfLength length).width sizes at outputLength
  simp [domainsSized, EncodedDomain.bitVectors] at counterLength scratchLength
  have indexEq : initial (.inr 0) = buffer (word index) :=
    (represented.1 (.inr 0) rfl)
  have arrayEq : initial (.inr 1) = encoded (element.arrayOfLength length) sizes array := represented.1 (.inr 1) rfl
  have replacementEq : initial (.inr 2) = encoded element sizes replacement := represented.1 (.inr 2) rfl
  have markerEq : initial (.inr 7) = unary (element.width sizes) := by
    have marker := represented.1 (.inr 7) rfl
    change initial (.inr 7) = encoded (EncodedDomain.unaryOfLength element.widthPolynomial) sizes _ at marker
    cases input ⟨.inr 7, rfl⟩
    exact marker.trans (EncodedDomain.encoded_unaryOfLength element.widthPolynomial sizes)
  obtain ⟨ticks, cost, localTrace⟩ := encoded_runsOfLength element length sizes index within array replacement
    oldOutput oldCounter scratch outputLength (counterLength.trans indexLength.symm)
    (scratchLength.trans indexLength.symm) flag
  have trace := localTrace.wire dataTapes
    (fun name => (domainsSized element indexDomain length name).width sizes) argumentReadOnly
    (by
      intro name
      change (domainsSized element indexDomain length (.inr name)).width sizes = _
      fin_cases name <;> norm_num [domainsSized, widths, ArrayUpdate.widths,
        ArrayBlockCopy.widths, ArrayUpdate.insertSource, Fin.insertNth,
        Fin.succAboveCases, Equiv.swap_apply_def, EncodedDomain.arrayOfLength,
        EncodedDomain.bitVectors, EncodedDomain.booleans, EncodedDomain.fixed,
        indexLength, EncodedDomain.unaryOfLength, EncodedDomain.width])
    (by intro name premise; exact premise) initial (fun _ => 0)
  have start : install dataTapes
      (initialFrame (element.width sizes) index
        (EncodedDomain.ArrayEncoding.bits ((element.arrayOfLength length).encode sizes array))
        (word (EncodedDomain.ArrayEncoding.bits (element.encode sizes replacement)))
        oldOutput oldCounter scratch flag) initial = initial := by
    funext name
    cases name with
    | inl parameter =>
      apply install_outside
      rintro ⟨name, equal⟩
      cases equal
    | inr name =>
      rw [show Sum.inr name = dataTapes name from rfl, install_at]
      fin_cases name
      · exact indexEq.symm
      · exact arrayEq.symm
      · exact replacementEq.symm
      · exact outputEq.symm
      · exact counterEq.symm
      · exact scratchEq.symm
      · exact flagEq.symm
      · exact markerEq.symm
  have positions : install dataTapes (fun _ : Fin 8 => (0 : ℤ))
      (fun _ : Parameter ⊕ Fin 8 => (0 : ℤ)) = fun _ => 0 := install_self dataTapes _
  rw [start, positions] at trace
  let updated := Function.update array ⟨value index, within⟩ replacement
  let output : Outputs (domainsSized element indexDomain length) outputTapes sizes := fun _ => updated
  refine ⟨ticks, output, _, ?_, trace, ?_, ?_⟩
  · simp only [map_add, map_mul, map_ofNat]
    simpa only [indexLength, Nat.add_assoc, EncodedDomain.width] using cost
  · refine ⟨valid, ?_⟩
    have equalIndex : (⟨value index, within⟩ : Fin (MvPolynomial.eval sizes length)) =
        ⟨toNat sizes indexValue, valid⟩ := Fin.ext indexValueEq
    exact congrArg (fun selected => Function.update array selected replacement) equalIndex
  · intro name; cases name
    change install dataTapes _ initial (dataTapes 3) = _
    rw [install_at]
    rfl

end Polytime2.RuntimeArrayUpdate
