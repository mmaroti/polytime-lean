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

import Polytime2.Arrays.RuntimeLookup
import Polytime2.Computation.Width

/-! # Polynomial-length encoded array lookup

The array length is a polynomial expression in the unary size inputs. -/

namespace Polytime2.RuntimeArrayLookup


open MultiTape CallingConvention
open Binary (Symbol word data value)

-- parameterLevel: unary size-parameter names; carrierLevel: array elements.
universe parameterLevel
variable {Parameter : Type parameterLevel} [Fintype Parameter]

/-- Encoded domains determine fixed tape widths, including private scratch. -/
noncomputable def domainsSized (element : EncodedDomain.{parameterLevel, 0} Parameter)
    (indexCapacity : Parameter) (length : MvPolynomial Parameter ℕ) :
    Sum Parameter (Fin 7) → EncodedDomain.{parameterLevel, 0} Parameter
  | .inl parameter => EncodedDomain.unary parameter
  | .inr name => if name = 1 then element.arrayOfLength length
      else if name = 2 then element
      else if name = 5 then EncodedDomain.booleans
      else if name = 6 then EncodedDomain.unaryOfLength element.widthPolynomial
      else EncodedDomain.binaryNaturals indexCapacity

def argumentReadOnly : Sum Parameter (Fin 7) → Bool
  | .inl _ => true
  | .inr name => RuntimeArrayLookup.readOnly name

def sizeTapes : Parameter ↪ Sum Parameter (Fin 7) :=
  ⟨Sum.inl, by intro first second equal; cases equal; rfl⟩

def dataTapes : Fin 7 ↪ Sum Parameter (Fin 7) :=
  ⟨Sum.inr, by intro first second equal; cases equal; rfl⟩

def outputTapes : Unit ↪ Sum Parameter (Fin 7) := oneTape (.inr 2)

noncomputable def algorithmSized :
    Machine (CallingConvention.Alphabet (Sum Parameter (Fin 7)))
      RuntimeArrayLookup.State :=
  MultiTape.wire dataTapes RuntimeArrayLookup.machine

/-- An in-range binary index returns the corresponding mathematical element.
Private scratch need not encode valid values on return. -/
theorem contractSized (element : EncodedDomain.{parameterLevel, 0} Parameter)
    (indexCapacity : Parameter)
    (length : MvPolynomial Parameter ℕ) :
    CallingConvention.Realizes (domainsSized element indexCapacity length)
      argumentReadOnly sizeTapes outputTapes algorithmSized
      RuntimeArrayLookup.entry RuntimeArrayLookup.exit
      (fun assignment input =>
        (input ⟨.inr 0, rfl⟩ : Fin (2 ^ assignment indexCapacity)).val <
          MvPolynomial.eval assignment length)
      (fun assignment input output => ∃ within : (input ⟨.inr 0, rfl⟩).val < MvPolynomial.eval assignment length,
        output () = input ⟨.inr 1, rfl⟩ ⟨(input ⟨.inr 0, rfl⟩).val, within⟩) := by
  refine ⟨(by intro parameter; rfl), (by intro name; rfl), (by intro symbols; simp [algorithmSized,
    MultiTape.wire, RuntimeArrayLookup.halt]),
    length * (6 * MvPolynomial.X indexCapacity + 3 * element.widthPolynomial + 16) +
      6 * MvPolynomial.X indexCapacity + 3 * element.widthPolynomial + 17, ?_⟩
  intro assignment input initial valid represented sizes
  let indexValue : Fin (2 ^ assignment indexCapacity) := input ⟨.inr 0, rfl⟩
  let index := EncodedDomain.ArrayEncoding.bits (BitVec.ofFin indexValue)
  let array : (element.arrayOfLength length).Carrier assignment := input ⟨.inr 1, rfl⟩
  have indexLength : index.length = assignment indexCapacity := List.length_ofFn
  have indexValueEq : value index = indexValue.val := Binary.value_bits (BitVec.ofFin indexValue)
  have within : value index < MvPolynomial.eval assignment length := by rw [indexValueEq]; exact valid
  obtain ⟨oldElement, elementLength, elementEq⟩ := represented.2 (.inr 2) rfl
  obtain ⟨oldCounter, counterLength, counterEq⟩ := represented.2 (.inr 3) rfl
  obtain ⟨scratch, scratchLength, scratchEq⟩ := represented.2 (.inr 4) rfl
  obtain ⟨flags, flagLength, flagEq⟩ := represented.2 (.inr 5) rfl
  norm_num [domainsSized, EncodedDomain.booleans, EncodedDomain.fixed, EncodedDomain.ofCodec] at flagLength
  obtain ⟨flag, rfl⟩ := List.length_eq_one_iff.mp flagLength
  change oldElement.length = element.width assignment at elementLength
  simp [domainsSized, EncodedDomain.binaryNaturals, EncodedDomain.ofCodec] at counterLength scratchLength
  have indexEq : initial (.inr 0) = buffer (word index) :=
    (represented.1 (.inr 0) rfl).trans (encoded_binaryNaturals_value indexCapacity assignment _)
  have arrayEq : initial (.inr 1) = encoded (element.arrayOfLength length) assignment array := represented.1 (.inr 1) rfl
  have markerEq : initial (.inr 6) = unary (element.width assignment) := by
    have marker := represented.1 (.inr 6) rfl
    change initial (.inr 6) = encoded (EncodedDomain.unaryOfLength element.widthPolynomial) assignment _ at marker
    cases input ⟨.inr 6, rfl⟩
    exact marker.trans (EncodedDomain.encoded_unaryOfLength element.widthPolynomial assignment)
  obtain ⟨ticks, cost, localTrace⟩ := encoded_runsOfLength element length assignment index within array oldElement oldCounter scratch elementLength (counterLength.trans indexLength.symm)
    (scratchLength.trans indexLength.symm) flag
  have trace := localTrace.wire dataTapes
    (fun name => (domainsSized element indexCapacity length name).width assignment)
    argumentReadOnly
    (by
      intro name
      change (domainsSized element indexCapacity length (.inr name)).width assignment = _
      fin_cases name <;> norm_num [domainsSized, widths, RuntimeArrayBlockCopy.widths, ArrayBlockCopy.widths, EncodedDomain.arrayOfLength,
        EncodedDomain.binaryNaturals, EncodedDomain.booleans, EncodedDomain.fixed,
        indexLength, EncodedDomain.unaryOfLength])
    (by intro name premise; exact premise) initial (fun _ => 0)
  have start : install dataTapes
      (initialFrame (element.width assignment) index (EncodedDomain.ArrayEncoding.bits ((element.arrayOfLength length).encode assignment array))
        oldElement oldCounter scratch flag) initial = initial := by
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
      · exact elementEq.symm
      · exact counterEq.symm
      · exact scratchEq.symm
      · exact flagEq.symm
      · exact markerEq.symm
  have positions : install dataTapes (fun _ : Fin 7 => (0 : ℤ))
      (fun _ : Sum Parameter (Fin 7) => (0 : ℤ)) = fun _ => 0 := install_self dataTapes _
  rw [start, positions] at trace
  let selected := array ⟨value index, within⟩
  let output : Outputs (domainsSized element indexCapacity length) outputTapes assignment :=
    fun _ => selected
  refine ⟨ticks, output, _, ?_, trace, ?_, ?_⟩
  · simp only [map_add, map_mul, map_ofNat, MvPolynomial.eval_X]
    simpa only [indexLength, Nat.add_assoc, EncodedDomain.width] using cost
  · refine ⟨valid, ?_⟩
    have equalIndex : (⟨value index, within⟩ : Fin (MvPolynomial.eval assignment length)) =
        ⟨indexValue.val, valid⟩ := Fin.ext indexValueEq
    exact congrArg array equalIndex
  · intro name
    cases name
    change install dataTapes _ initial (dataTapes 2) = _
    rw [install_at]
    rfl

end Polytime2.RuntimeArrayLookup
