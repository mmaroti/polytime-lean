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

import Polytime2.StandardArrayLookupContract

/-! # Polynomial-length encoded array lookup

The array length is a polynomial expression in the unary size inputs. -/

namespace Polytime2.StandardArrayLookupSized

open Polytime2.StandardArrayLookup

open MultiTape CallingConvention
open Binary (Symbol word data value)

-- parameterLevel: unary size-parameter names; carrierLevel: array elements.
universe parameterLevel
variable {Parameter : Type parameterLevel} [Fintype Parameter]

/-- Every tape carries a mathematical encoded value, including private scratch. -/
def domainsSized (element : EncodedDomain.{parameterLevel, 0} Parameter)
    (indexCapacity : Parameter) (length : MvPolynomial Parameter ℕ) :
    Sum Parameter (Fin 6) → EncodedDomain.{parameterLevel, 0} Parameter
  | .inl parameter => EncodedDomain.unary parameter
  | .inr name => if name = 1 then element.arrayOfLength length
      else if name = 2 then element
      else if name = 5 then EncodedDomain.booleans
      else EncodedDomain.binaryNaturals indexCapacity

def argumentReadOnly : Sum Parameter (Fin 6) → Bool
  | .inl _ => true
  | .inr name => StandardArrayLookup.readOnly name

def sizeTapes : Parameter ↪ Sum Parameter (Fin 6) :=
  ⟨Sum.inl, by intro first second equal; cases equal; rfl⟩

def dataTapes : Fin 6 ↪ Sum Parameter (Fin 6) :=
  ⟨Sum.inr, by intro first second equal; cases equal; rfl⟩

noncomputable def algorithmSized (elementWidth : ℕ) :
    Machine (CallingConvention.Alphabet (Sum Parameter (Fin 6)))
      (StandardArrayLookup.State elementWidth) :=
  MultiTape.wire dataTapes (StandardArrayLookup.machine elementWidth)

/-- An in-range binary index returns the corresponding mathematical element.
All scratch domains are valid on return, including for zero-bit elements. -/
theorem contractSized (element : EncodedDomain.{parameterLevel, 0} Parameter)
    (elementWidth : ℕ) (indexCapacity : Parameter)
    (length : MvPolynomial Parameter ℕ)
    (fixedWidth : ∀ assignment, element.width assignment = elementWidth) :
    CallingConvention.Realizes (domainsSized element indexCapacity length)
      argumentReadOnly sizeTapes (algorithmSized elementWidth)
      (StandardArrayLookup.entry elementWidth) (StandardArrayLookup.exit elementWidth)
      (fun assignment input =>
        (input ⟨.inr 0, rfl⟩ : Fin (2 ^ assignment indexCapacity)).val <
          MvPolynomial.eval assignment length)
      (fun assignment input output => ∃ within : (input ⟨.inr 0, rfl⟩).val < MvPolynomial.eval assignment length,
        output ⟨.inr 2, rfl⟩ = input ⟨.inr 1, rfl⟩ ⟨(input ⟨.inr 0, rfl⟩).val, within⟩) := by
  refine ⟨(by intro parameter; rfl), (by intro symbols; simp [algorithmSized,
    MultiTape.wire, StandardArrayLookup.halt]),
    length * (6 * MvPolynomial.X indexCapacity + MvPolynomial.C (2 * elementWidth + 11)) +
      6 * MvPolynomial.X indexCapacity + MvPolynomial.C (2 * elementWidth + 15), ?_⟩
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
  change flags.length = 1 at flagLength
  obtain ⟨flag, rfl⟩ := List.length_eq_one_iff.mp flagLength
  change oldElement.length = element.width assignment at elementLength
  change oldCounter.length = assignment indexCapacity at counterLength
  change scratch.length = assignment indexCapacity at scratchLength
  have indexEq : initial (.inr 0) = buffer (word index) := represented.1 (.inr 0) rfl
  have arrayEq : initial (.inr 1) = encoded (element.arrayOfLength length) assignment array := represented.1 (.inr 1) rfl
  obtain ⟨ticks, cost, localTrace⟩ := encoded_runsOfLength element length assignment index within array oldElement oldCounter scratch elementLength (counterLength.trans indexLength.symm)
    (scratchLength.trans indexLength.symm) flag
  have chosenWidth := fixedWidth assignment
  subst elementWidth
  have trace := localTrace.wire dataTapes
    (fun name => (domainsSized element indexCapacity length name).width assignment)
    argumentReadOnly
    (by
      intro name
      change (domainsSized element indexCapacity length (.inr name)).width assignment = _
      fin_cases name <;> norm_num [domainsSized, widths, EncodedDomain.arrayOfLength,
        EncodedDomain.binaryNaturals, EncodedDomain.booleans, EncodedDomain.fixed,
        indexLength])
    (by intro name premise; exact premise) initial (fun _ => 0)
  have start : install dataTapes
      (initialFrame index (EncodedDomain.ArrayEncoding.bits ((element.arrayOfLength length).encode assignment array))
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
  have positions : install dataTapes (fun _ : Fin 6 => (0 : ℤ))
      (fun _ : Sum Parameter (Fin 6) => (0 : ℤ)) = fun _ => 0 := install_self dataTapes _
  rw [start, positions] at trace
  let selected := array ⟨value index, within⟩
  let zeroValue : Fin (2 ^ assignment indexCapacity) :=
    ⟨value (List.replicate (assignment indexCapacity) false),
    by simpa only [List.length_replicate] using
      Binary.value_lt_pow_length (List.replicate (assignment indexCapacity) false)⟩
  let output : Outputs (domainsSized element indexCapacity length)
      argumentReadOnly assignment := fun name => by
    rcases name with ⟨name, writable⟩
    cases name with
    | inl parameter => contradiction
    | inr name =>
      by_cases arrayTape : name = 1
      · subst name; contradiction
      · by_cases resultTape : name = 2
        · subst name; exact selected
        · by_cases flagTape : name = 5
          · subst name; exact false
          · change (domainsSized element indexCapacity length (.inr name)).Carrier assignment
            simp only [domainsSized, arrayTape, resultTape, flagTape, ite_false]
            exact zeroValue
  refine ⟨ticks, output, _, ?_, trace, ?_, ?_⟩
  · simp only [map_add, map_mul, map_ofNat, MvPolynomial.eval_X, MvPolynomial.eval_C]
    simpa only [indexLength, Nat.add_assoc] using cost
  · refine ⟨valid, ?_⟩
    have equalIndex : (⟨value index, within⟩ : Fin (MvPolynomial.eval assignment length)) =
        ⟨indexValue.val, valid⟩ := Fin.ext indexValueEq
    exact congrArg array equalIndex
  · intro name writable
    cases name with
    | inl parameter => contradiction
    | inr name =>
      change install dataTapes _ initial (dataTapes name) = _
      rw [install_at]
      fin_cases name
      · contradiction
      · contradiction
      · rfl
      · simp only [frame]
        change buffer (word (List.replicate index.length false)) =
          encoded (EncodedDomain.binaryNaturals indexCapacity) assignment zeroValue
        rw [indexLength]
        exact (encoded_binaryNaturals indexCapacity assignment
          (List.replicate (assignment indexCapacity) false) List.length_replicate).symm
      · simp only [frame]
        change buffer (word (List.replicate index.length false)) =
          encoded (EncodedDomain.binaryNaturals indexCapacity) assignment zeroValue
        rw [indexLength]
        exact (encoded_binaryNaturals indexCapacity assignment
          (List.replicate (assignment indexCapacity) false) List.length_replicate).symm
      · exact (encoded_booleans assignment false).symm

end Polytime2.StandardArrayLookupSized
