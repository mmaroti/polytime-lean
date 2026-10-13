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

import Polytime2.MultiplyAdd

/-! # Mathematical contract for binary multiply-add -/

namespace Polytime2.MultiplyAdd

open MultiTape CallingConvention
open Binary (data word value)

def domains : Sum Bool (Fin 9) → EncodedDomain Bool
  | .inl parameter => EncodedDomain.unary parameter
  | .inr name => if name = 4 ∨ name = 8 then EncodedDomain.booleans
      else EncodedDomain.binaryNaturals (decide (name = 5))

def argumentReadOnly : Sum Bool (Fin 9) → Bool
  | .inl _ => true
  | .inr name => readOnly name

def dataTapes : Fin 9 ↪ Sum Bool (Fin 9) :=
  ⟨Sum.inr, by intro first second equal; cases equal; rfl⟩

def sizeTapes : Bool ↪ Sum Bool (Fin 9) :=
  ⟨Sum.inl, by intro first second equal; cases equal; rfl⟩

noncomputable def algorithm : Machine (CallingConvention.Alphabet (Sum Bool (Fin 9))) State :=
  MultiTape.wire dataTapes machine

/-- A row-major address is computed with immutable operands, arbitrary writable
contents, and valid private scratch on return. The bound is inferred internally. -/
theorem contract : CallingConvention.Realizes domains argumentReadOnly sizeTapes algorithm entry exit
    (fun assignment input =>
      (input ⟨.inr 1, rfl⟩ : Fin (2 ^ assignment false)).val *
        (input ⟨.inr 5, rfl⟩ : Fin (2 ^ assignment true)).val +
        (input ⟨.inr 6, rfl⟩ : Fin (2 ^ assignment false)).val < 2 ^ assignment false)
    (fun assignment input output =>
      (output ⟨.inr 7, rfl⟩ : Fin (2 ^ assignment false)).val =
        (input ⟨.inr 1, rfl⟩ : Fin (2 ^ assignment false)).val *
          (input ⟨.inr 5, rfl⟩ : Fin (2 ^ assignment true)).val +
          (input ⟨.inr 6, rfl⟩ : Fin (2 ^ assignment false)).val) := by
  refine ⟨(by intro parameter; rfl), (by intro symbols; simp [algorithm, MultiTape.wire]),
    MvPolynomial.X true * (6 * MvPolynomial.X false + 14) + 8 * MvPolynomial.X false + 17, ?_⟩
  intro assignment input initial valid represented sizes
  let factor := List.ofFn (fun index : Fin (assignment false) =>
    (BitVec.ofFin (input ⟨.inr 1, rfl⟩)).getLsbD index.val)
  let multiplier := List.ofFn (fun index : Fin (assignment true) =>
    (BitVec.ofFin (input ⟨.inr 5, rfl⟩)).getLsbD index.val)
  let addend := List.ofFn (fun index : Fin (assignment false) =>
    (BitVec.ofFin (input ⟨.inr 6, rfl⟩)).getLsbD index.val)
  have factorLength : factor.length = assignment false := List.length_ofFn
  have multiplierLength : multiplier.length = assignment true := List.length_ofFn
  have addendLength : addend.length = assignment false := List.length_ofFn
  have factorValue : value factor = (input ⟨.inr 1, rfl⟩ : Fin (2 ^ assignment false)).val :=
    Binary.value_bits (BitVec.ofFin (input ⟨.inr 1, rfl⟩))
  have multiplierValue : value multiplier = (input ⟨.inr 5, rfl⟩ : Fin (2 ^ assignment true)).val :=
    Binary.value_bits (BitVec.ofFin (input ⟨.inr 5, rfl⟩))
  have addendValue : value addend = (input ⟨.inr 6, rfl⟩ : Fin (2 ^ assignment false)).val :=
    Binary.value_bits (BitVec.ofFin (input ⟨.inr 6, rfl⟩))
  obtain ⟨oldProduct, productLength, productEq⟩ := represented.2 (.inr 0) rfl
  obtain ⟨oldShifted, shiftedLength, shiftedEq⟩ := represented.2 (.inr 2) rfl
  obtain ⟨oldNext, nextLength, nextEq⟩ := represented.2 (.inr 3) rfl
  obtain ⟨oldResult, oldResultLength, resultEq⟩ := represented.2 (.inr 7) rfl
  obtain ⟨multiplyFlags, multiplyFlagLength, multiplyFlagEq⟩ := represented.2 (.inr 4) rfl
  obtain ⟨addFlags, addFlagLength, addFlagEq⟩ := represented.2 (.inr 8) rfl
  change multiplyFlags.length = 1 at multiplyFlagLength
  change addFlags.length = 1 at addFlagLength
  obtain ⟨multiplyFlag, rfl⟩ := List.length_eq_one_iff.mp multiplyFlagLength
  obtain ⟨addFlag, rfl⟩ := List.length_eq_one_iff.mp addFlagLength
  have factorEq : initial (.inr 1) = buffer (word factor) := represented.1 (.inr 1) rfl
  have multiplierEq : initial (.inr 5) = buffer (word multiplier) := represented.1 (.inr 5) rfl
  have addendEq : initial (.inr 6) = buffer (word addend) := represented.1 (.inr 6) rfl
  have sameLength : addend.length = factor.length := addendLength.trans factorLength.symm
  have productFits : oldProduct.length = factor.length := productLength.trans factorLength.symm
  have shiftedFits : oldShifted.length = factor.length := shiftedLength.trans factorLength.symm
  have nextFits : oldNext.length = factor.length := nextLength.trans factorLength.symm
  have resultFits : oldResult.length = factor.length := oldResultLength.trans factorLength.symm
  have capacity : value factor * value multiplier + value addend < 2 ^ factor.length := by
    rw [factorValue, multiplierValue, addendValue, factorLength]
    exact valid
  have trace := (runs factor multiplier addend sameLength oldProduct oldShifted oldNext oldResult
    productFits shiftedFits nextFits resultFits multiplyFlag addFlag capacity).wire dataTapes
    (fun name => (domains name).width assignment) argumentReadOnly
    (by
      intro name
      change (domains (.inr name)).width assignment = _
      fin_cases name <;> norm_num [domains, widths, factorLength, multiplierLength,
        EncodedDomain.booleans, EncodedDomain.fixed, EncodedDomain.binaryNaturals])
    (by intro name premise; exact premise) initial (fun _ => 0)
  have start : install dataTapes
      (frame factor multiplier addend oldProduct oldShifted oldNext oldResult multiplyFlag addFlag) initial = initial := by
    funext name
    cases name with
    | inl parameter =>
      apply install_outside
      rintro ⟨name, equal⟩
      cases equal
    | inr name =>
      rw [show Sum.inr name = dataTapes name from rfl, install_at]
      fin_cases name
      · exact productEq.symm
      · exact factorEq.symm
      · exact shiftedEq.symm
      · exact nextEq.symm
      · exact multiplyFlagEq.symm
      · exact multiplierEq.symm
      · exact addendEq.symm
      · exact resultEq.symm
      · exact addFlagEq.symm
  have positions : install dataTapes (fun _ : Fin 9 => (0 : ℤ))
      (fun _ : Sum Bool (Fin 9) => (0 : ℤ)) = fun _ => 0 := install_self dataTapes _
  rw [start, positions] at trace
  let productBits := product factor multiplier oldShifted oldNext multiplyFlag
  let resultBits := result factor multiplier addend oldShifted oldNext multiplyFlag
  have productBitsLength : productBits.length = assignment false :=
    (product_length factor multiplier oldShifted oldNext multiplyFlag shiftedFits nextFits).trans factorLength
  have resultBitsLength : resultBits.length = assignment false :=
    (result_length factor multiplier addend oldShifted oldNext multiplyFlag sameLength shiftedFits nextFits).trans factorLength
  let productNatural : Fin (2 ^ assignment false) := ⟨value productBits,
    by simpa only [productBitsLength] using Binary.value_lt_pow_length productBits⟩
  let resultNatural : Fin (2 ^ assignment false) := ⟨value resultBits,
    by simpa only [resultBitsLength] using Binary.value_lt_pow_length resultBits⟩
  let zeroNatural : Fin (2 ^ assignment false) := ⟨value (List.replicate (assignment false) false),
    by simpa only [List.length_replicate] using Binary.value_lt_pow_length (List.replicate (assignment false) false)⟩
  let output : Outputs domains argumentReadOnly assignment := fun name => by
    rcases name with ⟨name, writable⟩
    cases name with
    | inl parameter => contradiction
    | inr name =>
      by_cases flag : name = 4 ∨ name = 8
      · change (if name = 4 ∨ name = 8 then EncodedDomain.booleans
          else EncodedDomain.binaryNaturals (decide (name = 5))).Carrier assignment
        rw [ite_eq_left flag]
        exact false
      · by_cases source : name = 5
        · subst name; contradiction
        · change (if name = 4 ∨ name = 8 then EncodedDomain.booleans
            else EncodedDomain.binaryNaturals (decide (name = 5))).Carrier assignment
          rw [ite_eq_right flag]
          simp only [source, decide_false]
          exact if name = 0 then productNatural else if name = 7 then resultNatural else zeroNatural
  refine ⟨multiplier.length * (6 * factor.length + 14) + 8 * factor.length + 17, output,
    install dataTapes (frame factor multiplier addend (word productBits)
      (word (List.replicate factor.length false)) (word (List.replicate factor.length false))
      (word resultBits) (data false) (data false)) initial, ?_, trace, ?_, ?_⟩
  · simp only [map_add, map_mul, map_ofNat, MvPolynomial.eval_X, factorLength, multiplierLength]
    exact le_rfl
  · change value resultBits = _
    simpa only [factorValue, multiplierValue, addendValue] using result_value factor multiplier addend
      oldShifted oldNext multiplyFlag sameLength shiftedFits nextFits capacity
  · intro name writable
    cases name with
    | inl parameter => contradiction
    | inr name =>
      change install dataTapes _ initial (dataTapes name) = _
      rw [install_at]
      fin_cases name
      · exact (encoded_binaryNaturals false assignment productBits productBitsLength).symm
      · contradiction
      · change buffer (word (List.replicate factor.length false)) =
          encoded (EncodedDomain.binaryNaturals false) assignment zeroNatural
        rw [factorLength]
        exact (encoded_binaryNaturals false assignment (List.replicate (assignment false) false) List.length_replicate).symm
      · change buffer (word (List.replicate factor.length false)) =
          encoded (EncodedDomain.binaryNaturals false) assignment zeroNatural
        rw [factorLength]
        exact (encoded_binaryNaturals false assignment (List.replicate (assignment false) false) List.length_replicate).symm
      · exact (encoded_booleans assignment false).symm
      · contradiction
      · contradiction
      · exact (encoded_binaryNaturals false assignment resultBits resultBitsLength).symm
      · exact (encoded_booleans assignment false).symm

end Polytime2.MultiplyAdd
