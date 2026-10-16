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

import Polytime2.StandardRowCombine

/-! # Mathematical contracts for finite row-entry operations -/

namespace Polytime2.StandardRowCombine

open MultiTape CallingConvention
open Binary (word)

-- carrierLevel: the mathematical scalar carrier fixed by specialization.
universe carrierLevel

noncomputable def encodedTable (domain : EncodedDomain.{0, carrierLevel} Empty)
    (operation : ∀ sizes, domain.Carrier sizes → domain.Carrier sizes → domain.Carrier sizes →
      domain.Carrier sizes × domain.Carrier sizes) :
    Register (domain.width Empty.elim) → Register (domain.width Empty.elim) →
      Register (domain.width Empty.elim) → BitVec (domain.width Empty.elim) × BitVec (domain.width Empty.elim) :=
  fun coefficient source target =>
    match domain.decode Empty.elim (BitVec.ofNat _ (Binary.value (List.ofFn coefficient))),
      domain.decode Empty.elim (BitVec.ofNat _ (Binary.value (List.ofFn source))),
      domain.decode Empty.elim (BitVec.ofNat _ (Binary.value (List.ofFn target))) with
    | some coefficientValue, some sourceValue, some targetValue =>
      let result := operation Empty.elim coefficientValue sourceValue targetValue
      (domain.encode Empty.elim result.1, domain.encode Empty.elim result.2)
    | _, _, _ => (0, 0)

def domains (domain : EncodedDomain.{0, carrierLevel} Empty) : Fin 5 → EncodedDomain Empty := fun _ => domain

def sizeTapes : Empty ↪ Fin 5 := ⟨Empty.elim, by intro parameter; cases parameter⟩

/-- False and true name the first and second scalar results. -/
def outputTapes : Bool ↪ Fin 5 :=
  ⟨(fun | false => 3 | true => 4), by
    intro first second equal
    cases first <;> cases second <;> first | rfl | cases equal⟩

noncomputable def algorithm (domain : EncodedDomain.{0, carrierLevel} Empty)
    (operation : ∀ sizes, domain.Carrier sizes → domain.Carrier sizes → domain.Carrier sizes →
      domain.Carrier sizes × domain.Carrier sizes) : Machine Alphabet (State (domain.width Empty.elim)) :=
  machine (encodedTable domain operation)

/-- A fixed finite scalar presentation supports every row-entry table.
Both outputs start arbitrary and are valid encoded scalars on return. -/
theorem contract (domain : EncodedDomain.{0, carrierLevel} Empty)
    (operation : ∀ sizes, domain.Carrier sizes → domain.Carrier sizes → domain.Carrier sizes →
      domain.Carrier sizes × domain.Carrier sizes) :
    CallingConvention.Realizes (domains domain) readOnly sizeTapes outputTapes (algorithm domain operation) entry exit
      (fun _ _ => True)
      (fun sizes input output => (output false, output true) =
        operation sizes (input ⟨0, rfl⟩) (input ⟨1, rfl⟩) (input ⟨2, rfl⟩)) := by
  refine ⟨(by intro parameter; cases parameter), (by intro name; cases name <;> rfl), (by intro symbols; rfl),
    MvPolynomial.C (10 * domain.width Empty.elim + 10), ?_⟩
  intro sizes input initial valid represented sizeHeaders
  have sameSizes : sizes = (Empty.elim : Empty → ℕ) := Subsingleton.elim _ _
  subst sizes
  let coefficientValue : domain.Carrier Empty.elim := input ⟨0, rfl⟩
  let sourceValue : domain.Carrier Empty.elim := input ⟨1, rfl⟩
  let targetValue : domain.Carrier Empty.elim := input ⟨2, rfl⟩
  let coefficientCode := domain.encode Empty.elim coefficientValue
  let sourceCode := domain.encode Empty.elim sourceValue
  let targetCode := domain.encode Empty.elim targetValue
  let coefficientBits := List.ofFn (fun index : Fin (domain.width Empty.elim) => coefficientCode.getLsbD index.val)
  let sourceBits := List.ofFn (fun index : Fin (domain.width Empty.elim) => sourceCode.getLsbD index.val)
  let targetBits := List.ofFn (fun index : Fin (domain.width Empty.elim) => targetCode.getLsbD index.val)
  let result := operation Empty.elim coefficientValue sourceValue targetValue
  have coefficientRegisterEq : (fun index : Fin (domain.width Empty.elim) =>
      (coefficientBits[index.val]?).getD false) = fun index => coefficientCode.getLsbD index.val := by
    funext index
    simp [coefficientBits, index.isLt]
  have sourceRegisterEq : (fun index : Fin (domain.width Empty.elim) =>
      (sourceBits[index.val]?).getD false) = fun index => sourceCode.getLsbD index.val := by
    funext index
    simp [sourceBits, index.isLt]
  have targetRegisterEq : (fun index : Fin (domain.width Empty.elim) =>
      (targetBits[index.val]?).getD false) = fun index => targetCode.getLsbD index.val := by
    funext index
    simp [targetBits, index.isLt]
  have selected : encodedTable domain operation
      (fun index => (coefficientBits[index.val]?).getD false)
      (fun index => (sourceBits[index.val]?).getD false)
      (fun index => (targetBits[index.val]?).getD false) =
      (domain.encode Empty.elim result.1, domain.encode Empty.elim result.2) := by
    rw [coefficientRegisterEq, sourceRegisterEq, targetRegisterEq]
    simp only [encodedTable, Binary.value_bits, BitVec.ofNat_toNat, BitVec.setWidth_eq,
      coefficientCode, sourceCode, targetCode, result]
    rw [domain.decode_encode, domain.decode_encode, domain.decode_encode]
  obtain ⟨oldFirst, firstLength, firstEq⟩ := represented.2 3 rfl
  obtain ⟨oldSecond, secondLength, secondEq⟩ := represented.2 4 rfl
  have initialEq : initial = frame coefficientBits sourceBits targetBits oldFirst oldSecond := by
    funext name
    fin_cases name
    · exact represented.1 0 rfl
    · exact represented.1 1 rfl
    · exact represented.1 2 rfl
    · exact firstEq
    · exact secondEq
  let output : Outputs (domains domain) outputTapes Empty.elim
    | false => result.1
    | true => result.2
  have trace := runs (encodedTable domain operation) coefficientBits sourceBits targetBits
    List.length_ofFn List.length_ofFn List.length_ofFn oldFirst oldSecond firstLength secondLength
  dsimp only at trace
  rw [selected] at trace
  refine ⟨10 * domain.width Empty.elim + 10, output,
    frame coefficientBits sourceBits targetBits
      (word (List.ofFn (fun index : Fin (domain.width Empty.elim) =>
        (domain.encode Empty.elim result.1).getLsbD index.val)))
      (word (List.ofFn (fun index : Fin (domain.width Empty.elim) =>
        (domain.encode Empty.elim result.2).getLsbD index.val))), by simp, ?_, rfl, ?_⟩
  · rw [initialEq]
    exact trace
  · intro name
    cases name <;> rfl

end Polytime2.StandardRowCombine
