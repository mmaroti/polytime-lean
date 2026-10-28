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

import Polytime2.Arrays.PrefixCount
import Polytime2.Computation.ComputedSizes

/-! # Certified source-coordinate arrays for shared stable packing -/

namespace Polytime2.EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

/-- Mathematical positions with the canonical word width used by prefix counts.
The extra bit is derived from the array length, not a caller capacity. -/
noncomputable def arrayPosition (length : MvPolynomial Parameter ℕ) : EncodedDomain Parameter :=
  boundedIndexOfWidth (fun sizes => MvPolynomial.eval sizes length) (length + 1)
    (by intro sizes; simp only [map_add, map_one]; exact
      (Nat.le_succ _).trans Nat.lt_two_pow_self.le)

/-- The derived position codec stores the ordinary numeric coordinate. -/
theorem arrayPosition_value (length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (index : (arrayPosition length).Carrier sizes) :
    Binary.value (ArrayEncoding.bits ((arrayPosition length).encode sizes index)) = index.val :=
  boundedIndexOfWidth_value _ _ _ sizes index

/-- Coordinate arithmetic can reuse the canonical unsigned word at the same
derived width. Only the mathematical carrier bound changes. -/
theorem arrayPosition_binary_bits (length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (coordinate : (arrayPosition length).Carrier sizes)
    (word : (binaryNaturalsOfWidth (length + 1)).Carrier sizes) (equal : word.val = coordinate.val) :
    ArrayEncoding.bits ((arrayPosition length).encode sizes coordinate) =
      ArrayEncoding.bits ((binaryNaturalsOfWidth (length + 1)).encode sizes word) := by
  change Fin (MvPolynomial.eval sizes length) at coordinate
  change Fin (2 ^ MvPolynomial.eval sizes (length + 1)) at word
  simp [arrayPosition, boundedIndexOfWidth, binaryNaturalsOfWidth, BitVec.ofNatLT_eq_ofNat, equal]
  funext index
  simp [BitVec.getLsbD_ofNat]
  have widthEval : MvPolynomial.eval sizes (length + 1) = MvPolynomial.eval sizes length + 1 := by simp
  have indexBound := index.isLt
  omega

end Polytime2.EncodedDomain

namespace Polytime2.Computation

variable {Parameter : Type} [Fintype Parameter]

/-- Construct an all-true Boolean array at the mathematical length. -/
noncomputable def arrayTrue (length : MvPolynomial Parameter ℕ) : Computation Parameter Empty where
  inputDomains := Empty.elim
  outputDomain := EncodedDomain.booleans.arrayOfLength length
  precondition _ _ := True
  compute _ _ := fun _ => true

theorem arrayTrue_realizable (length : MvPolynomial Parameter ℕ) : (arrayTrue length).Realizable := by
  exact (polynomialUnarySize_realizable length).withEncodedOutput
    (EncodedDomain.booleans.arrayOfLength length) (fun _ _ => fun _ => true) (by
      intro sizes
      simp [polynomialUnarySize, EncodedDomain.boundedUnary, EncodedDomain.arrayOfLength, EncodedDomain.booleans,
        EncodedDomain.fixed, EncodedDomain.ofCodec, show Nat.clog 2 2 = 1 by decide]) (by
      intro sizes arguments
      apply congrArg CallingConvention.tape
      change EncodedDomain.ArrayEncoding.bits
        ((EncodedDomain.booleans.arrayOfLength length).encode sizes (fun _ => true)) =
          EncodedDomain.ArrayEncoding.bits (BoundedUnary.encode _ (Fin.last _))
      rw [FirstFalse.boolean_bits, BoundedUnary.encode_bits]
      simp [BoundedUnary.bits, polynomialUnarySize, EncodedDomain.boundedUnary])

/-- Original positions, encoded with enough bits for every source coordinate.
Packing this array records the inverse of the shared source-to-dense table. -/
noncomputable def arrayIndices (length : MvPolynomial Parameter ℕ) : Computation Parameter Empty where
  inputDomains := Empty.elim
  outputDomain := (EncodedDomain.bitVectors (length + 1)).arrayOfLength length
  precondition _ _ := True
  compute sizes _ := fun index => BitVec.ofNat (MvPolynomial.eval sizes (length + 1)) index.val

theorem arrayIndices_realizable (length : MvPolynomial Parameter ℕ) :
    (arrayIndices length).Realizable := by
  have flags := arrayTrue_realizable length
  have counted := flags.followedBy (prefixCounts_realizable length) rfl (by intros; trivial)
  exact counted.withSpecification (fun _ _ => True) (arrayIndices length).compute (by intros; trivial) (by
    intro sizes arguments valid
    funext index
    change BitVec.ofNat _ (((List.ofFn (fun _ : Fin (MvPolynomial.eval sizes length) => true)).take index.val).count true) =
      BitVec.ofNat _ index.val
    congr 1
    simp)

/-- Enumerate the ordinary coordinates of an array, including an empty array. -/
noncomputable def arrayPositions (length : MvPolynomial Parameter ℕ) : Computation Parameter Empty where
  inputDomains := Empty.elim
  outputDomain := (EncodedDomain.arrayPosition length).arrayOfLength length
  precondition _ _ := True
  compute _ _ := id

theorem arrayPositions_realizable (length : MvPolynomial Parameter ℕ) :
    (arrayPositions length).Realizable := by
  have capacity (sizes : Parameter → ℕ) (index : Fin (MvPolynomial.eval sizes length)) :
      index.val < 2 ^ MvPolynomial.eval sizes (length + 1) := by
    simp only [map_add, map_one]
    exact index.isLt.trans_le ((Nat.le_succ _).trans Nat.lt_two_pow_self.le)
  have refined := (arrayIndices_realizable length).refineOutput
    (fun sizes values => ∀ index, (values index).toNat < MvPolynomial.eval sizes length) (by
      intro sizes arguments index
      change (BitVec.ofNat (MvPolynomial.eval sizes (length + 1)) index.val).toNat < _
      simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (capacity sizes index)] using index.isLt)
  have converted := refined.reinterpretOutput ((EncodedDomain.arrayPosition length).arrayOfLength length)
    (fun _ values index => ⟨(values.val index).toNat, values.property index⟩)
    (by intros; rfl) (by
      intro sizes values
      change {values : Fin (MvPolynomial.eval sizes length) →
        BitVec (MvPolynomial.eval sizes (length + 1)) //
          ∀ index, (values index).toNat < MvPolynomial.eval sizes length} at values
      change EncodedDomain.ArrayEncoding.bits
          (((EncodedDomain.arrayPosition length).arrayOfLength length).encode sizes
            (fun index => ⟨(values.val index).toNat, values.property index⟩)) =
        EncodedDomain.ArrayEncoding.bits
          (((EncodedDomain.bitVectors (length + 1)).arrayOfLength length).encode sizes values.val)
      erw [EncodedDomain.arrayOfLength_encode_bits, EncodedDomain.arrayOfLength_encode_bits]
      change EncodedDomain.ArrayEncoding.bits
          (EncodedDomain.ArrayEncoding.encode
            (fun index : Fin (MvPolynomial.eval sizes length) =>
              BitVec.ofNatLT index.val (capacity sizes index))
            (MvPolynomial.eval sizes length)
            (fun index => ⟨(values.val index).toNat, values.property index⟩)) =
        EncodedDomain.ArrayEncoding.bits
          (EncodedDomain.ArrayEncoding.encode id (MvPolynomial.eval sizes length) values.val)
      rw [EncodedDomain.ArrayEncoding.bits_encode, EncodedDomain.ArrayEncoding.bits_encode]
      apply congrArg List.flatten
      apply congrArg List.ofFn
      funext index
      change EncodedDomain.ArrayEncoding.bits (BitVec.ofNatLT (values.val index).toNat _) =
        EncodedDomain.ArrayEncoding.bits (values.val index)
      rw [BitVec.ofNatLT_toNat])
  exact converted.withSpecification (fun _ _ => True) (arrayPositions length).compute
    (by intros; trivial) (by
      intro sizes arguments valid
      funext index
      apply Fin.ext
      change (BitVec.ofNat (MvPolynomial.eval sizes (length + 1)) index.val).toNat = index.val
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (capacity sizes index)])

end Polytime2.Computation
