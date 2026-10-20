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

import Polytime2.Encoding.EncodedDomain
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Canonical fixed-length arrays

Elements occupy consecutive equal-width blocks, with element zero first in
little-endian tape order. The element presentation remains opaque to callers.
-/

namespace Polytime2.EncodedDomain

-- parameterLevel: size names; carrierLevel: mathematical array elements.
universe parameterLevel carrierLevel
variable {Parameter : Type parameterLevel} [Fintype Parameter]

namespace ArrayEncoding

variable {Carrier : Type carrierLevel} {width : ℕ}

/-- Concatenate element encodings in increasing coordinate order. -/
def encode (element : Carrier → BitVec width) :
    (length : ℕ) → (Fin length → Carrier) → BitVec (length * width)
  | 0, _ => BitVec.ofNat _ 0
  | length + 1, values =>
    ((encode element length (Fin.tail values)) ++ element (values 0)).cast
      (Nat.succ_mul length width).symm

/-- Reject the array if any element block is invalid. -/
def decode (element : BitVec width → Option Carrier) :
    (length : ℕ) → BitVec (length * width) → Option (Fin length → Carrier)
  | 0, _ => some Fin.elim0
  | length + 1, bits => do
    let split := bits.cast (Nat.succ_mul length width)
    let first ← element (split.extractLsb' 0 width)
    let rest ← decode element length (split.extractLsb' width (length * width))
    pure (Fin.cons first rest)

theorem decode_encode (elementEncode : Carrier → BitVec width)
    (elementDecode : BitVec width → Option Carrier)
    (inverse : ∀ value, elementDecode (elementEncode value) = some value)
    (length : ℕ) (values : Fin length → Carrier) :
    decode elementDecode length (encode elementEncode length values) = some values := by
  induction length with
  | zero => simp [decode, Subsingleton.elim values Fin.elim0]
  | succ length hypothesis =>
    simp [encode, decode, BitVec.cast_cast,
      BitVec.extractLsb'_append_eq_left, BitVec.extractLsb'_append_eq_right,
      inverse, hypothesis]

theorem encode_decode (elementEncode : Carrier → BitVec width)
    (elementDecode : BitVec width → Option Carrier)
    (inverse : ∀ bits value, elementDecode bits = some value → elementEncode value = bits)
    (length : ℕ) (bits : BitVec (length * width)) (values : Fin length → Carrier)
    (accepted : decode elementDecode length bits = some values) :
    encode elementEncode length values = bits := by
  induction length with
  | zero => apply BitVec.eq_of_getLsbD_eq; intro index bounded; omega
  | succ length hypothesis =>
    simp only [decode, Bind.bind, Option.bind_eq_some_iff, Pure.pure, Option.some.injEq] at accepted
    obtain ⟨first, firstAccepted, rest, restAccepted, equality⟩ := accepted
    cases equality
    simp only [encode, Fin.tail_cons, Fin.cons_zero]
    rw [inverse _ _ firstAccepted, hypothesis _ _ restAccepted]
    simp [BitVec.extractLsb'_append_extractLsb', BitVec.cast_cast]

/-- The bit order used by the tape controllers. -/
abbrev bits {width : ℕ} (value : BitVec width) : List Bool :=
  List.ofFn (fun index : Fin width => value.getLsbD index.val)

/-- Canonical bit lists determine their bit vectors. -/
theorem bits_injective {width : ℕ} : Function.Injective (bits : BitVec width → List Bool) := by
  intro first second equal
  apply BitVec.eq_of_getLsbD_eq
  intro index within
  have entry := congrArg (fun values : List Bool => values[index]?) equal
  simpa only [bits, List.getElem?_ofFn, within, dite_true, Option.some.injEq] using entry

/-- Resizing equal canonical words preserves equality, regardless of their
original vector widths. -/
theorem bits_setWidth_congr {firstWidth secondWidth capacity : ℕ}
    {first : BitVec firstWidth} {second : BitVec secondWidth}
    (equal : bits first = bits second) : bits (first.setWidth capacity) = bits (second.setWidth capacity) := by
  have widths : firstWidth = secondWidth := by
    simpa only [bits, List.length_ofFn] using congrArg List.length equal
  subst secondWidth
  exact congrArg (fun value => bits (value.setWidth capacity)) (bits_injective equal)

/-- Reindexing an array by an equality of lengths does not change its bit
encoding, after casting the resulting vector width. -/
theorem encode_cast {Carrier : Type carrierLevel} {width firstLength secondLength : ℕ}
    (element : Carrier → BitVec width) (sameLength : firstLength = secondLength)
    (values : Fin secondLength → Carrier) :
    (encode element firstLength (fun index => values (Fin.cast sameLength index))).cast
      (congrArg (fun length => length * width) sameLength) =
      encode element secondLength values := by
  cases sameLength
  rfl

@[simp] theorem bits_cast {firstWidth secondWidth : ℕ}
    (equal : firstWidth = secondWidth) (value : BitVec firstWidth) :
    bits (value.cast equal) = bits value := by cases equal; rfl

theorem bits_append {firstWidth secondWidth : ℕ}
    (high : BitVec firstWidth) (low : BitVec secondWidth) :
    bits (high ++ low) = bits low ++ bits high := by
  apply List.ext_getElem
  · simp [bits, Nat.add_comm]
  · intro index leftBound rightBound
    simp only [bits, List.getElem_ofFn, BitVec.getLsbD_append]
    by_cases inLow : index < secondWidth
    · simp [inLow]
    · simp only [List.getElem_append, List.length_ofFn, List.getElem_ofFn]
      simp only [inLow, dite_false, ite_false]

/-- Array encoding agrees with consecutive element blocks on the tape. -/
theorem bits_encode (element : Carrier → BitVec width) (length : ℕ)
    (values : Fin length → Carrier) :
    bits (encode element length values) =
      (List.ofFn (fun index => bits (element (values index)))).flatten := by
  induction length with
  | zero => simp [bits]
  | succ length hypothesis =>
    rw [encode, bits_cast, bits_append, hypothesis, List.ofFn_succ]
    rfl

/-- A selected element starts after exactly `index * width` bits. -/
theorem split_encode (element : Carrier → BitVec width) (length : ℕ)
    (values : Fin length → Carrier) (index : Fin length) :
    ∃ beforeBits afterBits,
      bits (encode element length values) =
        beforeBits ++ bits (element (values index)) ++ afterBits ∧
      beforeBits.length = index.val * width := by
  induction length with
  | zero => exact Fin.elim0 index
  | succ length hypothesis =>
    refine Fin.cases ?_ (fun smaller => ?_) index
    · refine ⟨[], bits (encode element length (Fin.tail values)), ?_, by simp⟩
      simp [encode, bits_append]
    · obtain ⟨beforeBits, afterBits, decomposition, prefixLength⟩ :=
        hypothesis (Fin.tail values) smaller
      refine ⟨bits (element (values 0)) ++ beforeBits, afterBits, ?_, ?_⟩
      · simp only [encode, bits_cast, bits_append, decomposition, List.append_assoc]
        rfl
      · simp only [List.length_append, bits, List.length_ofFn, prefixLength, Fin.val_succ]
        simp [Nat.add_mul, Nat.add_comm]

/-- Replacing one array coordinate changes exactly its encoded block. The
prefix and suffix are shared with the original array encoding. -/
theorem split_encode_update (element : Carrier → BitVec width) (length : ℕ)
    (values : Fin length → Carrier) (index : Fin length) (replacement : Carrier) :
    ∃ beforeBits afterBits,
      bits (encode element length values) =
        beforeBits ++ bits (element (values index)) ++ afterBits ∧
      beforeBits.length = index.val * width ∧
      bits (encode element length (Function.update values index replacement)) =
        beforeBits ++ bits (element replacement) ++ afterBits := by
  induction length with
  | zero => exact Fin.elim0 index
  | succ length hypothesis =>
    refine Fin.cases ?_ (fun smaller => ?_) index
    · refine ⟨[], bits (encode element length (Fin.tail values)), ?_, by simp, ?_⟩
      · simp [encode, bits_cast, bits_append]
      · have headUpdate : Function.update values 0 replacement 0 = replacement := by
          simp [Function.update]
        have tailUpdate : Fin.tail (Function.update values 0 replacement) = Fin.tail values := by
          funext position
          simp
        simp [encode, bits_cast, bits_append, tailUpdate]
    · obtain ⟨beforeBits, afterBits, decomposition, prefixLength, updated⟩ :=
        hypothesis (Fin.tail values) smaller
      have tailValue : Fin.tail values smaller = values (Fin.succ smaller) := rfl
      rw [tailValue] at decomposition
      refine ⟨bits (element (values 0)) ++ beforeBits, afterBits, ?_, ?_, ?_⟩
      · simp [encode, bits_cast, bits_append, decomposition, List.append_assoc]
      · simp only [List.length_append, bits, List.length_ofFn, prefixLength,
          Fin.val_succ]
        simp [Nat.add_mul, Nat.add_comm]
      · have headUpdate :
            Function.update values (Fin.succ smaller) replacement 0 = values 0 := by
          change (if (0 : Fin (length + 1)) = Fin.succ smaller then
            replacement else values 0) = values 0
          split
          · rename_i equal
            exact False.elim (Fin.succ_ne_zero smaller equal.symm)
          · rfl
        have tailUpdate :
            Fin.tail (Function.update values (Fin.succ smaller) replacement) =
              Function.update (Fin.tail values) smaller replacement := by
          funext position
          simp [Fin.tail, Function.update]
        simp [encode, bits_cast, bits_append, headUpdate, tailUpdate, updated,
          List.append_assoc]

end ArrayEncoding

namespace MatrixEncoding

-- carrierLevel: entries of the mathematical matrix.
variable {Carrier : Type carrierLevel} {rows columns : ℕ}

/-- Row-major equivalence between rectangular matrices and flat arrays. -/
def flattenEquiv : (Fin rows → Fin columns → Carrier) ≃
    (Fin (rows * columns) → Carrier) where
  toFun matrix index :=
    let coordinate := finProdFinEquiv.symm index
    matrix coordinate.1 coordinate.2
  invFun array row column := array (finProdFinEquiv (row, column))
  left_inv matrix := by
    funext row column
    exact congrArg (fun coordinate => matrix coordinate.1 coordinate.2)
      (finProdFinEquiv.left_inv (row, column))
  right_inv array := by
    funext index
    exact congrArg array (finProdFinEquiv.right_inv index)

/-- Reindex a function's coordinates along an equivalence. -/
def functionEquiv {Index Source : Type*} (equivalence : Index ≃ Source) :
    (Source → Carrier) ≃ (Index → Carrier) where
  toFun values index := values (equivalence index)
  invFun values source := values (equivalence.symm source)
  left_inv values := by
    funext source
    simp
  right_inv values := by
    funext index
    simp

/-- Flatten a matrix into a polynomial-length array, preserving row-major
order even when evaluation of a product needs a cast. -/
noncomputable def flattenPolynomial (rows columns : MvPolynomial Parameter ℕ)
    (assignment : Parameter → ℕ) :
    (Fin (MvPolynomial.eval assignment rows) →
      Fin (MvPolynomial.eval assignment columns) → Carrier) ≃
        (Fin (MvPolynomial.eval assignment (rows * columns)) → Carrier) := by
  let sameLength : MvPolynomial.eval assignment (rows * columns) =
      MvPolynomial.eval assignment rows * MvPolynomial.eval assignment columns := by
    simp [MvPolynomial.eval_mul]
  exact flattenEquiv.trans (functionEquiv (finCongr sameLength))

end MatrixEncoding

@[simp] theorem constant_encode_bits (domain : EncodedDomain.{0, carrierLevel} Empty)
    (sizes : Parameter → ℕ) (value : domain.Carrier Empty.elim) :
    ArrayEncoding.bits ((domain.constant (Parameter := Parameter)).encode sizes value) =
      ArrayEncoding.bits (domain.encode Empty.elim value) := by
  simp only [constant, ofCodec, ArrayEncoding.bits_cast]

@[simp] theorem fixed_encode_bits {Carrier : Type carrierLevel} {cardinality : ℕ}
    (enumeration : Carrier ≃ Fin cardinality) (sizes : Parameter → ℕ) (value : Carrier) :
    ArrayEncoding.bits ((fixed (Parameter := Parameter) enumeration).encode sizes value) =
      ArrayEncoding.bits (BitVec.ofNat (Nat.clog 2 cardinality) (enumeration value).val) := by
  simp only [fixed, ofCodec, ArrayEncoding.bits_cast, BitVec.ofNatLT_eq_ofNat]

theorem reindex_encode_bits (domain : EncodedDomain.{parameterLevel, carrierLevel} Parameter)
    (Carrier' : (Parameter → ℕ) → Type carrierLevel)
    (equivalence : ∀ assignment, Carrier' assignment ≃ domain.Carrier assignment)
    (sizes : Parameter → ℕ) (value : Carrier' sizes) :
    ArrayEncoding.bits ((domain.reindex Carrier' equivalence).encode sizes value) =
      ArrayEncoding.bits (domain.encode sizes (equivalence sizes value)) := rfl

/-- Arrays whose length is any polynomial expression in the size parameters. -/
noncomputable def arrayOfLength (element : EncodedDomain.{parameterLevel, carrierLevel} Parameter)
    (length : MvPolynomial Parameter ℕ) : EncodedDomain Parameter :=
  ofCodec (fun assignment => Fin (MvPolynomial.eval assignment length) → element.Carrier assignment)
    (length * element.widthPolynomial)
    (fun assignment => MvPolynomial.eval assignment length * element.width assignment)
    (by intro assignment; simp)
    (fun assignment => ArrayEncoding.encode (element.encode assignment) _)
    (fun assignment => ArrayEncoding.decode (element.decode assignment) _)
    (fun assignment => ArrayEncoding.decode_encode _ _ (element.decode_encode assignment) _)
    (fun assignment => ArrayEncoding.encode_decode _ _ (element.encode_decode assignment) _)

/-- Arrays of a named assigned length are the common coordinate-indexed case. -/
noncomputable def array (element : EncodedDomain.{parameterLevel, carrierLevel} Parameter)
    (lengthParameter : Parameter) : EncodedDomain Parameter :=
  ofCodec (fun assignment => Fin (assignment lengthParameter) → element.Carrier assignment)
    (MvPolynomial.X lengthParameter * element.widthPolynomial)
    (fun assignment => assignment lengthParameter * element.width assignment)
    (by intro assignment; simp)
    (fun assignment => ArrayEncoding.encode (element.encode assignment) _)
    (fun assignment => ArrayEncoding.decode (element.decode assignment) _)
    (fun assignment => ArrayEncoding.decode_encode _ _ (element.decode_encode assignment) _)
    (fun assignment => ArrayEncoding.encode_decode _ _ (element.encode_decode assignment) _)

@[simp] theorem arrayOfLength_widthPolynomial (element : EncodedDomain.{parameterLevel, carrierLevel} Parameter)
    (length : MvPolynomial Parameter ℕ) :
    (element.arrayOfLength length).widthPolynomial = length * element.widthPolynomial := rfl

@[simp] theorem array_widthPolynomial (element : EncodedDomain.{parameterLevel, carrierLevel} Parameter)
    (parameter : Parameter) :
    (element.array parameter).widthPolynomial = MvPolynomial.X parameter * element.widthPolynomial := rfl

/-- Polynomial evaluation casts leave the concatenated array bits unchanged. -/
@[simp] theorem arrayOfLength_encode_bits (element : EncodedDomain.{parameterLevel, carrierLevel} Parameter)
    (length : MvPolynomial Parameter ℕ) (assignment : Parameter → ℕ)
    (values : (element.arrayOfLength length).Carrier assignment) :
    ArrayEncoding.bits ((element.arrayOfLength length).encode assignment values) =
      ArrayEncoding.bits (ArrayEncoding.encode (element.encode assignment) _ values) := by
  simp only [arrayOfLength, ofCodec, ArrayEncoding.bits_cast]

/-- Lift a bounded raw-block lookup through the array codec once, independently
of the controller, tape layout, or way the element width is supplied. -/
theorem array_lookup_of_blocks (element : EncodedDomain.{parameterLevel, carrierLevel} Parameter)
    (length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (index : ℕ) (within : index < MvPolynomial.eval sizes length)
    (array : (element.arrayOfLength length).Carrier sizes) (unit overhead : ℕ)
    (property : ℕ → ℕ → List Bool → List Bool → Prop)
    (blocks : ∀ before block after : List Bool,
      before.length = index * element.width sizes → block.length = element.width sizes →
      ∃ ticks, ticks ≤ index * unit + overhead ∧
        property ticks (before ++ block ++ after).length (before ++ block ++ after) block) :
    ∃ ticks, ticks ≤ MvPolynomial.eval sizes length * unit + overhead ∧
      property ticks ((element.arrayOfLength length).width sizes)
        (ArrayEncoding.bits ((element.arrayOfLength length).encode sizes array))
        (ArrayEncoding.bits (element.encode sizes (array ⟨index, within⟩))) := by
  obtain ⟨before, after, decomposition, prefixLength⟩ :=
    ArrayEncoding.split_encode (element.encode sizes) _ array ⟨index, within⟩
  let block := ArrayEncoding.bits (element.encode sizes (array ⟨index, within⟩))
  have whole : ArrayEncoding.bits ((element.arrayOfLength length).encode sizes array) =
      before ++ block ++ after := by simpa only [arrayOfLength_encode_bits] using decomposition
  have wholeLength : (before ++ block ++ after).length = (element.arrayOfLength length).width sizes := by
    rw [← whole]
    exact List.length_ofFn
  obtain ⟨ticks, cost, correct⟩ := blocks before block after prefixLength List.length_ofFn
  refine ⟨ticks, cost.trans (Nat.add_le_add_right (Nat.mul_le_mul_right unit within.le) overhead), ?_⟩
  rw [wholeLength] at correct
  rw [← whole] at correct
  exact correct

/-- Lift separate-output block replacement without repeating codec decompositions
or polynomial cost arithmetic in fixed-width and runtime-width adapters. -/
theorem array_update_of_blocks (element : EncodedDomain.{parameterLevel, carrierLevel} Parameter)
    (length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (index : ℕ) (within : index < MvPolynomial.eval sizes length)
    (array : (element.arrayOfLength length).Carrier sizes) (replacement : element.Carrier sizes)
    (unit overhead : ℕ) (property : ℕ → ℕ → List Bool → List Bool → Prop)
    (blocks : ∀ before block after : List Bool,
      before.length = index * element.width sizes → block.length = element.width sizes →
      (before ++ block ++ after).length = (element.arrayOfLength length).width sizes →
      ∃ ticks, ticks ≤ index * unit + 2 * (before ++ block ++ after).length + overhead ∧
        property ticks (before ++ block ++ after).length (before ++ block ++ after)
          (before ++ ArrayEncoding.bits (element.encode sizes replacement) ++ after)) :
    ∃ ticks, ticks ≤ MvPolynomial.eval sizes length * (unit + 2 * element.width sizes) + overhead ∧
      property ticks ((element.arrayOfLength length).width sizes)
        (ArrayEncoding.bits ((element.arrayOfLength length).encode sizes array))
        (ArrayEncoding.bits ((element.arrayOfLength length).encode sizes
          (Function.update array ⟨index, within⟩ replacement))) := by
  obtain ⟨before, after, decomposition, prefixLength, updated⟩ :=
    ArrayEncoding.split_encode_update (element.encode sizes) _ array ⟨index, within⟩ replacement
  let block := ArrayEncoding.bits (element.encode sizes (array ⟨index, within⟩))
  have whole : ArrayEncoding.bits ((element.arrayOfLength length).encode sizes array) =
      before ++ block ++ after := by simpa only [arrayOfLength_encode_bits] using decomposition
  have newWhole : ArrayEncoding.bits ((element.arrayOfLength length).encode sizes
      (Function.update array ⟨index, within⟩ replacement)) =
      before ++ ArrayEncoding.bits (element.encode sizes replacement) ++ after := by
    simpa only [arrayOfLength, ofCodec, ArrayEncoding.bits_cast] using updated
  have wholeLength : (before ++ block ++ after).length = (element.arrayOfLength length).width sizes := by
    rw [← whole]
    exact List.length_ofFn
  obtain ⟨ticks, cost, correct⟩ := blocks before block after prefixLength List.length_ofFn wholeLength
  refine ⟨ticks, ?_, ?_⟩
  · have widthEq : (element.arrayOfLength length).width sizes =
        MvPolynomial.eval sizes length * element.width sizes := by simp [arrayOfLength, ofCodec]
    have bound := Nat.mul_le_mul_right unit within.le
    calc
      ticks ≤ index * unit + 2 * (before ++ block ++ after).length + overhead := cost
      _ = index * unit + 2 * (MvPolynomial.eval sizes length * element.width sizes) + overhead := by
        rw [wholeLength, widthEq]
      _ ≤ MvPolynomial.eval sizes length * unit +
          2 * (MvPolynomial.eval sizes length * element.width sizes) + overhead :=
        Nat.add_le_add_right (Nat.add_le_add_right bound _) overhead
      _ = _ := by simp [Nat.mul_add, Nat.mul_left_comm]
  · rw [wholeLength] at correct
    rw [← whole, ← newWhole] at correct
    exact correct

/-- Named-length arrays have the same consecutive element blocks. -/
@[simp] theorem array_encode_bits (element : EncodedDomain.{parameterLevel, carrierLevel} Parameter)
    (parameter : Parameter) (assignment : Parameter → ℕ)
    (values : (element.array parameter).Carrier assignment) :
    ArrayEncoding.bits ((element.array parameter).encode assignment values) =
      ArrayEncoding.bits (ArrayEncoding.encode (element.encode assignment) _ values) := by
  simp only [array, ofCodec, ArrayEncoding.bits_cast]

/-- Named arrays and variable-length polynomials use the same element blocks. -/
theorem array_X_encode_bits (element : EncodedDomain.{parameterLevel, carrierLevel} Parameter)
    (parameter : Parameter) (sizes : Parameter → ℕ)
    (values : Fin (sizes parameter) → element.Carrier sizes) :
    ArrayEncoding.bits ((element.array parameter).encode sizes values) =
      ArrayEncoding.bits ((element.arrayOfLength (MvPolynomial.X parameter)).encode sizes
        (Equiv.arrowCongr (finCongr (MvPolynomial.eval_X (f := sizes) parameter).symm) (Equiv.refl _) values)) := by
  simp only [array, arrayOfLength, ofCodec, ArrayEncoding.bits_cast, ArrayEncoding.bits_encode]
  exact congrArg List.flatten
    (List.ofFn_congr (MvPolynomial.eval_X parameter).symm
      (fun position => ArrayEncoding.bits (element.encode sizes (values position))))

/-- Rectangular matrices use their mathematical row and column indices while
retaining a flat row-major array encoding. -/
noncomputable def matrix (element : EncodedDomain.{parameterLevel, carrierLevel} Parameter)
    (rows columns : MvPolynomial Parameter ℕ) : EncodedDomain Parameter :=
  (arrayOfLength element (rows * columns)).reindex
    (fun assignment => Fin (MvPolynomial.eval assignment rows) →
      Fin (MvPolynomial.eval assignment columns) → element.Carrier assignment)
    (fun assignment => MatrixEncoding.flattenPolynomial
      (Carrier := element.Carrier assignment) rows columns assignment)

/-- Matrix values are encoded exactly as their row-major flat arrays. -/
theorem matrix_encode (element : EncodedDomain.{parameterLevel, carrierLevel} Parameter)
    (rows columns : MvPolynomial Parameter ℕ) (assignment : Parameter → ℕ)
    (value : (matrix element rows columns).Carrier assignment) :
    (matrix element rows columns).encode assignment value =
      (arrayOfLength element (rows * columns)).encode assignment
        (MatrixEncoding.flattenPolynomial (Carrier := element.Carrier assignment)
          rows columns assignment value) := rfl

end Polytime2.EncodedDomain
