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

import Polytime2.Encoding.Integers
import Polytime2.Encoding.ParameterRename
import Mathlib.Data.Matrix.Basic

/-! # Canonical encodings of bounded ordinary integer matrices

The carrier is a rectangular integer matrix with one common entry bound. The
codec reuses the existing row-major matrix of bounded signed integers through
Mathlib's equivalence between a pointwise predicate and a function of subtypes.
No dimensions, capacities, or padding are added to the mathematical instance.
-/

namespace Polytime2.IntegerMatrix

variable {Row Column : Type}

/-- Move entry bounds between a matrix predicate and its individual entries. -/
def entryBoundEquiv (bound : ℕ) :
    {matrix : Matrix Row Column ℤ // ∀ row column, (matrix row column).natAbs < bound} ≃
      Matrix Row Column {value : ℤ // value.natAbs < bound} :=
  (Equiv.subtypePiEquivPi (α := Row) (β := fun _ => Column → ℤ)
    (p := fun _ values => ∀ column, (values column).natAbs < bound)).trans
    (Equiv.piCongrRight (fun _ => Equiv.subtypePiEquivPi
      (α := Column) (β := fun _ => ℤ) (p := fun _ value => value.natAbs < bound)))

@[simp]
theorem entryBoundEquiv_apply (bound : ℕ)
    (value : {matrix : Matrix Row Column ℤ // ∀ row column, (matrix row column).natAbs < bound})
    (row : Row) (column : Column) :
    (entryBoundEquiv bound value row column).val = value.val row column := rfl

@[simp]
theorem entryBoundEquiv_symm_apply (bound : ℕ)
    (value : Matrix Row Column {value : ℤ // value.natAbs < bound})
    (row : Row) (column : Column) :
    ((entryBoundEquiv bound).symm value).val row column = (value row column).val := rfl

end Polytime2.IntegerMatrix

namespace Polytime2.EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

/-- Ordinary rectangular integer matrices with a polynomial magnitude bound. -/
noncomputable def integerMatrices (rows columns width : MvPolynomial Parameter ℕ) :
    EncodedDomain Parameter :=
  (matrix (binaryIntegers width) rows columns).reindex
    (fun sizes => {value : Matrix (Fin (MvPolynomial.eval sizes rows))
      (Fin (MvPolynomial.eval sizes columns)) ℤ //
        ∀ row column, (value row column).natAbs < 2 ^ MvPolynomial.eval sizes width})
    (fun sizes => IntegerMatrix.entryBoundEquiv (2 ^ MvPolynomial.eval sizes width))

/-- Algebraically equal widths and equal matrices have identical canonical encodings. -/
theorem integerMatrices_encode_congr (rows columns firstWidth secondWidth : MvPolynomial Parameter ℕ)
    (sameWidth : firstWidth = secondWidth) (sizes : Parameter → ℕ)
    (first : (integerMatrices rows columns firstWidth).Carrier sizes)
    (second : (integerMatrices rows columns secondWidth).Carrier sizes) (sameValues : first.val = second.val) :
    ArrayEncoding.bits ((integerMatrices rows columns firstWidth).encode sizes first) =
      ArrayEncoding.bits ((integerMatrices rows columns secondWidth).encode sizes second) := by
  cases sameWidth
  have same : first = second := Subtype.ext sameValues
  cases same
  rfl

/-- The ordinary matrix bound preserves the nested signed-word storage width. -/
theorem integerMatrices_nested_width (rows columns width : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ) :
    (integerMatrices rows columns width).width sizes =
      (((binaryIntegers width).arrayOfLength columns).arrayOfLength rows).width sizes :=
  congrArg (MvPolynomial.eval sizes) (mul_assoc rows columns (binaryIntegers width).widthPolynomial)

/-- Moving the bound to individual entries preserves every canonical bit. -/
theorem integerMatrices_nested_encode_bits (rows columns width : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ) (value : (integerMatrices rows columns width).Carrier sizes) :
    ArrayEncoding.bits ((integerMatrices rows columns width).encode sizes value) =
      ArrayEncoding.bits ((((binaryIntegers width).arrayOfLength columns).arrayOfLength rows).encode sizes
        (IntegerMatrix.entryBoundEquiv (2 ^ MvPolynomial.eval sizes width) value)) :=
  matrix_nested_encode_bits (binaryIntegers width) rows columns sizes _


/-- Reassemble ordinary matrix bounds from nested signed entries without changing bits. -/
theorem integerMatrices_of_nested_encode_bits (rows columns width : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (value : (((binaryIntegers width).arrayOfLength columns).arrayOfLength rows).Carrier sizes) :
    ArrayEncoding.bits ((integerMatrices rows columns width).encode sizes
      ((IntegerMatrix.entryBoundEquiv (2 ^ MvPolynomial.eval sizes width)).symm value)) =
        ArrayEncoding.bits ((((binaryIntegers width).arrayOfLength columns).arrayOfLength rows).encode sizes value) :=
  (integerMatrices_nested_encode_bits rows columns width sizes
    ((IntegerMatrix.entryBoundEquiv (2 ^ MvPolynomial.eval sizes width)).symm value)).trans
    (congrArg (fun value => ArrayEncoding.bits
      ((((binaryIntegers width).arrayOfLength columns).arrayOfLength rows).encode sizes value))
      ((IntegerMatrix.entryBoundEquiv (2 ^ MvPolynomial.eval sizes width)).apply_symm_apply value))

/-- Reindex a host matrix at renamed row, column, and entry-width polynomials. -/
noncomputable def integerMatricesRenameValues {NewParameter : Type} [Fintype NewParameter]
    (rows columns width : MvPolynomial Parameter ℕ) (names : Parameter → NewParameter)
    (sizes : NewParameter → ℕ) (value : (integerMatrices rows columns width).Carrier (sizes ∘ names)) :
    (integerMatrices (MvPolynomial.rename names rows) (MvPolynomial.rename names columns)
      (MvPolynomial.rename names width)).Carrier sizes :=
  ⟨fun row column => value.val
    (Fin.cast (MvPolynomial.eval_rename names sizes rows) row)
    (Fin.cast (MvPolynomial.eval_rename names sizes columns) column), by
      intro row column
      simpa only [MvPolynomial.eval_rename] using value.property
        (Fin.cast (MvPolynomial.eval_rename names sizes rows) row)
        (Fin.cast (MvPolynomial.eval_rename names sizes columns) column)⟩

set_option backward.isDefEq.respectTransparency false in
/-- Renaming mathematical matrix dimensions preserves canonical row-major bits. -/
theorem integerMatricesRenameValues_bits {NewParameter : Type} [Fintype NewParameter]
    (rows columns width : MvPolynomial Parameter ℕ) (names : Parameter → NewParameter)
    (sizes : NewParameter → ℕ) (value : (integerMatrices rows columns width).Carrier (sizes ∘ names)) :
    ArrayEncoding.bits ((integerMatrices (MvPolynomial.rename names rows) (MvPolynomial.rename names columns)
      (MvPolynomial.rename names width)).encode sizes (integerMatricesRenameValues rows columns width names sizes value)) =
      ArrayEncoding.bits (((integerMatrices rows columns width).renameParameters names).encode sizes value) := by
  rw [renameParameters_bits, integerMatrices_nested_encode_bits, integerMatrices_nested_encode_bits]
  simp only [arrayOfLength_encode_bits, ArrayEncoding.bits_encode, binaryIntegers_encode_bits]
  simp only [MvPolynomial.eval_rename, integerMatricesRenameValues, IntegerMatrix.entryBoundEquiv_apply]
  simp only [binaryNaturalsOfWidth_encode_bits, Fin.cast,
    booleans, fixed, ofCodec, ArrayEncoding.bits_cast]
  simp only [ArrayEncoding.bits, BitVec.getLsbD_ofNatLT, BitVec.getLsbD_ofFin,
    MvPolynomial.eval_rename]
  rfl

/-- Parameter renaming is an equivalence of the two ordinary matrix carriers. -/
noncomputable def integerMatricesRenameEquiv {NewParameter : Type} [Fintype NewParameter]
    (rows columns width : MvPolynomial Parameter ℕ) (names : Parameter → NewParameter)
    (sizes : NewParameter → ℕ) :
    (integerMatrices rows columns width).Carrier (sizes ∘ names) ≃
      (integerMatrices (MvPolynomial.rename names rows) (MvPolynomial.rename names columns)
        (MvPolynomial.rename names width)).Carrier sizes where
  toFun := integerMatricesRenameValues rows columns width names sizes
  invFun value := ⟨fun row column => value.val
    (Fin.cast (MvPolynomial.eval_rename names sizes rows).symm row)
    (Fin.cast (MvPolynomial.eval_rename names sizes columns).symm column), by
      intro row column
      simpa only [MvPolynomial.eval_rename] using value.property
        (Fin.cast (MvPolynomial.eval_rename names sizes rows).symm row)
        (Fin.cast (MvPolynomial.eval_rename names sizes columns).symm column)⟩
  left_inv value := by apply Subtype.ext; rfl
  right_inv value := by apply Subtype.ext; rfl

/-- The inverse matrix parameter view retains the same canonical bits. -/
theorem integerMatricesRenameEquiv_symm_bits {NewParameter : Type} [Fintype NewParameter]
    (rows columns width : MvPolynomial Parameter ℕ) (names : Parameter → NewParameter)
    (sizes : NewParameter → ℕ)
    (value : (integerMatrices (MvPolynomial.rename names rows) (MvPolynomial.rename names columns)
      (MvPolynomial.rename names width)).Carrier sizes) :
    ArrayEncoding.bits (((integerMatrices rows columns width).renameParameters names).encode sizes
      ((integerMatricesRenameEquiv rows columns width names sizes).symm value)) =
      ArrayEncoding.bits ((integerMatrices (MvPolynomial.rename names rows) (MvPolynomial.rename names columns)
        (MvPolynomial.rename names width)).encode sizes value) := by
  have bits := integerMatricesRenameValues_bits rows columns width names sizes
    ((integerMatricesRenameEquiv rows columns width names sizes).symm value)
  change ArrayEncoding.bits ((integerMatrices (MvPolynomial.rename names rows) (MvPolynomial.rename names columns)
    (MvPolynomial.rename names width)).encode sizes ((integerMatricesRenameEquiv rows columns width names sizes)
    ((integerMatricesRenameEquiv rows columns width names sizes).symm value))) = _ at bits
  rw [Equiv.apply_symm_apply] at bits
  exact bits.symm

end Polytime2.EncodedDomain
