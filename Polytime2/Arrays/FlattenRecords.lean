import Polytime2.Primitives.BitOperations
import Polytime2.Encoding.Records

/-! # Flattening arrays of homogeneous fixed records

Fixed records and arrays concatenate the same canonical element words. This
row-major conversion changes only the mathematical indexing, with no padding
or element decoding. Circuit constructor stages use it before serialization.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

private theorem flatten_list {Carrier : Type*} {rows columns : ℕ}
    (matrix : Fin rows → Fin columns → Carrier) :
    List.ofFn (MatrixEncoding.flattenEquiv matrix) = (List.ofFn (fun row => List.ofFn (matrix row))).flatten := by
  rw [List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext row
  apply congrArg List.ofFn
  funext column
  have equal : (⟨row.val * columns + column.val, by
      have bounded := (finProdFinEquiv (row, column)).isLt
      simpa only [finProdFinEquiv, Equiv.coe_fn_mk, Nat.mul_comm, Nat.add_comm] using bounded⟩ :
      Fin (rows * columns)) = finProdFinEquiv (row, column) := by
    apply Fin.ext
    simp [finProdFinEquiv, Nat.mul_comm, Nat.add_comm]
  simp only [MatrixEncoding.flattenEquiv, Equiv.coe_fn_mk, equal, Equiv.symm_apply_apply]

/-- Regard a homogeneous fixed record as an array, retaining every element
and its canonical bits. -/
noncomputable def recordToArray (element : EncodedDomain Parameter) (count : ℕ) : Computation Parameter Unit :=
  encodingMap (record count (fun _ => element)) (element.arrayOfLength (MvPolynomial.C count))
    (fun _ values index => values (index.cast (MvPolynomial.eval_C count)))

theorem recordToArray_realizable (element : EncodedDomain Parameter) (count : ℕ) :
    (recordToArray element count).Realizable := by
  apply encodingMap_realizable
  · intro sizes
    simp [width, record_widthPolynomial, nsmul_eq_mul]
  · intro sizes values
    rw [bits_record_encode, arrayOfLength_encode_bits, ArrayEncoding.bits_encode]
    exact congrArg List.flatten (List.ofFn_congr (MvPolynomial.eval_C count).symm
      (fun index => ArrayEncoding.bits (element.encode sizes (values index))))

theorem recordToArray_list (element : EncodedDomain Parameter) (count : ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (recordToArray element count).Arguments sizes // True}) :
    List.ofFn ((recordToArray element count).compute sizes arguments) = List.ofFn (arguments.val ()) := by
  exact (List.ofFn_congr (MvPolynomial.eval_C count).symm (arguments.val ())).symm

/-- Flatten a rectangular array without changing its canonical element words. -/
noncomputable def arrayFlatten (element : EncodedDomain Parameter)
    (rows columns : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  encodingMap ((element.arrayOfLength columns).arrayOfLength rows)
    (element.arrayOfLength (rows * columns)) (fun sizes matrix => MatrixEncoding.flattenPolynomial rows columns sizes matrix)

theorem arrayFlatten_realizable (element : EncodedDomain Parameter)
    (rows columns : MvPolynomial Parameter ℕ) : (arrayFlatten element rows columns).Realizable := by
  apply encodingMap_realizable
  · intro sizes
    simp [EncodedDomain.width, arrayOfLength, mul_assoc]
  · intro sizes matrix
    exact (matrix_nested_encode_bits element rows columns sizes matrix).symm

theorem arrayFlatten_list (element : EncodedDomain Parameter) (rows columns : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ) (arguments : {arguments : (arrayFlatten element rows columns).Arguments sizes // True}) :
    List.ofFn ((arrayFlatten element rows columns).compute sizes arguments) =
      (List.ofFn (fun row => List.ofFn (arguments.val () row))).flatten := by
  change List.ofFn (fun index => MatrixEncoding.flattenEquiv (arguments.val ()) (index.cast (map_mul (MvPolynomial.eval sizes) rows columns))) = _
  rw [List.ofFn_congr (map_mul (MvPolynomial.eval sizes) rows columns)]
  simp only [Fin.cast_cast, Fin.cast_refl, id_eq]
  exact flatten_list _

/-- Flatten fixed-width mathematical rows, retaining their canonical bits. -/
noncomputable def arrayFlattenRecords (element : EncodedDomain Parameter) (columns : ℕ)
    (rows : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  encodingMap ((record columns (fun _ => element)).arrayOfLength rows)
    (element.arrayOfLength (rows * MvPolynomial.C columns))
    (fun sizes matrix index => MatrixEncoding.flattenEquiv matrix (index.cast (by simp)))

theorem arrayFlattenRecords_realizable (element : EncodedDomain Parameter) (columns : ℕ)
    (rows : MvPolynomial Parameter ℕ) : (arrayFlattenRecords element columns rows).Realizable := by
  apply encodingMap_realizable
  · intro sizes
    simp [EncodedDomain.width, arrayOfLength, record_widthPolynomial, nsmul_eq_mul, mul_assoc]
  · intro sizes matrix
    rw [arrayOfLength_encode_bits, arrayOfLength_encode_bits, ArrayEncoding.bits_encode_cast]
    have nested : ArrayEncoding.bits
        (ArrayEncoding.encode ((record columns (fun _ => element)).encode sizes)
          (MvPolynomial.eval sizes rows) matrix) =
        ArrayEncoding.bits (ArrayEncoding.encode (ArrayEncoding.encode (element.encode sizes) columns)
          (MvPolynomial.eval sizes rows) matrix) := by
      apply ArrayEncoding.bits_encode_congr
      intro row
      rw [bits_record_encode, ArrayEncoding.bits_encode]
    exact nested.trans (MatrixEncoding.bits_encode_nested (element.encode sizes) matrix)

/-- Flattening preserves the complete row-major sequence of values. -/
theorem arrayFlattenRecords_list (element : EncodedDomain Parameter) (columns : ℕ)
    (rows : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (arrayFlattenRecords element columns rows).Arguments sizes // True}) :
    List.ofFn ((arrayFlattenRecords element columns rows).compute sizes arguments) =
      (List.ofFn (fun row => List.ofFn (arguments.val () row))).flatten := by
  change List.ofFn (fun index => MatrixEncoding.flattenEquiv (arguments.val ()) (index.cast (by simp))) = _
  rw [List.ofFn_congr (show MvPolynomial.eval sizes (rows * MvPolynomial.C columns) =
    MvPolynomial.eval sizes rows * columns by simp)]
  simp only [Fin.cast_cast, Fin.cast_refl, id_eq]
  exact flatten_list _

end Polytime2.Computation
