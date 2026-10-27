import Polytime2.Arrays.FixedArrayCall
import Polytime2.Computation.Records

/-! # Retaining a flag and exact array after a computed-length call

A fixed-element array consumer may return a Boolean flag and an array at the
called length. Repackage that result as a flag and an exact bounded array at
the caller's capacity. Only field order changes; counts and payload bits stay
canonical. The source's capacity padding never becomes mathematical elements.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

private noncomputable def flaggedArrayFrame (element : EncodedDomain Empty)
    (capacity : MvPolynomial Parameter ℕ) : EncodedDomain Parameter :=
  atComputedSizeDomain (fun _ : Unit => capacity)
    ((booleans : EncodedDomain Unit).prod ((element.constant : EncodedDomain Unit).array ()))

private def retained (element : EncodedDomain Empty) (capacity : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ) (frame : (flaggedArrayFrame element capacity).Carrier sizes) :
    (boundedArray element.constant capacity).Carrier sizes := ⟨frame.1 (), frame.2.2⟩

private theorem flaggedArrayFrame_bits (element : EncodedDomain Empty)
    (capacity : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (frame : (flaggedArrayFrame element capacity).Carrier sizes) :
    ArrayEncoding.bits ((flaggedArrayFrame element capacity).encode sizes frame) =
      ArrayEncoding.bits ((boundedUnary capacity).encode sizes (frame.1 ())) ++
        ArrayEncoding.bits ((booleans : EncodedDomain Parameter).encode sizes frame.2.1) ++
          ArrayEncoding.bits ((ArrayEncoding.encode ((element.constant : EncodedDomain Parameter).encode sizes)
            (frame.1 ()).val frame.2.2).setWidth
              (MvPolynomial.eval sizes (capacity * (element.constant : EncodedDomain Parameter).widthPolynomial))) := by
  have countBits : ArrayEncoding.bits ((computedSizeDomain (fun _ : Unit => capacity)).encode sizes frame.1) =
      ArrayEncoding.bits ((boundedUnary capacity).encode sizes (frame.1 ())) := by
    have eta : frame.1 = fun _ => frame.1 () := by funext name; cases name; rfl
    rw [eta]
    exact namedRecord_unit_bits _ _ _
  simp only [flaggedArrayFrame, atComputedSizeDomain, boundedSigma_encode_bits]
  rw [countBits]
  have scalar (actual : Unit → ℕ) (values : Fin (actual ()) → element.Carrier Empty.elim) :
      ArrayEncoding.bits (((element.constant : EncodedDomain Unit).array ()).encode actual values) =
        ArrayEncoding.bits (ArrayEncoding.encode ((element.constant : EncodedDomain Parameter).encode sizes)
          (actual ()) values) := by
    rw [array_encode_bits]
    simp only [ArrayEncoding.bits_encode, constant_encode_bits]
  have capacityEq : SizeSubstitution.polynomial (fun _ : Unit => capacity)
      (((booleans : EncodedDomain Unit).prod ((element.constant : EncodedDomain Unit).array ())).widthPolynomial) =
        1 + capacity * (element.constant : EncodedDomain Parameter).widthPolynomial := by
    have clog : Nat.clog 2 2 = 1 := by decide
    simp [SizeSubstitution.polynomial, booleans, clog]
  rw [capacityEq]
  have fits := computedSizeWidth_bound (fun _ : Unit => capacity)
    ((booleans : EncodedDomain Unit).prod ((element.constant : EncodedDomain Unit).array ())) sizes frame.1
  rw [capacityEq] at fits
  rw [bits_setWidth _ fits]
  rw [bits_prod_encode, scalar]
  have bounded : (frame.1 ()).val ≤ MvPolynomial.eval sizes capacity := Nat.le_of_lt_succ (frame.1 ()).isLt
  rw [bits_setWidth _ (by
    simp only [map_mul]
    exact Nat.mul_le_mul_right _ bounded)]
  have flagBits : ArrayEncoding.bits ((booleans : EncodedDomain Unit).encode
      (computedSizeAssignment (fun _ : Unit => capacity) sizes frame.1) frame.2.1) =
      ArrayEncoding.bits ((booleans : EncodedDomain Parameter).encode sizes frame.2.1) := by
    simp only [booleans, fixed_encode_bits]
  rw [flagBits]
  have padding : MvPolynomial.eval sizes (1 + capacity * (element.constant : EncodedDomain Parameter).widthPolynomial) -
      ((booleans : EncodedDomain Unit).prod ((element.constant : EncodedDomain Unit).array ())).width
        (computedSizeAssignment (fun _ : Unit => capacity) sizes frame.1) =
      MvPolynomial.eval sizes (capacity * (element.constant : EncodedDomain Parameter).widthPolynomial) -
        (frame.1 ()).val * (element.constant : EncodedDomain Parameter).width sizes := by
    have clog : Nat.clog 2 2 = 1 := by decide
    simp [width, booleans, clog, computedSizeAssignment, map_mul]
    omega
  rw [padding]
  simp only [List.append_assoc, computedSizeAssignment, EncodedDomain.width]

/-- Retain the consumer's flag and exact output array at the host capacity. -/
noncomputable def retainFixedArrayFlag (element : EncodedDomain Empty)
    (capacity : MvPolynomial Parameter ℕ) : Computation Parameter Unit where
  inputDomains _ := flaggedArrayFrame element capacity
  outputDomain := booleans.prod (boundedArray element.constant capacity)
  precondition _ _ := True
  compute sizes arguments := ((arguments.val ()).2.1, retained element capacity sizes (arguments.val ()))

theorem retainFixedArrayFlag_realizable (element : EncodedDomain Empty)
    (capacity : MvPolynomial Parameter ℕ) : (retainFixedArrayFlag element capacity).Realizable := by
  let source := flaggedArrayFrame element capacity
  let target := boundedArray (element.constant : EncodedDomain Parameter) capacity
  let bitCapacity := capacity * (element.constant : EncodedDomain Parameter).widthPolynomial
  have flag : (unaryMap source booleans (fun _ _ => True) (fun _ frame => frame.val.2.1)).Realizable := by
    apply Realizable.Internal.fieldProjection _ _ (boundedUnary capacity).widthPolynomial
    intro sizes frame
    refine ⟨ArrayEncoding.bits ((boundedUnary capacity).encode sizes (frame.val.1 ())),
      ArrayEncoding.bits ((ArrayEncoding.encode ((element.constant : EncodedDomain Parameter).encode sizes)
        (frame.val.1 ()).val frame.val.2.2).setWidth (MvPolynomial.eval sizes bitCapacity)), ?_, ?_⟩
    · exact flaggedArrayFrame_bits element capacity sizes frame.val
    · simp [ArrayEncoding.bits]
  have count : (unaryMap source (boundedUnary capacity) (fun _ _ => True)
      (fun _ frame => frame.val.1 ())).Realizable := by
    apply Realizable.Internal.fieldProjection _ _ 0
    intro sizes frame
    refine ⟨[], ArrayEncoding.bits ((booleans : EncodedDomain Parameter).encode sizes frame.val.2.1) ++
      ArrayEncoding.bits ((ArrayEncoding.encode ((element.constant : EncodedDomain Parameter).encode sizes)
        (frame.val.1 ()).val frame.val.2.2).setWidth (MvPolynomial.eval sizes bitCapacity)), ?_, by simp⟩
    simpa only [List.nil_append, List.append_assoc] using flaggedArrayFrame_bits element capacity sizes frame.val
  have payload : (unaryMap source (bitVectors bitCapacity) (fun _ _ => True)
      (fun sizes frame => (ArrayEncoding.encode ((element.constant : EncodedDomain Parameter).encode sizes)
        (frame.val.1 ()).val frame.val.2.2).setWidth (MvPolynomial.eval sizes bitCapacity))).Realizable := by
    apply Realizable.Internal.fieldProjection _ _ ((boundedUnary capacity).widthPolynomial + 1)
    intro sizes frame
    refine ⟨ArrayEncoding.bits ((boundedUnary capacity).encode sizes (frame.val.1 ())) ++
      ArrayEncoding.bits ((booleans : EncodedDomain Parameter).encode sizes frame.val.2.1), [], ?_, ?_⟩
    · simpa only [List.append_nil] using flaggedArrayFrame_bits element capacity sizes frame.val
    · have clog : Nat.clog 2 2 = 1 := by decide
      simp [ArrayEncoding.bits, booleans, clog]
  have packed := (count.prodMk payload).withEncodedOutput target
    (fun sizes arguments => retained element capacity sizes (arguments.val ()))
    (by intros; rfl) (by intros; rfl)
  exact flag.prodMk packed

end Polytime2.Computation
