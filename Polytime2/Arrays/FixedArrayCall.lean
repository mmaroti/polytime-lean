import Polytime2.Arrays.PackingResult
import Polytime2.Computation.ComputedCall

/-! # Calling at the actual length of arrays of fixed elements

A bounded array already stores its exact count and canonical element bits.
For elements independent of runtime sizes, the same bits form a computed-size
frame without retaining the caller's unrelated size parameters.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

private theorem fixedArrayCapacity (element : EncodedDomain.{0, 0} Empty)
    (capacity : MvPolynomial Parameter ℕ) :
    SizeSubstitution.polynomial (fun _ : Unit => capacity)
      (((element.constant : EncodedDomain Unit).array ()).widthPolynomial) =
        capacity * (element.constant : EncodedDomain Parameter).widthPolynomial := by
  simp [SizeSubstitution.polynomial]

/-- Reuse a bounded array's canonical bits as a call frame at its exact length.
No element value is needed when the array is empty. -/
noncomputable def fixedArrayCallFrame (element : EncodedDomain.{0, 0} Empty)
    (capacity : MvPolynomial Parameter ℕ) : Computation Parameter Unit where
  inputDomains _ := boundedArray element.constant capacity
  outputDomain := atComputedSizeDomain (fun _ : Unit => capacity)
    ((element.constant : EncodedDomain Unit).array ())
  precondition _ _ := True
  compute _ arguments := ⟨(fun _ => (arguments.val ()).1), (arguments.val ()).2⟩

theorem fixedArrayCallFrame_realizable (element : EncodedDomain.{0, 0} Empty)
    (capacity : MvPolynomial Parameter ℕ) : (fixedArrayCallFrame element capacity).Realizable := by
  apply (copy_realizable (boundedArray element.constant capacity)).reinterpretOutput
    (fixedArrayCallFrame element capacity).outputDomain
    (fun _ value => ⟨(fun _ => value.1), value.2⟩)
  · intro sizes
    change MvPolynomial.eval sizes ((computedSizeDomain (fun _ : Unit => capacity)).widthPolynomial +
      SizeSubstitution.polynomial (fun _ : Unit => capacity)
        (((element.constant : EncodedDomain Unit).array ()).widthPolynomial)) = _
    rw [fixedArrayCapacity]
    simp only [computedSizeDomain, namedRecord_unit_widthPolynomial]
    rfl
  · intro sizes value
    simp only [fixedArrayCallFrame, atComputedSizeDomain, boundedSigma_encode_bits]
    rw [fixedArrayCapacity]
    simp only [computedSizeDomain, namedRecord_unit_bits]
    change ArrayEncoding.bits ((boundedUnary capacity).encode sizes value.1) ++
      ArrayEncoding.bits (((element.constant : EncodedDomain Unit).array ()).encode
        (computedSizeAssignment (fun _ : Unit => capacity) sizes (fun _ => value.1)) value.2 |>.setWidth _) = _
    change _ = ArrayEncoding.bits (((boundedUnary capacity).prod
      (bitVectors (capacity * (element.constant : EncodedDomain Parameter).widthPolynomial))).encode sizes
        (value.1, (ArrayEncoding.encode ((element.constant : EncodedDomain Parameter).encode sizes)
          value.1.val value.2).setWidth _))
    rw [bits_prod_encode]
    apply congrArg (fun bits => ArrayEncoding.bits ((boundedUnary capacity).encode sizes value.1) ++ bits)
    apply ArrayEncoding.bits_setWidth_congr
    rw [array_encode_bits, ArrayEncoding.bits_encode]
    simp only [ArrayEncoding.bits_encode, constant_encode_bits]
    rfl

/-- Invoke a total unary consumer at a bounded fixed-element array's exact
length. The existing computed-size call supplies all runtime preparation. -/
noncomputable def callFixedArray (element : EncodedDomain.{0, 0} Empty)
    (capacity : MvPolynomial Parameter ℕ) (consumer : Computation Unit Unit)
    (inputEqual : consumer.inputDomains () = (element.constant : EncodedDomain Unit).array ())
    (total : ∀ sizes arguments, consumer.precondition sizes arguments) : Computation Parameter Unit :=
  (fixedArrayCallFrame element capacity).followedBy
    (consumer.atComputedUnarySizes (fun _ : Unit => capacity))
    (by change atComputedSizeDomain _ (consumer.inputDomains ()) = _; rw [inputEqual]; rfl)
    (by intros; apply total)

theorem Realizable.callFixedArray {consumer : Computation Unit Unit} (ready : consumer.Realizable)
    (element : EncodedDomain.{0, 0} Empty) (capacity : MvPolynomial Parameter ℕ)
    (inputEqual : consumer.inputDomains () = (element.constant : EncodedDomain Unit).array ())
    (total : ∀ sizes arguments, consumer.precondition sizes arguments) :
    (callFixedArray element capacity consumer inputEqual total).Realizable :=
  (fixedArrayCallFrame_realizable element capacity).followedBy
    (ready.atComputedUnarySizes (fun _ : Unit => capacity))
    (by change atComputedSizeDomain _ (consumer.inputDomains ()) = _; rw [inputEqual]; rfl)
    (by intros; apply total)

end Polytime2.Computation
