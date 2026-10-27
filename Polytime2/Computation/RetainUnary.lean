import Polytime2.Computation.ComputedSizes
import Polytime2.Computation.Fields

/-! # Retaining computed unary sizes at the caller's capacity

A callee's unary count is already zero padded in its computed-size result.
Discard the callee-size header and retain that payload as a caller-sized unary
count. The numeric value does not change and no binary conversion is needed.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

private noncomputable def unaryFrame (capacity : MvPolynomial Parameter ℕ) : EncodedDomain Parameter :=
  atComputedSizeDomain (fun _ : Unit => capacity) (boundedUnary (MvPolynomial.X ()))

private def retainedUnary (capacity : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (frame : (unaryFrame capacity).Carrier sizes) : (boundedUnary capacity).Carrier sizes :=
  ⟨frame.2.val, by
    have outer := (frame.1 ()).isLt
    dsimp only at outer
    have inner := frame.2.isLt
    simp only [MvPolynomial.eval_X, computedSizeAssignment] at inner
    omega⟩

private theorem unaryFrame_bits (capacity : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (frame : (unaryFrame capacity).Carrier sizes) :
    ArrayEncoding.bits ((unaryFrame capacity).encode sizes frame) =
      ArrayEncoding.bits ((boundedUnary capacity).encode sizes (frame.1 ())) ++
        ArrayEncoding.bits ((boundedUnary capacity).encode sizes (retainedUnary capacity sizes frame)) := by
  have countBits : ArrayEncoding.bits ((computedSizeDomain (fun _ : Unit => capacity)).encode sizes frame.1) =
      ArrayEncoding.bits ((boundedUnary capacity).encode sizes (frame.1 ())) := by
    have eta : frame.1 = fun _ => frame.1 () := by funext name; cases name; rfl
    rw [eta]
    exact namedRecord_unit_bits _ _ _
  have payloadCapacity : SizeSubstitution.polynomial (fun _ : Unit => capacity)
      (boundedUnary (MvPolynomial.X ())).widthPolynomial = capacity := by
    simp [boundedUnary, SizeSubstitution.polynomial]
  have payloadFits := computedSizeWidth_bound (fun _ : Unit => capacity)
    (boundedUnary (MvPolynomial.X ())) sizes frame.1
  rw [payloadCapacity] at payloadFits
  simp only [unaryFrame, atComputedSizeDomain, boundedSigma_encode_bits]
  rw [countBits, payloadCapacity, bits_setWidth _ payloadFits]
  simp only [width, boundedUnary, BoundedUnary.encode_bits, retainedUnary, BoundedUnary.bits,
    MvPolynomial.eval_X, computedSizeAssignment]
  have outer := (frame.1 ()).isLt
  dsimp only at outer
  have inner := frame.2.isLt
  simp only [MvPolynomial.eval_X, computedSizeAssignment] at inner
  have padding : MvPolynomial.eval sizes capacity - frame.2.val =
      ((frame.1 ()).val - frame.2.val) + (MvPolynomial.eval sizes capacity - (frame.1 ()).val) := by omega
  rw [padding, List.replicate_add]
  simp only [List.append_assoc]

/-- Retain a computed unary count in the caller's original capacity. -/
noncomputable def retainComputedUnarySize (capacity : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  unaryMap (unaryFrame capacity) (boundedUnary capacity) (fun _ _ => True)
    (fun sizes frame => retainedUnary capacity sizes frame.val)

theorem retainComputedUnarySize_realizable (capacity : MvPolynomial Parameter ℕ) :
    (retainComputedUnarySize capacity).Realizable := by
  apply Realizable.Internal.fieldProjection _ _ (boundedUnary capacity).widthPolynomial
  intro sizes frame
  refine ⟨ArrayEncoding.bits ((boundedUnary capacity).encode sizes (frame.val.1 ())), [], ?_, ?_⟩
  · simpa only [List.append_nil] using unaryFrame_bits capacity sizes frame.val
  · simp [ArrayEncoding.bits]

/-- Retaining the count changes only its capacity, not its mathematical value. -/
theorem retainComputedUnarySize_correct (capacity : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (frame : (unaryFrame capacity).Carrier sizes) :
    ((retainComputedUnarySize capacity).compute sizes ⟨(fun _ => frame), trivial⟩).val = frame.2.val := rfl

end Polytime2.Computation
