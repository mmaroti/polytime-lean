import Polytime2.Arrays.PadValues
import Polytime2.Computation.ComputedSizes

/-! # Retaining a computed-length array at its polynomial host capacity

A fixed element's zero-coded filler interprets the computed frame's existing
zero padding as mathematical array entries. No element scan is required.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter NewParameter : Type} [Fintype Parameter] [Fintype NewParameter]

/-- Retain all actual elements and fill the unused polynomial capacity. -/
noncomputable def padComputedArray (element : EncodedDomain Empty)
    (length : MvPolynomial NewParameter ℕ)
    (bounds : NewParameter → MvPolynomial Parameter ℕ)
    (filler : element.Carrier Empty.elim) : Computation Parameter Unit where
  inputDomains _ := atComputedSizeDomain bounds (element.constant.arrayOfLength length)
  outputDomain := element.constant.arrayOfLength (SizeSubstitution.polynomial bounds length)
  precondition _ _ := True
  compute sizes arguments := padArrayValues
    (SizeSubstitution.eval_le bounds length sizes
      (computedSizeAssignment bounds sizes (arguments.val ()).1)
      (fun name => Nat.le_of_lt_succ ((arguments.val ()).1 name).isLt))
    filler (arguments.val ()).2

/-- Existing computed-frame padding already consists of zero-coded fillers. -/
theorem padComputedArray_realizable (element : EncodedDomain Empty)
    (length : MvPolynomial NewParameter ℕ)
    (bounds : NewParameter → MvPolynomial Parameter ℕ)
    (filler : element.Carrier Empty.elim)
    (zero : ArrayEncoding.bits (element.encode Empty.elim filler) =
      List.replicate (element.width Empty.elim) false) :
    (padComputedArray element length bounds filler).Realizable := by
  let computation := padComputedArray element length bounds filler
  let capacity := SizeSubstitution.polynomial bounds length
  let source := atComputedSizeDomain bounds (element.constant.arrayOfLength length)
  let target := (computedSizeDomain bounds).prod (element.constant.arrayOfLength capacity)
  let viewed := encodingMap source target (fun sizes frame =>
    (frame.1, computation.compute sizes ⟨fun _ => frame, trivial⟩))
  have ready : viewed.Realizable := by
    apply encodingMap_realizable
    · intro sizes
      simp [source, target, atComputedSizeDomain, boundedSigma_widthPolynomial,
        width, capacity, SizeSubstitution.polynomial]
    · intro sizes frame
      rw [bits_prod_encode]
      change ArrayEncoding.bits ((boundedSigma (computedSizeDomain bounds)
        (computedSizeAssignment bounds) (element.constant.arrayOfLength length)
        (SizeSubstitution.polynomial bounds (element.constant.arrayOfLength length).widthPolynomial)
        (computedSizeWidth_bound bounds (element.constant.arrayOfLength length))).encode sizes frame) = _
      rw [boundedSigma_encode_bits]
      apply congrArg (fun payload => ArrayEncoding.bits
        ((computedSizeDomain bounds).encode sizes frame.1) ++ payload)
      rw [bits_setWidth _ (computedSizeWidth_bound bounds _ sizes frame.1)]
      simp only [arrayOfLength_encode_bits, ArrayEncoding.bits_encode, constant_encode_bits]
      let fits := SizeSubstitution.eval_le bounds length sizes
        (computedSizeAssignment bounds sizes frame.1)
        (fun name => Nat.le_of_lt_succ (frame.1 name).isLt)
      change (List.ofFn (fun index => ArrayEncoding.bits
        (element.encode Empty.elim (frame.2 index)))).flatten ++ _ =
        (List.ofFn (fun index => ArrayEncoding.bits (element.encode Empty.elim
          (padArrayValues fits filler frame.2 index)))).flatten
      have mapped := map_padArrayValues fits filler frame.2
        (fun value => ArrayEncoding.bits (element.encode Empty.elim value))
      rw [mapped, padArrayValues_list, zero, List.flatten_append]
      simp [SizeSubstitution.polynomial,
        width, Nat.sub_mul]
  exact ready.snd

end Polytime2.Computation
