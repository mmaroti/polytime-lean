import Polytime2.Computation.ComputedSizes
import Polytime2.Computation.Fields

/-! # Boolean results of computed-size calls

A Boolean result has a fixed canonical width, so its computed-size frame can
be discarded by the shared field-projection rule.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter NewParameter : Type} [Fintype Parameter] [Fintype NewParameter]

/-- Return the actual Boolean result, discarding the internal runtime counts. -/
noncomputable def retainComputedBoolean (bounds : NewParameter → MvPolynomial Parameter ℕ) :
    Computation Parameter Unit :=
  unaryMap (atComputedSizeDomain bounds (booleans : EncodedDomain NewParameter)) booleans
    (fun _ _ => True) (fun _ frame => frame.val.2)

theorem retainComputedBoolean_realizable (bounds : NewParameter → MvPolynomial Parameter ℕ) :
    (retainComputedBoolean bounds).Realizable := by
  apply Realizable.Internal.fieldProjection _ _ (computedSizeDomain bounds).widthPolynomial
  intro sizes frame
  refine ⟨ArrayEncoding.bits ((computedSizeDomain bounds).encode sizes frame.val.1), [], ?_, by simp⟩
  simp only [List.append_nil, atComputedSizeDomain, boundedSigma_encode_bits]
  congr 1
  have bits : ArrayEncoding.bits ((booleans : EncodedDomain NewParameter).encode
      (computedSizeAssignment bounds sizes frame.val.1) frame.val.2) =
      ArrayEncoding.bits ((booleans : EncodedDomain Parameter).encode sizes frame.val.2) := by
    simp only [booleans, fixed_encode_bits]
  have capacity : MvPolynomial.eval sizes
      (SizeSubstitution.polynomial bounds (booleans : EncodedDomain NewParameter).widthPolynomial) =
      (booleans : EncodedDomain Parameter).width sizes := by
    simp [SizeSubstitution.polynomial, booleans, width]
  have padded := ArrayEncoding.bits_setWidth_congr_of_eq
    (firstCapacity := MvPolynomial.eval sizes
      (SizeSubstitution.polynomial bounds (booleans : EncodedDomain NewParameter).widthPolynomial))
    (secondCapacity := (booleans : EncodedDomain Parameter).width sizes) bits capacity
  simpa only [BitVec.setWidth_eq] using padded

end Polytime2.Computation
