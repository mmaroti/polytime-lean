import Polytime2.Arrays.PackingRead
import Polytime2.Primitives.BitOperations

/-! # Stored Boolean fields across named size parameters

The exact count and payload are unchanged when a direct stored Boolean field
is viewed through a named-size reader. Padding stays inside the codec.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain

noncomputable def storedBooleanField {Parameter : Type} [Fintype Parameter]
    (host : Parameter) : EncodedDomain Parameter :=
  boundedArray ((booleans : EncodedDomain Empty).constant) (MvPolynomial.X host)

def renamedBooleanFieldValue {Parameter : Type} [Fintype Parameter]
    (host : Parameter) (sizes : Parameter → ℕ) (field : (storedBooleanField host).Carrier sizes) :
    ((boundedArray (booleans : EncodedDomain Unit) (MvPolynomial.X ())).renameParameters
      (fun _ : Unit => host)).Carrier sizes :=
  ⟨⟨field.1.val, by simpa only [MvPolynomial.eval_X, Function.comp_apply] using field.1.isLt⟩, field.2⟩

variable {Parameter : Type} [Fintype Parameter]

/-- Convert a stored binary field to the named-size reader convention without
changing its count, payload, or canonical bits. -/
noncomputable def storedBooleanFieldView (host : Parameter) : Computation Parameter Unit :=
  encodingMap (storedBooleanField host)
    ((boundedArray (booleans : EncodedDomain Unit) (MvPolynomial.X ())).renameParameters
      (fun _ : Unit => host)) (renamedBooleanFieldValue host)

theorem storedBooleanFieldView_realizable (host : Parameter) :
    (storedBooleanFieldView host).Realizable := by
  apply encodingMap_realizable
  · intro sizes
    simp [storedBooleanField, width, boundedArray, booleans, constant_widthPolynomial,
      renameParameters_widthPolynomial, boundedUnary, ofBoundedCodec]
  · intro sizes field
    symm
    rw [renameParameters_bits]
    exact (boundedArrayConvert_bits
      ((booleans : EncodedDomain Empty).constant : EncodedDomain Parameter)
      (booleans : EncodedDomain Unit) (MvPolynomial.X host) (MvPolynomial.X ())
      sizes (sizes ∘ (fun _ : Unit => host)) (by simp) id
      (by simp [width, booleans])
      (by intro value; simp [constant_encode_bits, booleans, fixed_encode_bits]) field).symm

end Polytime2.Computation
