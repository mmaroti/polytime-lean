import Polytime2.Primitives.BitOperations

/-! # Decoding codecs that use every bit pattern

A surjective canonical encoding is an equivalence with its exact-width bit
vectors. Its inverse preserves those bits, so the existing identity encoding
map realizes decoding. No totality claim is made for arbitrary partial codecs.
-/

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

/-- Interpret an exact-width bit vector when every pattern is a valid code.
The mathematical result is the unique value with those canonical bits. -/
noncomputable def decodeFullCodec (domain : EncodedDomain Parameter)
    (full : ∀ sizes, Function.Surjective (domain.encode sizes)) : Computation Parameter Unit :=
  encodingMap (bitVectors domain.widthPolynomial) domain
    (fun sizes bits => (Equiv.ofBijective (domain.encode sizes)
      ⟨domain.encode_injective sizes, full sizes⟩).symm bits)

theorem decodeFullCodec_realizable (domain : EncodedDomain Parameter)
    (full : ∀ sizes, Function.Surjective (domain.encode sizes)) :
    (decodeFullCodec domain full).Realizable := by
  apply encodingMap_realizable
  · intros; rfl
  · intro sizes bits
    apply congrArg ArrayEncoding.bits
    exact (Equiv.ofBijective (domain.encode sizes)
      ⟨domain.encode_injective sizes, full sizes⟩).apply_symm_apply bits |>.symm

/-- The bit-preserving interpretation agrees with the domain's actual decoder. -/
theorem decodeFullCodec_correct (domain : EncodedDomain Parameter)
    (full : ∀ sizes, Function.Surjective (domain.encode sizes)) (sizes : Parameter → ℕ)
    (bits : BitVec (domain.width sizes)) :
    domain.decode sizes bits = some ((decodeFullCodec domain full).compute sizes ⟨(fun _ => bits), trivial⟩) := by
  have canonical := (Equiv.ofBijective (domain.encode sizes)
    ⟨domain.encode_injective sizes, full sizes⟩).apply_symm_apply bits
  exact (congrArg (domain.decode sizes) canonical.symm).trans (domain.decode_encode sizes _)

end Polytime2.Computation
