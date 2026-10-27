import Polytime2.Computation.FullCodec
import Polytime2.Computation.Optional

/-! # Canonical exact-width decoding contracts

An arbitrary codec specifies decoding but need not have a certified decoder.
This computation fixes the mathematical contract; callers supply realizability
separately. Full codecs reuse their bit-preserving interpretation.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

/-- Decode exact-width bits to an actual value or none. No runtime claim is
implicit in this specification. -/
noncomputable def decodeCanonicalBits (domain : EncodedDomain Parameter) : Computation Parameter Unit :=
  unaryMap (bitVectors domain.widthPolynomial) (optional domain) (fun _ _ => True)
    (fun sizes bits => domain.decode sizes bits.val)

/-- Full codecs have a certified canonical decoder by interpretation and
optional construction; no validation machine is necessary. -/
theorem decodeCanonicalBits_of_full (domain : EncodedDomain Parameter)
    (full : ∀ sizes, Function.Surjective (domain.encode sizes)) :
    (decodeCanonicalBits domain).Realizable := by
  have ready := (decodeFullCodec_realizable domain full).followedBy
    (optionalSome_realizable domain) rfl (by intros; trivial)
  apply ready.withSpecification (fun _ _ => True) (decodeCanonicalBits domain).compute (by intros; trivial)
  intro sizes arguments valid
  exact (decodeFullCodec_correct domain full sizes (arguments ())).symm

/-- An encoding-preserving carrier equivalence transports a certified decoder.
Optional rejection and inactive padding are preserved, including empty carriers. -/
theorem decodeCanonicalBits_reindex (domain : EncodedDomain Parameter)
    (Carrier : (Parameter → ℕ) → Type)
    (equivalence : ∀ sizes, Carrier sizes ≃ domain.Carrier sizes)
    (ready : (decodeCanonicalBits domain).Realizable) :
    (decodeCanonicalBits (domain.reindex Carrier equivalence)).Realizable := by
  have converted := ready.reinterpretOutput (optional (domain.reindex Carrier equivalence))
    (fun sizes value => value.map (equivalence sizes).symm) (by intros; rfl) (by
      intro sizes value
      symm
      apply optional_encode_bits_congr domain (domain.reindex Carrier equivalence) sizes sizes
        (equivalence sizes).symm rfl _ value
      intro element
      simp only [reindex, Equiv.apply_symm_apply])
  exact converted.withSpecification (fun _ _ => True)
    (decodeCanonicalBits (domain.reindex Carrier equivalence)).compute (by intros; trivial) (by intros; rfl)

end Polytime2.Computation
