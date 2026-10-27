import Polytime2.CSP.Encoding
import Polytime2.Complexity.StoredFieldDecode

/-! # Canonical decoding of stored dense instance fields

The mathematical target is the instance codec at the supplied variable count.
Its full-codec proof supplies the exact-width decoder; the shared field rule
owns width validation, extraction, and all malformed-field rejection.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.CSP

open EncodedDomain Polytime2.Computation

variable (L : FirstOrder.Language.{0, 0}) [L.IsRelational] [Fintype (RelationSymbol L)]

/-- Dense instance tables use every pattern at their exact mathematical width. -/
theorem instanceFieldBits_realizable :
    (decodeCanonicalBits ((instanceDomain L).renameParameters (fun _ : Unit => true))).Realizable :=
  decodeCanonicalBits_of_full _ (renameParameters_encode_surjective (instanceDomain L)
    (instanceDomain_encode_surjective L) (fun _ : Unit => true))

/-- Decode a stored Boolean instance field, rejecting every wrong length. -/
noncomputable def decodeStoredInstance : Computation Bool Unit :=
  decodeStoredBits ((instanceDomain L).renameParameters (fun _ : Unit => true)) false

theorem decodeStoredInstance_realizable : (decodeStoredInstance L).Realizable :=
  decodeStoredBits_realizable _ _ (instanceFieldBits_realizable L)

/-- The stored-field result agrees with canonical dense-instance decoding on
all contents and lengths, including zero variables and nullary relations. -/
theorem decodeStoredInstance_correct (sizes : Bool → ℕ)
    (arguments : (decodeStoredInstance L).Arguments sizes) :
    (decodeStoredInstance L).compute sizes ⟨arguments, trivial⟩ =
      (instanceDomain L).decodeWord (fun _ => sizes true) ((List.ofFn (arguments ()).2).map Sum.inl) := by
  exact (decodeStoredBits_correct _ false sizes (arguments ())).trans
    (renameParameters_decodeWord (instanceDomain L) (fun _ : Unit => true) sizes _)

end Polytime2.CSP
