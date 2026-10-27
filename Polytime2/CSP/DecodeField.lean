import Polytime2.CSP.ReadInstance

/-! # Strict decoding of stored instance word fields

The shared field decoder checks binary letters, exact width, and canonical
codes. Its realization uses the full dense-instance codec, and its contract
covers all original stored words.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.CSP

open EncodedDomain Polytime2.Computation Complexity

variable (L : FirstOrder.Language.{0, 0}) [L.IsRelational] [Fintype (RelationSymbol L)]

/-- Decode the instance table word at the supplied variable count. All
nonbinary letters and noncanonical field lengths return none. -/
noncomputable def decodeInstanceWordField : Computation Bool Unit :=
  decodeStoredWord ((instanceDomain L).renameParameters (fun _ : Unit => true)) false

theorem decodeInstanceWordField_realizable : (decodeInstanceWordField L).Realizable :=
  decodeStoredWord_realizable _ _ (instanceFieldBits_realizable L)

/-- The complete decoder agrees with canonical decoding on every stored word. -/
theorem decodeInstanceWordField_correct (sizes : Bool → ℕ)
    (field : (boundedArray ((fixed (Fintype.equivFin Letter) : EncodedDomain Empty).constant)
      (MvPolynomial.X false)).Carrier sizes) :
    (decodeInstanceWordField L).compute sizes ⟨(fun _ => field), trivial⟩ =
      (instanceDomain L).decodeWord (fun _ => sizes true) (List.ofFn field.2) := by
  exact (decodeStoredWord_correct _ false sizes field).trans
    (renameParameters_decodeWord (instanceDomain L) (fun _ : Unit => true) sizes _)

end Polytime2.CSP
