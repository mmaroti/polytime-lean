import Polytime2.CSP.ReadInstance
import Polytime2.Complexity.BinaryDecoder
import Polytime2.Arrays.BooleanField

/-! # Strict decoding of stored instance word fields

Binary-letter validation precedes the stored-field width guard and dense
instance decoder. Every failure returns none; success returns the actual
relational structure. Host capacity and canonical padding remain internal.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.CSP

open EncodedDomain Polytime2.Computation Complexity

variable (L : FirstOrder.Language.{0, 0}) [L.IsRelational] [Fintype (RelationSymbol L)]

private noncomputable def booleanField : EncodedDomain Bool := storedBooleanField false

private noncomputable def decodeBooleanField : Computation Bool Unit :=
  (storedBooleanFieldView false).followedBy (decodeStoredInstance L) rfl (by intros; trivial)

private theorem decodeBooleanField_realizable : (decodeBooleanField L).Realizable :=
  (storedBooleanFieldView_realizable false).followedBy (decodeStoredInstance_realizable L)
    rfl (by intros; trivial)

private theorem decodeBooleanField_correct (sizes : Bool → ℕ) (field : booleanField.Carrier sizes) :
    (decodeBooleanField L).compute sizes ⟨(fun _ => field), trivial⟩ =
      (instanceDomain L).decodeWord (fun _ => sizes true) ((List.ofFn field.2).map Sum.inl) :=
  (decodeStoredInstance_correct L sizes (fun _ => renamedBooleanFieldValue false sizes field)).trans rfl

/-- Decode a stored word field at a supplied variable count. Every nonbinary
symbol or noncanonical field length rejects before returning a structure. -/
noncomputable def decodeInstanceWordField : Computation Bool Unit :=
  (storedBinaryWordDecoder (MvPolynomial.X false)).followedBy
    (optionalBind booleanField ((instanceDomain L).renameParameters (fun _ : Unit => true))
      (fun sizes field => (decodeBooleanField L).compute sizes ⟨(fun _ => field), trivial⟩))
    rfl (by intros; trivial)

theorem decodeInstanceWordField_realizable : (decodeInstanceWordField L).Realizable := by
  have consumer := optionalBind_realizable booleanField
    ((instanceDomain L).renameParameters (fun _ : Unit => true))
    (fun sizes field => (decodeBooleanField L).compute sizes ⟨(fun _ => field), trivial⟩)
    (decodeBooleanField_realizable L)
  exact (storedBinaryWordDecoder_realizable (MvPolynomial.X false)).followedBy consumer rfl (by intros; trivial)

/-- The composed field decoder agrees with canonical word decoding on every
stored word: invalid letters and all wrong widths return none. -/
theorem decodeInstanceWordField_correct (sizes : Bool → ℕ)
    (field : (boundedArray ((fixed (Fintype.equivFin Letter) : EncodedDomain Empty).constant)
      (MvPolynomial.X false)).Carrier sizes) :
    (decodeInstanceWordField L).compute sizes ⟨(fun _ => field), trivial⟩ =
      (instanceDomain L).decodeWord (fun _ => sizes true) (List.ofFn field.2) := by
  let binary := (storedBinaryWordDecoder (MvPolynomial.X false)).compute sizes ⟨(fun _ => field), trivial⟩
  have matching := storedBinaryWordDecoder_correct (MvPolynomial.X false) sizes field
  change binary.bind (fun bits => (decodeBooleanField L).compute sizes ⟨(fun _ => bits), trivial⟩) = _
  rw [decodeWord_eq_decodeBinaryWord, ← matching]
  change binary.bind _ = (binary.map _).bind _
  cases decoded : binary with
  | none => rfl
  | some bits =>
    change (decodeBooleanField L).compute sizes ⟨(fun _ => bits), trivial⟩ = _
    rw [decodeBooleanField_correct, decodeWord_eq_decodeBinaryWord]
    rw [(decodeBinaryWord_some_iff _ _).mpr rfl]
    rfl

end Polytime2.CSP
