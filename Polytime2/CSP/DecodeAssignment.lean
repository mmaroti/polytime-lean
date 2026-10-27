import Polytime2.CSP.Encoding
import Polytime2.Computation.FixedArrayDecode
import Polytime2.Complexity.StoredFieldDecode

/-! # Canonical assignment decoding through shared rules

Finite carrier codes are validated by the specialization-fixed array decoder.
The shared stored-field decoder owns letter validation, exact-width checking,
and extraction. Every result contains actual values, with no default element
or inhabitance hypothesis, including for empty template carriers.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.CSP

open EncodedDomain Polytime2.Computation Complexity

variable (Carrier : Type) [Fintype Carrier]

/-- Decode an assignment's exact canonical bits. Unused scalar codes reject. -/
noncomputable def decodeAssignmentBits : Computation Unit Unit :=
  decodeCanonicalBits (assignmentDomain Carrier)

theorem decodeAssignmentBits_realizable : (decodeAssignmentBits Carrier).Realizable :=
  decodeFixedNamedArray_realizable (fixed (Fintype.equivFin Carrier)) ()

/-- Exact-width assignment decoding is the canonical codec decoder. -/
theorem decodeAssignmentBits_correct (sizes : Unit → ℕ)
    (bits : BitVec ((assignmentDomain Carrier).width sizes)) :
    (decodeAssignmentBits Carrier).compute sizes ⟨(fun _ => bits), trivial⟩ =
      (assignmentDomain Carrier).decode sizes bits := rfl

/-- The same certified scalar validation applies at the parsed variable count. -/
theorem assignmentFieldBits_realizable :
    (decodeCanonicalBits ((assignmentDomain Carrier).renameParameters (fun _ : Unit => true))).Realizable := by
  simpa only [assignmentDomain, array_renameParameters, constant_renameParameters] using
    (decodeFixedNamedArray_realizable (Parameter := Bool)
      (fixed (Fintype.equivFin Carrier) : EncodedDomain Empty) true)

/-- Decode a stored Boolean assignment field, rejecting all wrong widths and
unused codes before returning actual carrier values. -/
noncomputable def decodeStoredAssignment : Computation Bool Unit :=
  decodeStoredBits ((assignmentDomain Carrier).renameParameters (fun _ : Unit => true)) false

theorem decodeStoredAssignment_realizable : (decodeStoredAssignment Carrier).Realizable :=
  decodeStoredBits_realizable _ _ (assignmentFieldBits_realizable Carrier)

/-- Every stored Boolean field has exactly the canonical assignment-decoder
answer, including malformed lengths and empty template carriers. -/
theorem decodeStoredAssignment_correct (sizes : Bool → ℕ)
    (arguments : (decodeStoredAssignment Carrier).Arguments sizes) :
    (decodeStoredAssignment Carrier).compute sizes ⟨arguments, trivial⟩ =
      (assignmentDomain Carrier).decodeWord (fun _ => sizes true)
        ((List.ofFn (arguments ()).2).map Sum.inl) := by
  exact (decodeStoredBits_correct _ false sizes (arguments ())).trans
    (renameParameters_decodeWord (assignmentDomain Carrier) (fun _ : Unit => true) sizes _)

/-- Both truncated and overlong witnesses return none. -/
theorem decodeStoredAssignment_wrong_length (sizes : Bool → ℕ)
    (arguments : (decodeStoredAssignment Carrier).Arguments sizes)
    (mismatch : (arguments ()).1.val ≠ sizes true * Nat.clog 2 (Fintype.card Carrier)) :
    (decodeStoredAssignment Carrier).compute sizes ⟨arguments, trivial⟩ = none := by
  change (if accepted : decide ((arguments ()).1.val = _) = true then _ else none) = none
  rw [dite_eq_right]
  simpa [assignmentDomain_widthPolynomial, width] using mismatch

/-- Decode a stored witness directly to the assignment codec used by the
checker. Every malformed letter, width, or scalar code returns none. -/
noncomputable def decodeAssignmentWitnessField : Computation Bool Unit :=
  decodeStoredWord ((assignmentDomain Carrier).renameParameters (fun _ : Unit => true)) false

theorem decodeAssignmentWitnessField_realizable : (decodeAssignmentWitnessField Carrier).Realizable :=
  decodeStoredWord_realizable _ _ (assignmentFieldBits_realizable Carrier)

/-- The complete witness decoder agrees with canonical decoding on every
stored word, with the supplied count as its mathematical assignment length. -/
theorem decodeAssignmentWitnessField_correct (sizes : Bool → ℕ)
    (field : (boundedArray ((fixed (Fintype.equivFin Letter) : EncodedDomain Empty).constant)
      (MvPolynomial.X false)).Carrier sizes) :
    (decodeAssignmentWitnessField Carrier).compute sizes ⟨(fun _ => field), trivial⟩ =
      (assignmentDomain Carrier).decodeWord (fun _ => sizes true) (List.ofFn field.2) := by
  exact (decodeStoredWord_correct _ false sizes field).trans
    (renameParameters_decodeWord (assignmentDomain Carrier) (fun _ : Unit => true) sizes _)

end Polytime2.CSP
