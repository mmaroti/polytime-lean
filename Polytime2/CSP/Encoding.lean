import Polytime2.CSP.Instance
import Polytime2.Encoding.Records
import Polytime2.Encoding.BinaryEncoding

/-! # Canonical dense relational instances and assignments

A scope table of arity `k` has carrier `(Fin k → Fin N) → Bool` and exactly
`N^k` canonical bits. Its recursively nested array codec orders tuples by their
first coordinate, then the remaining coordinates. In particular arity zero
has one bit even at `N = 0`. Tables are internal presentations of Mathlib
relational structures, with no extra mathematical constraints.

A fixed finite signature is ordered once by the existing named-record codec.
An assignment uses the existing fixed-carrier codec at each of its `N`
positions. No satisfiability assumption enters either domain.
-/

namespace Polytime2.CSP

open FirstOrder FirstOrder.Language EncodedDomain

/-- Separate the first scope coordinate from the remaining coordinates. -/
def scopeSplit (size arity : ℕ) :
    ((Fin (arity + 1) → Fin size) → Bool) ≃ (Fin size → (Fin arity → Fin size) → Bool) where
  toFun := fun table first rest => table (Fin.cons first rest)
  invFun := fun rows scope => rows (scope 0) (Fin.tail scope)
  left_inv := by intro table; funext scope; simp
  right_inv := by intro rows; funext first rest; rfl

private noncomputable def scopeCodec : (arity : ℕ) →
    Σ domain : EncodedDomain Unit,
      ∀ sizes, ((Fin arity → Fin (sizes ())) → Bool) ≃ domain.Carrier sizes
  | 0 => ⟨booleans, fun _ => {
      toFun := fun table => table Fin.elim0
      invFun := fun bit _ => bit
      left_inv := by intro table; funext scope; exact congrArg table (Subsingleton.elim _ _)
      right_inv := fun _ => rfl }⟩
  | arity + 1 =>
      let previous := scopeCodec arity
      ⟨previous.1.array (), fun sizes =>
        (scopeSplit (sizes ()) arity).trans (Equiv.piCongrRight fun _ => previous.2 sizes)⟩

/-- Fixed-arity dense tables reuse the Boolean and nested-array codecs. -/
noncomputable def scopeDomain (arity : ℕ) : EncodedDomain Unit :=
  (scopeCodec arity).1.reindex (fun sizes => (Fin arity → Fin (sizes ())) → Bool)
    (scopeCodec arity).2

/-- Splitting a scope changes only its mathematical presentation. -/
theorem scopeDomain_succ_bits (arity : ℕ) (sizes : Unit → ℕ)
    (table : (Fin (arity + 1) → Fin (sizes ())) → Bool) :
    ArrayEncoding.bits ((scopeDomain (arity + 1)).encode sizes table) =
      ArrayEncoding.bits (((scopeDomain arity).array ()).encode sizes (scopeSplit (sizes ()) arity table)) := by
  dsimp only [scopeDomain, scopeCodec, reindex, array, arrayOfLength, ofCodec]
  simp only [ArrayEncoding.bits_cast, ArrayEncoding.bits_encode]
  congr 2

/-- Every tuple has one bit, including the unique empty tuple. -/
theorem scopeDomain_widthPolynomial (arity : ℕ) :
    (scopeDomain arity).widthPolynomial = MvPolynomial.X () ^ arity := by
  change (scopeCodec arity).1.widthPolynomial = _
  induction arity with
  | zero => norm_num [scopeCodec, booleans]
  | succ arity hypothesis =>
    simp [scopeCodec, array, reindex, hypothesis, pow_succ, mul_comm]

private theorem scopeCodec_encode_surjective (arity : ℕ) (sizes : Unit → ℕ) :
    Function.Surjective ((scopeCodec arity).1.encode sizes) := by
  induction arity generalizing sizes with
  | zero => exact booleans_encode_surjective sizes
  | succ arity hypothesis => exact array_encode_surjective _ hypothesis () sizes

variable (L : Language.{0, 0}) [L.IsRelational]

/-- A relational structure is equivalent to its Boolean scope tables. This
classical equivalence only changes the mathematical interpretation of codecs;
the bits themselves are still the ordinary Boolean tables. -/
noncomputable def instanceTablesEquiv (variableCount : ℕ) :
    Instance L variableCount ≃
      ((symbol : RelationSymbol L) → (Fin symbol.1 → Fin variableCount) → Bool) := by
  classical
  exact {
    toFun := fun input symbol tuple => decide (input.RelMap symbol.2 tuple)
    invFun := fun tables => {
      funMap := fun symbol => isEmptyElim symbol
      RelMap := fun symbol tuple => tables ⟨_, symbol⟩ tuple = true }
    left_inv := by
      intro input
      apply Structure.ext
      · funext arity symbol; exact isEmptyElim symbol
      · funext arity symbol tuple
        change (decide (input.RelMap symbol tuple) = true) = input.RelMap symbol tuple
        simp
    right_inv := by
      intro tables
      funext symbol tuple
      rcases symbol with ⟨arity, symbol⟩
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      rfl }

variable [Fintype (RelationSymbol L)]

/-- Canonical dense instances use the existing named record of scope tables. -/
noncomputable def instanceDomain : EncodedDomain Unit :=
  (namedRecord (fun symbol : RelationSymbol L => scopeDomain symbol.1)).reindex
    (fun sizes => Instance L (sizes ())) (fun sizes => instanceTablesEquiv L (sizes ()))

/-- The exact instance width is the sum of `N^arity` over all fixed symbols. -/
theorem instanceDomain_widthPolynomial :
    (instanceDomain L).widthPolynomial = ∑ symbol : RelationSymbol L, MvPolynomial.X () ^ symbol.1 := by
  classical
  change (record (Fintype.card (RelationSymbol L))
    (fun index => scopeDomain ((Fintype.equivFin (RelationSymbol L)).symm index).1)).widthPolynomial = _
  rw [record_widthPolynomial]
  simp only [scopeDomain_widthPolynomial]
  exact (Equiv.sum_comp (Fintype.equivFin (RelationSymbol L)).symm
    (fun symbol : RelationSymbol L => (MvPolynomial.X () : MvPolynomial Unit ℕ) ^ symbol.1))

/-- Every bit pattern of the exact dense-instance width represents a relational
structure. In particular, empty relations and nullary relation bits impose no
extra decoding conditions. -/
theorem instanceDomain_encode_surjective (sizes : Unit → ℕ) :
    Function.Surjective ((instanceDomain L).encode sizes) := by
  apply reindex_encode_surjective
  apply namedRecord_encode_surjective
  intro symbol
  exact reindex_encode_surjective _ _ _ sizes (scopeCodec_encode_surjective symbol.1 sizes)

/-- Dense instance decoding is total at the exact width. This asserts no
computational property of arbitrary codecs. -/
theorem instanceDomain_decode_total (sizes : Unit → ℕ)
    (bits : BitVec ((instanceDomain L).width sizes)) :
    ∃ input, (instanceDomain L).decode sizes bits = some input :=
  ((instanceDomain L).encode_surjective_iff_decode_total sizes).mp
    (instanceDomain_encode_surjective L sizes) bits

/-- Assignment values are ordinary carrier elements with the existing finite
codec. Invalid element codes are rejected by the array decoder. -/
noncomputable def assignmentDomain (Carrier : Type) [Fintype Carrier] : EncodedDomain Unit :=
  ((fixed (Fintype.equivFin Carrier) : EncodedDomain Empty).constant).array ()

/-- Assignment width is linear in the variable count with a fixed coefficient. -/
theorem assignmentDomain_widthPolynomial (Carrier : Type) [Fintype Carrier] :
    (assignmentDomain Carrier).widthPolynomial =
      MvPolynomial.X () * MvPolynomial.C (Nat.clog 2 (Fintype.card Carrier)) := by
  simp [assignmentDomain, array, reindex, constant, width, fixed]

end Polytime2.CSP
