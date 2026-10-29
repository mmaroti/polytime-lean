import Polytime2.Complexity.CookLevin.WordPrefix
import Polytime2.Complexity.WordArrays
import Polytime2.Arrays.FlattenRecords

/-! # Certified one-hot input assignments for word circuits

Each external letter becomes its five one-hot bits, in the same coordinate
order used by `encodeWordBits`. Letter tests, array transformation, and record
flattening reuse existing certified operations.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Complexity.CookLevin

open EncodedDomain Polytime2.Computation

attribute [local instance] Classical.propDecidable

private noncomputable def assignmentRows (length : MvPolynomial Unit ℕ) : Computation Unit Unit :=
  mapArray letterDomain (record (Fintype.card Letter) (fun _ => booleans)) length
    (fun _ letter index => decide (letter = (Fintype.equivFin Letter).symm index))

private theorem assignmentRows_realizable (length : MvPolynomial Unit ℕ) : (assignmentRows length).Realizable := by
  apply mapArray_realizable
  apply Realizable.recordOutputs (fun _ : Unit => letterDomain) (Fintype.card Letter)
    (fun _ => booleans) (fun _ _ => True)
  intro index
  exact (letterTest_realizable (fun letter => decide (letter = (Fintype.equivFin Letter).symm index))).withSpecification
    (fun _ _ => True) _ (by intros; trivial) (by intros; exact Bool.decide_congr Iff.rfl)

/-- Prepare exactly the one-hot assignment expected by a word-input circuit. -/
noncomputable def wordAssignment (length : MvPolynomial Unit ℕ) : Computation Unit Unit :=
  (assignmentRows length).followedBy (arrayFlattenRecords booleans (Fintype.card Letter) length)
    rfl (by intros; trivial)

theorem wordAssignment_realizable (length : MvPolynomial Unit ℕ) : (wordAssignment length).Realizable :=
  (assignmentRows_realizable length).followedBy
    (arrayFlattenRecords_realizable booleans (Fintype.card Letter) length) rfl (by intros; trivial)

/-- The constructed bits have exactly the existing circuit input semantics. -/
theorem wordAssignment_correct (length : MvPolynomial Unit ℕ) (sizes : Unit → ℕ)
    (arguments : (wordAssignment length).Arguments sizes)
    (index : Fin (MvPolynomial.eval sizes (length * MvPolynomial.C (Fintype.card Letter)))) :
    (wordAssignment length).compute sizes ⟨arguments, trivial⟩ index =
      encodeWordBits (arguments ()) (index.cast (by simp)) := by
  simp only [wordAssignment, followedBy, assignmentRows, mapArray,
    arrayFlattenRecords, encodingMap, unaryMap, encodeWordBits, MatrixEncoding.flattenEquiv, Equiv.coe_fn_mk]
  exact Bool.decide_congr Iff.rfl

/-- The complete output word is the canonical one-hot encoding of the input list. -/
theorem wordAssignment_list (length : MvPolynomial Unit ℕ) (sizes : Unit → ℕ)
    (arguments : (wordAssignment length).Arguments sizes) :
    List.ofFn ((wordAssignment length).compute sizes ⟨arguments, trivial⟩) =
      List.ofFn (encodeWordBits (List.ofFn (arguments ())).get) := by
  have dimension : MvPolynomial.eval sizes (length * MvPolynomial.C (Fintype.card Letter)) =
      MvPolynomial.eval sizes length * Fintype.card Letter := by simp
  rw [List.ofFn_congr dimension]
  have same : (fun index => (wordAssignment length).compute sizes ⟨arguments, trivial⟩
      (index.cast dimension.symm)) = encodeWordBits (arguments ()) := by
    funext index
    rw [wordAssignment_correct]
    simp only [Fin.cast_cast, Fin.cast_eq_self]
  rw [same]
  exact encodeWordBits_ofFn (arguments ())

end Polytime2.Complexity.CookLevin
