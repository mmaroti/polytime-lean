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
  (arrayTransform Empty.elim letterDomain (record (Fintype.card Letter) (fun _ => booleans)) length
    (fun _ _ letter index => decide (letter = (Fintype.equivFin Letter).symm index))).onResults
      (fun _ => letterDomain.arrayOfLength length) (fun _ _ => True)
      (fun name _ arguments => match name with | .inl empty => nomatch empty | .inr () => arguments.val ())
      (by intros; trivial)

private theorem assignmentRows_realizable (length : MvPolynomial Unit ℕ) : (assignmentRows length).Realizable := by
  have step : (arrayTransformStep Empty.elim letterDomain (record (Fintype.card Letter) (fun _ => booleans))
      (fun _ _ letter index => decide (letter = (Fintype.equivFin Letter).symm index))).Realizable := by
    let context : Empty ⊕ Unit → EncodedDomain Unit := Sum.elim Empty.elim (fun _ => letterDomain)
    apply Realizable.recordOutputs context (Fintype.card Letter) (fun _ => booleans) (fun _ _ => True)
    intro index
    have tested := (letterTest_realizable (fun letter => decide (letter = (Fintype.equivFin Letter).symm index))).onArguments
      context (fun _ _ => True) (fun _ => .inr ()) (by intros; rfl) (by intros; trivial)
    exact tested.withSpecification (fun _ _ => True) _ (by intros; trivial) (by
      intros
      simp only [onResults, letterTest, unaryMap]
      exact Bool.decide_congr Iff.rfl)
  apply (arrayTransform_realizable Empty.elim letterDomain (record (Fintype.card Letter) (fun _ => booleans))
    length _ step).onResults
  intro name
  cases name with
  | inl empty => cases empty
  | inr singleton => exact Realizable.argument _ () (fun _ _ => True)

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
  simp only [wordAssignment, followedBy, assignmentRows, onResults, arrayTransform,
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
