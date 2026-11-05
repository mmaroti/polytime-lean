import Polytime2.Graph.Construction
import Polytime2.Arrays.Contains
import Polytime2.Arrays.FiniteSubsets

/-! # Certified recovery of an assignment from an occurrence clique

A variable is true exactly when a selected positive literal mentions it.
The computation is total on finite subsets; its satisfaction contract assumes
that the supplied subset is a clique of the required size.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.SAT

open EncodedDomain Polytime2.Computation

variable {Parameter : Type} [Fintype Parameter]

private noncomputable def scanInputs (wires length : MvPolynomial Parameter ℕ) : Option Bool → EncodedDomain Parameter
  | none => (literalDomain wires).arrayOfLength length
  | some false => finiteSubsets length
  | some true => arrayPosition wires

private noncomputable def positiveFlags (wires length : MvPolynomial Parameter ℕ) :=
  arrayTabulate (scanInputs wires length) booleans length (fun sizes arguments index => by
    classical
    let literals : Fin (MvPolynomial.eval sizes length) → Literal (Fin (MvPolynomial.eval sizes wires)) := arguments none
    let selected : Finset (Fin (MvPolynomial.eval sizes length)) := arguments (some false)
    let atom : Fin (MvPolynomial.eval sizes wires) := arguments (some true)
    exact decide (index ∈ selected ∧ literals index = (atom, false)))

private theorem positiveFlags_realizable (wires length : MvPolynomial Parameter ℕ) :
    (positiveFlags wires length).Realizable := by
  classical
  apply arrayTabulate_realizable
  let inputs := Sum.elim (scanInputs wires length) (fun _ : Unit => arrayPosition length)
  have literal := (Realizable.Internal.arrayLookupWithIndex_realizable
    (literalDomain wires) (arrayPosition length) (fun _ index => index.val)
    (arrayPosition_value length) length).onArguments inputs (fun _ _ => True)
    (fun name => if name then .inl none else .inr ())
    (by intro name; cases name <;> rfl) (by intro sizes arguments; exact (arguments.val (.inr ())).isLt)
  have membership := (Realizable.Internal.arrayLookupWithIndex_realizable booleans
    (arrayPosition length) (fun _ index => index.val) (arrayPosition_value length) length).reinterpretInputs
    (fun name => if name then finiteSubsets length else arrayPosition length)
    (fun name sizes value => match name with
      | false => value
      | true => finiteSubsetEquiv _ value)
    (by intro name sizes; cases name <;> rfl)
    (by intro name sizes value; cases name <;> rfl)
    (fun _ _ => True) (by intro sizes arguments valid; exact (arguments false).isLt)
  have selected := membership.onArguments inputs (fun _ _ => True)
    (fun name => if name then .inl (some false) else .inr ())
    (by intro name; cases name <;> rfl) (by intros; trivial)
  have zero := (booleanOperation_realizable (Parameter := Parameter)
    (fun _ : Empty → Bool => false)).onResults inputs (fun _ _ => True)
    (fun empty => nomatch empty) (by intros; trivial) (fun empty => nomatch empty)
  have target := Realizable.pairOutputs inputs (arrayPosition wires) booleans (fun _ _ => True)
    (fun _ arguments => arguments.val (.inl (some true))) (fun _ _ => false)
    (Realizable.argument inputs (.inl (some true)) (fun _ _ => True)) zero
  have equal := (elementsEqual_realizable (literalDomain wires)).onResults inputs (fun _ _ => True)
    (fun name _ arguments => if name then (arguments.val (.inl (some true)), false)
      else arguments.val (.inl none) (arguments.val (.inr ()))) (by intros; trivial) (by
        intro name
        cases name
        · exact literal
        · exact target)
  have combined := (booleanOperation_realizable (Parameter := Parameter)
    (fun flags : Bool → Bool => flags false && flags true)).onResults inputs (fun _ _ => True)
    (fun name _ arguments => if name then
      decide (arguments.val (.inl none) (arguments.val (.inr ())) = (arguments.val (.inl (some true)), false))
      else decide (arguments.val (.inr ()) ∈ (show Finset _ from arguments.val (.inl (some false)))))
    (by intros; trivial) (by
      intro name
      cases name
      · apply selected.withSpecification (fun _ _ => True) _ (by intros; trivial)
        intro sizes arguments valid
        apply Bool.eq_iff_iff.mpr
        simp [onResults, reinterpretInputs, Realizable.Internal.arrayLookupWithIndex,
          finiteSubsetEquiv]
      · exact equal)
  apply combined.withSpecification (fun _ _ => True) _ (by intros; trivial)
  intro sizes arguments valid
  apply Bool.eq_iff_iff.mpr
  simp [onResults, booleanOperation]

private noncomputable def positiveSelected (wires length : MvPolynomial Parameter ℕ) :=
  (arrayContains booleans length).onResults (scanInputs wires length) (fun _ _ => True)
    (fun name sizes arguments => match name with
      | false => (positiveFlags wires length).compute sizes arguments
      | true => true) (by intros; trivial)

private theorem positiveSelected_realizable (wires length : MvPolynomial Parameter ℕ) :
    (positiveSelected wires length).Realizable := by
  apply (arrayContains_realizable booleans length).onResults
  intro name
  cases name
  · exact positiveFlags_realizable wires length
  · exact (booleanOperation_realizable (Parameter := Parameter)
      (fun _ : Empty → Bool => true)).onResults (scanInputs wires length) (fun _ _ => True)
      (fun empty => nomatch empty) (by intros; trivial) (fun empty => nomatch empty)

private noncomputable def flatInputs (wires length : MvPolynomial Parameter ℕ) : Bool → EncodedDomain Parameter
  | false => (literalDomain wires).arrayOfLength length
  | true => finiteSubsets length

private noncomputable def flatAssignment (wires length : MvPolynomial Parameter ℕ) :=
  arrayTabulate (flatInputs wires length) booleans wires
    (fun sizes arguments atom => (positiveSelected wires length).compute sizes
      ⟨(fun name => match name with
        | none => arguments false | some false => arguments true | some true => atom), trivial⟩)

private theorem flatAssignment_realizable (wires length : MvPolynomial Parameter ℕ) :
    (flatAssignment wires length).Realizable := by
  apply arrayTabulate_realizable
  have scan := (positiveSelected_realizable wires length).onArguments
    (Sum.elim (flatInputs wires length) (fun _ : Unit => arrayPosition wires)) (fun _ _ => True)
    (fun name => match name with | none => .inl false | some false => .inl true | some true => .inr ())
    (by rintro (_ | (_ | _)) <;> rfl) (by intros; trivial)
  exact scan.withSpecification (fun _ _ => True) _ (by intros; trivial) (by intros; rfl)

/-- Recover a Boolean assignment from a formula and a numbered occurrence set.
Variables without selected positive occurrences receive false. -/
noncomputable def reverseClique (wires clauses : MvPolynomial Parameter ℕ) :=
  (flatAssignment wires (clauses * MvPolynomial.C 3)).onResults
    (fun name : Bool => if name then finiteSubsets (clauses * MvPolynomial.C 3)
      else (clauseDomain wires).arrayOfLength clauses) (fun _ _ => True)
    (fun name sizes arguments => match name with
      | false => (arrayFlattenRecords (literalDomain wires) 3 clauses).compute sizes
          ⟨fun _ => arguments.val false, trivial⟩
      | true => arguments.val true) (by intros; trivial)

theorem reverseClique_realizable (wires clauses : MvPolynomial Parameter ℕ) :
    (reverseClique wires clauses).Realizable := by
  apply (flatAssignment_realizable wires (clauses * MvPolynomial.C 3)).onResults
  intro name
  cases name
  · exact (arrayFlattenRecords_realizable (literalDomain wires) 3 clauses).onArguments
      (reverseClique wires clauses).inputDomains (fun _ _ => True) (fun _ => false)
      (by intros; rfl) (by intros; trivial)
  · exact Realizable.argument (reverseClique wires clauses).inputDomains true (fun _ _ => True)

/-- The computed assignment is exactly the mathematical reverse witness under
canonical numbering. -/
theorem reverseClique_compute (wires clauses : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (formula : Fin (MvPolynomial.eval sizes clauses) → Clause (Fin (MvPolynomial.eval sizes wires)))
    (selected : Finset (Fin (MvPolynomial.eval sizes (clauses * MvPolynomial.C 3)))) :
    (reverseClique wires clauses).compute sizes
      ⟨(fun name => match name with | false => formula | true => selected), trivial⟩ =
      cliqueAssignment formula (selected.map (occurrenceNumbering clauses sizes).symm.toEmbedding) := by
  classical
  funext atom
  apply Bool.eq_iff_iff.mpr
  have scanCorrect : (reverseClique wires clauses).compute sizes
      ⟨(fun name => match name with | false => formula | true => selected), trivial⟩ atom = true ↔
      ∃ index ∈ selected, (arrayFlattenRecords (literalDomain wires) 3 clauses).compute sizes
        ⟨fun _ => formula, trivial⟩ index = (atom, false) := by
    dsimp only [reverseClique, onResults, flatAssignment, arrayTabulate, positiveSelected,
      arrayContains, positiveFlags]
    dsimp only [arrayFlattenRecords, encodingMap, unaryMap, literalDomain, EncodedDomain.prod,
      arrayPosition, boundedIndexOfWidth, booleans, fixed, ofCodec]
    simp only [decide_eq_true_eq]
  rw [scanCorrect]
  simp only [cliqueAssignment, decide_eq_true_eq]
  constructor
  · rintro ⟨index, present, literal⟩
    obtain ⟨vertex, rfl⟩ := (occurrenceNumbering clauses sizes).surjective index
    refine ⟨vertex, ?_, ?_⟩
    · exact Finset.mem_map.mpr ⟨occurrenceNumbering clauses sizes vertex, present, by simp⟩
    · change (arrayFlattenRecords (literalDomain wires) 3 clauses).compute sizes
        ⟨fun _ => formula, trivial⟩ ((finProdFinEquiv vertex).cast (by simp)) = (atom, false) at literal
      rwa [arrayFlattenRecords_apply] at literal
  · rintro ⟨vertex, present, literal⟩
    obtain ⟨index, present, equal⟩ := Finset.mem_map.mp present
    have numbered : occurrenceNumbering clauses sizes vertex = index := by
      simpa using congrArg (occurrenceNumbering clauses sizes) equal.symm
    refine ⟨index, present, ?_⟩
    rw [← numbered]
    change (arrayFlattenRecords (literalDomain wires) 3 clauses).compute sizes
      ⟨fun _ => formula, trivial⟩ ((finProdFinEquiv vertex).cast (by simp)) = (atom, false)
    rwa [arrayFlattenRecords_apply]

/-- A full-size clique produces a satisfying assignment, including when the
formula has no clauses or contains repeated literals. -/
theorem reverseClique_satisfied (wires clauses : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (formula : Fin (MvPolynomial.eval sizes clauses) → Clause (Fin (MvPolynomial.eval sizes wires)))
    (selected : Finset (Fin (MvPolynomial.eval sizes (clauses * MvPolynomial.C 3))))
    (clique : (numberedOccurrenceGraph wires clauses sizes formula).IsNClique
      (MvPolynomial.eval sizes clauses) selected) :
    Formula.Satisfied ((reverseClique wires clauses).compute sizes
      ⟨(fun name => match name with | false => formula | true => selected), trivial⟩) (List.ofFn formula) := by
  rw [reverseClique_compute]
  apply cliqueAssignment_satisfied
  refine ⟨?_, (Finset.card_map _).trans clique.card_eq⟩
  intro first firstMember second secondMember different
  obtain ⟨first, firstPresent, rfl⟩ := Finset.mem_map.mp firstMember
  obtain ⟨second, secondPresent, rfl⟩ := Finset.mem_map.mp secondMember
  have adjacent := clique.isClique firstPresent secondPresent
    (fun equal => different (congrArg (occurrenceNumbering clauses sizes).symm equal))
  apply (SimpleGraph.map_adj_apply (f := (occurrenceNumbering clauses sizes).toEmbedding)).mp
  simpa only [numberedOccurrenceGraph, Equiv.toEmbedding_apply, Equiv.apply_symm_apply] using adjacent

/-- Standalone machine for the complete reverse witness computation. -/
theorem reverseClique_tm0 (wires clauses : MvPolynomial Parameter ℕ) :
    (reverseClique wires clauses).TM0Realizable :=
  (reverseClique_realizable wires clauses).tm0

/-- Time and assignment length are polynomial in the complete source encoding,
including formula, selected vertices, and size headers. -/
theorem reverseClique_polynomialTime (wires clauses : MvPolynomial Parameter ℕ) :
    Complexity.PolynomialTime (reverseClique wires clauses).inputWord
      (reverseClique wires clauses).outputWord (reverseClique wires clauses).result :=
  (reverseClique_realizable wires clauses).polynomialTime

end Polytime2.SAT
