import Polytime2.Complexity.UnaryHeader
import Polytime2.Arrays.SearchGuard
import Polytime2.Arrays.SearchCoordinates

/-! # Validation of unary header separators

Boundary search is followed by a checked lookup of the separator. Missing
boundaries and first non-count letters other than the separator reject.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Complexity

open EncodedDomain Polytime2.Computation

private noncomputable def separatorCheck : Computation Unit (Unit ⊕ Unit) where
  inputDomains := Sum.elim (fun _ => letterDomain.arrayOfLength (MvPolynomial.X ()))
    (fun _ => arraySearchResult (MvPolynomial.X ()))
  outputDomain := booleans
  precondition _ _ := True
  compute _ arguments := by
    classical
    exact (arguments.val (.inr ())).any (fun index => decide (arguments.val (.inl ()) index = .inr 0))

private theorem separatorCheck_realizable : separatorCheck.Realizable := by
  classical
  let computation := separatorCheck
  let missing (_sizes : Unit → ℕ) (arguments : computation.Arguments _sizes) : Bool :=
    (arguments (.inr ())).isNone
  have guard := (arraySearchIsNone_realizable (MvPolynomial.X ())).onArguments
    computation.inputDomains computation.precondition (fun _ => .inr ())
    (by intros; rfl) (by intros; trivial)
  apply Realizable.ofCases (computation := computation) missing guard
  · let allowed sizes arguments := computation.precondition sizes arguments ∧ missing sizes arguments = true
    have constant := booleanOperation_realizable (Parameter := Unit) (fun _ : Empty → Bool => false)
    have prepared := constant.onResults computation.inputDomains allowed (fun empty => empty.elim)
      (by intros; trivial) (fun empty => empty.elim)
    apply prepared.withSpecification allowed _ (by intros; trivial)
    intro sizes arguments valid
    have absent : arguments (.inr ()) = none := Option.isNone_iff_eq_none.mp valid.2
    simp [separatorCheck, computation, absent, booleanOperation, onResults]
  · let allowed sizes arguments := computation.precondition sizes arguments ∧ missing sizes arguments = false
    have found := (arraySearchFound_realizable (MvPolynomial.X ())).onArguments
      computation.inputDomains allowed (fun _ => .inr ()) (by intros; rfl) (by
        intro sizes arguments
        change (arguments.val (.inr ())).isSome = true
        have flag := arguments.property.2
        change (arguments.val (.inr ())).isNone = false at flag
        cases value : arguments.val (.inr ()) <;> simp_all)
    have selected := (arrayLookup_realizable letterDomain (MvPolynomial.X ())).onResults
      computation.inputDomains allowed
      (fun choice sizes arguments => match choice with
      | false => (arguments.val (.inr ())).get (by
          have flag := arguments.property.2
          change (arguments.val (.inr ())).isNone = false at flag
          cases value : arguments.val (.inr ()) <;> simp_all)
      | true => arguments.val (.inl ()))
      (by intros; trivial) (by
        intro choice
        cases choice
        · exact found
        · exact Realizable.argument computation.inputDomains (.inl ()) allowed)
    have tested := selected.followedBy (letterTest_realizable (fun letter => decide (letter = .inr 0)))
      rfl (by intros; trivial)
    apply tested.withSpecification allowed _ (by intros; trivial)
    intro sizes arguments valid
    have present : (arguments (.inr ())).isSome = true := by
      have flag := valid.2
      change (arguments (.inr ())).isNone = false at flag
      cases value : arguments (.inr ()) <;> simp_all
    simp only [followedBy, arrayLookup, onResults, letterTest, unaryMap]
    let test : Fin (MvPolynomial.eval sizes (MvPolynomial.X ())) → Bool :=
      fun index => decide (arguments (.inl ()) index = .inr 0)
    change (_ : Bool) = (_ : Bool)
    calc
      _ = (some ((arguments (.inr ())).get present)).any test := by
        apply Bool.eq_iff_iff.mpr
        simp only [Option.any_some, test, decide_eq_true_eq]
      _ = (arguments (.inr ())).any test := congrArg (fun value => value.any test) (Option.some_get present)
      _ = computation.compute sizes ⟨arguments, valid.1⟩ := by
        change (arguments (.inr ())).any test = (arguments (.inr ())).any _
        apply congrArg (fun predicate => (arguments (.inr ())).any predicate)
        funext index
        apply Bool.eq_iff_iff.mpr
        simp only [test, decide_eq_true_eq]

/-- Test that a word starts with a complete unary header, including its
separator. The payload is unrestricted and remains to be validated. -/
noncomputable def unaryHeaderValid : Computation Unit Unit where
  inputDomains := unaryHeaderBoundary.inputDomains
  outputDomain := booleans
  precondition _ _ := True
  compute sizes arguments := by
    classical
    exact (unaryHeaderBoundary.compute sizes arguments).any
      (fun index => decide (arguments.val () index = .inr 0))

theorem unaryHeaderValid_realizable : unaryHeaderValid.Realizable := by
  have ready := unaryHeaderBoundary_realizable.letThen separatorCheck_realizable
    (by intros; rfl) rfl (by intros; trivial)
  exact ready.withSpecification (fun _ _ => True) unaryHeaderValid.compute
    (by intros; trivial) (by intros; rfl)

private theorem readPairHeader_isSome (word : Word) :
    (readPairHeader word).isSome =
      (word[word.findIdx (fun letter => decide (letter ≠ .inr 1))]?).any
        (fun letter => decide (letter = .inr 0)) := by
  induction word with
  | nil => simp [readPairHeader]
  | cons letter rest hypothesis =>
    by_cases zero : letter = .inr 0
    · subst letter
      simp [readPairHeader, List.findIdx_cons]
    · by_cases one : letter = .inr 1
      · subst letter
        simpa [readPairHeader, List.findIdx_cons] using hypothesis
      · simp [readPairHeader, zero, one, List.findIdx_cons]

/-- The total validator accepts exactly the words on which unary header
parsing succeeds, including malformed words and missing separators. -/
theorem unaryHeaderValid_correct (sizes : Unit → ℕ)
    (letters : Fin (MvPolynomial.eval sizes (MvPolynomial.X ())) → Letter) :
    unaryHeaderValid.compute sizes ⟨(fun _ => letters), trivial⟩ =
      (readPairHeader (List.ofFn letters)).isSome := by
  let flags : Fin (MvPolynomial.eval sizes (MvPolynomial.X ())) → Bool :=
    fun index => decide (letters index = .inr 1)
  let test : Fin (MvPolynomial.eval sizes (MvPolynomial.X ())) → Bool :=
    fun index => decide (letters index = .inr 0)
  have boundary : unaryHeaderBoundary.compute sizes ⟨(fun _ => letters), trivial⟩ =
      ArraySearch.firstFalse flags := by
    apply congrArg ArraySearch.firstFalse
    funext index
    apply Bool.eq_iff_iff.mpr
    simp [flags]
  have validated : unaryHeaderValid.compute sizes ⟨(fun _ => letters), trivial⟩ =
      (ArraySearch.firstFalse flags).any test := by
    unfold unaryHeaderValid
    dsimp only
    rw [boundary]
    apply congrArg (fun predicate => (ArraySearch.firstFalse flags).any predicate)
    funext index
    apply Bool.eq_iff_iff.mpr
    simp [test]
  have counts : (List.ofFn flags).findIdx (! ·) =
      (List.ofFn letters).findIdx (fun letter => decide (letter ≠ .inr 1)) := by
    have mapped : List.ofFn flags = (List.ofFn letters).map (fun letter => decide (letter = .inr 1)) := by
      rw [List.map_ofFn]
      rfl
    rw [mapped, List.findIdx_map]
    congr 1
  rw [validated, readPairHeader_isSome]
  unfold ArraySearch.firstFalse
  split_ifs with within
  · rw [Option.any_some]
    rw [← counts]
    simp only [List.getElem?_ofFn, within, ↓reduceDIte, Option.any_some, test]
  · rw [← counts]
    simp only [List.getElem?_ofFn, within, ↓reduceDIte, Option.any_none]

/-- Header success is decidable in polynomial time on all raw words. This
includes separator validation but places no restriction on the payload. -/
theorem readPairHeader_isSome_polynomialTime :
    PolynomialTime id encodeBool (fun word => (readPairHeader word).isSome) := by
  have specified := unaryHeaderValid_realizable.withSpecification (fun _ _ => True)
    (fun _ arguments => (readPairHeader (List.ofFn (arguments.val ()))).isSome)
    (by intros; trivial) (by
      intro sizes arguments valid
      have eta : arguments = fun _ => arguments () := by funext name; cases name; rfl
      rw [eta]
      exact unaryHeaderValid_correct sizes (arguments ()))
  exact specified.onWordDecision (fun word => (readPairHeader word).isSome)

end Polytime2.Complexity
