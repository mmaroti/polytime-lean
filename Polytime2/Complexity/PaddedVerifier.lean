import Polytime2.Complexity.WitnessCounts
import Polytime2.Complexity.WitnessSelection
import Polytime2.Complexity.StoredDecision

/-! # Certified fixed-length padded witness verification

The total verifier removes nested witness framing before calling the original
verifier. Pair validation guards every partial field extraction. All retained
letters use the existing stored-array codec and computed-size call rules.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Complexity

open EncodedDomain Polytime2.Computation

private noncomputable def fieldInputs : Bool → EncodedDomain Unit :=
  fun name => if name then pairFields.outputDomain else letterDomain.arrayOfLength (MvPolynomial.X ())

private noncomputable def counts (sizes : Unit → ℕ) (arguments : ∀ name, (fieldInputs name).Carrier sizes) :=
  witnessCounts.compute sizes ⟨(fun _ => arguments true), trivial⟩

private def fieldsAgree (sizes : Unit → ℕ) (arguments : ∀ name, (fieldInputs name).Carrier sizes) : Prop :=
  decodePair (List.ofFn (arguments false)) =
    some (List.ofFn (arguments true).1.2, List.ofFn (arguments true).2.2)

private def fieldsFit (sizes : Unit → ℕ) (arguments : ∀ name, (fieldInputs name).Carrier sizes) : Prop :=
  2 * (counts sizes arguments).1.val + 2 * (counts sizes arguments).2.val + 2 ≤ sizes ()

private noncomputable def selectFields : Computation Unit Bool :=
  (selectNestedWitness (MvPolynomial.X ())).onResults fieldInputs fieldsFit
    (fun name sizes arguments => match name with
      | none => arguments.val false
      | some false => (counts sizes arguments.val).1
      | some true => (counts sizes arguments.val).2) (by
      intro sizes arguments
      change 2 * (counts sizes arguments.val).1.val + 2 * (counts sizes arguments.val).2.val + 2 ≤ _
      simpa only [MvPolynomial.eval_X, fieldsFit] using arguments.property)

private theorem selectFields_realizable : selectFields.Realizable := by
  have lengths := witnessCounts_realizable.onArguments fieldInputs fieldsFit
    (fun _ => true) (by intros; rfl) (by intros; trivial)
  apply (selectNestedWitness_realizable (MvPolynomial.X ())).onResults
  intro name
  cases name with
  | none => exact Realizable.argument fieldInputs false fieldsFit
  | some name =>
    cases name
    · exact lengths.fst
    · exact lengths.snd

private theorem innerFit (sizes : Unit → ℕ) (arguments : ∀ name, (fieldInputs name).Carrier sizes)
    (agrees : fieldsAgree sizes arguments) (witness padding : Word)
    (inner : decodePair (List.ofFn (arguments true).2.2) = some (witness, padding)) :
    fieldsFit sizes arguments := by
  have outerLength := decodePair_length agrees
  have innerLength := decodePair_length inner
  have first := witnessCounts_input sizes (arguments true)
  have second := witnessCounts_witness sizes (arguments true) witness padding inner
  change (counts sizes arguments).1.val = _ at first
  change (counts sizes arguments).2.val = _ at second
  dsimp only at outerLength innerLength
  change 2 * (counts sizes arguments).1.val + 2 * (counts sizes arguments).2.val + 2 ≤ sizes ()
  rw [first, second]
  simp only [List.length_ofFn, MvPolynomial.eval_X] at outerLength innerLength ⊢
  omega

private theorem selectFields_correct (sizes : Unit → ℕ) (arguments : ∀ name, (fieldInputs name).Carrier sizes)
    (agrees : fieldsAgree sizes arguments) (witness padding : Word)
    (inner : decodePair (List.ofFn (arguments true).2.2) = some (witness, padding)) :
    List.ofFn (selectFields.compute sizes ⟨arguments, innerFit sizes arguments agrees witness padding inner⟩).2 =
      encodePair (List.ofFn (arguments true).1.2, witness) := by
  change List.ofFn ((selectNestedWitness (MvPolynomial.X ())).compute sizes ⟨_, _⟩).2 = _
  apply selectNestedWitness_normalizes _ _ _ _ _ witness padding
  · have outer := decodePair_canonical agrees
    have nested := decodePair_canonical inner
    simpa only [nested] using outer
  · exact witnessCounts_input sizes (arguments true)
  · exact witnessCounts_witness sizes (arguments true) witness padding inner

private noncomputable def verifySelected (verify : Word → Bool) : Computation Unit Bool :=
  selectFields.followedBy (storedDecision (MvPolynomial.X ()) verify) rfl (by intros; trivial)

private theorem verifySelected_realizable (verify : Word → Bool) (ready : PolynomialTime id encodeBool verify) :
    (verifySelected verify).Realizable :=
  selectFields_realizable.followedBy (storedDecision_realizable (MvPolynomial.X ()) verify ready) rfl (by intros; trivial)

private theorem verifySelected_correct (verify : Word → Bool) (sizes : Unit → ℕ)
    (arguments : ∀ name, (fieldInputs name).Carrier sizes) (agrees : fieldsAgree sizes arguments)
    (witness padding : Word) (inner : decodePair (List.ofFn (arguments true).2.2) = some (witness, padding)) :
    (verifySelected verify).compute sizes ⟨arguments, innerFit sizes arguments agrees witness padding inner⟩ =
      verify (normalizePaddedPair (List.ofFn (arguments false))) := by
  change (storedDecision (MvPolynomial.X ()) verify).compute sizes ⟨_, trivial⟩ = _
  rw [storedDecision_correct, selectFields_correct sizes arguments agrees witness padding inner]
  dsimp only [fieldsAgree] at agrees
  simp only [normalizePaddedPair, agrees, inner]

private noncomputable def fieldVerifier (verify : Word → Bool) : Computation Unit Bool :=
  Computation.mk fieldInputs booleans fieldsAgree
    (fun _ arguments => verify (normalizePaddedPair (List.ofFn (arguments.val false))))

private theorem fieldVerifier_realizable (verify : Word → Bool) (ready : PolynomialTime id encodeBool verify)
    (rejectEmpty : verify [] = false) : (fieldVerifier verify).Realizable := by
  let condition := fun sizes (arguments : ∀ name, (fieldInputs name).Carrier sizes) =>
    (decodePair (List.ofFn (arguments true).2.2)).isSome
  apply Realizable.ofCases condition
  · have guard := ((Realizable.argument fieldInputs true fieldsAgree).snd).followedBy
      (storedPairValid_realizable (MvPolynomial.X ())) rfl (by intros; trivial)
    exact guard.withSpecification fieldsAgree _ (by intros; assumption) (by intros; rfl)
  · let allowed := fun sizes arguments => fieldsAgree sizes arguments ∧ condition sizes arguments = true
    have fits : ∀ sizes arguments, allowed sizes arguments → fieldsFit sizes arguments := by
      intro sizes arguments accepted
      cases inner : decodePair (List.ofFn (arguments true).2.2) with
      | none => simp [allowed, condition, inner] at accepted
      | some pair => exact innerFit sizes arguments accepted.1 pair.1 pair.2 inner
    have called := (verifySelected_realizable verify ready).withPrecondition allowed fits
    apply called.withSpecification allowed
      (fun _ arguments => verify (normalizePaddedPair (List.ofFn (arguments.val false)))) (by intros; assumption)
    intro sizes arguments accepted
    cases inner : decodePair (List.ofFn (arguments true).2.2) with
    | none => simp [allowed, condition, inner] at accepted
    | some pair => exact verifySelected_correct verify sizes arguments accepted.1 pair.1 pair.2 inner
  · let allowed := fun sizes arguments => fieldsAgree sizes arguments ∧ condition sizes arguments = false
    have rejected := (booleanOperation_realizable (Parameter := Unit) (fun _ : Empty → Bool => false)).onResults
      fieldInputs allowed (fun empty => nomatch empty) (by intros; trivial) (fun empty => nomatch empty)
    apply rejected.withSpecification allowed
      (fun _ arguments => verify (normalizePaddedPair (List.ofFn (arguments.val false)))) (by intros; assumption)
    intro sizes arguments accepted
    cases inner : decodePair (List.ofFn (arguments true).2.2) with
    | none =>
      change false = verify (normalizePaddedPair (List.ofFn (arguments false)))
      have outer := accepted.1
      dsimp only [fieldsAgree] at outer
      simp only [normalizePaddedPair, outer, inner, rejectEmpty]
    | some pair => simp [allowed, condition, inner] at accepted

private noncomputable def outerContinuation (verify : Word → Bool) : Computation Unit (Unit ⊕ Unit) :=
  (fieldVerifier verify).onResults
    (Sum.elim (fun _ => letterDomain.arrayOfLength (MvPolynomial.X ())) (fun _ => pairFields.outputDomain))
    (fun sizes arguments => fieldsAgree sizes (fun name => match name with | false => arguments (.inl ()) | true => arguments (.inr ())))
    (fun name _ arguments => match name with | false => arguments.val (.inl ()) | true => arguments.val (.inr ()))
    (by intro sizes arguments; exact arguments.property)

private theorem outerContinuation_realizable (verify : Word → Bool) (ready : PolynomialTime id encodeBool verify)
    (rejectEmpty : verify [] = false) : (outerContinuation verify).Realizable := by
  let context : Unit ⊕ Unit → EncodedDomain Unit :=
    Sum.elim (fun _ => letterDomain.arrayOfLength (MvPolynomial.X ())) (fun _ => pairFields.outputDomain)
  apply (fieldVerifier_realizable verify ready rejectEmpty).onResults
  intro name
  cases name
  · exact Realizable.argument context (.inl ()) _
  · exact Realizable.argument context (.inr ()) _

private theorem outerCompatible (verify : Word → Bool) (sizes : Unit → ℕ)
    (arguments : parsedPair.Arguments sizes) (valid : parsedPair.precondition sizes arguments) :
    (outerContinuation verify).precondition sizes (fun name => match name with
      | .inl () => arguments ()
      | .inr () => parsedPair.compute sizes ⟨arguments, valid⟩) := by
  change (decodePair (List.ofFn (arguments ()))).isSome = true at valid
  cases decoded : decodePair (List.ofFn (arguments ())) with
  | none => simp only [decoded, Option.isSome_none, Bool.false_eq_true] at valid
  | some pair =>
    have fields := parsedPair_correct sizes arguments valid pair.1 pair.2 decoded
    change decodePair (List.ofFn (arguments ())) = some _
    rw [fields]
    exact decoded

private noncomputable def checkedOuter (verify : Word → Bool) : Computation Unit Unit :=
  parsedPair.letThen (outerContinuation verify) (by intros; rfl) rfl (outerCompatible verify)

private theorem checkedOuter_realizable (verify : Word → Bool) (ready : PolynomialTime id encodeBool verify)
    (rejectEmpty : verify [] = false) : (checkedOuter verify).Realizable :=
  parsedPair_realizable.letThen (outerContinuation_realizable verify ready rejectEmpty)
    (by intros; rfl) rfl (outerCompatible verify)

/-- Verify an input with a nested padded witness by applying the original
verifier to its exactly normalized pair. Malformed pairs normalize to empty. -/
noncomputable def paddedVerifier (verify : Word → Bool) : Computation Unit Unit :=
  Computation.mk (fun _ => letterDomain.arrayOfLength (MvPolynomial.X ())) booleans (fun _ _ => True)
    (fun _ arguments => verify (normalizePaddedPair (List.ofFn (arguments.val ()))))

theorem paddedVerifier_realizable (verify : Word → Bool) (ready : PolynomialTime id encodeBool verify)
    (rejectEmpty : verify [] = false) : (paddedVerifier verify).Realizable := by
  let context := (paddedVerifier verify).inputDomains
  let condition := fun sizes (arguments : ∀ name, (context name).Carrier sizes) =>
    (decodePair (List.ofFn (arguments ()))).isSome
  apply Realizable.ofCases condition
  · exact pairValid_realizable.withSpecification (fun _ _ => True) _ (by intros; trivial) (by intros; rfl)
  · let allowed := fun sizes arguments => True ∧ condition sizes arguments = true
    apply (checkedOuter_realizable verify ready rejectEmpty).withSpecification allowed _ (by
      intro sizes arguments accepted
      exact accepted.2)
    intros
    rfl
  · let allowed := fun sizes arguments => True ∧ condition sizes arguments = false
    have rejected := (booleanOperation_realizable (Parameter := Unit) (fun _ : Empty → Bool => false)).onResults
      context allowed (fun empty => nomatch empty) (by intros; trivial) (fun empty => nomatch empty)
    apply rejected.withSpecification allowed _ (by intros; trivial)
    intro sizes arguments accepted
    change false = verify (normalizePaddedPair (List.ofFn (arguments ())))
    have selected := accepted.2
    change (decodePair (List.ofFn (arguments ()))).isSome = false at selected
    cases decoded : decodePair (List.ofFn (arguments ())) with
    | none => simp only [normalizePaddedPair, decoded, rejectEmpty]
    | some pair => simp only [decoded, Option.isSome_some, Bool.true_eq_false] at selected

/-- The padded verifier is polynomial-time on every raw word. This includes
both framing checks, exact field selection, and the original verifier call. -/
theorem paddedVerifier_polynomialTime (verify : Word → Bool) (ready : PolynomialTime id encodeBool verify)
    (rejectEmpty : verify [] = false) :
    PolynomialTime id encodeBool (fun word => verify (normalizePaddedPair word)) :=
  (paddedVerifier_realizable verify ready rejectEmpty).onWordDecision (fun word => verify (normalizePaddedPair word))

end Polytime2.Complexity
