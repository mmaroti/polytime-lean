import Polytime2.Arrays.FoldContract
import Polytime2.Computation.Equality
import Polytime2.Computation.RecordArguments

/-! # Membership in a canonical array

Equality and disjunction are composed through the existing fold. The public
answer is ordinary membership, including for empty arrays and zero-width
encodings. The dense three-SAT compiler uses this operation for clause tables.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

/-- Test whether the supplied element occurs in the array. -/
noncomputable def arrayContains (element : EncodedDomain Parameter)
    (length : MvPolynomial Parameter ℕ) : Computation Parameter Bool := by
  classical
  exact {
    inputDomains := fun name => if name then element else element.arrayOfLength length
    outputDomain := booleans
    precondition := fun _ _ => True
    compute := fun _ arguments => decide (∃ index, arguments.val false index = arguments.val true) }

private theorem fold_or_any {Element : Type} (predicate : Element → Bool)
    (values : List Element) (initial : Bool) :
    values.foldl (fun accumulator value => accumulator || predicate value) initial =
      (initial || values.any predicate) := by
  induction values generalizing initial with
  | nil => simp
  | cons value values hypothesis => simp [hypothesis, Bool.or_assoc]

theorem arrayContains_realizable (element : EncodedDomain Parameter)
    (length : MvPolynomial Parameter ℕ) : (arrayContains element length).Realizable := by
  classical
  let computation := arrayContains element length
  let context : Unit → EncodedDomain Parameter := fun _ => element
  let update (sizes : Parameter → ℕ) (arguments : ∀ name, (context name).Carrier sizes)
      (accumulator : Bool) (value : element.Carrier sizes) :=
    accumulator || decide (value = arguments ())
  let step := arrayFoldStep context element booleans (fun _ _ _ _ => True) update
  have equal := (elementsEqual_realizable element).onArguments step.inputDomains (fun _ _ => True)
    (fun name => if name then .inl () else .inr true)
    (by intro name; cases name <;> rfl) (by intros; trivial)
  have stepReady : step.Realizable := by
    have combined := (booleanOperation_realizable (Parameter := Parameter)
      (fun arguments : Bool → Bool => arguments false || arguments true)).onResults
      step.inputDomains (fun _ _ => True)
      (fun name sizes arguments => if name then decide (arguments.val (.inr true) = arguments.val (.inl ())) else arguments.val (.inr false))
      (by intros; trivial) (by
        intro name
        cases name
        · exact Realizable.argument step.inputDomains (.inr false) (fun _ _ => True)
        · exact equal)
    exact combined.withSpecification (fun _ _ => True) step.compute
      (by intros; trivial) (by intros; rfl)
  have folded := arrayFold_total_realizable context element booleans length update stepReady
  have complete := folded.onResults computation.inputDomains (fun _ _ => True)
    (fun name sizes arguments => match name with
      | .inl _ => arguments.val true
      | .inr false => false
      | .inr true => arguments.val false)
    (by intros; trivial) (by
      intro name
      rcases name with name | flag
      · exact Realizable.argument computation.inputDomains true (fun _ _ => True)
      · cases flag
        · exact (booleanOperation_realizable (Parameter := Parameter)
            (fun _ : Empty → Bool => false)).onResults computation.inputDomains
            (fun _ _ => True) (fun empty => nomatch empty) (by intros; trivial)
            (fun empty => nomatch empty)
        · exact Realizable.argument computation.inputDomains false (fun _ _ => True))
  apply complete.withSpecification (fun _ _ => True) computation.compute (by intros; trivial)
  intro sizes arguments valid
  change ArrayFold.prefixValue (fun accumulator value => accumulator || decide (value = arguments true))
    (arguments false) false (MvPolynomial.eval sizes length) = _
  have taken : (List.ofFn (arguments false)).take (MvPolynomial.eval sizes length) =
      List.ofFn (arguments false) := List.take_of_length_le (by simp)
  simp only [ArrayFold.prefixValue, taken,
    fold_or_any, Bool.false_or, computation, arrayContains]
  apply Bool.eq_iff_iff.mpr
  simp

end Polytime2.Computation
