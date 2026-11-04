import Polytime2.CSP.ScopeLookup
import Polytime2.CSP.ScopeSearch
import Polytime2.Computation.Equality

/-! # Certified dense relation images on numbered quotient classes

The input is a relation, a label for each original vertex, and one original
representative per output vertex. The output relates a tuple exactly when an
original related tuple has the indicated labels. No validity assumptions are
needed for this operation; quotient correctness is a separate mathematical
contract on the supplied labels and representatives.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.CSP

open EncodedDomain Polytime2.Computation

variable {Parameter : Type} [Fintype Parameter]

noncomputable def quotientScopeInputs (vertices classes : MvPolynomial Parameter ℕ)
    (arity : ℕ) : Option Bool → EncodedDomain Parameter
  | none => (scopeDomain arity).substitute (fun _ => vertices)
  | some false => (boundedIndex vertices).arrayOfLength vertices
  | some true => (boundedIndex vertices).arrayOfLength classes

/-- Push forward a dense relation through labels and output representatives. -/
noncomputable def quotientScope (vertices classes : MvPolynomial Parameter ℕ)
    (arity : ℕ) : Computation Parameter (Option Bool) := by
  classical
  exact scopeTabulate (quotientScopeInputs vertices classes arity) classes arity
    (fun _ arguments tuple => decide (∃ original, arguments none original = true ∧
      ∀ coordinate, arguments (some false) (original coordinate) =
        arguments (some true) (tuple coordinate)))

theorem quotientScope_realizable (vertices classes : MvPolynomial Parameter ℕ)
    (arity : ℕ) : (quotientScope vertices classes arity).Realizable := by
  classical
  let inputs := quotientScopeInputs vertices classes arity
  let outer := Sum.elim inputs (fun _ : Fin arity => arrayPosition classes)
  let inner := Sum.elim outer (fun _ : Fin arity => arrayPosition vertices)
  let predicate sizes (arguments : ∀ name, (inner name).Carrier sizes) :=
    decide (arguments (.inl (.inl none)) (fun coordinate => arguments (.inr coordinate)) = true ∧
      ∀ coordinate, arguments (.inl (.inl (some false))) (arguments (.inr coordinate)) =
        arguments (.inl (.inl (some true))) (arguments (.inl (.inr coordinate))))
  have related := (scopeLookup_realizable vertices arity).onArguments inner (fun _ _ => True)
    (fun name => match name with
      | none => .inl (.inl none)
      | some coordinate => .inr coordinate)
    (by intro name; cases name <;> rfl) (by intros; trivial)
  have equal (coordinate : Fin arity) :
      (Computation.mk inner booleans (fun _ _ => True) (fun _ arguments =>
        decide (arguments.val (.inl (.inl (some false))) (arguments.val (.inr coordinate)) =
          arguments.val (.inl (.inl (some true))) (arguments.val (.inl (.inr coordinate)))))).Realizable := by
    have original := (Realizable.Internal.arrayLookupWithIndex_realizable
      (boundedIndex vertices) (arrayPosition vertices) (fun _ index => index.val)
      (arrayPosition_value vertices) vertices).onResults inner (fun _ _ => True)
      (fun name _ arguments => match name with
        | false => arguments.val (.inr coordinate)
        | true => arguments.val (.inl (.inl (some false))))
      (by intro sizes arguments; exact (arguments.val (.inr coordinate)).isLt) (by
        intro name
        cases name
        · exact Realizable.argument inner (.inr coordinate) (fun _ _ => True)
        · exact Realizable.argument inner (.inl (.inl (some false))) (fun _ _ => True))
    have representative := (Realizable.Internal.arrayLookupWithIndex_realizable
      (boundedIndex vertices) (arrayPosition classes) (fun _ index => index.val)
      (arrayPosition_value classes) classes).onResults inner (fun _ _ => True)
      (fun name _ arguments => match name with
        | false => arguments.val (.inl (.inr coordinate))
        | true => arguments.val (.inl (.inl (some true))))
      (by intro sizes arguments; exact (arguments.val (.inl (.inr coordinate))).isLt) (by
        intro name
        cases name
        · exact Realizable.argument inner (.inl (.inr coordinate)) (fun _ _ => True)
        · exact Realizable.argument inner (.inl (.inl (some true))) (fun _ _ => True))
    have compared := (elementsEqual_realizable (boundedIndex vertices)).onResults inner (fun _ _ => True)
      (fun name _ arguments => match name with
        | false => arguments.val (.inl (.inl (some false))) (arguments.val (.inr coordinate))
        | true => arguments.val (.inl (.inl (some true))) (arguments.val (.inl (.inr coordinate))))
      (by intros; trivial) (by
        intro name
        cases name
        · exact original.withSpecification (fun _ _ => True) _ (by intros; trivial) (by intros; rfl)
        · exact representative.withSpecification (fun _ _ => True) _ (by intros; trivial) (by intros; rfl))
    exact compared.withSpecification (fun _ _ => True) _ (by intros; trivial) (by intros; rfl)
  let combine (flags : Option (Fin arity) → Bool) :=
    decide (flags none = true ∧ ∀ coordinate, flags (some coordinate) = true)
  have combined := (booleanOperation_realizable combine).onResults inner (fun _ _ => True)
    (fun name _ arguments => match name with
      | none => arguments.val (.inl (.inl none)) (fun coordinate => arguments.val (.inr coordinate))
      | some coordinate => decide
          (arguments.val (.inl (.inl (some false))) (arguments.val (.inr coordinate)) =
            arguments.val (.inl (.inl (some true))) (arguments.val (.inl (.inr coordinate)))))
    (by intros; trivial) (by
      intro name
      cases name with
      | none => exact related.withSpecification (fun _ _ => True) _ (by intros; trivial) (by intros; rfl)
      | some coordinate => exact equal coordinate)
  have predicateReady : (Computation.mk inner booleans (fun _ _ => True)
      (fun sizes arguments => predicate sizes arguments.val)).Realizable := by
    apply combined.withSpecification (fun _ _ => True) _ (by intros; trivial)
    intro sizes arguments valid
    simp only [onResults, booleanOperation, combine, predicate, decide_eq_true_eq]
  have tabulated := scopeTabulate_realizable outer vertices arity
    (fun _ arguments original => decide (arguments (.inl none) original = true ∧
      ∀ coordinate, arguments (.inl (some false)) (original coordinate) =
        arguments (.inl (some true)) (arguments (.inr coordinate)))) predicateReady
  have existsReady := tabulated.followedBy (scopeExists_realizable vertices arity) rfl (by intros; trivial)
  apply scopeTabulate_realizable
  apply existsReady.withSpecification (fun _ _ => True) _ (by intros; trivial)
  intro sizes arguments valid
  apply Bool.eq_iff_iff.mpr
  simp only [followedBy, scopeTabulate, scopeExists, unaryMap, decide_eq_true_eq]

end Polytime2.CSP
