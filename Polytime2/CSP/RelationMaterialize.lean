import Polytime2.CSP.ScopeProgram
import Polytime2.Arrays.Contains
import Polytime2.Computation.Optional

/-! # Canonical dense relations from optional constraint facts

An entry is either an asserted scope or no fact. Materialization uses ordinary
array membership for each target tuple, so repeated facts, empty arrays, and
nullary relations need no extra conditions. The output uses the existing
canonical dense scope codec.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.CSP

open EncodedDomain Polytime2.Computation

variable {Parameter : Type} [Fintype Parameter]

/-- An optional mathematical tuple, with storage choices kept in its codec. -/
noncomputable def relationFactDomain (vertices : MvPolynomial Parameter ℕ) (arity : ℕ) :
    EncodedDomain Parameter :=
  (record arity (fun _ => arrayPosition vertices)).optional

/-- Assert exactly the tuples occurring as actual facts in the input array. -/
noncomputable def materializeRelation (vertices facts : MvPolynomial Parameter ℕ) (arity : ℕ) :
    Computation Parameter Unit := by
  classical
  exact scopeTabulate (fun _ : Unit => (relationFactDomain vertices arity).arrayOfLength facts) vertices arity
    (fun _ arguments tuple => decide (∃ index, arguments () index = some tuple))

theorem materializeRelation_realizable (vertices facts : MvPolynomial Parameter ℕ) (arity : ℕ) :
    (materializeRelation vertices facts arity).Realizable := by
  classical
  let tupleDomain := record arity (fun _ => arrayPosition vertices)
  let context : Unit → EncodedDomain Parameter := fun _ => (relationFactDomain vertices arity).arrayOfLength facts
  let inputs := Sum.elim context (fun _ : Fin arity => arrayPosition vertices)
  have tupleReady := Realizable.recordOutputs inputs arity (fun _ => arrayPosition vertices)
    (fun _ _ => True) (fun coordinate _ arguments => arguments.val (.inr coordinate))
    (fun coordinate => Realizable.argument inputs (.inr coordinate) (fun _ _ => True))
  have present := tupleReady.followedBy (optionalSome_realizable tupleDomain) rfl (by intros; trivial)
  have membership := (arrayContains_realizable (relationFactDomain vertices arity) facts).onResults inputs
    (fun _ _ => True)
    (fun name _ arguments => match name with
      | false => arguments.val (.inl ())
      | true => some (fun coordinate => arguments.val (.inr coordinate))) (by intros; trivial) (by
        intro name
        cases name
        · exact Realizable.argument inputs (.inl ()) (fun _ _ => True)
        · exact present.withSpecification (fun _ _ => True) _ (by intros; trivial) (by intros; rfl))
  apply scopeTabulate_realizable
  apply membership.withSpecification (fun _ _ => True) _ (by intros; trivial)
  intro sizes arguments valid
  apply Bool.eq_iff_iff.mpr
  simp only [onResults, arrayContains, decide_eq_true_eq]

/-- The materialized table has exactly the asserted scopes, independently of
their order and multiplicity in the fact array. -/
theorem materializeRelation_correct (vertices facts : MvPolynomial Parameter ℕ) (arity : ℕ)
    (sizes : Parameter → ℕ)
    (input : (relationFactDomain vertices arity).arrayOfLength facts |>.Carrier sizes)
    (tuple : Fin arity → Fin (MvPolynomial.eval sizes vertices)) :
    (materializeRelation vertices facts arity).compute sizes ⟨fun _ => input, trivial⟩ tuple = true ↔
      ∃ index, input index = some tuple := by
  classical
  simp only [materializeRelation, scopeTabulate, decide_eq_true_eq]

end Polytime2.CSP
