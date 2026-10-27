import Polytime2.Computation.Optional
import Polytime2.Arithmetic.BitComparison

/-! # Rejecting absent inputs before a total decision

Presence is checked for every input. The supplied decision receives only
actual mathematical values; any missing input returns false. Empty payload
carriers require no default values.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter InputName : Type} [Fintype Parameter] [Fintype InputName]

/-- Lift a total Boolean decision to optional inputs, rejecting any absence. -/
noncomputable def optionalDecision (inputs : InputName → EncodedDomain Parameter)
    (answer : ∀ sizes, (∀ name, (inputs name).Carrier sizes) → Bool) :
    Computation Parameter InputName where
  inputDomains name := optional (inputs name)
  outputDomain := booleans
  precondition _ _ := True
  compute sizes arguments := if present : ∀ name, (arguments.val name).isSome = true then
    answer sizes (fun name => (arguments.val name).get (present name)) else false

theorem optionalDecision_realizable (inputs : InputName → EncodedDomain Parameter)
    (answer : ∀ sizes, (∀ name, (inputs name).Carrier sizes) → Bool)
    (ready : (Computation.mk inputs booleans (fun _ _ => True)
      (fun sizes arguments => answer sizes arguments.val)).Realizable) :
    (optionalDecision inputs answer).Realizable := by
  classical
  let computation := optionalDecision inputs answer
  let condition := fun sizes (arguments : computation.Arguments sizes) =>
    decide (∀ name, (arguments name).isSome = true)
  have guard := (booleanOperation_realizable (Parameter := Parameter)
    (fun flags : InputName → Bool => decide (∀ name, flags name = true))).onResults
      computation.inputDomains (fun _ _ => True)
      (fun name _ arguments => (arguments.val name).isSome) (by intros; trivial) (by
        intro name
        exact (optionalIsSome_realizable (inputs name)).onArguments computation.inputDomains
          (fun _ _ => True) (fun _ => name) (by intros; rfl) (by intros; trivial))
  apply Realizable.ofCases (computation := computation) condition guard
  · let selected := fun sizes arguments => True ∧ condition sizes arguments = true
    let values sizes (arguments : {arguments : computation.Arguments sizes // selected sizes arguments}) name :=
      (arguments.val name).get ((of_decide_eq_true arguments.property.2) name)
    have active := ready.onResults computation.inputDomains selected (fun name sizes arguments => values sizes arguments name) (by intros; trivial) (by
      intro name
      exact (optionalGet_realizable (inputs name)).onArguments computation.inputDomains selected
        (fun _ => name) (by intros; rfl) (by
          intro sizes arguments
          exact (of_decide_eq_true arguments.property.2) name))
    apply active.withSpecification selected _ (by intros; trivial)
    intro sizes arguments valid
    change answer sizes _ = if present : ∀ name, (arguments name).isSome = true then _ else false
    rw [dite_eq_left (of_decide_eq_true valid.2)]
  · let rejected := fun sizes arguments => True ∧ condition sizes arguments = false
    have absent := (booleanOperation_realizable (Parameter := Parameter)
      (fun _ : Empty → Bool => false)).onResults computation.inputDomains rejected
        (fun empty => empty.elim) (by intros; trivial) (fun empty => empty.elim)
    apply absent.withSpecification rejected _ (by intros; trivial)
    intro sizes arguments valid
    change false = if present : ∀ name, (arguments name).isSome = true then _ else false
    rw [dite_eq_right (by
      intro present
      have accepted : condition sizes arguments = true := decide_eq_true present
      rw [valid.2] at accepted
      contradiction)]

end Polytime2.Computation
