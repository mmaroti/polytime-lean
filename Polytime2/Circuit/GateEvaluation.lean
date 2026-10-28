import Polytime2.Circuit.Construction
import Polytime2.Arrays.Operations
import Polytime2.Computation.Conditional

/-! # Evaluating a bounded gate on ordinary Boolean wire values

The gate is a constant or a NAND of two actual finite wire coordinates.
All array reads and Boolean operations use existing certified computations.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Circuit

open EncodedDomain Polytime2.Computation
open Polytime2.Computation.Realizable.Internal

variable {Parameter : Type} [Fintype Parameter]

/-- Evaluate one bounded gate without any acyclicity assumption. -/
noncomputable def evaluateGate (wires : MvPolynomial Parameter ℕ) : Computation Parameter Bool where
  inputDomains name := if name then booleans.arrayOfLength wires else gateDomain wires
  outputDomain := booleans
  precondition _ _ := True
  compute _ arguments := match arguments.val false with
    | .inl value => value
    | .inr pair => !(arguments.val true pair.1 && arguments.val true pair.2)

theorem evaluateGate_realizable (wires : MvPolynomial Parameter ℕ) : (evaluateGate wires).Realizable := by
  let computation := evaluateGate wires
  let inputs := computation.inputDomains
  let operands := (arrayPosition wires).prod (arrayPosition wires)
  let condition := fun sizes (arguments : computation.Arguments sizes) => (arguments false).isLeft
  apply Realizable.ofCases condition
  · have tested := (sumIsLeft_realizable booleans operands).withArguments
      inputs (MultiTape.oneTape false) (fun _ => rfl)
    exact tested.withSpecification _ _ (by intros; trivial) (by intros; rfl)
  · let allowed := fun sizes (arguments : ∀ name, (inputs name).Carrier sizes) =>
      True ∧ condition sizes arguments = true
    let payload := ((sumLeft booleans operands).withArguments inputs (MultiTape.oneTape false)
      (fun _ => rfl)).withPrecondition allowed (by intro sizes arguments accepted; exact accepted.2)
    have extracted : payload.Realizable := ((sumLeft_realizable booleans operands).withArguments
      inputs (MultiTape.oneTape false) (fun _ => rfl)).withPrecondition allowed
        (by intro sizes arguments accepted; exact accepted.2)
    apply extracted.withSpecification _ _ (by intros; assumption)
    intro sizes arguments accepted
    cases equal : arguments false with
    | inl value =>
      simp only [computation, evaluateGate, equal]
      simp [payload, withPrecondition, withArguments, sumLeft, unaryMap,
        MultiTape.oneTape, equal]
    | inr pair => simp [condition, equal] at accepted
  · let allowed := fun sizes (arguments : ∀ name, (inputs name).Carrier sizes) =>
      True ∧ condition sizes arguments = false
    let payload := ((sumRight booleans operands).withArguments inputs (MultiTape.oneTape false)
      (fun _ => rfl)).withPrecondition allowed (by intro sizes arguments accepted; exact accepted.2)
    have extracted : payload.Realizable := ((sumRight_realizable booleans operands).withArguments
      inputs (MultiTape.oneTape false) (fun _ => rfl)).withPrecondition allowed
        (by intro sizes arguments accepted; exact accepted.2)
    have lookup (first : Bool) := (arrayLookupWithIndex_realizable booleans (arrayPosition wires)
      (fun _ position => position.val) (arrayPosition_value wires) wires).onResults inputs allowed
      (fun name sizes arguments => match name with
        | false => if first then (payload.compute sizes arguments).1 else (payload.compute sizes arguments).2
        | true => arguments.val true)
      (by intro sizes arguments; exact (if first then (payload.compute sizes arguments).1 else
        (payload.compute sizes arguments).2).isLt) (by
          intro name
          cases name
          · cases first
            · exact extracted.snd
            · exact extracted.fst
          · exact Realizable.argument inputs true allowed)
    have nand := (booleanOperation_realizable (fun flags : Bool → Bool => !(flags false && flags true))).onResults
      inputs allowed (fun first sizes arguments => arguments.val true
        (if first then (payload.compute sizes arguments).1 else (payload.compute sizes arguments).2))
      (by intros; trivial) lookup
    apply nand.withSpecification _ _ (by intros; assumption)
    intro sizes arguments accepted
    cases equal : arguments false with
    | inl value => simp [condition, equal] at accepted
    | inr pair =>
      have payloadEqual : payload.compute sizes ⟨arguments, accepted⟩ = pair := by
        simp [payload, withPrecondition, withArguments, sumRight, unaryMap,
          MultiTape.oneTape, equal]
      simp only [onResults, booleanOperation, payloadEqual, Bool.false_eq_true,
        ↓reduceIte, computation, evaluateGate, equal]
      exact Bool.and_comm _ _ |> congrArg Bool.not

end Polytime2.Circuit
