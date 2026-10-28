import Polytime2.SAT.TseitinEncoding
import Polytime2.Computation.Conditional

/-! # Certified three-clause emission for one circuit gate

The output reference is supplied separately from the bounded gate. Every
result is a mathematical three-clause block with the canonical record codec.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.SAT

open EncodedDomain Polytime2.Computation

variable {Parameter : Type} [Fintype Parameter]

/-- False selects the gate; true selects its actual output wire. -/
noncomputable def gateClauseInputs (wires : MvPolynomial Parameter ℕ) : Bool → EncodedDomain Parameter :=
  fun name => if name then arrayPosition wires else Circuit.gateDomain wires

/-- Emit all three Tseitin clauses for one bounded gate and output reference. -/
noncomputable def gateClauseBlock (wires : MvPolynomial Parameter ℕ) : Computation Parameter Bool :=
  specification (gateClauseInputs wires) (record 3 (fun _ => clauseDomain wires)) (fun _ _ => True)
    (fun _ arguments => boundedGateClauses (arguments.val true) (arguments.val false))

/-- Forgetting finite storage bounds yields exactly the mathematical clauses. -/
theorem gateClauseBlock_value (wires : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (gateClauseBlock wires).Arguments sizes // True}) :
    (fun index => clauseValue ((gateClauseBlock wires).compute sizes arguments index)) =
      gateClauses (arguments.val true).val (Circuit.gateValue (arguments.val false)) := by
  simp only [gateClauseBlock, specification_compute]
  exact boundedGateClauses_value _ _

private def nandTemplates : Fin 3 → Fin 3 → Fin 3 × Bool :=
  ![![(0, false), (2, false), (2, false)],
    ![(1, false), (2, false), (2, false)],
    ![(0, true), (1, true), (2, true)]]

theorem gateClauseBlock_realizable (wires : MvPolynomial Parameter ℕ) : (gateClauseBlock wires).Realizable := by
  let computation := gateClauseBlock wires
  let inputs := gateClauseInputs wires
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
    have negated := extracted.followedBy
      (booleanOperation_realizable (fun flags : Unit → Bool => !(flags ()))) rfl (by intros; trivial)
    have literal := (Realizable.argument inputs true allowed).prodMk negated
    have clause := Realizable.recordOutputs inputs 3 (fun _ => literalDomain wires) allowed
      (fun _ sizes arguments => (arguments.val true, !(payload.compute sizes arguments))) (fun _ => literal)
    have block := Realizable.recordOutputs inputs 3 (fun _ => clauseDomain wires) allowed
      (fun _ sizes arguments _ => (arguments.val true, !(payload.compute sizes arguments))) (fun _ => clause)
    apply block.withSpecification _ _ (by intros; assumption)
    intro sizes arguments accepted
    cases equal : arguments false with
    | inl value =>
      have payloadEqual : payload.compute sizes ⟨arguments, accepted⟩ = value := by
        simp [payload, withPrecondition, withArguments, sumLeft, unaryMap,
          MultiTape.oneTape, equal]
      simp only [computation, gateClauseBlock, specification_compute, equal,
        boundedGateClauses, payloadEqual]
    | inr pair => simp [condition, equal] at accepted
  · let allowed := fun sizes (arguments : ∀ name, (inputs name).Carrier sizes) =>
      True ∧ condition sizes arguments = false
    let payload := ((sumRight booleans operands).withArguments inputs (MultiTape.oneTape false)
      (fun _ => rfl)).withPrecondition allowed (by intro sizes arguments accepted; exact accepted.2)
    have extracted : payload.Realizable := ((sumRight_realizable booleans operands).withArguments
      inputs (MultiTape.oneTape false) (fun _ => rfl)).withPrecondition allowed
        (by intro sizes arguments accepted; exact accepted.2)
    have instantiated := (instantiateClauses_realizable wires nandTemplates).onResults inputs allowed
      (fun port sizes arguments => match port with
        | 0 => (payload.compute sizes arguments).1
        | 1 => (payload.compute sizes arguments).2
        | 2 => arguments.val true) (by intros; trivial) (by
          intro port
          fin_cases port
          · exact extracted.fst
          · exact extracted.snd
          · exact Realizable.argument inputs true allowed)
    apply instantiated.withSpecification _ _ (by intros; assumption)
    intro sizes arguments accepted
    cases equal : arguments false with
    | inl value => simp [condition, equal] at accepted
    | inr pair =>
      have payloadEqual : payload.compute sizes ⟨arguments, accepted⟩ = pair := by
        simp [payload, withPrecondition, withArguments, sumRight, unaryMap,
          MultiTape.oneTape, equal]
      simp only [computation, gateClauseBlock, specification_compute, equal,
        boundedGateClauses, onResults, instantiateClauses, payloadEqual]
      funext clause position
      fin_cases clause <;> fin_cases position <;> rfl

end Polytime2.SAT
