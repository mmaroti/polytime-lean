import Polytime2.SAT.TseitinEncoding
import Polytime2.Graph.WitnessSelection
import Polytime2.Arrays.Operations
import Polytime2.Computation.RecordArguments
import Polytime2.Arithmetic.BitComparison

/-! # Certified evaluation of an actual literal

Input a literal on the finite variable set and a Boolean assignment. Return
its truth value through existing coordinate lookup and Boolean operations.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.SAT

open EncodedDomain Polytime2.Computation

variable {Parameter : Type} [Fintype Parameter]

/-- Evaluate a literal using its actual variable coordinate and negation bit. -/
noncomputable def evaluateLiteral (wires : MvPolynomial Parameter ℕ) : Computation Parameter Bool where
  inputDomains name := if name then booleans.arrayOfLength wires else literalDomain wires
  outputDomain := booleans
  precondition _ _ := True
  compute sizes arguments := by
    let literal : Literal (Fin (MvPolynomial.eval sizes wires)) := arguments.val false
    let assignment : Fin (MvPolynomial.eval sizes wires) → Bool := arguments.val true
    exact decide (assignment literal.1 ≠ literal.2)

theorem evaluateLiteral_realizable (wires : MvPolynomial Parameter ℕ) :
    (evaluateLiteral wires).Realizable := by
  let computation := evaluateLiteral wires
  let inputs := computation.inputDomains
  have variableReady := (pairProjection_realizable (arrayPosition wires) booleans false).onArguments
    inputs (fun _ _ => True) (fun _ => false) (by intros; rfl) (by intros; trivial)
  have signReady := (pairProjection_realizable (arrayPosition wires) booleans true).onArguments
    inputs (fun _ _ => True) (fun _ => false) (by intros; rfl) (by intros; trivial)
  have valueReady := (Realizable.Internal.arrayLookupWithIndex_realizable booleans (arrayPosition wires)
    (fun _ index => index.val) (arrayPosition_value wires) wires).onResults inputs (fun _ _ => True)
    (fun name _ arguments => match name with
      | false => (arguments.val false).1
      | true => arguments.val true)
    (by intro sizes arguments; exact (arguments.val false).1.isLt) (by
      intro name
      cases name
      · exact variableReady
      · exact Realizable.argument inputs true (fun _ _ => True))
  have combined := (booleanOperation_realizable (Parameter := Parameter)
    (fun values : Bool → Bool => decide (values false ≠ values true))).onResults inputs (fun _ _ => True)
    (fun name _ arguments => if name then (arguments.val false).2
      else arguments.val true (arguments.val false).1) (by intros; trivial) (by
        intro name
        cases name
        · exact valueReady
        · exact signReady)
  exact combined.withSpecification computation.precondition computation.compute
    (by intros; trivial) (by intros; rfl)


/-- Select an actual satisfied position of one clause under an assignment.
The result remains total when all three literals are false. -/
noncomputable def chooseClausePosition (wires : MvPolynomial Parameter ℕ) : Computation Parameter Bool where
  inputDomains name := if name then booleans.arrayOfLength wires else clauseDomain wires
  outputDomain := (fixed (Parameter := Empty) (Equiv.refl (Fin 3))).constant
  precondition _ _ := True
  compute sizes arguments := by
    classical
    let clause : Clause (Fin (MvPolynomial.eval sizes wires)) := arguments.val false
    let assignment : Fin (MvPolynomial.eval sizes wires) → Bool := arguments.val true
    exact truePosition (fun position => decide (Literal.Satisfied assignment (clause position)))

theorem chooseClausePosition_realizable (wires : MvPolynomial Parameter ℕ) :
    (chooseClausePosition wires).Realizable := by
  classical
  let computation := chooseClausePosition wires
  let inputs := computation.inputDomains
  have each (position : Fin 3) : (Computation.mk inputs booleans (fun _ _ => True)
      (fun _ arguments => decide (arguments.val true (arguments.val false position).1 ≠
        (arguments.val false position).2))).Realizable := by
    have literal := (recordProjection_realizable 3 (fun _ => literalDomain wires) position).onArguments
      inputs (fun _ _ => True) (fun _ => false) (by intros; rfl) (by intros; trivial)
    have complete := (evaluateLiteral_realizable wires).onResults inputs (fun _ _ => True)
      (fun name _ arguments => match name with
        | false => arguments.val false position
        | true => arguments.val true) (by intros; trivial) (by
          intro name
          cases name
          · exact literal
          · exact Realizable.argument inputs true (fun _ _ => True))
    apply complete.withSpecification (fun _ _ => True) _ (by intros; trivial)
    intro sizes arguments valid
    apply Bool.eq_iff_iff.mpr
    simp only [onResults, evaluateLiteral, decide_eq_true_eq]
  have finite := selectTrueLiteral_realizable.withConstantSizes (Parameter := Parameter)
  have normalized := finite.reinterpretInputs (fun _ : Fin 3 => (booleans : EncodedDomain Parameter))
    (fun _ _ value => value)
    (by intros; simp [withConstantSizes, selectTrueLiteral, finiteOperation, width, booleans])
    (by intros; simp [withConstantSizes, selectTrueLiteral, finiteOperation,
      constant_encode_bits, booleans, fixed_encode_bits])
    (fun _ _ => True) (by intros; trivial)
  have combined := normalized.onResults inputs (fun _ _ => True)
    (fun position _ arguments => decide (arguments.val true (arguments.val false position).1 ≠
      (arguments.val false position).2)) (by intros; trivial) each
  apply combined.withSpecification computation.precondition computation.compute (by intros; trivial)
  intro sizes arguments valid
  change truePosition (fun position => decide (arguments true (arguments false position).1 ≠
    (arguments false position).2)) =
    truePosition (fun position => decide (Literal.Satisfied (arguments true) (arguments false position)))
  apply congrArg truePosition
  funext position
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, Literal.Satisfied]


/-- Select one literal position for every clause using the supplied assignment. -/
noncomputable def chooseFormulaPositions (wires clauses : MvPolynomial Parameter ℕ) : Computation Parameter Bool where
  inputDomains name := if name then booleans.arrayOfLength wires else (clauseDomain wires).arrayOfLength clauses
  outputDomain := ((fixed (Parameter := Empty) (Equiv.refl (Fin 3))).constant).arrayOfLength clauses
  precondition _ _ := True
  compute _sizes arguments := assignmentPositions (arguments.val false) (arguments.val true)

theorem chooseFormulaPositions_realizable (wires clauses : MvPolynomial Parameter ℕ) :
    (chooseFormulaPositions wires clauses).Realizable := by
  let computation := chooseFormulaPositions wires clauses
  let output : EncodedDomain Parameter := (fixed (Parameter := Empty) (Equiv.refl (Fin 3))).constant
  let context : Unit → EncodedDomain Parameter := fun _ => booleans.arrayOfLength wires
  let operation := fun sizes (arguments : ∀ name, (context name).Carrier sizes)
    (clause : (clauseDomain wires).Carrier sizes) =>
      (chooseClausePosition wires).compute sizes ⟨fun name => match name with
        | false => clause | true => arguments (), trivial⟩
  have step := (chooseClausePosition_realizable wires).onArguments
    (arrayTransformStep context (clauseDomain wires) output operation).inputDomains
    (fun _ _ => True) (fun name => if name then .inl () else .inr ())
    (by intro name; cases name <;> rfl) (by intros; trivial)
  have stepReady : (arrayTransformStep context (clauseDomain wires) output operation).Realizable :=
    step.withSpecification (fun _ _ => True) _ (by intros; trivial) (by intros; rfl)
  have transformed := (arrayTransform_realizable context (clauseDomain wires) output clauses operation stepReady).onArguments
    computation.inputDomains computation.precondition
    (fun name => match name with | .inl _ => true | .inr _ => false)
    (by rintro (name | name) <;> rfl) (by intros; trivial)
  exact transformed.withSpecification computation.precondition computation.compute
    (by intros; trivial) (by intros; rfl)


/-- Every selected position satisfies its source clause under a satisfying
assignment. This is the mathematical forward-witness observation. -/
theorem chooseFormulaPositions_satisfied (wires clauses : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (input : Fin (MvPolynomial.eval sizes clauses) → Clause (Fin (MvPolynomial.eval sizes wires)))
    (assignment : Fin (MvPolynomial.eval sizes wires) → Bool)
    (satisfied : Formula.Satisfied assignment (List.ofFn input))
    (clause : Fin (MvPolynomial.eval sizes clauses)) :
    Literal.Satisfied assignment (input clause
      ((chooseFormulaPositions wires clauses).compute sizes
        ⟨(fun name => match name with | false => input | true => assignment), trivial⟩ clause)) :=
  assignmentPositions_satisfied input assignment satisfied clause

end Polytime2.SAT
