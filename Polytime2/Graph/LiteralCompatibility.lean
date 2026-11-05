import Polytime2.Graph.LiteralEvaluation
import Polytime2.Computation.Equality

/-! # Certified compatibility of two actual literals

Different variables are always compatible. Two occurrences of the same
variable are compatible exactly when their negation bits agree.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.SAT

open EncodedDomain Polytime2.Computation

variable {Parameter : Type} [Fintype Parameter]

/-- Decide whether two literals can be simultaneously true. -/
noncomputable def compatibleLiterals (wires : MvPolynomial Parameter ℕ) : Computation Parameter Bool where
  inputDomains _ := literalDomain wires
  outputDomain := booleans
  precondition _ _ := True
  compute sizes arguments := by
    classical
    let first : Literal (Fin (MvPolynomial.eval sizes wires)) := arguments.val false
    let second : Literal (Fin (MvPolynomial.eval sizes wires)) := arguments.val true
    exact decide (Literal.Compatible first second)

theorem compatibleLiterals_realizable (wires : MvPolynomial Parameter ℕ) :
    (compatibleLiterals wires).Realizable := by
  classical
  let computation := compatibleLiterals wires
  let inputs := computation.inputDomains
  have coordinates (name : Bool) := (pairProjection_realizable (arrayPosition wires) booleans false).onArguments
    inputs (fun _ _ => True) (fun _ => name) (by intros; rfl) (by intros; trivial)
  have signs (name : Bool) := (pairProjection_realizable (arrayPosition wires) booleans true).onArguments
    inputs (fun _ _ => True) (fun _ => name) (by intros; rfl) (by intros; trivial)
  have sameVariable := (elementsEqual_realizable (arrayPosition wires)).onResults inputs (fun _ _ => True)
    (fun name _ arguments => (arguments.val name).1) (by intros; trivial) coordinates
  have sameSign := (elementsEqual_realizable (booleans : EncodedDomain Parameter)).onResults inputs (fun _ _ => True)
    (fun name _ arguments => (arguments.val name).2) (by intros; trivial) signs
  have complete := (booleanOperation_realizable (Parameter := Parameter)
    (fun values : Bool → Bool => !values false || values true)).onResults inputs (fun _ _ => True)
    (fun name _ arguments => if name then decide ((arguments.val false).2 = (arguments.val true).2)
      else decide ((arguments.val false).1 = (arguments.val true).1)) (by intros; trivial) (by
        intro name
        cases name
        · exact sameVariable
        · exact sameSign)
  apply complete.withSpecification computation.precondition computation.compute (by intros; trivial)
  intro sizes arguments valid
  apply Bool.eq_iff_iff.mpr
  simp [onResults, booleanOperation, computation, compatibleLiterals, Literal.Compatible]


/-- The nine compatibility flags for the actual literals of two clauses.
The constructor's separate clause-index test removes edges within a clause. -/
noncomputable def clauseCompatibilityBlock (wires : MvPolynomial Parameter ℕ) : Computation Parameter Bool where
  inputDomains _ := clauseDomain wires
  outputDomain := record 3 (fun _ => record 3 (fun _ => booleans))
  precondition _ _ := True
  compute sizes arguments := by
    classical
    let first : Clause (Fin (MvPolynomial.eval sizes wires)) := arguments.val false
    let second : Clause (Fin (MvPolynomial.eval sizes wires)) := arguments.val true
    exact fun left right => decide (Literal.Compatible (first left) (second right))

theorem clauseCompatibilityBlock_realizable (wires : MvPolynomial Parameter ℕ) :
    (clauseCompatibilityBlock wires).Realizable := by
  classical
  let computation := clauseCompatibilityBlock wires
  let inputs := computation.inputDomains
  apply Realizable.recordOutputs
  intro left
  apply Realizable.recordOutputs
  intro right
  have first := (recordProjection_realizable 3 (fun _ => literalDomain wires) left).onArguments
    inputs (fun _ _ => True) (fun _ => false) (by intros; rfl) (by intros; trivial)
  have second := (recordProjection_realizable 3 (fun _ => literalDomain wires) right).onArguments
    inputs (fun _ _ => True) (fun _ => true) (by intros; rfl) (by intros; trivial)
  have complete := (compatibleLiterals_realizable wires).onResults inputs (fun _ _ => True)
    (fun name _ arguments => if name then arguments.val true right else arguments.val false left)
    (by intros; trivial) (by
      intro name
      cases name
      · exact first
      · exact second)
  exact complete.withSpecification (fun _ _ => True) _ (by intros; trivial) (by intros; rfl)

end Polytime2.SAT
