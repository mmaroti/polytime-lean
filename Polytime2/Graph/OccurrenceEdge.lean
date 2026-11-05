import Polytime2.Graph.LiteralCompatibility

/-! # Certified adjacency queries on actual literal occurrences

The query receives the source clause array and two actual clause coordinates.
Literal positions are fixed components of the nine entries of each edge block.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.SAT

open EncodedDomain Polytime2.Computation

variable {Parameter : Type} [Fintype Parameter]

/-- Source formula and the two clause coordinates of an adjacency query. -/
noncomputable def occurrenceEdgeInputs (wires clauses : MvPolynomial Parameter ℕ) : Option Bool → EncodedDomain Parameter
  | none => (clauseDomain wires).arrayOfLength clauses
  | some _ => arrayPosition clauses

/-- Query the exact mathematical edge predicate, allowing repeated literals. -/
noncomputable def occurrenceEdge (wires clauses : MvPolynomial Parameter ℕ)
    (left right : Fin 3) : Computation Parameter (Option Bool) where
  inputDomains := occurrenceEdgeInputs wires clauses
  outputDomain := booleans
  precondition _ _ := True
  compute sizes arguments := by
    classical
    let formula : Fin (MvPolynomial.eval sizes clauses) → Clause (Fin (MvPolynomial.eval sizes wires)) := arguments.val none
    let first : Fin (MvPolynomial.eval sizes clauses) := arguments.val (some false)
    let second : Fin (MvPolynomial.eval sizes clauses) := arguments.val (some true)
    exact decide (first ≠ second ∧ Literal.Compatible (formula first left) (formula second right))

theorem occurrenceEdge_realizable (wires clauses : MvPolynomial Parameter ℕ)
    (left right : Fin 3) : (occurrenceEdge wires clauses left right).Realizable := by
  classical
  let computation := occurrenceEdge wires clauses left right
  let inputs := computation.inputDomains
  have clauseReady (name : Bool) := (Realizable.Internal.arrayLookupWithIndex_realizable
    (clauseDomain wires) (arrayPosition clauses) (fun _ index => index.val)
    (arrayPosition_value clauses) clauses).onArguments inputs (fun _ _ => True)
    (fun choice => if choice then none else some name) (by intro choice; cases choice <;> rfl)
    (by intro sizes arguments; exact (arguments.val (some name)).isLt)
  have block := (clauseCompatibilityBlock_realizable wires).onResults inputs (fun _ _ => True)
    (fun name _ arguments => arguments.val none (arguments.val (some name)))
    (by intros; trivial) clauseReady
  have row := block.followedBy
    (recordProjection_realizable 3 (fun _ => record 3 (fun _ => booleans)) left) rfl (by intros; trivial)
  have flag := row.followedBy (recordProjection_realizable 3 (fun _ => booleans) right) rfl (by intros; trivial)
  have same := (elementsEqual_realizable (arrayPosition clauses)).onArguments inputs (fun _ _ => True)
    some (by intros; rfl) (by intros; trivial)
  have combined := (booleanOperation_realizable (Parameter := Parameter)
    (fun values : Bool → Bool => !values false && values true)).onResults inputs (fun _ _ => True)
    (fun name _ arguments => if name then
      decide (Literal.Compatible
        (arguments.val none (arguments.val (some false)) left)
        (arguments.val none (arguments.val (some true)) right))
      else decide (arguments.val (some false) = arguments.val (some true))) (by intros; trivial) (by
        intro name
        cases name
        · exact same
        · exact flag)
  apply combined.withSpecification computation.precondition computation.compute (by intros; trivial)
  intro sizes arguments valid
  apply Bool.eq_iff_iff.mpr
  simp [onResults, booleanOperation, computation, occurrenceEdge]


/-- The computed answer is exactly adjacency in the mathematical occurrence
graph, including nonedges within a clause and contradictory literals. -/
theorem occurrenceEdge_correct (wires clauses : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (formula : Fin (MvPolynomial.eval sizes clauses) → Clause (Fin (MvPolynomial.eval sizes wires)))
    (first second : Fin (MvPolynomial.eval sizes clauses)) (left right : Fin 3) :
    (occurrenceEdge wires clauses left right).compute sizes
      ⟨(fun name => match name with | none => formula | some false => first | some true => second), trivial⟩ = true ↔
      (occurrenceGraph formula).Adj (first, left) (second, right) := by
  classical
  change decide (first ≠ second ∧ Literal.Compatible (formula first left) (formula second right)) = true ↔ _
  simp only [decide_eq_true_eq, occurrenceGraph]

end Polytime2.SAT
