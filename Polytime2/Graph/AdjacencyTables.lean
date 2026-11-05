import Polytime2.Graph.OccurrenceEdge
import Polytime2.Graph.ForwardClique
import Polytime2.Arrays.Tabulate
import Polytime2.Arrays.FlattenRecords

/-! # Certified dense adjacency tables of the occurrence graph

Rows and columns follow clause order and then literal position. All dimensions
are derived from the clause count; variable and clause counts remain independent.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.SAT

open EncodedDomain Polytime2.Computation

variable {Parameter : Type} [Fintype Parameter]

private noncomputable def rowInputs (wires clauses : MvPolynomial Parameter ℕ) : Bool → EncodedDomain Parameter
  | false => (clauseDomain wires).arrayOfLength clauses
  | true => arrayPosition clauses

private noncomputable def rowBlocks (wires clauses : MvPolynomial Parameter ℕ) (left : Fin 3) :=
  arrayTabulate (rowInputs wires clauses) (record 3 (fun _ => booleans)) clauses
    (fun sizes arguments second right => (occurrenceEdge wires clauses left right).compute sizes
      ⟨(fun name => match name with
        | none => arguments false | some false => arguments true | some true => second), trivial⟩)

private theorem rowBlocks_realizable (wires clauses : MvPolynomial Parameter ℕ) (left : Fin 3) :
    (rowBlocks wires clauses left).Realizable := by
  apply arrayTabulate_realizable
  apply Realizable.recordOutputs
  intro right
  have query := (occurrenceEdge_realizable wires clauses left right).onArguments
    (Sum.elim (rowInputs wires clauses) (fun _ : Unit => arrayPosition clauses))
    (fun _ _ => True)
    (fun name => match name with | none => .inl false | some false => .inl true | some true => .inr ())
    (by rintro (_ | (_ | _)) <;> rfl) (by intros; trivial)
  exact query.withSpecification (fun _ _ => True) _ (by intros; trivial) (by intros; rfl)

private noncomputable def edgeRow (wires clauses : MvPolynomial Parameter ℕ) (left : Fin 3) :=
  (rowBlocks wires clauses left).followedBy (arrayFlattenRecords booleans 3 clauses) rfl (by intros; trivial)

private theorem edgeRow_realizable (wires clauses : MvPolynomial Parameter ℕ) (left : Fin 3) :
    (edgeRow wires clauses left).Realizable :=
  (rowBlocks_realizable wires clauses left).followedBy (arrayFlattenRecords_realizable booleans 3 clauses)
    rfl (by intros; trivial)

private noncomputable def rowGroup (wires clauses : MvPolynomial Parameter ℕ) : Computation Parameter Bool :=
  Computation.mk (rowInputs wires clauses)
    (record 3 (fun _ => booleans.arrayOfLength (clauses * MvPolynomial.C 3)))
    (fun _ _ => True) (fun sizes arguments left => (edgeRow wires clauses left).compute sizes arguments)

private theorem rowGroup_realizable (wires clauses : MvPolynomial Parameter ℕ) :
    (rowGroup wires clauses).Realizable := by
  apply Realizable.recordOutputs
  exact edgeRow_realizable wires clauses

private noncomputable def allRowGroups (wires clauses : MvPolynomial Parameter ℕ) :=
  arrayTabulate (fun _ : Unit => (clauseDomain wires).arrayOfLength clauses)
    (record 3 (fun _ => booleans.arrayOfLength (clauses * MvPolynomial.C 3))) clauses
    (fun sizes arguments first => (rowGroup wires clauses).compute sizes
      ⟨(fun name => match name with | false => arguments () | true => first), trivial⟩)

private theorem allRowGroups_realizable (wires clauses : MvPolynomial Parameter ℕ) :
    (allRowGroups wires clauses).Realizable := by
  apply arrayTabulate_realizable
  have grouped := (rowGroup_realizable wires clauses).onArguments
    (Sum.elim (fun _ : Unit => (clauseDomain wires).arrayOfLength clauses)
      (fun _ : Unit => arrayPosition clauses)) (fun _ _ => True)
    (fun name => if name then .inr () else .inl ())
    (by intro name; cases name <;> rfl) (by intros; trivial)
  exact grouped.withSpecification (fun _ _ => True) _ (by intros; trivial) (by intros; rfl)

/-- Construct every adjacency bit on exactly three vertices per clause. -/
noncomputable def occurrenceAdjacencyTables (wires clauses : MvPolynomial Parameter ℕ) :=
  (allRowGroups wires clauses).followedBy
    (arrayFlattenRecords (booleans.arrayOfLength (clauses * MvPolynomial.C 3)) 3 clauses)
    rfl (by intros; trivial)

theorem occurrenceAdjacencyTables_realizable (wires clauses : MvPolynomial Parameter ℕ) :
    (occurrenceAdjacencyTables wires clauses).Realizable :=
  (allRowGroups_realizable wires clauses).followedBy
    (arrayFlattenRecords_realizable (booleans.arrayOfLength (clauses * MvPolynomial.C 3)) 3 clauses)
    rfl (by intros; trivial)


/-- The complete table agrees entry by entry with the mathematical occurrence
graph in the shared numbering used by the forward clique witness. -/
theorem occurrenceAdjacencyTables_correct (wires clauses : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (formula : Fin (MvPolynomial.eval sizes clauses) → Clause (Fin (MvPolynomial.eval sizes wires)))
    (first second : Occurrence (MvPolynomial.eval sizes clauses)) :
    (occurrenceAdjacencyTables wires clauses).compute sizes ⟨fun _ => formula, trivial⟩
      (occurrenceNumbering clauses sizes first) (occurrenceNumbering clauses sizes second) = true ↔
      (occurrenceGraph formula).Adj first second := by
  unfold occurrenceAdjacencyTables followedBy
  change (arrayFlattenRecords (booleans.arrayOfLength (clauses * MvPolynomial.C 3)) 3 clauses).compute
    sizes ⟨fun _ => (allRowGroups wires clauses).compute sizes ⟨fun _ => formula, trivial⟩, trivial⟩
    ((finProdFinEquiv first).cast (by simp)) (occurrenceNumbering clauses sizes second) = true ↔ _
  rw [arrayFlattenRecords_apply]
  unfold allRowGroups arrayTabulate rowGroup edgeRow followedBy
  change (arrayFlattenRecords booleans 3 clauses).compute sizes
    ⟨fun _ => (rowBlocks wires clauses first.2).compute sizes
      ⟨(fun name => match name with | false => formula | true => first.1), trivial⟩, trivial⟩
    ((finProdFinEquiv second).cast (by simp)) = true ↔ _
  rw [arrayFlattenRecords_apply]
  exact occurrenceEdge_correct wires clauses sizes formula first.1 second.1 first.2 second.2

end Polytime2.SAT
