import Polytime2.CSP.GadgetEquations
import Polytime2.Arrays.Tabulate
import Polytime2.Arrays.FlattenRecords
import Polytime2.Arrays.Append
import Polytime2.Arrays.Operations
import Polytime2.SAT.TseitinEncoding

/-! # Polynomial arrays of allocation equations

Every source variable contributes a fixed record for its shared coordinates
and domain pool; every clause contributes a fixed record for its clause pool.
Duplicated boundary equations preserve the mathematical quotient and let the
combined equation count be a fixed multiple of the raw variable count.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.CSP.GadgetExpansion

open FirstOrder FirstOrder.Language EncodedDomain Polytime2.Computation GadgetAllocation

private noncomputable def domainEquationIndex (dimension poolSize : ℕ) :
    Fin ((dimension + poolSize) * (1 + 3 * dimension)) ≃
      ((Fin dimension ⊕ Fin poolSize) × Option (Fin 3 × Fin dimension)) :=
  (Fintype.equivFinOfCardEq (by simp [Nat.add_comm])).symm

private noncomputable def clauseEquationIndex (dimension poolSize : ℕ) :
    Fin (poolSize * (1 + 3 * dimension)) ≃ (Fin poolSize × Option (Fin 3 × Fin dimension)) :=
  (Fintype.equivFinOfCardEq (by simp [Nat.add_comm])).symm

variable {L : Language.{0, 0}} [L.IsRelational]
variable {Carrier : Type} [L.Structure Carrier] [Finite Carrier] [Nonempty Carrier]
variable {dimension poolSize : ℕ}
variable (domainFormula : L.Formula (Fin dimension))
variable (clauseFormulas : (Fin 3 → Bool) → L.Formula (Fin 3 × Fin dimension))
variable (enumeration : Pool (Carrier := Carrier) domainFormula clauseFormulas ≃ Fin poolSize)
variable {Parameter : Type} [Fintype Parameter]

/-- All projection equations and boundary equations at one source variable.
Shared slots repeat their boundary equation; pool slots supply their projection
and repeat all boundary equations. Repetition does not change the quotient. -/
noncomputable def domainEquationRow (wires clauses : MvPolynomial Parameter ℕ) : Computation Parameter Unit where
  inputDomains _ := arrayPosition wires
  outputDomain := record ((dimension + poolSize) * (1 + 3 * dimension)) (fun _ =>
    (boundedIndex (allocationSize wires clauses dimension poolSize)).prod
      (boundedIndex (allocationSize wires clauses dimension poolSize)))
  precondition _ _ := True
  compute sizes arguments index :=
    match domainEquationIndex dimension poolSize index with
    | (.inl coordinate, _) =>
      (domainBoundaryEquation domainFormula clauseFormulas enumeration wires clauses coordinate).compute sizes arguments
    | (.inr poolIndex, none) =>
      (domainProjectionEquation domainFormula clauseFormulas enumeration wires clauses
        (enumeration.symm poolIndex)).compute sizes arguments
    | (.inr _, some coordinate) =>
      (domainBoundaryEquation domainFormula clauseFormulas enumeration wires clauses coordinate.2).compute sizes arguments

omit [L.IsRelational] in
theorem domainEquationRow_realizable (wires clauses : MvPolynomial Parameter ℕ) :
    (domainEquationRow domainFormula clauseFormulas enumeration wires clauses).Realizable := by
  apply Realizable.recordOutputs
  intro index
  dsimp only [domainEquationRow]
  rcases domainEquationIndex dimension poolSize index with ⟨slot, edge⟩
  cases slot with
  | inl coordinate =>
    exact domainBoundaryEquation_realizable domainFormula clauseFormulas enumeration wires clauses coordinate
  | inr poolIndex =>
    cases edge with
    | none =>
      exact domainProjectionEquation_realizable domainFormula clauseFormulas enumeration wires clauses
        (enumeration.symm poolIndex)
    | some coordinate => exact domainBoundaryEquation_realizable domainFormula clauseFormulas enumeration wires clauses coordinate.2

private noncomputable def equationRowInputs (wires clauses : MvPolynomial Parameter ℕ) :
    Unit ⊕ Unit → EncodedDomain Parameter :=
  Sum.elim (fun _ => (SAT.clauseDomain wires).arrayOfLength clauses) (fun _ => arrayPosition clauses)

/-- A clause pool's projections and all its boundary identifications. -/
noncomputable def clauseEquationRow (wires clauses : MvPolynomial Parameter ℕ) :
    Computation Parameter (Unit ⊕ Unit) where
  inputDomains := equationRowInputs wires clauses
  outputDomain := record (poolSize * (1 + 3 * dimension)) (fun _ =>
    (boundedIndex (allocationSize wires clauses dimension poolSize)).prod
      (boundedIndex (allocationSize wires clauses dimension poolSize)))
  precondition _ _ := True
  compute sizes arguments index :=
    let clause := arguments.val (.inl ()) (arguments.val (.inr ()))
    match clauseEquationIndex dimension poolSize index with
    | (poolIndex, none) =>
      (clauseProjectionEquation domainFormula clauseFormulas enumeration wires clauses
        (enumeration.symm poolIndex)).compute sizes
        ⟨(fun name => match name with
          | none => arguments.val (.inr ()) | some coordinate => (clause coordinate).2), trivial⟩
    | (_, some coordinate) =>
      (clauseBoundaryEquation domainFormula clauseFormulas enumeration wires clauses coordinate).compute sizes
        ⟨(fun name => match name with
          | .inl _ => (clause coordinate.1).1
          | .inr clauseName => match clauseName with
            | none => arguments.val (.inr ()) | some position => (clause position).2), trivial⟩

omit [L.IsRelational] in
theorem clauseEquationRow_realizable (wires clauses : MvPolynomial Parameter ℕ) :
    (clauseEquationRow domainFormula clauseFormulas enumeration wires clauses).Realizable := by
  let inputs := equationRowInputs wires clauses
  have lookup := (Realizable.Internal.arrayLookupWithIndex_realizable (SAT.clauseDomain wires) (arrayPosition clauses)
    (fun _ index => index.val) (arrayPosition_value clauses) clauses).onResults inputs (fun _ _ => True)
    (fun name _ arguments => match name with
      | false => arguments.val (.inr ()) | true => arguments.val (.inl ())) (by
        intro sizes arguments
        exact (arguments.val (.inr ())).isLt) (by
          intro name
          cases name
          · exact Realizable.argument inputs (.inr ()) (fun _ _ => True)
          · exact Realizable.argument inputs (.inl ()) (fun _ _ => True))
  have literal (coordinate : Fin 3) := lookup.followedBy
    (recordProjection_realizable 3 (fun _ => SAT.literalDomain wires) coordinate) rfl (by intros; trivial)
  apply Realizable.recordOutputs
  intro index
  dsimp only [clauseEquationRow]
  rcases clauseEquationIndex dimension poolSize index with ⟨poolIndex, edge⟩
  cases edge with
  | none =>
    have ready := (clauseProjectionEquation_realizable domainFormula clauseFormulas enumeration wires clauses
      (enumeration.symm poolIndex)).onResults inputs (fun _ _ => True)
      (fun name _ arguments => match name with
        | none => arguments.val (.inr ())
        | some coordinate => (arguments.val (.inl ()) (arguments.val (.inr ())) coordinate).2)
      (by intros; trivial) (by
        intro name
        cases name with
        | none => exact Realizable.argument inputs (.inr ()) (fun _ _ => True)
        | some coordinate => exact (literal coordinate).snd)
    exact ready.withSpecification (fun _ _ => True) _ (by intros; trivial) (by intros; rfl)
  | some coordinate =>
    have ready := (clauseBoundaryEquation_realizable domainFormula clauseFormulas enumeration wires clauses coordinate).onResults
      inputs (fun _ _ => True)
      (fun name _ arguments => match name with
        | .inl _ => (arguments.val (.inl ()) (arguments.val (.inr ())) coordinate.1).1
        | .inr clauseName => match clauseName with
          | none => arguments.val (.inr ())
          | some position => (arguments.val (.inl ()) (arguments.val (.inr ())) position).2)
      (by intros; trivial) (by
        intro name
        rcases name with unitValue | clauseName
        · exact (literal coordinate.1).fst
        · cases clauseName with
          | none => exact Realizable.argument inputs (.inr ()) (fun _ _ => True)
          | some position => exact (literal position).snd)
    exact ready.withSpecification (fun _ _ => True) _ (by intros; trivial) (by intros; rfl)

/-- Tabulate the fixed domain equation record at every source variable. -/
noncomputable def domainEquationRows (wires clauses : MvPolynomial Parameter ℕ) :=
  arrayTabulate (Empty.elim : Empty → EncodedDomain Parameter)
    (domainEquationRow domainFormula clauseFormulas enumeration wires clauses).outputDomain wires
    (fun sizes _ source => (domainEquationRow domainFormula clauseFormulas enumeration wires clauses).compute sizes
      ⟨fun _ => source, trivial⟩)

omit [L.IsRelational] in
theorem domainEquationRows_realizable (wires clauses : MvPolynomial Parameter ℕ) :
    (domainEquationRows domainFormula clauseFormulas enumeration wires clauses).Realizable := by
  apply arrayTabulate_realizable
  exact (domainEquationRow_realizable domainFormula clauseFormulas enumeration wires clauses).onArguments
    (Sum.elim (Empty.elim : Empty → EncodedDomain Parameter) (fun _ : Unit => arrayPosition wires))
    (fun _ _ => True) (fun _ => .inr ()) (by intros; rfl) (by intros; trivial)

/-- Tabulate every clause's equation record, reading the immutable clause array. -/
noncomputable def clauseEquationRows (wires clauses : MvPolynomial Parameter ℕ) :=
  arrayTabulate (fun _ : Unit => (SAT.clauseDomain wires).arrayOfLength clauses)
    (clauseEquationRow domainFormula clauseFormulas enumeration wires clauses).outputDomain clauses
    (fun sizes arguments clause =>
      (clauseEquationRow domainFormula clauseFormulas enumeration wires clauses).compute sizes
        ⟨(fun name => match name with | .inl name => arguments name | .inr _ => clause), trivial⟩)

omit [L.IsRelational] in
theorem clauseEquationRows_realizable (wires clauses : MvPolynomial Parameter ℕ) :
    (clauseEquationRows domainFormula clauseFormulas enumeration wires clauses).Realizable := by
  apply arrayTabulate_realizable
  exact clauseEquationRow_realizable domainFormula clauseFormulas enumeration wires clauses

/-- The two source-wise row counts before flattening. -/
noncomputable def equationArraySize (wires clauses : MvPolynomial Parameter ℕ) (dimension poolSize : ℕ) :=
  wires * MvPolynomial.C ((dimension + poolSize) * (1 + 3 * dimension)) +
    clauses * MvPolynomial.C (poolSize * (1 + 3 * dimension))

omit [Fintype Parameter] in
/-- Equation count depends only on the raw variable count, as required by the
existing quotient compiler. No additional input-derived size is promoted. -/
theorem equationArraySize_eq (wires clauses : MvPolynomial Parameter ℕ) (dimension poolSize : ℕ) :
    equationArraySize wires clauses dimension poolSize =
      allocationSize wires clauses dimension poolSize * MvPolynomial.C (1 + 3 * dimension) := by
  simp only [equationArraySize, allocationSize, map_mul]
  ring

/-- All pool projection and boundary equations, with fixed polynomial length. -/
noncomputable def gadgetEquationArray (wires clauses : MvPolynomial Parameter ℕ) :=
  let element := (boundedIndex (allocationSize wires clauses dimension poolSize)).prod
    (boundedIndex (allocationSize wires clauses dimension poolSize))
  let context : Unit → EncodedDomain Parameter := fun _ => (SAT.clauseDomain wires).arrayOfLength clauses
  let domains := ((domainEquationRows domainFormula clauseFormulas enumeration wires clauses).followedBy
    (arrayFlattenRecords element ((dimension + poolSize) * (1 + 3 * dimension)) wires) rfl
      (by intros; trivial)).onResults context (fun _ _ => True)
        (fun empty => nomatch empty) (by intros; trivial)
  let clauseRows := (clauseEquationRows domainFormula clauseFormulas enumeration wires clauses).followedBy
    (arrayFlattenRecords element (poolSize * (1 + 3 * dimension)) clauses) rfl (by intros; trivial)
  (Computation.mk context
    ((element.arrayOfLength (wires * MvPolynomial.C ((dimension + poolSize) * (1 + 3 * dimension)))).prod
      (element.arrayOfLength (clauses * MvPolynomial.C (poolSize * (1 + 3 * dimension)))))
    (fun _ _ => True) (fun sizes arguments => (domains.compute sizes arguments, clauseRows.compute sizes arguments))).followedBy
      (arrayAppend element (wires * MvPolynomial.C ((dimension + poolSize) * (1 + 3 * dimension)))
        (clauses * MvPolynomial.C (poolSize * (1 + 3 * dimension)))) rfl (by intros; trivial)

omit [L.IsRelational] in
theorem gadgetEquationArray_realizable (wires clauses : MvPolynomial Parameter ℕ) :
    (gadgetEquationArray domainFormula clauseFormulas enumeration wires clauses).Realizable := by
  let element := (boundedIndex (allocationSize wires clauses dimension poolSize)).prod
    (boundedIndex (allocationSize wires clauses dimension poolSize))
  have domains := ((domainEquationRows_realizable domainFormula clauseFormulas enumeration wires clauses).followedBy
    (arrayFlattenRecords_realizable element ((dimension + poolSize) * (1 + 3 * dimension)) wires) rfl
      (by intros; trivial)).onResults
        (fun _ : Unit => (SAT.clauseDomain wires).arrayOfLength clauses) (fun _ _ => True)
        (fun empty => nomatch empty) (by intros; trivial) (fun empty => nomatch empty)
  have clauseRows := (clauseEquationRows_realizable domainFormula clauseFormulas enumeration wires clauses).followedBy
    (arrayFlattenRecords_realizable element (poolSize * (1 + 3 * dimension)) clauses) rfl (by intros; trivial)
  exact (domains.prodMk clauseRows).followedBy
    (arrayAppend_realizable element (wires * MvPolynomial.C ((dimension + poolSize) * (1 + 3 * dimension)))
      (clauses * MvPolynomial.C (poolSize * (1 + 3 * dimension)))) rfl (by intros; trivial)

omit [L.IsRelational] in
/-- Flattening preserves every source-wise equation, with domain rows first. -/
theorem gadgetEquationArray_list (wires clauses : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (input : ((SAT.clauseDomain wires).arrayOfLength clauses).Carrier sizes) :
    List.ofFn ((gadgetEquationArray domainFormula clauseFormulas enumeration wires clauses).compute sizes
      ⟨fun _ => input, trivial⟩) =
      (List.ofFn (fun source : Fin (MvPolynomial.eval sizes wires) => List.ofFn
        ((domainEquationRow domainFormula clauseFormulas enumeration wires clauses).compute sizes
          ⟨fun _ => source, trivial⟩))).flatten ++
      (List.ofFn (fun clause : Fin (MvPolynomial.eval sizes clauses) => List.ofFn
        ((clauseEquationRow domainFormula clauseFormulas enumeration wires clauses).compute sizes
          ⟨(fun name => match name with | .inl _ => input | .inr _ => clause), trivial⟩))).flatten := by
  dsimp only [gadgetEquationArray, followedBy]
  rw [arrayAppend_list]
  dsimp only [onResults]
  rw [arrayFlattenRecords_list, arrayFlattenRecords_list]
  rfl

omit [L.IsRelational] in
/-- Repeated entries in a domain row impose exactly the projection and
boundary conditions, with no extra requirement on the equation predicate. -/
theorem domainEquationRow_forall (wires clauses : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (source : Fin (MvPolynomial.eval sizes wires))
    (predicate : (Fin (MvPolynomial.eval sizes (allocationSize wires clauses dimension poolSize)) ×
      Fin (MvPolynomial.eval sizes (allocationSize wires clauses dimension poolSize))) → Prop) :
    (∀ index, predicate ((domainEquationRow domainFormula clauseFormulas enumeration wires clauses).compute sizes
      ⟨fun _ => source, trivial⟩ index)) ↔
    (∀ value, predicate ((domainProjectionEquation domainFormula clauseFormulas enumeration wires clauses value).compute sizes
      ⟨fun _ => source, trivial⟩)) ∧
    (∀ coordinate, predicate ((domainBoundaryEquation domainFormula clauseFormulas enumeration wires clauses coordinate).compute sizes
      ⟨fun _ => source, trivial⟩)) := by
  constructor
  · intro every
    constructor
    · intro value
      have selected := every ((domainEquationIndex dimension poolSize).symm (.inr (enumeration value), none))
      simpa only [domainEquationRow, domainProjectionEquation, domainPoolPosition, Equiv.apply_symm_apply, Equiv.symm_apply_apply] using selected
    · intro coordinate
      have selected := every ((domainEquationIndex dimension poolSize).symm (.inl coordinate, none))
      simpa only [domainEquationRow, Equiv.apply_symm_apply] using selected
  · rintro ⟨projections, boundaries⟩ index
    dsimp only [domainEquationRow]
    rcases domainEquationIndex dimension poolSize index with ⟨slot, edge⟩
    cases slot with
    | inl coordinate => exact boundaries coordinate
    | inr poolIndex =>
      cases edge with
      | none => exact projections (enumeration.symm poolIndex)
      | some coordinate => exact boundaries coordinate.2

omit [L.IsRelational] in
/-- Every clause boundary is present despite row padding: the fixed pool is
nonempty, even when the source has no variables or clauses. -/
theorem clauseEquationRow_forall (wires clauses : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (input : ((SAT.clauseDomain wires).arrayOfLength clauses).Carrier sizes)
    (clause : Fin (MvPolynomial.eval sizes clauses))
    (predicate : (Fin (MvPolynomial.eval sizes (allocationSize wires clauses dimension poolSize)) ×
      Fin (MvPolynomial.eval sizes (allocationSize wires clauses dimension poolSize))) → Prop) :
    (∀ index, predicate ((clauseEquationRow domainFormula clauseFormulas enumeration wires clauses).compute sizes
      ⟨(fun name => match name with | .inl _ => input | .inr _ => clause), trivial⟩ index)) ↔
    (∀ value, predicate ((clauseProjectionEquation domainFormula clauseFormulas enumeration wires clauses value).compute sizes
      ⟨(fun name => match name with | none => clause | some coordinate => (input clause coordinate).2), trivial⟩)) ∧
    (∀ coordinate : Fin 3 × Fin dimension,
      predicate ((clauseBoundaryEquation domainFormula clauseFormulas enumeration wires clauses coordinate).compute sizes
        ⟨(fun name => match name with
          | .inl _ => (input clause coordinate.1).1
          | .inr clauseName => match clauseName with
            | none => clause | some position => (input clause position).2), trivial⟩)) := by
  classical
  let anchor : Fin poolSize := enumeration ⟨.inl (), fun _ => Classical.choice (inferInstance : Nonempty Carrier)⟩
  constructor
  · intro every
    constructor
    · intro value
      have selected := every ((clauseEquationIndex dimension poolSize).symm (enumeration value, none))
      simpa only [clauseEquationRow, clauseProjectionEquation, clausePoolPosition, Equiv.apply_symm_apply, Equiv.symm_apply_apply] using selected
    · intro coordinate
      have selected := every ((clauseEquationIndex dimension poolSize).symm (anchor, some coordinate))
      simpa only [clauseEquationRow, Equiv.apply_symm_apply] using selected
  · rintro ⟨projections, boundaries⟩ index
    dsimp only [clauseEquationRow]
    rcases clauseEquationIndex dimension poolSize index with ⟨poolIndex, edge⟩
    cases edge with
    | none => exact projections (enumeration.symm poolIndex)
    | some coordinate => exact boundaries coordinate

omit [L.IsRelational] in
/-- A condition holds on the full equation array exactly when it holds on
every domain and clause row. Combine with the two row contracts to discard
all repeated equations without unfolding array traversal. -/
theorem gadgetEquationArray_forall (wires clauses : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (input : ((SAT.clauseDomain wires).arrayOfLength clauses).Carrier sizes)
    (predicate : (Fin (MvPolynomial.eval sizes (allocationSize wires clauses dimension poolSize)) ×
      Fin (MvPolynomial.eval sizes (allocationSize wires clauses dimension poolSize))) → Prop) :
    (∀ index, predicate ((gadgetEquationArray domainFormula clauseFormulas enumeration wires clauses).compute sizes
      ⟨fun _ => input, trivial⟩ index)) ↔
    (∀ source : Fin (MvPolynomial.eval sizes wires), ∀ index,
      predicate ((domainEquationRow domainFormula clauseFormulas enumeration wires clauses).compute sizes
        ⟨fun _ => source, trivial⟩ index)) ∧
    (∀ clause : Fin (MvPolynomial.eval sizes clauses), ∀ index,
      predicate ((clauseEquationRow domainFormula clauseFormulas enumeration wires clauses).compute sizes
        ⟨(fun name => match name with | .inl _ => input | .inr _ => clause), trivial⟩ index)) := by
  rw [← List.forall_mem_ofFn_iff, gadgetEquationArray_list]
  simp only [List.forall_mem_append, List.forall_mem_flatten, List.forall_mem_ofFn_iff]

omit [L.IsRelational] in
/-- The certified array imposes precisely the mathematical pool projections
and domain/clause boundary equations. Its contract mentions actual allocated
variables, without row indices, record padding, or binary capacities. -/
theorem gadgetEquationArray_respects_iff (wires clauses : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (input : ((SAT.clauseDomain wires).arrayOfLength clauses).Carrier sizes)
    {Value : Type*}
    (assignment : Fin (MvPolynomial.eval sizes (allocationSize wires clauses dimension poolSize)) → Value) :
    let place := allocationEquiv enumeration wires clauses dimension sizes
    (∀ index,
      let equation := (gadgetEquationArray domainFormula clauseFormulas enumeration wires clauses).compute sizes
        ⟨fun _ => input, trivial⟩ index
      assignment equation.1 = assignment equation.2) ↔
    (∀ source : Fin (MvPolynomial.eval sizes wires),
      (∀ value, assignment (place (.inr (.inl source, value))) =
        assignment (place (.inr (.inl source, selectedPool domainFormula clauseFormulas (.inl ()) value)))) ∧
      (∀ coordinate, assignment (place (.inr (.inl source,
        poolBoundary (Carrier := Carrier) domainFormula clauseFormulas (.inl ()) coordinate))) =
          assignment (place (.inl (source, coordinate))))) ∧
    (∀ clause : Fin (MvPolynomial.eval sizes clauses),
      (∀ value, assignment (place (.inr (.inr clause, value))) =
        assignment (place (.inr (.inr clause, selectedPool domainFormula clauseFormulas
          (.inr (SAT.Clause.falsifyingPattern (input clause))) value)))) ∧
      (∀ coordinate : Fin 3 × Fin dimension,
        assignment (place (.inr (.inr clause, poolBoundary (Carrier := Carrier) domainFormula clauseFormulas
          (.inr (SAT.Clause.falsifyingPattern (input clause))) coordinate))) =
            assignment (place (.inl ((input clause coordinate.1).1, coordinate.2))))) := by
  dsimp only
  refine (gadgetEquationArray_forall domainFormula clauseFormulas enumeration wires clauses sizes input
    (fun equation => assignment equation.1 = assignment equation.2)).trans ?_
  apply and_congr
  · apply forall_congr'
    intro source
    refine (domainEquationRow_forall domainFormula clauseFormulas enumeration wires clauses sizes source
      (fun equation => assignment equation.1 = assignment equation.2)).trans ?_
    simp only [domainProjectionEquation, domainBoundaryEquation, domainPoolPosition,
      sharedPosition_compute enumeration]
    rfl
  · apply forall_congr'
    intro clause
    refine (clauseEquationRow_forall domainFormula clauseFormulas enumeration wires clauses sizes input clause
      (fun equation => assignment equation.1 = assignment equation.2)).trans ?_
    simp only [clauseProjectionEquation, clauseBoundaryEquation, clausePoolPosition,
      sharedPosition_compute enumeration]
    rfl

end Polytime2.CSP.GadgetExpansion
