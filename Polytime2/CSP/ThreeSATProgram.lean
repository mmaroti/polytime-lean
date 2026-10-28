import Polytime2.CSP.ThreeSATClauses
import Polytime2.CSP.Encoding
import Polytime2.Arrays.Contains
import Polytime2.Arrays.Tabulate
import Polytime2.Computation.Dependent

/-! # Certified dense three-SAT instance construction

Each of the eight tables enumerates the ordered variable triples and tests
clause occurrence. Equality, array folds, and tabulation provide the complete
realization without a separate machine implementation.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.CSP.ThreeSAT

open EncodedDomain Polytime2.Computation

variable {Parameter : Type} [Fintype Parameter]

private noncomputable def tableCube (wires count : MvPolynomial Parameter ℕ)
    (pattern : Fin 3 → Bool) : Computation Parameter Unit :=
  arrayTabulate (fun _ => (SAT.clauseDomain wires).arrayOfLength count)
    ((booleans.arrayOfLength wires).arrayOfLength wires) wires
    (fun _ arguments first second third => clauseArrayTable (arguments ()) pattern ![first, second, third])

private theorem tableCube_realizable (wires count : MvPolynomial Parameter ℕ)
    (pattern : Fin 3 → Bool) : (tableCube wires count pattern).Realizable := by
  classical
  let inputs : Unit → EncodedDomain Parameter := fun _ => (SAT.clauseDomain wires).arrayOfLength count
  let firstInputs := Sum.elim inputs (fun _ : Unit => arrayPosition wires)
  let secondInputs := Sum.elim firstInputs (fun _ : Unit => arrayPosition wires)
  let thirdInputs := Sum.elim secondInputs (fun _ : Unit => arrayPosition wires)
  let query sizes (arguments : {arguments : ∀ name, (thirdInputs name).Carrier sizes // True}) :=
    fun position : Fin 3 =>
      (![arguments.val (.inl (.inl (.inr ()))), arguments.val (.inl (.inr ())),
        arguments.val (.inr ())] position, pattern position)
  have queryReady : (Computation.mk thirdInputs (SAT.clauseDomain wires) (fun _ _ => True) query).Realizable := by
    apply Realizable.recordOutputs
    intro position
    have variableReady : (Computation.mk thirdInputs (arrayPosition wires) (fun _ _ => True)
        (fun _ arguments => (![arguments.val (.inl (.inl (.inr ()))),
          arguments.val (.inl (.inr ())), arguments.val (.inr ())] position))).Realizable := by
      fin_cases position
      · exact Realizable.argument thirdInputs (.inl (.inl (.inr ()))) (fun _ _ => True)
      · exact Realizable.argument thirdInputs (.inl (.inr ())) (fun _ _ => True)
      · exact Realizable.argument thirdInputs (.inr ()) (fun _ _ => True)
    have polarityReady := (booleanOperation_realizable (Parameter := Parameter)
      (fun _ : Empty → Bool => pattern position)).onResults thirdInputs (fun _ _ => True)
      (fun empty => nomatch empty) (by intros; trivial) (fun empty => nomatch empty)
    have pair := variableReady.prodMk polarityReady
    exact pair.withSpecification (fun _ _ => True) _ (by intros; trivial) (by intros; rfl)
  have lookup := (arrayContains_realizable (SAT.clauseDomain wires) count).onResults
    thirdInputs (fun _ _ => True)
    (fun name sizes arguments => match name with
      | false => arguments.val (.inl (.inl (.inl ())))
      | true => query sizes arguments)
    (by intros; trivial) (by
      intro name
      cases name
      · exact Realizable.argument thirdInputs (.inl (.inl (.inl ()))) (fun _ _ => True)
      · exact queryReady)
  apply arrayTabulate_realizable
  change (arrayTabulate firstInputs (booleans.arrayOfLength wires) wires
    (fun _ arguments second third => clauseArrayTable (arguments (.inl ())) pattern
      ![arguments (.inr ()), second, third])).Realizable
  apply arrayTabulate_realizable
  change (arrayTabulate secondInputs booleans wires
    (fun _ arguments third => clauseArrayTable (arguments (.inl (.inl ()))) pattern
      ![arguments (.inl (.inr ())), arguments (.inr ()), third])).Realizable
  apply arrayTabulate_realizable
  exact lookup.withSpecification (fun _ _ => True) _ (by intros; trivial)
    (by
      intro sizes arguments valid
      apply Bool.eq_iff_iff.mpr
      simp only [onResults, arrayContains, clauseArrayTable, decide_eq_true_eq]
      rfl)

private theorem tableCube_bits (wires : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (table : (Fin 3 → Fin (MvPolynomial.eval sizes wires)) → Bool) :
    ArrayEncoding.bits (((scopeDomain 3).substitute (fun _ => wires)).encode sizes table) =
      ArrayEncoding.bits ((((booleans.arrayOfLength wires).arrayOfLength wires).arrayOfLength wires).encode
        sizes (fun first second third => table ![first, second, third])) := by
  simp only [substitute_encode_bits, scopeDomain_succ_bits, array_encode_bits,
    arrayOfLength_encode_bits, ArrayEncoding.bits_encode, scopeDomain_zero_bits, booleans, fixed_encode_bits]
  rfl

private noncomputable def tableProgram (wires count : MvPolynomial Parameter ℕ)
    (pattern : Fin 3 → Bool) : Computation Parameter Unit :=
  unaryMap ((SAT.clauseDomain wires).arrayOfLength count)
    ((scopeDomain 3).substitute (fun _ => wires)) (fun _ _ => True)
    (fun _ arguments => clauseArrayTable arguments.val pattern)

private theorem tableProgram_realizable (wires count : MvPolynomial Parameter ℕ)
    (pattern : Fin 3 → Bool) : (tableProgram wires count pattern).Realizable := by
  have converted := (tableCube_realizable wires count pattern).reinterpretOutput
    ((scopeDomain 3).substitute (fun _ => wires))
    (fun _ cube scope => cube (scope 0) (scope 1) (scope 2))
    (by
      intro sizes
      have lengths := congrArg List.length (tableCube_bits wires sizes (fun _ => false))
      simp only [ArrayEncoding.bits, List.length_ofFn] at lengths
      exact lengths)
    (by
      intro sizes cube
      exact tableCube_bits wires sizes (fun scope => cube (scope 0) (scope 1) (scope 2)))
  apply converted.withSpecification (fun _ _ => True) (tableProgram wires count pattern).compute
    (by intros; trivial)
  intro sizes arguments valid
  change (fun scope => clauseArrayTable (arguments ()) pattern ![scope 0, scope 1, scope 2]) =
    clauseArrayTable (arguments ()) pattern
  funext scope
  congr 1
  funext position
  fin_cases position <;> rfl

private theorem instanceTables_bits (wires : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (tables : ∀ symbol : RelationSymbol language,
      (Fin symbol.1 → Fin (MvPolynomial.eval sizes wires)) → Bool) :
    ArrayEncoding.bits (((instanceDomain language).substitute (fun _ => wires)).encode sizes
      ((instanceTablesEquiv language (MvPolynomial.eval sizes wires)).symm tables)) =
    ArrayEncoding.bits ((namedRecord (fun symbol : RelationSymbol language =>
      (scopeDomain symbol.1).substitute (fun _ => wires))).encode sizes tables) := by
  rw [substitute_encode_bits]
  change ArrayEncoding.bits ((namedRecord (fun symbol : RelationSymbol language => scopeDomain symbol.1)).encode
    (SizeSubstitution.assignment (fun _ => wires) sizes)
    ((instanceTablesEquiv language (MvPolynomial.eval sizes wires))
      ((instanceTablesEquiv language (MvPolynomial.eval sizes wires)).symm tables))) = _
  rw [Equiv.apply_symm_apply]
  change ArrayEncoding.bits ((record (Fintype.card (RelationSymbol language))
    (fun index => scopeDomain ((Fintype.equivFin (RelationSymbol language)).symm index).1)).encode
    (SizeSubstitution.assignment (fun _ => wires) sizes)
    (fun index => tables ((Fintype.equivFin (RelationSymbol language)).symm index))) =
    ArrayEncoding.bits ((record (Fintype.card (RelationSymbol language))
    (fun index => (scopeDomain ((Fintype.equivFin (RelationSymbol language)).symm index).1).substitute
      (fun _ => wires))).encode sizes
    (fun index => tables ((Fintype.equivFin (RelationSymbol language)).symm index)))
  apply record_encode_bits_congr
  intro index
  exact (substitute_encode_bits _ _ _ _).symm

/-- Convert the clause array to the existing dense relational instance on
exactly its finite variable set. No assumptions on clauses are required. -/
noncomputable def instanceProgram (wires count : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  unaryMap ((SAT.clauseDomain wires).arrayOfLength count)
    ((instanceDomain language).substitute (fun _ => wires)) (fun _ _ => True)
    (fun _ arguments => instanceOfFormula (List.ofFn arguments.val))

theorem instanceProgram_realizable (wires count : MvPolynomial Parameter ℕ) :
    (instanceProgram wires count).Realizable := by
  classical
  let inputs : Unit → EncodedDomain Parameter := fun _ => (SAT.clauseDomain wires).arrayOfLength count
  let fields := fun symbol : RelationSymbol language => (scopeDomain symbol.1).substitute (fun _ => wires)
  let results (symbol : RelationSymbol language) (sizes : Parameter → ℕ)
      (arguments : {arguments : ∀ name, (inputs name).Carrier sizes // True}) : (fields symbol).Carrier sizes :=
    fun scope => decide ((instanceOfFormula (List.ofFn (arguments.val ()))).RelMap symbol.2 scope)
  have fieldReady (symbol : RelationSymbol language) :
      (Computation.mk inputs (fields symbol) (fun _ _ => True) (results symbol)).Realizable := by
    rcases symbol with ⟨arity, pattern, equality⟩
    subst arity
    apply (tableProgram_realizable wires count pattern).withSpecification (fun _ _ => True) _
      (by intros; trivial)
    intro sizes arguments valid
    funext scope
    apply Bool.eq_iff_iff.mpr
    simp only [results, decide_eq_true_eq]
    exact clauseArrayTable_correct (arguments ()) pattern scope
  have packed := Realizable.namedRecordOutputs inputs fields (fun _ _ => True) results fieldReady
  have converted := packed.reinterpretOutput
    ((instanceDomain language).substitute (fun _ => wires))
    (fun sizes tables => (instanceTablesEquiv language (MvPolynomial.eval sizes wires)).symm tables)
    (by
      intro sizes
      have lengths := congrArg List.length (instanceTables_bits wires sizes (fun _ _ => false))
      simp only [ArrayEncoding.bits, List.length_ofFn] at lengths
      exact lengths)
    (instanceTables_bits wires)
  apply converted.withSpecification (fun _ _ => True) (instanceProgram wires count).compute
    (by intros; trivial)
  intro sizes arguments valid
  exact (instanceTablesEquiv language (MvPolynomial.eval sizes wires)).symm_apply_apply
    (instanceOfFormula (List.ofFn (arguments ())))

/-- Dense-table construction preserves the constructor's formula semantics. -/
theorem instanceProgram_satisfiable (wires count : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (clauses : Fin (MvPolynomial.eval sizes count) → SAT.Clause (Fin (MvPolynomial.eval sizes wires))) :
    Instance.Satisfiable language ((instanceProgram wires count).compute sizes ⟨fun _ => clauses, trivial⟩) Bool ↔
      SAT.Formula.Satisfiable (SAT.formulaValue clauses) :=
  instanceOfClauseArray_satisfiable clauses

end Polytime2.CSP.ThreeSAT
