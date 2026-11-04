import Polytime2.CSP.GadgetFactArrays
import Polytime2.CSP.InstanceMaterialize

/-! # Certified raw relational gadget instances

Enumerate every tuple in each fixed pool table, generate the corresponding
domain and clause facts, and materialize the canonical dense instance. Only
the original clause array and mathematical source sizes are runtime inputs.
Boundary equations and quotient compilation are subsequent stages.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.CSP.GadgetExpansion

open FirstOrder FirstOrder.Language EncodedDomain Polytime2.Computation GadgetAllocation

variable {L : Language.{0, 0}} [L.IsRelational] [Fintype (RelationSymbol L)]
variable {Carrier : Type} [L.Structure Carrier] [Finite Carrier] [Nonempty Carrier]
variable {dimension poolSize : ℕ}
variable (domainFormula : L.Formula (Fin dimension))
variable (clauseFormulas : (Fin 3 → Bool) → L.Formula (Fin 3 × Fin dimension))
variable (enumeration : Pool (Carrier := Carrier) domainFormula clauseFormulas ≃ Fin poolSize)
variable {Parameter : Type} [Fintype Parameter]

/-- A fixed enumeration of all mathematical local pool tuples. -/
noncomputable def poolTupleEnumeration (arity : ℕ) :
    Fin (Fintype.card (Fin arity → Fin poolSize)) ≃
      (Fin arity → Pool (Carrier := Carrier) domainFormula clauseFormulas) :=
  (Fintype.equivFin (Fin arity → Fin poolSize)).symm.trans
    (_root_.Equiv.arrowCongr (Equiv.refl (Fin arity)) enumeration.symm)

private noncomputable def factCounts (wires clauses : MvPolynomial Parameter ℕ) :
    RelationSymbol L → MvPolynomial Parameter ℕ :=
  fun symbol => wires * MvPolynomial.C (Fintype.card (Fin symbol.1 → Fin poolSize)) +
    clauses * MvPolynomial.C (Fintype.card (Fin symbol.1 → Fin poolSize))

private noncomputable def rawFactFamily (wires clauses : MvPolynomial Parameter ℕ) :
    Computation Parameter Unit where
  inputDomains _ := (SAT.clauseDomain wires).arrayOfLength clauses
  outputDomain := instanceFactsDomain L (allocationSize wires clauses dimension poolSize)
    (factCounts (L := L) (poolSize := poolSize) wires clauses)
  precondition _ _ := True
  compute sizes arguments symbol :=
    (gadgetFactArray domainFormula clauseFormulas enumeration
      (poolTupleEnumeration domainFormula clauseFormulas enumeration symbol.1) wires clauses symbol.2).compute sizes arguments

omit [L.IsRelational] [Finite Carrier] in
private theorem rawFactFamily_realizable (wires clauses : MvPolynomial Parameter ℕ) :
    (rawFactFamily domainFormula clauseFormulas enumeration wires clauses).Realizable := by
  apply Realizable.namedRecordOutputs
  intro symbol
  exact gadgetFactArray_realizable domainFormula clauseFormulas enumeration
    (poolTupleEnumeration domainFormula clauseFormulas enumeration symbol.1) wires clauses symbol.2

/-- The raw dense relational instance of all fresh gadget copies. The result
has the exact mathematical allocation size; no caller capacity is required. -/
noncomputable def gadgetRawInstance (wires clauses : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  (rawFactFamily domainFormula clauseFormulas enumeration wires clauses).followedBy
    (materializeInstance L (allocationSize wires clauses dimension poolSize)
      (factCounts (L := L) (poolSize := poolSize) wires clauses)) rfl (by intros; trivial)

omit [Finite Carrier] in
theorem gadgetRawInstance_realizable (wires clauses : MvPolynomial Parameter ℕ) :
    (gadgetRawInstance domainFormula clauseFormulas enumeration wires clauses).Realizable :=
  (rawFactFamily_realizable domainFormula clauseFormulas enumeration wires clauses).followedBy
    (materializeInstance_realizable L (allocationSize wires clauses dimension poolSize)
      (factCounts (L := L) (poolSize := poolSize) wires clauses)) rfl (by intros; trivial)

omit [Finite Carrier] in
/-- The output asserts exactly the facts generated from the fixed local
tables at source-variable and clause occurrences. -/
theorem gadgetRawInstance_correct (wires clauses : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (input : ((SAT.clauseDomain wires).arrayOfLength clauses).Carrier sizes)
    {arity : ℕ} (symbol : L.Relations arity)
    (tuple : Fin arity → Fin (MvPolynomial.eval sizes (allocationSize wires clauses dimension poolSize))) :
    ((gadgetRawInstance domainFormula clauseFormulas enumeration wires clauses).compute sizes
      ⟨fun _ => input, trivial⟩).RelMap symbol tuple ↔
      ∃ index, (gadgetFactArray domainFormula clauseFormulas enumeration
        (poolTupleEnumeration domainFormula clauseFormulas enumeration arity) wires clauses symbol).compute sizes
          ⟨fun _ => input, trivial⟩ index = some tuple := by
  exact materializeInstance_correct L (allocationSize wires clauses dimension poolSize)
    (factCounts (L := L) (poolSize := poolSize) wires clauses) sizes
    ((rawFactFamily domainFormula clauseFormulas enumeration wires clauses).compute sizes ⟨fun _ => input, trivial⟩)
    symbol tuple

omit [Finite Carrier] in
/-- The raw relation tables are exactly the placed fixed pool relations,
with all local tuples included and no dependence on enumeration choices. -/
theorem gadgetRawInstance_relMap_iff (wires clauses : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (input : ((SAT.clauseDomain wires).arrayOfLength clauses).Carrier sizes)
    {arity : ℕ} (symbol : L.Relations arity)
    (tuple : Fin arity → Fin (MvPolynomial.eval sizes (allocationSize wires clauses dimension poolSize))) :
    ((gadgetRawInstance domainFormula clauseFormulas enumeration wires clauses).compute sizes
      ⟨fun _ => input, trivial⟩).RelMap symbol tuple ↔
      (∃ source : Fin (MvPolynomial.eval sizes wires),
        ∃ localTuple : Fin arity → Pool (Carrier := Carrier) domainFormula clauseFormulas,
          poolRelation domainFormula clauseFormulas (.inl ()) symbol localTuple ∧
            domainFactScope domainFormula clauseFormulas enumeration wires clauses localTuple sizes source = tuple) ∨
      (∃ clause : Fin (MvPolynomial.eval sizes clauses),
        ∃ localTuple : Fin arity → Pool (Carrier := Carrier) domainFormula clauseFormulas,
          poolRelation domainFormula clauseFormulas (.inr (SAT.Clause.falsifyingPattern (input clause))) symbol localTuple ∧
            clauseFactScope domainFormula clauseFormulas enumeration wires clauses localTuple sizes clause = tuple) := by
  rw [gadgetRawInstance_correct, gadgetFactArray_some_iff]
  have pattern_eq (clause : Fin (MvPolynomial.eval sizes clauses)) :
      SAT.Clause.falsifyingPattern (input clause) = (fun coordinate => (input clause coordinate).2) := rfl
  let tuples := poolTupleEnumeration domainFormula clauseFormulas enumeration arity
  have inverse (localTuple : Fin arity → Pool (Carrier := Carrier) domainFormula clauseFormulas) :
      poolTupleEnumeration domainFormula clauseFormulas enumeration arity (tuples.symm localTuple) = localTuple :=
    tuples.apply_symm_apply localTuple
  constructor
  · rintro (⟨source, index, related, agrees⟩ | ⟨clause, index, related, agrees⟩)
    · exact Or.inl ⟨source, tuples index, related, agrees⟩
    · exact Or.inr ⟨clause, tuples index, related, agrees⟩
  · rintro (⟨source, localTuple, related, agrees⟩ | ⟨clause, localTuple, related, agrees⟩)
    · refine Or.inl ⟨source, tuples.symm localTuple, ?_, ?_⟩
      · simpa only [inverse] using related
      · simpa only [inverse] using agrees
    · rw [pattern_eq clause] at related
      refine Or.inr ⟨clause, tuples.symm localTuple, ?_, ?_⟩
      · simpa only [inverse] using related
      · simpa only [inverse] using agrees

end Polytime2.CSP.GadgetExpansion
