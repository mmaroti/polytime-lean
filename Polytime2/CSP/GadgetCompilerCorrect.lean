import Polytime2.CSP.GadgetCompiler
import Polytime2.CSP.GadgetSourceLayout

/-! # Solution correspondence for the complete fixed-gadget computation

The certified raw tables and equations describe the original mathematical
allocation under the clause-array layout. Quotient compilation therefore
preserves exactly its homomorphism solutions and the represented Boolean SAT
problem, including empty sources and repeated literal scopes.
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

/-- The computed dense quotient has exactly the solutions of the mathematical
allocated expansion. Its output size and numbering are computed internally. -/
theorem gadgetCompiler_satisfiable_iff_allocated (wires clauses : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (input : ((SAT.clauseDomain wires).arrayOfLength clauses).Carrier sizes) :
    Instance.Satisfiable L
      ((gadgetCompiler domainFormula clauseFormulas enumeration wires clauses).compute sizes ⟨fun _ => input, trivial⟩).2
      Carrier ↔
    Satisfiable L (AllocatedQuotient (Carrier := Carrier) domainFormula clauseFormulas (List.ofFn input)) Carrier := by
  let placement := allocationEquiv enumeration wires clauses dimension sizes
  have mathematical := allocated_satisfiable_iff_sourceAssignments domainFormula clauseFormulas input placement
  refine (gadgetCompiler_satisfiable_iff_raw domainFormula clauseFormulas enumeration wires clauses sizes input).trans
    (Iff.trans ?_ mathematical.symm)
  apply exists_congr
  intro assignment
  apply and_congr
  · constructor
    · intro preserves occurrence arity symbol tuple related
      rw [sourceOccurrence_kind] at related
      cases occurrence with
      | inl source =>
        exact preserves arity symbol (domainFactScope domainFormula clauseFormulas enumeration wires clauses tuple sizes source)
          ((gadgetRawInstance_relMap_iff domainFormula clauseFormulas enumeration wires clauses sizes input symbol _).mpr
            (Or.inl ⟨source, tuple, related, rfl⟩))
      | inr clause =>
        exact preserves arity symbol (clauseFactScope domainFormula clauseFormulas enumeration wires clauses tuple sizes clause)
          ((gadgetRawInstance_relMap_iff domainFormula clauseFormulas enumeration wires clauses sizes input symbol _).mpr
            (Or.inr ⟨clause, tuple, related, rfl⟩))
    · intro preserves arity symbol tuple rawRelated
      obtain (⟨source, localTuple, related, rfl⟩ | ⟨clause, localTuple, related, rfl⟩) :=
        (gadgetRawInstance_relMap_iff domainFormula clauseFormulas enumeration wires clauses sizes input symbol tuple).mp rawRelated
      · apply preserves (.inl source) arity symbol localTuple
        rw [sourceOccurrence_kind]
        exact related
      · apply preserves (.inr clause) arity symbol localTuple
        rw [sourceOccurrence_kind]
        exact related
  · refine List.forall_mem_ofFn_iff.trans ?_
    refine (gadgetEquationArray_respects_iff domainFormula clauseFormulas enumeration wires clauses sizes input assignment).trans ?_
    exact (sourceEquations_respects_iff domainFormula clauseFormulas input
      (fun value => assignment (placement value))).symm

/-- For a fixed Boolean pp gadget family, the complete certified computation
preserves satisfiability of the original finite clause array. -/
theorem gadgetCompiler_satisfiable_iff
    {subalgebra : (polymorphismLanguage L Carrier).Substructure (Fin dimension → Carrier)}
    {quotient : subalgebra → Bool} {equalityFormula : L.Formula (Fin 2 × Fin dimension)}
    (family : IsBooleanGadgetFamily subalgebra quotient domainFormula equalityFormula clauseFormulas)
    (representatives : Bool → subalgebra) (sectionLaw : Function.RightInverse representatives quotient)
    (wires clauses : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (input : ((SAT.clauseDomain wires).arrayOfLength clauses).Carrier sizes) :
    Instance.Satisfiable L
      ((gadgetCompiler domainFormula clauseFormulas enumeration wires clauses).compute sizes ⟨fun _ => input, trivial⟩).2
      Carrier ↔ SAT.Formula.Satisfiable (List.ofFn input) :=
  (gadgetCompiler_satisfiable_iff_allocated domainFormula clauseFormulas enumeration wires clauses sizes input).trans
    (allocated_satisfiable_iff domainFormula clauseFormulas family representatives sectionLaw (List.ofFn input))

end Polytime2.CSP.GadgetExpansion
