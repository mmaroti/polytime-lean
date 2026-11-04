import Polytime2.CSP.GadgetCompilerCorrect

/-! # Exact mathematical variable count of the gadget compiler

The generated equations and the mathematical allocation have the same
quotient under the source layout. This proves exact output cardinality,
not merely preservation of satisfiability or an upper bound on storage.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.CSP.GadgetExpansion

open FirstOrder FirstOrder.Language EncodedDomain Polytime2.Computation GadgetAllocation

private noncomputable def quotientOfLayout {First Second : Type} (layout : First ≃ Second)
    (firstRelation : First → First → Prop) (secondRelation : Second → Second → Prop)
    (forward : ∀ first second, firstRelation first second →
      Quot.mk secondRelation (layout first) = Quot.mk secondRelation (layout second))
    (backward : ∀ first second, secondRelation first second →
      Quot.mk firstRelation (layout.symm first) = Quot.mk firstRelation (layout.symm second)) :
    Quot firstRelation ≃ Quot secondRelation where
  toFun := Quot.lift (fun value => Quot.mk secondRelation (layout value)) forward
  invFun := Quot.lift (fun value => Quot.mk firstRelation (layout.symm value)) backward
  left_inv := by
    intro value
    refine Quot.inductionOn value ?_
    intro representative
    exact congrArg (Quot.mk firstRelation) (layout.symm_apply_apply representative)
  right_inv := by
    intro value
    refine Quot.inductionOn value ?_
    intro representative
    exact congrArg (Quot.mk secondRelation) (layout.apply_symm_apply representative)

variable {L : Language.{0, 0}} [L.IsRelational] [Fintype (RelationSymbol L)]
variable {Carrier : Type} [L.Structure Carrier] [Finite Carrier] [Nonempty Carrier]
variable {dimension poolSize : ℕ}
variable (domainFormula : L.Formula (Fin dimension))
variable (clauseFormulas : (Fin 3 → Bool) → L.Formula (Fin 3 × Fin dimension))
variable (enumeration : Pool (Carrier := Carrier) domainFormula clauseFormulas ≃ Fin poolSize)
variable {Parameter : Type} [Fintype Parameter]

/-- Generated equation classes are exactly the mathematical allocated
variables after boundary identification, under the source-layout equivalence. -/
noncomputable def gadgetEquationQuotientEquiv (wires clauses : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (input : ((SAT.clauseDomain wires).arrayOfLength clauses).Carrier sizes) :
    Quot (ArrayQuotient.equationRelation (List.ofFn
      ((gadgetEquationArray domainFormula clauseFormulas enumeration wires clauses).compute sizes
        ⟨fun _ => input, trivial⟩))) ≃
      AllocatedQuotient (Carrier := Carrier) domainFormula clauseFormulas (List.ofFn input) := by
  let equations := List.ofFn ((gadgetEquationArray domainFormula clauseFormulas enumeration wires clauses).compute sizes
    ⟨fun _ => input, trivial⟩)
  let original := allocatedEquations (Carrier := Carrier) domainFormula clauseFormulas (List.ofFn input)
  let placement := (sourceAllocationEquiv domainFormula clauseFormulas input).trans
    (allocationEquiv enumeration wires clauses dimension sizes)
  have respects (Value : Type)
      (assignment : Fin (MvPolynomial.eval sizes (allocationSize wires clauses dimension poolSize)) → Value) :
      (∀ first second, ArrayQuotient.equationRelation equations first second →
        assignment first = assignment second) ↔
      (∀ first second, original first second → assignment (placement first) = assignment (placement second)) := by
    have listed : (∀ first second, ArrayQuotient.equationRelation equations first second →
        assignment first = assignment second) ↔
        ∀ equation ∈ equations, assignment equation.1 = assignment equation.2 := by
      constructor
      · intro every equation member
        exact every equation.1 equation.2 member
      · intro every first second member
        exact every (first, second) member
    refine listed.trans (List.forall_mem_ofFn_iff.trans ?_)
    refine (gadgetEquationArray_respects_iff domainFormula clauseFormulas enumeration wires clauses sizes input assignment).trans ?_
    exact (sourceEquations_respects_iff domainFormula clauseFormulas input
      (fun value => assignment (allocationEquiv enumeration wires clauses dimension sizes value))).symm
  apply quotientOfLayout placement.symm (ArrayQuotient.equationRelation equations) original
  · apply (respects (Quot original) (fun value => Quot.mk original (placement.symm value))).mpr
    intro first second related
    simpa only [Equiv.symm_apply_apply] using (Quot.sound related)
  · have every := (respects (Quot (ArrayQuotient.equationRelation equations))
      (Quot.mk (ArrayQuotient.equationRelation equations))).mp
      (fun _ _ related => Quot.sound related)
    exact every

/-- The compiler's actual variable count equals the original expansion's
cardinality. Internal uniform pool slots and padding add no output variables. -/
theorem gadgetCompiler_count_expansion (wires clauses : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (input : ((SAT.clauseDomain wires).arrayOfLength clauses).Carrier sizes) :
    ((((gadgetCompiler domainFormula clauseFormulas enumeration wires clauses).compute sizes
      ⟨fun _ => input, trivial⟩).1 ()).val) =
      Nat.card (ExpandedVariables (Carrier := Carrier) domainFormula clauseFormulas (List.ofFn input)) :=
  (gadgetCompiler_count domainFormula clauseFormulas enumeration wires clauses sizes input).trans
    ((Nat.card_congr (gadgetEquationQuotientEquiv domainFormula clauseFormulas enumeration wires clauses sizes input)).trans
      (allocatedQuotient_card domainFormula clauseFormulas (List.ofFn input)))

end Polytime2.CSP.GadgetExpansion
