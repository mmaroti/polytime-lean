import Polytime2.CSP.GadgetExpansionAllocation
import Polytime2.CSP.GadgetLayout

/-! # Clause-array coordinates of the mathematical gadget expansion

An ordinary finite clause array and its list presentation have identical
occurrences, scopes, and allocated variables. These mathematical equivalences
account for the list-length equality before any codec or machine is involved.
-/

namespace Polytime2.CSP.GadgetExpansion

open FirstOrder FirstOrder.Language GadgetAllocation

variable {L : Language.{0, 0}} [L.IsRelational]
variable {Carrier : Type} [L.Structure Carrier] [Finite Carrier] [Nonempty Carrier]
variable {dimension variableCount clauseCount poolSize : ℕ}
variable (domainFormula : L.Formula (Fin dimension))
variable (clauseFormulas : (Fin 3 → Bool) → L.Formula (Fin 3 × Fin dimension))
variable (input : Fin clauseCount → SAT.Clause (Fin variableCount))

/-- The list presentation changes no domain or clause occurrence. -/
def sourceOccurrenceEquiv :
    (Fin variableCount ⊕ Fin (List.ofFn input).length) ≃ (Fin variableCount ⊕ Fin clauseCount) :=
  Equiv.sumCongr (Equiv.refl _) (finCongr (List.length_ofFn (f := input)))

theorem sourceOccurrence_domain (source : Fin variableCount) :
    (sourceOccurrenceEquiv input).symm (.inl source) = .inl source := rfl

theorem sourceOccurrence_clause (clause : Fin clauseCount) :
    (sourceOccurrenceEquiv input).symm (.inr clause) =
      .inr (Fin.cast (List.length_ofFn (f := input)).symm clause) := rfl

theorem sourceClause_get (clause : Fin clauseCount) :
    (List.ofFn input).get (Fin.cast (List.length_ofFn (f := input)).symm clause) = input clause := by
  simp

theorem sourceClause_get_index (clause : Fin (List.ofFn input).length) :
    (List.ofFn input).get clause = input (Fin.cast (List.length_ofFn (f := input)) clause) := by
  simp [Fin.cast]

/-- The formula and clause array choose exactly the same local gadget. -/
theorem sourceOccurrence_kind (occurrence : Fin variableCount ⊕ Fin clauseCount) :
    occurrenceKind (List.ofFn input) ((sourceOccurrenceEquiv input).symm occurrence) =
      (match occurrence with | .inl _ => .inl () | .inr clause => .inr (input clause).falsifyingPattern) := by
  cases occurrence with
  | inl source => rfl
  | inr clause =>
    simp only [sourceOccurrence_clause, occurrenceKind, sourceClause_get]

theorem sourceOccurrence_scope_domain (source : Fin variableCount) (coordinate : Fin dimension) :
    scope (List.ofFn input) ((sourceOccurrenceEquiv input).symm (.inl source)) coordinate =
      (source, coordinate) := rfl

theorem sourceOccurrence_scope_clause (clause : Fin clauseCount) (coordinate : Fin 3 × Fin dimension) :
    scope (List.ofFn input) ((sourceOccurrenceEquiv input).symm (.inr clause)) coordinate =
      ((input clause coordinate.1).1, coordinate.2) := by
  simp only [sourceOccurrence_clause, scope, sourceClause_get, SAT.Clause.scope]

/-- Forget only the proved equality of the list and array occurrence counts. -/
def sourceAllocationEquiv :
    AllocatedVariables (Carrier := Carrier) domainFormula clauseFormulas (List.ofFn input) ≃
      ((Fin variableCount × Fin dimension) ⊕
        ((Fin variableCount ⊕ Fin clauseCount) × Pool (Carrier := Carrier) domainFormula clauseFormulas)) :=
  Equiv.sumCongr (Equiv.refl _) (Equiv.prodCongr (sourceOccurrenceEquiv input) (Equiv.refl _))

/-- Number the original mathematical allocation in clause-array order. -/
noncomputable def sourceLayoutEquiv
    (enumeration : Pool (Carrier := Carrier) domainFormula clauseFormulas ≃ Fin poolSize) :
    AllocatedVariables (Carrier := Carrier) domainFormula clauseFormulas (List.ofFn input) ≃
      Fin (variableCount * (dimension + poolSize) + clauseCount * poolSize) :=
  (sourceAllocationEquiv domainFormula clauseFormulas input).trans
    (layoutEquiv enumeration variableCount clauseCount dimension)

omit [L.IsRelational] [Finite Carrier] [Nonempty Carrier] in
theorem sourceLayout_shared
    (enumeration : Pool (Carrier := Carrier) domainFormula clauseFormulas ≃ Fin poolSize)
    (source : Fin variableCount) (coordinate : Fin dimension) :
    sourceLayoutEquiv domainFormula clauseFormulas input enumeration (.inl (source, coordinate)) =
      layoutEquiv enumeration variableCount clauseCount dimension (.inl (source, coordinate)) := rfl

omit [L.IsRelational] [Finite Carrier] [Nonempty Carrier] in
theorem sourceLayout_local
    (enumeration : Pool (Carrier := Carrier) domainFormula clauseFormulas ≃ Fin poolSize)
    (occurrence : Fin variableCount ⊕ Fin clauseCount)
    (value : Pool (Carrier := Carrier) domainFormula clauseFormulas) :
    sourceLayoutEquiv domainFormula clauseFormulas input enumeration
      (.inr ((sourceOccurrenceEquiv input).symm occurrence, value)) =
        layoutEquiv enumeration variableCount clauseCount dimension (.inr (occurrence, value)) := by
  simp [sourceLayoutEquiv, sourceAllocationEquiv]

/-- Transport the quotient's assignment contract through the clause-array
layout and any mathematical numbering of its variables. Relation occurrences
use array indices; the original allocation equations retain their exact meaning. -/
theorem allocated_satisfiable_iff_sourceAssignments {Variables : Type}
    (placement : ((Fin variableCount × Fin dimension) ⊕
      ((Fin variableCount ⊕ Fin clauseCount) × Pool (Carrier := Carrier) domainFormula clauseFormulas)) ≃ Variables) :
    Satisfiable L (AllocatedQuotient (Carrier := Carrier) domainFormula clauseFormulas (List.ofFn input)) Carrier ↔
    ∃ assignment : Variables → Carrier,
      (∀ occurrence arity (symbol : L.Relations arity)
        (tuple : Fin arity → Pool (Carrier := Carrier) domainFormula clauseFormulas),
        poolRelation domainFormula clauseFormulas
          (occurrenceKind (List.ofFn input) ((sourceOccurrenceEquiv input).symm occurrence)) symbol tuple →
            Structure.RelMap symbol (fun coordinate => assignment (placement (.inr (occurrence, tuple coordinate))))) ∧
      ∀ first second, allocatedEquations domainFormula clauseFormulas (List.ofFn input) first second →
        assignment (placement (sourceAllocationEquiv domainFormula clauseFormulas input first)) =
          assignment (placement (sourceAllocationEquiv domainFormula clauseFormulas input second)) := by
  refine (allocated_satisfiable_iff_assignments domainFormula clauseFormulas (List.ofFn input)).trans ?_
  let numbering := (sourceAllocationEquiv domainFormula clauseFormulas input).trans placement
  refine (Equiv.arrowCongr numbering (Equiv.refl Carrier)).exists_congr' ?_
  intro assignment
  apply and_congr
  · refine (sourceOccurrenceEquiv input).forall_congr_left.trans ?_
    apply forall_congr'
    intro occurrence
    change (∀ arity (symbol : L.Relations arity)
      (tuple : Fin arity → Pool (Carrier := Carrier) domainFormula clauseFormulas),
      poolRelation domainFormula clauseFormulas
        (occurrenceKind (List.ofFn input) ((sourceOccurrenceEquiv input).symm occurrence)) symbol tuple →
          Structure.RelMap symbol (fun coordinate => assignment
            (numbering (.inr ((sourceOccurrenceEquiv input).symm occurrence, tuple coordinate))))) ↔ _
    simp [numbering, sourceAllocationEquiv]
  · rfl

omit [L.IsRelational] in
/-- Reindexing the mathematical allocation equations gives exactly the
source-wise and clause-wise projection and boundary conditions. -/
theorem sourceEquations_respects_iff {Value : Type*}
    (assignment : ((Fin variableCount × Fin dimension) ⊕
      ((Fin variableCount ⊕ Fin clauseCount) × Pool (Carrier := Carrier) domainFormula clauseFormulas)) → Value) :
    (∀ first second, allocatedEquations domainFormula clauseFormulas (List.ofFn input) first second →
      assignment (sourceAllocationEquiv domainFormula clauseFormulas input first) =
        assignment (sourceAllocationEquiv domainFormula clauseFormulas input second)) ↔
    (∀ source : Fin variableCount,
      (∀ value, assignment (.inr (.inl source, value)) =
        assignment (.inr (.inl source, selectedPool domainFormula clauseFormulas (.inl ()) value))) ∧
      (∀ coordinate, assignment (.inr (.inl source,
        poolBoundary (Carrier := Carrier) domainFormula clauseFormulas (.inl ()) coordinate)) =
          assignment (.inl (source, coordinate)))) ∧
    (∀ clause : Fin clauseCount,
      (∀ value, assignment (.inr (.inr clause, value)) =
        assignment (.inr (.inr clause, selectedPool domainFormula clauseFormulas
          (.inr (input clause).falsifyingPattern) value))) ∧
      (∀ coordinate : Fin 3 × Fin dimension,
        assignment (.inr (.inr clause, poolBoundary (Carrier := Carrier) domainFormula clauseFormulas
          (.inr (input clause).falsifyingPattern) coordinate)) =
            assignment (.inl ((input clause coordinate.1).1, coordinate.2)))) := by
  refine (allocatedEquations_respects_iff domainFormula clauseFormulas (List.ofFn input)
    (fun value => assignment (sourceAllocationEquiv domainFormula clauseFormulas input value))).trans ?_
  constructor
  · rintro ⟨projections, boundaries⟩
    constructor
    · intro source
      constructor
      · intro value
        simpa [sourceAllocationEquiv, sourceOccurrenceEquiv, occurrenceKind] using projections (.inl source) value
      · intro coordinate
        simpa [sourceAllocationEquiv, sourceOccurrenceEquiv, occurrenceKind, scope] using boundaries (.inl source) coordinate
    · intro clause
      constructor
      · intro value
        simpa [sourceAllocationEquiv, sourceOccurrenceEquiv, occurrenceKind] using
          projections ((sourceOccurrenceEquiv input).symm (.inr clause)) value
      · intro coordinate
        have given := boundaries (.inr (Fin.cast (List.length_ofFn (f := input)).symm clause)) coordinate
        change assignment (.inr (.inr clause, poolBoundary (Carrier := Carrier) domainFormula clauseFormulas
          (.inr ((List.ofFn input).get (Fin.cast (List.length_ofFn (f := input)).symm clause)).falsifyingPattern) coordinate)) =
          assignment (.inl ((((List.ofFn input).get (Fin.cast (List.length_ofFn (f := input)).symm clause)) coordinate.1).1,
            coordinate.2)) at given
        rw [sourceClause_get] at given
        exact given
  · rintro ⟨domains, clauses⟩
    constructor
    · rintro (source | clause) value
      · simpa [sourceAllocationEquiv, sourceOccurrenceEquiv, occurrenceKind] using (domains source).1 value
      · change assignment (.inr (.inr (Fin.cast (List.length_ofFn (f := input)) clause), value)) =
          assignment (.inr (.inr (Fin.cast (List.length_ofFn (f := input)) clause),
            selectedPool domainFormula clauseFormulas (.inr ((List.ofFn input).get clause).falsifyingPattern) value))
        rw [sourceClause_get_index]
        exact (clauses (Fin.cast (List.length_ofFn (f := input)) clause)).1 value
    · rintro (source | clause) coordinate
      · simpa [sourceAllocationEquiv, sourceOccurrenceEquiv, occurrenceKind, scope] using (domains source).2 coordinate
      · change assignment (.inr (.inr (Fin.cast (List.length_ofFn (f := input)) clause),
          poolBoundary (Carrier := Carrier) domainFormula clauseFormulas (.inr ((List.ofFn input).get clause).falsifyingPattern)
            coordinate)) = assignment (.inl ((((List.ofFn input).get clause) coordinate.1).1, coordinate.2))
        rw [sourceClause_get_index]
        exact (clauses (Fin.cast (List.length_ofFn (f := input)) clause)).2 coordinate

end Polytime2.CSP.GadgetExpansion
