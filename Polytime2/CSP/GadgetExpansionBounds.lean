import Polytime2.CSP.GadgetExpansion
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Linear size bounds for mathematical gadget expansion

The constants depend only on the fixed gadget family and template. Counts are
mathematical variables and distinct asserted relation facts, not bit lengths.
Numbering quotient variables and certifying the dense-table compiler remain
separate realization obligations.
-/

namespace Polytime2.CSP.GadgetExpansion

open FirstOrder FirstOrder.Language

universe languageLevel carrierLevel

variable {L : Language.{languageLevel, languageLevel}} [L.IsRelational]
variable {Carrier : Type carrierLevel} [L.Structure Carrier] [Finite Carrier]
variable [Finite (RelationSymbol L)] {dimension : ℕ}

/-- A fixed family gives one uniform linear bound for variables and asserted
constraints, including formulas with no clauses or no variables. -/
theorem exists_linear_bounds (domainFormula : L.Formula (Fin dimension))
    (clauseFormulas : (Fin 3 → Bool) → L.Formula (Fin 3 × Fin dimension)) :
    ∃ constant : ℕ, ∀ variableCount (formula : SAT.Formula (Fin variableCount)),
      Nat.card (ExpandedVariables (Carrier := Carrier) domainFormula clauseFormulas formula) ≤
          constant * (variableCount + formula.length) ∧
        Nat.card (EnabledFact L (ExpandedVariables (Carrier := Carrier) domainFormula clauseFormulas formula)) ≤
          constant * (variableCount + formula.length) := by
  classical
  let variableBound := Finset.univ.sup (fun kind : Kind => Nat.card (Host (Carrier := Carrier) domainFormula clauseFormulas kind))
  let factBound := Finset.univ.sup (fun kind : Kind => Nat.card (EnabledFact L (Host (Carrier := Carrier) domainFormula clauseFormulas kind)))
  refine ⟨dimension + variableBound + factBound, ?_⟩
  intro variableCount formula
  have variableSums : (∑ occurrence : Fin variableCount ⊕ Fin formula.length,
      Nat.card (Host (Carrier := Carrier) domainFormula clauseFormulas (occurrenceKind formula occurrence))) ≤
      (variableCount + formula.length) * variableBound := by
    calc
      _ ≤ ∑ _occurrence : Fin variableCount ⊕ Fin formula.length, variableBound :=
        Finset.sum_le_sum (fun occurrence _ => Finset.le_sup (Finset.mem_univ (occurrenceKind formula occurrence)))
      _ = _ := by simp
  have factSums : (∑ occurrence : Fin variableCount ⊕ Fin formula.length,
      Nat.card (EnabledFact L (Host (Carrier := Carrier) domainFormula clauseFormulas (occurrenceKind formula occurrence)))) ≤
      (variableCount + formula.length) * factBound := by
    calc
      _ ≤ ∑ _occurrence : Fin variableCount ⊕ Fin formula.length, factBound :=
        Finset.sum_le_sum (fun occurrence _ => Finset.le_sup (Finset.mem_univ (occurrenceKind formula occurrence)))
      _ = _ := by simp
  constructor
  · have rawBound := glued_variable_count_le
      (occurrenceBoundary (Carrier := Carrier) domainFormula clauseFormulas formula) (scope formula)
    simp only [Nat.card_prod, Nat.card_fin] at rawBound
    calc
      _ ≤ variableCount * dimension + (variableCount + formula.length) * variableBound :=
        rawBound.trans (Nat.add_le_add_left variableSums _)
      _ ≤ (variableCount + formula.length) * dimension + (variableCount + formula.length) * variableBound :=
        Nat.add_le_add_right (Nat.mul_le_mul_right dimension (Nat.le_add_right _ _)) _
      _ = (variableCount + formula.length) * (dimension + variableBound) := (Nat.mul_add _ _ _).symm
      _ ≤ (variableCount + formula.length) * (dimension + variableBound + factBound) :=
        Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
      _ = _ := Nat.mul_comm _ _
  · have rawBound := glued_constraint_count_le (L := L)
      (occurrenceBoundary (Carrier := Carrier) domainFormula clauseFormulas formula) (scope formula)
    calc
      _ ≤ (variableCount + formula.length) * factBound := rawBound.trans factSums
      _ ≤ (variableCount + formula.length) * (dimension + variableBound + factBound) :=
        Nat.mul_le_mul_left _ (Nat.le_add_left _ _)
      _ = _ := Nat.mul_comm _ _

/-- Step 13 for a fixed template: choose the gadgets once, then every Boolean
formula expands to a finite relational structure with the same satisfiability
and with uniformly linear variable and constraint counts. -/
theorem exists_bounded_expansion_of_noTaylorPolymorphism
    (rigid : IsRigidCore L Carrier) (noTaylor : ¬ HasTaylorPolymorphism L Carrier) :
    ∃ domainFormula : L.Formula (Fin (Nat.card Carrier ^ 2)),
      ∃ clauseFormulas : (Fin 3 → Bool) → L.Formula (Fin 3 × Fin (Nat.card Carrier ^ 2)),
        ∃ constant : ℕ, ∀ variableCount (formula : SAT.Formula (Fin variableCount)),
          (Satisfiable L (ExpandedVariables (Carrier := Carrier) domainFormula clauseFormulas formula) Carrier ↔
            SAT.Formula.Satisfiable formula) ∧
          Nat.card (ExpandedVariables (Carrier := Carrier) domainFormula clauseFormulas formula) ≤
              constant * (variableCount + formula.length) ∧
            Nat.card (EnabledFact L (ExpandedVariables (Carrier := Carrier) domainFormula clauseFormulas formula)) ≤
              constant * (variableCount + formula.length) := by
  obtain ⟨choices, witness⟩ := exists_boolean_gadgets_of_noTaylorPolymorphism rigid noTaylor
  let _ : (polymorphismLanguage L Carrier).Structure Bool := projectionStructure choices Bool
  dsimp only at witness
  obtain ⟨subalgebra, quotient, surjective, representatives, sectionLaw,
    domainFormula, equalityFormula, clauseFormulas, family⟩ := witness
  obtain ⟨constant, bounds⟩ := exists_linear_bounds (Carrier := Carrier) domainFormula clauseFormulas
  exact ⟨domainFormula, clauseFormulas, constant, fun variableCount formula =>
    ⟨satisfiable_iff family representatives sectionLaw formula, bounds variableCount formula⟩⟩

end Polytime2.CSP.GadgetExpansion
