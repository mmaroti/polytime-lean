import Polytime2.CSP.ThreeSAT
import Polytime2.SAT.TseitinEncoding

/-! # Canonical clause arrays as dense three-SAT relations

A pattern/scope table entry is enabled exactly when the corresponding clause
occurs in the input array. This identifies the table compiler's mathematical
contract with the existing relational instance, including repeated clauses,
repeated variables, empty arrays, and zero variables.
-/

namespace Polytime2.CSP.ThreeSAT

/-- The dense ternary table for one falsifying pattern. -/
noncomputable def clauseArrayTable {count variableCount : ℕ}
    (clauses : Fin count → SAT.Clause (Fin variableCount))
    (pattern : Fin 3 → Bool) (scope : Fin 3 → Fin variableCount) : Bool := by
  classical
  exact decide (∃ index, clauses index = fun position => (scope position, pattern position))

/-- Clause equality gives precisely the existing relation-enabling contract. -/
theorem clauseArrayTable_correct {count variableCount : ℕ}
    (clauses : Fin count → SAT.Clause (Fin variableCount))
    (pattern : Fin 3 → Bool) (scope : Fin 3 → Fin variableCount) :
    clauseArrayTable clauses pattern scope = true ↔
      (instanceOfFormula (List.ofFn clauses)).RelMap ⟨pattern, rfl⟩ scope := by
  classical
  simp only [clauseArrayTable, decide_eq_true_eq]
  constructor
  · rintro ⟨index, equal⟩
    refine ⟨clauses index, List.mem_ofFn.mpr ⟨index, rfl⟩, ?_, ?_⟩
    · rw [equal]; rfl
    · rw [equal]; rfl
  · rintro ⟨clause, member, patternEqual, scopeEqual⟩
    obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
    refine ⟨index, ?_⟩
    funext position
    exact Prod.ext (congrFun scopeEqual position).symm (congrFun patternEqual position)

/-- The natural-variable formula emitted by the certified constructor has
exactly the satisfiability of its finite relational interpretation. -/
theorem instanceOfClauseArray_satisfiable {count variableCount : ℕ}
    (clauses : Fin count → SAT.Clause (Fin variableCount)) :
    Instance.Satisfiable language (instanceOfFormula (List.ofFn clauses)) Bool ↔
      SAT.Formula.Satisfiable (SAT.formulaValue clauses) :=
  (satisfiable_iff (List.ofFn clauses)).trans (SAT.formulaValue_satisfiable clauses).symm

end Polytime2.CSP.ThreeSAT
