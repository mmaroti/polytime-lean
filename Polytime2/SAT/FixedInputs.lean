import Polytime2.SAT.Tseitin
import Mathlib.Data.List.OfFn

/-! # Fixing a circuit input prefix through ordinary three-literal clauses

Every supplied Boolean value contributes one repeated-literal unit clause.
The remaining input bits and all generated gate variables remain existential.
-/

namespace Polytime2.SAT

/-- Retain a formula and require its first variables to equal the given bits. -/
def fixInputs (fixedBits : List Bool) (formula : Formula ℕ) : Formula ℕ :=
  formula ++ List.ofFn (fun index : Fin fixedBits.length => fun _ => (index.val, !(fixedBits.get index)))

theorem fixInputs_length (fixedBits : List Bool) (formula : Formula ℕ) :
    (fixInputs fixedBits formula).length = formula.length + fixedBits.length := by simp [fixInputs]

private theorem literal_fixed (assignment : ℕ → Bool) (wire : ℕ) (value : Bool) :
    Literal.Satisfied assignment (wire, !value) ↔ assignment wire = value := by
  cases value <;> simp

/-- Fixed-input clauses impose precisely the requested Boolean equalities. -/
theorem fixInputs_satisfied (fixedBits : List Bool) (formula : Formula ℕ) (assignment : ℕ → Bool) :
    Formula.Satisfied assignment (fixInputs fixedBits formula) ↔
      Formula.Satisfied assignment formula ∧ ∀ index : Fin fixedBits.length, assignment index.val = fixedBits.get index := by
  rw [fixInputs, Formula.satisfied_append]
  simp only [Formula.Satisfied, List.mem_ofFn, forall_exists_index, forall_apply_eq_imp_iff,
    Clause.satisfied_repeat, literal_fixed]

/-- Satisfiability after fixing a prefix is acceptance by an input assignment
with exactly that prefix. The circuit-validity hypothesis is unchanged. -/
theorem fixInputs_tseitin (inputs : ℕ) (circuit : Circuit.Network) (valid : Circuit.Valid inputs circuit)
    (fixedBits : List Bool) (bounded : fixedBits.length ≤ inputs) :
    Formula.Satisfiable (fixInputs fixedBits (tseitin inputs circuit)) ↔
      ∃ assignment : Fin inputs → Bool, Circuit.evaluate inputs circuit assignment = true ∧
        ∀ index : Fin fixedBits.length,
          assignment ⟨index.val, index.isLt.trans_le bounded⟩ = fixedBits.get index := by
  constructor
  · rintro ⟨values, satisfied⟩
    rw [fixInputs_satisfied] at satisfied
    exact ⟨(fun index => values index.val), tseitin_restrict inputs circuit valid values satisfied.1,
      fun index => satisfied.2 index⟩
  · rintro ⟨assignment, accepted, fixed⟩
    refine ⟨extendAssignment inputs circuit assignment, ?_⟩
    rw [fixInputs_satisfied]
    refine ⟨tseitin_extend inputs circuit valid assignment accepted, ?_⟩
    intro index
    exact (extendAssignment_input inputs circuit assignment ⟨index.val, index.isLt.trans_le bounded⟩).trans (fixed index)

/-- The fixed prefix adds no variable outside the actual circuit wire set. -/
theorem fixInputs_tseitin_variables (inputs : ℕ) (circuit : Circuit.Network) (valid : Circuit.Valid inputs circuit)
    (fixedBits : List Bool) (bounded : fixedBits.length ≤ inputs) :
    ∀ clause ∈ fixInputs fixedBits (tseitin inputs circuit), ∀ position, (clause position).1 < inputs + circuit.1.length := by
  intro clause member position
  rw [fixInputs, List.mem_append] at member
  rcases member with member | member
  · exact tseitin_variables inputs circuit valid clause member position
  · obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
    exact index.isLt.trans_le (bounded.trans (Nat.le_add_right _ _))

/-- The finite-array version fixes precisely the supplied Boolean coordinates. -/
theorem fixInputs_ofFn_tseitin (inputs count : ℕ) (circuit : Circuit.Network) (valid : Circuit.Valid inputs circuit)
    (fixedBits : Fin count → Bool) (bounded : count ≤ inputs) :
    Formula.Satisfiable (fixInputs (List.ofFn fixedBits) (tseitin inputs circuit)) ↔
      ∃ assignment : Fin inputs → Bool, Circuit.evaluate inputs circuit assignment = true ∧
        ∀ index : Fin count, assignment (index.castLE bounded) = fixedBits index := by
  rw [fixInputs_tseitin inputs circuit valid (List.ofFn fixedBits) (by simpa using bounded)]
  constructor
  · rintro ⟨assignment, accepted, fixed⟩
    refine ⟨assignment, accepted, ?_⟩
    intro index
    have selected := fixed ⟨index.val, by simp⟩
    rw [List.get_ofFn] at selected
    exact selected
  · rintro ⟨assignment, accepted, fixed⟩
    refine ⟨assignment, accepted, ?_⟩
    intro index
    rw [List.get_ofFn]
    exact fixed (index.cast List.length_ofFn)

end Polytime2.SAT
