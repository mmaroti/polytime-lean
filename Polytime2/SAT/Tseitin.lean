import Polytime2.SAT.ThreeSAT
import Polytime2.Circuit.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.VecNotation

/-! # Tseitin clauses for shared-wire NAND circuits

Each gate contributes exactly three three-literal clauses. Constant gates
repeat their unit clause three times; binary clauses repeat a literal. One
last unit clause asserts the selected output. Variables are ordinary natural
wire numbers. For a valid circuit, satisfying input assignments extend to
satisfying formula assignments, and formula assignments restrict back to
accepting inputs. No encoding or execution model enters these statements.
-/

namespace Polytime2.SAT

universe variableLevel

variable {Variable : Type variableLevel}

/-- Three clauses enforce one constant or NAND gate equation at its output. -/
def gateClauses (wire : ℕ) (gate : Circuit.Gate) : Fin 3 → Clause ℕ :=
  match gate with
  | .inl value => fun _ _ => (wire, !value)
  | .inr (left, right) =>
    ![![(left, false), (wire, false), (wire, false)],
      ![(right, false), (wire, false), (wire, false)],
      ![(left, true), (right, true), (wire, true)]]

/-- The gate clauses hold exactly when the output has its specified value. -/
theorem gateClauses_correct (values : ℕ → Bool) (wire : ℕ) (gate : Circuit.Gate) :
    (∀ index, Clause.Satisfied values (gateClauses wire gate index)) ↔
      values wire = gate.eval values := by
  cases gate with
  | inl value =>
    cases value <;> cases output : values wire <;>
      simp [gateClauses, Clause.Satisfied, Literal.Satisfied, Circuit.Gate.eval, output]
  | inr pair =>
    rcases pair with ⟨left, right⟩
    cases first : values left <;> cases second : values right <;> cases output : values wire <;>
      simp [gateClauses, Clause.Satisfied, Literal.Satisfied, Circuit.Gate.eval,
        Fin.forall_fin_succ, Fin.exists_fin_succ, first, second, output]

/-- Gate equations in execution order, starting at the first fresh wire. -/
def programFormula (start : ℕ) (gates : List Circuit.Gate) : Formula ℕ :=
  match gates with
  | [] => []
  | gate :: rest => List.ofFn (gateClauses start gate) ++ programFormula (start + 1) rest

/-- Gate blocks follow the same order as a finite mathematical gate array. -/
theorem programFormula_ofFn {length : ℕ} (gates : Fin length → Circuit.Gate) (start : ℕ) :
    programFormula start (List.ofFn gates) =
      (List.ofFn (fun index => List.ofFn (gateClauses (start + index.val) (gates index)))).flatten := by
  induction length generalizing start with
  | zero => rfl
  | succ length induction =>
    rw [List.ofFn_succ, programFormula, induction]
    conv_rhs => rw [List.ofFn_succ, List.flatten_cons]
    simp only [Fin.val_zero, Nat.add_zero, Fin.val_succ]
    congr 1
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext index
    have equal : start + 1 + index.val = start + (index.val + 1) := by omega
    rw [equal]

/-- The complete reduction, including the assertion that the output is true. -/
def tseitin (inputs : ℕ) (circuit : Circuit.Network) : Formula ℕ :=
  programFormula inputs circuit.1 ++ [fun _ => (circuit.2, false)]

theorem programFormula_length (start : ℕ) (gates : List Circuit.Gate) :
    (programFormula start gates).length = 3 * gates.length := by
  induction gates generalizing start with
  | nil => rfl
  | cons gate rest induction => simp [programFormula, induction]; omega

/-- Exact clause count, also for circuits with no gates. -/
theorem tseitin_length (inputs : ℕ) (circuit : Circuit.Network) :
    (tseitin inputs circuit).length = 3 * circuit.1.length + 1 := by
  simp [tseitin, programFormula_length]

private theorem satisfied_gateClauses (values : ℕ → Bool) (wire : ℕ) (gate : Circuit.Gate) :
    Formula.Satisfied values (List.ofFn (gateClauses wire gate)) ↔ values wire = gate.eval values := by
  simp only [Formula.Satisfied, List.mem_ofFn, forall_exists_index, forall_apply_eq_imp_iff]
  exact gateClauses_correct values wire gate

private theorem gate_eval_agrees {gate : Circuit.Gate} {start : ℕ}
    (valid : gate.Valid start) (first second : ℕ → Bool)
    (agree : ∀ wire < start, first wire = second wire) : gate.eval first = gate.eval second := by
  cases gate with
  | inl value => rfl
  | inr pair => exact congrArg₂ (fun left right => !(left && right)) (agree _ valid.1) (agree _ valid.2)

/-- Executing an acyclic program supplies a simultaneous solution of all its
Tseitin gate equations, while retaining the original input values. -/
theorem programFormula_extend {start : ℕ} {gates : List Circuit.Gate}
    (valid : Circuit.WellFormed start gates) (initial : ℕ → Bool) :
    Formula.Satisfied (Circuit.run start gates initial) (programFormula start gates) := by
  induction gates generalizing start initial with
  | nil => exact Formula.satisfied_nil _
  | cons gate rest induction =>
    rw [programFormula, Formula.satisfied_append, satisfied_gateClauses]
    refine ⟨?_, induction valid.2 _⟩
    change Circuit.run (start + 1) rest (Function.update initial start (gate.eval initial)) start = _
    rw [Circuit.run_preserves rest (start + 1) _ start (by omega), Function.update_self]
    apply gate_eval_agrees valid.1
    intro wire bounded
    change initial wire = Circuit.run (start + 1) rest (Function.update initial start (gate.eval initial)) wire
    rw [Circuit.run_preserves rest (start + 1) _ wire (by omega), Function.update_of_ne (by omega)]

/-- Any solution of the gate equations agrees with circuit execution on all
inputs and generated wires, provided the starting input values agree. -/
theorem programFormula_restrict {start : ℕ} {gates : List Circuit.Gate}
    (valid : Circuit.WellFormed start gates) (initial values : ℕ → Bool)
    (agree : ∀ wire < start, initial wire = values wire)
    (satisfied : Formula.Satisfied values (programFormula start gates)) :
    ∀ wire < start + gates.length, Circuit.run start gates initial wire = values wire := by
  induction gates generalizing start initial with
  | nil => exact agree
  | cons gate rest induction =>
    rw [programFormula, Formula.satisfied_append, satisfied_gateClauses] at satisfied
    have equation : gate.eval initial = values start :=
      (gate_eval_agrees valid.1 initial values agree).trans satisfied.1.symm
    have next : ∀ wire < start + 1, Function.update initial start (gate.eval initial) wire = values wire := by
      intro wire bounded
      by_cases current : wire = start
      · subst wire
        simpa only [Function.update_self] using equation
      · rw [Function.update_of_ne current]
        exact agree wire (by omega)
    intro wire bounded
    exact induction valid.2 _ next satisfied.2 wire (by simp only [List.length_cons] at bounded; omega)

private theorem gateClauses_variables {bound wire : ℕ} {gate : Circuit.Gate}
    (valid : gate.Valid bound) (outputBound : wire < bound) :
    ∀ index position, (gateClauses wire gate index position).1 < bound := by
  cases gate with
  | inl value => exact fun _ _ => outputBound
  | inr pair =>
    simp [gateClauses, Fin.forall_fin_succ, valid.1, valid.2, outputBound]

/-- Every variable in the gate clauses is an actual input or generated wire. -/
theorem programFormula_variables {start : ℕ} {gates : List Circuit.Gate}
    (valid : Circuit.WellFormed start gates) :
    ∀ clause ∈ programFormula start gates, ∀ position, (clause position).1 < start + gates.length := by
  induction gates generalizing start with
  | nil => simp [programFormula]
  | cons gate rest induction =>
    intro clause member position
    rw [programFormula, List.mem_append] at member
    rcases member with member | member
    · obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
      exact gateClauses_variables (valid.1.mono (by simp)) (by simp) index position
    · have bounded := induction valid.2 clause member position
      simp only [List.length_cons]
      omega

/-- All reduction variables are below the exact circuit wire count. -/
theorem tseitin_variables (inputs : ℕ) (circuit : Circuit.Network) (valid : Circuit.Valid inputs circuit) :
    ∀ clause ∈ tseitin inputs circuit, ∀ position, (clause position).1 < inputs + circuit.1.length := by
  intro clause member position
  rw [tseitin, List.mem_append] at member
  rcases member with member | member
  · exact programFormula_variables valid.1 clause member position
  · simp only [List.mem_singleton] at member
    subst clause
    exact valid.2

/-- Extend input values by executing every gate in its mathematical order. -/
def extendAssignment (inputs : ℕ) (circuit : Circuit.Network) (assignment : Fin inputs → Bool) : ℕ → Bool :=
  Circuit.run inputs circuit.1 (fun wire => if bounded : wire < inputs then assignment ⟨wire, bounded⟩ else false)

theorem extendAssignment_input (inputs : ℕ) (circuit : Circuit.Network) (assignment : Fin inputs → Bool)
    (index : Fin inputs) : extendAssignment inputs circuit assignment index.val = assignment index := by
  rw [extendAssignment, Circuit.run_preserves circuit.1 inputs _ index.val index.isLt]
  simp only [dite_eq_left index.isLt]

/-- A satisfying formula assignment restricts to an accepting circuit input. -/
theorem tseitin_restrict (inputs : ℕ) (circuit : Circuit.Network) (valid : Circuit.Valid inputs circuit)
    (values : ℕ → Bool) (satisfied : Formula.Satisfied values (tseitin inputs circuit)) :
    Circuit.evaluate inputs circuit (fun index => values index.val) = true := by
  rw [tseitin, Formula.satisfied_append] at satisfied
  have output : values circuit.2 = true := by simpa [Formula.Satisfied] using satisfied.2
  have correct := programFormula_restrict valid.1
    (fun wire => if bounded : wire < inputs then values wire else false) values
    (by intro wire bounded; simp [bounded]) satisfied.1 circuit.2 valid.2
  exact correct.trans output

/-- The execution extension of an accepting input satisfies every clause. -/
theorem tseitin_extend (inputs : ℕ) (circuit : Circuit.Network) (valid : Circuit.Valid inputs circuit)
    (assignment : Fin inputs → Bool) (accepted : Circuit.evaluate inputs circuit assignment = true) :
    Formula.Satisfied (extendAssignment inputs circuit assignment) (tseitin inputs circuit) := by
  rw [tseitin, Formula.satisfied_append]
  refine ⟨programFormula_extend valid.1 _, ?_⟩
  simpa [Formula.Satisfied, extendAssignment, Circuit.evaluate] using accepted

/-- Exact satisfiability equivalence with explicit extension and restriction. -/
theorem tseitin_correct (inputs : ℕ) (circuit : Circuit.Network) (valid : Circuit.Valid inputs circuit) :
    Formula.Satisfiable (tseitin inputs circuit) ↔ Circuit.Satisfiable inputs circuit := by
  constructor
  · rintro ⟨values, satisfied⟩
    exact ⟨(fun index => values index.val), tseitin_restrict inputs circuit valid values satisfied⟩
  · rintro ⟨assignment, accepted⟩
    exact ⟨extendAssignment inputs circuit assignment, tseitin_extend inputs circuit valid assignment accepted⟩

end Polytime2.SAT
