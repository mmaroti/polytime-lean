import Polytime2.SAT.Tseitin
import Polytime2.Circuit.Construction
import Mathlib.Tactic.FinCases

/-! # Canonical clause records and fixed Tseitin templates

Literals retain their mathematical variable and negation bit. Clauses and
three-clause gate blocks use the existing product and fixed-record codecs.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.SAT

open EncodedDomain Polytime2.Computation

variable {Parameter : Type} [Fintype Parameter]

/-- A literal on the actual finite wire set, in the existing product codec. -/
noncomputable def literalDomain (wires : MvPolynomial Parameter ℕ) : EncodedDomain Parameter :=
  (arrayPosition wires).prod booleans

/-- Exactly three ordered literals, including repeated occurrences. -/
noncomputable def clauseDomain (wires : MvPolynomial Parameter ℕ) : EncodedDomain Parameter :=
  record 3 (fun _ => literalDomain wires)

/-- Forget only established finite bounds on the clause's variables. -/
def clauseValue {wires : ℕ} (clause : Clause (Fin wires)) : Clause ℕ :=
  fun position => ((clause position).1.val, (clause position).2)

theorem clauseValue_injective {wires : ℕ} : Function.Injective (@clauseValue wires) := by
  intro first second equal
  funext position
  apply Prod.ext
  · exact Fin.ext (congrArg Prod.fst (congrFun equal position))
  · change (clauseValue first position).2 = (clauseValue second position).2
    exact congrArg Prod.snd (congrFun equal position)

/-- Observe a canonical clause array as an ordinary mathematical formula. -/
def formulaValue {count wires : ℕ} (clauses : Fin count → Clause (Fin wires)) : Formula ℕ :=
  List.ofFn (fun index => clauseValue (clauses index))

/-- Finite bounds are codec metadata and do not change satisfiability. -/
theorem formulaValue_satisfiable {count wires : ℕ}
    (clauses : Fin count → Clause (Fin wires)) :
    Formula.Satisfiable (formulaValue clauses) ↔
      Formula.Satisfiable (List.ofFn clauses) :=
  Formula.satisfiable_ofFn_rename Fin.val Fin.val_injective clauses

theorem formulaValue_injective {count wires : ℕ} : Function.Injective (@formulaValue count wires) := by
  intro first second equal
  funext index
  exact clauseValue_injective (congrFun (List.ofFn_injective equal) index)

/-- Attach the output wire to the mathematical three-clause gate template. -/
def boundedGateClauses {wires : ℕ} (wire : Fin wires)
    (gate : Bool ⊕ (Fin wires × Fin wires)) : Fin 3 → Clause (Fin wires) :=
  match gate with
  | .inl value => fun _ _ => (wire, !value)
  | .inr (left, right) =>
    ![![(left, false), (wire, false), (wire, false)],
      ![(right, false), (wire, false), (wire, false)],
      ![(left, true), (right, true), (wire, true)]]

theorem boundedGateClauses_value {wires : ℕ} (wire : Fin wires)
    (gate : Bool ⊕ (Fin wires × Fin wires)) :
    (fun index => clauseValue (boundedGateClauses wire gate index)) =
      gateClauses wire.val (Circuit.gateValue gate) := by
  cases gate with
  | inl value => rfl
  | inr pair =>
    funext index position
    fin_cases index <;> fin_cases position <;> rfl

/-- Fill specialization-fixed literal templates from actual variable values. -/
noncomputable def instantiateClauses (wires : MvPolynomial Parameter ℕ) {arity : ℕ}
    (templates : Fin 3 → Fin 3 → Fin arity × Bool) : Computation Parameter (Fin arity) where
  inputDomains _ := arrayPosition wires
  outputDomain := record 3 (fun _ => clauseDomain wires)
  precondition _ _ := True
  compute _ arguments clause position :=
    (arguments.val (templates clause position).1, (templates clause position).2)

theorem instantiateClauses_realizable (wires : MvPolynomial Parameter ℕ) {arity : ℕ}
    (templates : Fin 3 → Fin 3 → Fin arity × Bool) : (instantiateClauses wires templates).Realizable := by
  let inputs : Fin arity → EncodedDomain Parameter := fun _ => arrayPosition wires
  apply Realizable.recordOutputs
  intro clause
  apply Realizable.recordOutputs
  intro position
  have negation := (booleanOperation_realizable (Parameter := Parameter)
    (fun _ : Empty → Bool => (templates clause position).2)).onResults inputs (fun _ _ => True)
      (fun empty => nomatch empty) (by intros; trivial) (fun empty => nomatch empty)
  exact (Realizable.argument inputs (templates clause position).1 (fun _ _ => True)).prodMk negation

end Polytime2.SAT
