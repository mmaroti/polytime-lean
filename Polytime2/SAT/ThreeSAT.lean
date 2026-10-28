import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Logic.Function.Basic

/-! # Shared mathematical semantics of three-literal CNF formulas

A literal pairs a variable with a negation bit: `false` means positive and
`true` means negated. A clause is an ordered triple, allowing repeated variables
and literals; a formula is a list of clauses, allowing repetitions and the
empty conjunction. These are mathematical carriers for both CSP and CLIQUE
reductions. No encoding or complexity claim is part of their semantics.
-/

namespace Polytime2.SAT

universe variableLevel

/-- A variable and its negation bit. Equivalently, the bit is the variable
value making this literal false. -/
abbrev Literal (Variable : Type variableLevel) := Variable × Bool

/-- Exactly three ordered literals; repeated variables are allowed. -/
abbrev Clause (Variable : Type variableLevel) := Fin 3 → Literal Variable

/-- An ordered conjunction of three-literal clauses. -/
abbrev Formula (Variable : Type variableLevel) := List (Clause Variable)

variable {Variable : Type variableLevel}

/-- A literal is true when its variable differs from its falsifying value. -/
def Literal.Satisfied (assignment : Variable → Bool) (literal : Literal Variable) : Prop :=
  assignment literal.1 ≠ literal.2

/-- A clause is the disjunction of its three literals. -/
def Clause.Satisfied (assignment : Variable → Bool) (clause : Clause Variable) : Prop :=
  ∃ position, Literal.Satisfied assignment (clause position)

/-- A formula is the conjunction of its clauses. -/
def Formula.Satisfied (assignment : Variable → Bool) (formula : Formula Variable) : Prop :=
  ∀ clause ∈ formula, Clause.Satisfied assignment clause

/-- Formula satisfiability asserts existence of a Boolean assignment. -/
def Formula.Satisfiable (formula : Formula Variable) : Prop :=
  ∃ assignment, Formula.Satisfied assignment formula

/-- The ordered variable scope of a clause, with repetitions retained. -/
def Clause.scope (clause : Clause Variable) : Fin 3 → Variable :=
  fun position => (clause position).1

/-- The unique falsifying triple on the three literal positions. With repeated
variables this triple need not arise from any assignment to the actual scope. -/
def Clause.falsifyingPattern (clause : Clause Variable) : Fin 3 → Bool :=
  fun position => (clause position).2

/-- Positive literals demand truth. -/
@[simp] theorem Literal.satisfied_positive (assignment : Variable → Bool) (atom : Variable) :
    Literal.Satisfied assignment (atom, false) ↔ assignment atom = true := by
  simp [Literal.Satisfied]

/-- Negated literals demand falsity. -/
@[simp] theorem Literal.satisfied_negative (assignment : Variable → Bool) (atom : Variable) :
    Literal.Satisfied assignment (atom, true) ↔ assignment atom = false := by
  simp [Literal.Satisfied]

/-- A clause accepts exactly the Boolean triples other than its falsifying
pattern, after substituting its actual variables, including repeated ones. -/
theorem Clause.satisfied_iff_ne_falsifyingPattern
    (assignment : Variable → Bool) (clause : Clause Variable) :
    Clause.Satisfied assignment clause ↔
      assignment ∘ clause.scope ≠ clause.falsifyingPattern := by
  classical
  simp only [Clause.Satisfied, Literal.Satisfied, ne_eq, funext_iff, not_forall,
    Function.comp_apply, Clause.scope, Clause.falsifyingPattern]

/-- Repeating one literal three times does not change its meaning. -/
@[simp] theorem Clause.satisfied_repeat (assignment : Variable → Bool) (literal : Literal Variable) :
    Clause.Satisfied assignment (fun _ => literal) ↔ Literal.Satisfied assignment literal := by
  simp [Clause.Satisfied]

/-- The empty conjunction is true under every assignment. -/
@[simp] theorem Formula.satisfied_nil (assignment : Variable → Bool) :
    Formula.Satisfied assignment ([] : Formula Variable) := by
  simp [Formula.Satisfied]

/-- Zero clauses are satisfiable, even when the variable carrier is empty. -/
theorem Formula.satisfiable_nil : Formula.Satisfiable ([] : Formula Variable) :=
  ⟨fun _ => false, Formula.satisfied_nil _⟩

/-- Injectively renaming the variables of a clause array preserves
satisfiability, including empty arrays and empty variable carriers. -/
theorem Formula.satisfiable_ofFn_rename {Target : Type*} {count : ℕ}
    (rename : Variable → Target) (injective : Function.Injective rename)
    (clauses : Fin count → Clause Variable) :
    Formula.Satisfiable (List.ofFn (fun index position =>
      (rename (clauses index position).1, (clauses index position).2))) ↔
      Formula.Satisfiable (List.ofFn clauses) := by
  constructor
  · rintro ⟨assignment, satisfied⟩
    refine ⟨assignment ∘ rename, ?_⟩
    intro clause member
    obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
    exact satisfied _ (List.mem_ofFn.mpr ⟨index, rfl⟩)
  · rintro ⟨assignment, satisfied⟩
    refine ⟨Function.extend rename assignment (fun _ => false), ?_⟩
    intro clause member
    obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
    obtain ⟨position, accepted⟩ :=
      satisfied _ (List.mem_ofFn.mpr ⟨index, rfl⟩)
    refine ⟨position, ?_⟩
    change Function.extend rename assignment (fun _ => false)
      (rename (clauses index position).1) ≠ (clauses index position).2
    rw [injective.extend_apply]
    exact accepted

/-- Satisfaction of concatenated formulas is satisfaction of both conjuncts. -/
@[simp] theorem Formula.satisfied_append (values : Variable → Bool) (first second : Formula Variable) :
    Formula.Satisfied values (first ++ second) ↔ Formula.Satisfied values first ∧ Formula.Satisfied values second := by
  simp [Formula.Satisfied, or_imp, forall_and]


/-- Changing values of variables absent from all clause occurrences preserves
satisfaction. No distinctness assumption is made on occurrences. -/
theorem Formula.satisfied_congr (formula : Formula Variable)
    (first second : Variable → Bool)
    (agree : ∀ clause ∈ formula, ∀ position, first (clause position).1 = second (clause position).1) :
    Formula.Satisfied first formula ↔ Formula.Satisfied second formula := by
  unfold Formula.Satisfied Clause.Satisfied Literal.Satisfied
  apply forall_congr'
  intro clause
  apply forall_congr'
  intro member
  apply exists_congr
  intro position
  rw [agree clause member position]

end Polytime2.SAT
