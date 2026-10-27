import Polytime2.CSP.Instance
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.OfFn

/-! # Mathematical correctness of assignment checking

Preservation is exactly the homomorphism condition. The recursive Boolean
checker visits the fixed-arity scope table and has that condition as its
contract, including nullary relations and empty variable or value carriers.
This module contains no codecs, machines, or realization predicates.
-/

namespace Polytime2.CSP

open FirstOrder FirstOrder.Language

namespace Internal

/-- Check a fixed-arity table by recursively visiting all variable tuples.
The recursion is over the fixed relation arity; each array traversal has the
mathematical variable count as its length. -/
def relationCheckValue (Carrier : Type) (variableCount : ℕ) :
    (arity : ℕ) → ((Fin arity → Carrier) → Bool) → (Fin variableCount → Carrier) →
      ((Fin arity → Fin variableCount) → Bool) → Bool
  | 0, relation, _, enabled => !enabled Fin.elim0 || relation Fin.elim0
  | arity + 1, relation, assignment, enabled =>
      (List.ofFn (fun first : Fin variableCount =>
        relationCheckValue Carrier variableCount arity
          (fun rest => relation (Fin.cons (assignment first) rest)) assignment
          (fun rest => enabled (Fin.cons first rest)))).all id

theorem relationCheckValue_correct (Carrier : Type) (variableCount arity : ℕ)
    (relation : (Fin arity → Carrier) → Bool) (assignment : Fin variableCount → Carrier)
    (enabled : (Fin arity → Fin variableCount) → Bool) :
    relationCheckValue Carrier variableCount arity relation assignment enabled = true ↔
      ∀ tuple, enabled tuple = true → relation (assignment ∘ tuple) = true := by
  induction arity with
  | zero =>
    simp only [relationCheckValue, Bool.or_eq_true, Bool.not_eq_true']
    constructor
    · intro accepted tuple active
      have tupleEmpty : tuple = Fin.elim0 := Subsingleton.elim _ _
      have mappedEmpty : assignment ∘ tuple = Fin.elim0 := Subsingleton.elim _ _
      rcases accepted with inactive | holds
      · simp [tupleEmpty, inactive] at active
      · simpa only [mappedEmpty] using holds
    · intro preserves
      by_cases active : enabled Fin.elim0 = true
      · exact Or.inr (by
          have mappedEmpty : assignment ∘ (Fin.elim0 : Fin 0 → Fin variableCount) = Fin.elim0 :=
            Subsingleton.elim _ _
          simpa only [mappedEmpty] using preserves Fin.elim0 active)
      · exact Or.inl (by simpa using active)
  | succ arity hypothesis =>
    simp only [relationCheckValue, List.all_eq_true, List.forall_mem_ofFn_iff, id_eq, hypothesis]
    constructor
    · intro preserves tuple active
      have accepted := preserves (tuple 0) (Fin.tail tuple)
      have holds := accepted (by simpa using active)
      change relation (Fin.cons ((assignment ∘ tuple) 0) (Fin.tail (assignment ∘ tuple))) = true at holds
      simpa only [Fin.cons_self_tail] using holds
    · intro preserves first rest active
      simpa only [Fin.comp_cons] using preserves (Fin.cons first rest) active

end Internal

variable (L : Language.{0, 0}) [L.IsRelational]
variable (Carrier : Type) [L.Structure Carrier]

/-- Every enabled tuple must map to the fixed template relation. -/
def Preserves (variableCount : ℕ) (input : Instance L variableCount)
    (assignment : Fin variableCount → Carrier) : Prop :=
  ∀ symbol : RelationSymbol L, ∀ tuple : Fin symbol.1 → Fin variableCount,
    input.RelMap symbol.2 tuple → Structure.RelMap symbol.2 (assignment ∘ tuple)

/-- Homomorphism existence is exactly existence of a preserving assignment. -/
theorem satisfiable_iff_exists_preserves (variableCount : ℕ) (input : Instance L variableCount) :
    Instance.Satisfiable L input Carrier ↔ ∃ assignment, Preserves L Carrier variableCount input assignment := by
  rw [Instance.satisfiable_iff_exists_assignment]
  apply exists_congr
  intro assignment
  constructor
  · intro preserves symbol tuple; exact preserves symbol.1 symbol.2 tuple
  · intro preserves arity symbol tuple; exact preserves ⟨arity, symbol⟩ tuple

end Polytime2.CSP
