import Polytime2.CSP.Instance
import Polytime2.SAT.ThreeSAT
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.Pi

/-! # Three-SAT as a fixed-template relational CSP

The template has carrier `Bool` and exactly eight ternary relation symbols,
indexed by the excluded triple. Its relation for `pattern` is the complement
of that singleton in `Bool³`. The language has no other relation symbols and
no function symbols.

An input list of three-literal clauses becomes a structure on the same `Fin N`
variables. Each clause enables its ordered scope in the relation indexed by
its falsifying pattern. The assignment correspondence is exact, including
repeated variables, duplicate clauses, unused variables, and zero clauses.
All definitions here are mathematical; no polynomial reduction is certified.

Source: Brady, *Notes on CSPs and Polymorphisms*, section 0.2, the example
identifying 3-SAT with the eight relations `Bool³ \ {pattern}`.
-/

namespace Polytime2.CSP.ThreeSAT

open FirstOrder FirstOrder.Language

/-- The eight ternary symbols, with the arity equality retained only to fit
Mathlib's arity-indexed language. Symbols are actual Boolean triples. -/
def language : Language where
  Functions := fun _ => Empty
  Relations := fun arity => {_pattern : Fin 3 → Bool // arity = 3}

instance languageIsRelational : language.IsRelational := by
  intro arity
  change IsEmpty Empty
  infer_instance

/-- Total relation symbols correspond bijectively to Boolean triples. -/
def relationSymbolsEquiv : (Σ arity, language.Relations arity) ≃ (Fin 3 → Bool) where
  toFun := fun symbol => symbol.2.val
  invFun := fun pattern => ⟨3, ⟨pattern, rfl⟩⟩
  left_inv := by
    rintro ⟨arity, pattern, equality⟩
    cases equality
    rfl
  right_inv := fun _ => rfl

instance finiteRelationSymbols : Finite (Σ arity, language.Relations arity) :=
  Finite.of_equiv (Fin 3 → Bool) relationSymbolsEquiv.symm

/-- Fix the relation enumeration through the eight Boolean triples. -/
noncomputable instance relationSymbolsFintype : Fintype (Σ arity, language.Relations arity) :=
  Fintype.ofEquiv (Fin 3 → Bool) relationSymbolsEquiv.symm

/-- The signature contains exactly eight relations in total. -/
theorem relationSymbols_card : Nat.card (Σ arity, language.Relations arity) = 8 := by
  rw [Nat.card_congr relationSymbolsEquiv, Nat.card_fun]
  simp

/-- Each template relation excludes exactly its indexing triple. -/
instance template : language.Structure Bool where
  RelMap symbol tuple := tuple ∘ Fin.cast symbol.property.symm ≠ symbol.val

/-- At arity three, relation membership is simply inequality of triples. -/
@[simp] theorem template_relation (pattern tuple : Fin 3 → Bool) :
    Structure.RelMap (L := language) ⟨pattern, rfl⟩ tuple ↔ tuple ≠ pattern := Iff.rfl

/-- Interpret a formula as a structure on its original variables. Multiple
identical clauses impose one relation application; no distinctness of the
three variables is required. -/
@[instance_reducible] def instanceOfFormula {variableCount : ℕ}
    (formula : SAT.Formula (Fin variableCount)) : Instance language variableCount where
  RelMap symbol tuple := ∃ clause ∈ formula,
    clause.falsifyingPattern = symbol.val ∧
      tuple = clause.scope ∘ Fin.cast symbol.property

/-- An assignment preserves every instance relation exactly when it satisfies
the original formula. Witness transport in both directions is the identity. -/
theorem preserves_iff_satisfied {variableCount : ℕ}
    (formula : SAT.Formula (Fin variableCount)) (assignment : Fin variableCount → Bool) :
    (∀ (arity : ℕ) (symbol : language.Relations arity) (tuple : Fin arity → Fin variableCount),
      (instanceOfFormula formula).RelMap symbol tuple →
        Structure.RelMap symbol (assignment ∘ tuple)) ↔ SAT.Formula.Satisfied assignment formula := by
  constructor
  · intro preserves clause member
    exact (SAT.Clause.satisfied_iff_ne_falsifyingPattern assignment clause).mpr
      (preserves 3 ⟨clause.falsifyingPattern, rfl⟩ clause.scope
        ⟨clause, member, rfl, rfl⟩)
  · intro satisfied arity symbol tuple enabled
    rcases symbol with ⟨pattern, equality⟩
    subst arity
    obtain ⟨clause, member, pattern_eq, tuple_eq⟩ := enabled
    change clause.falsifyingPattern = pattern at pattern_eq
    change tuple = clause.scope at tuple_eq
    subst tuple
    change assignment ∘ clause.scope ≠ pattern
    rw [← pattern_eq]
    exact (SAT.Clause.satisfied_iff_ne_falsifyingPattern assignment clause).mp
      (satisfied clause member)

/-- Formula satisfiability is equivalent to existence of a homomorphism into
the eight-relation Boolean template. This is a semantic equivalence only. -/
theorem satisfiable_iff {variableCount : ℕ} (formula : SAT.Formula (Fin variableCount)) :
    Instance.Satisfiable language (instanceOfFormula formula) Bool ↔ SAT.Formula.Satisfiable formula := by
  rw [Instance.satisfiable_iff_exists_assignment]
  exact exists_congr (fun assignment => preserves_iff_satisfied formula assignment)

/-- Enumerate the enabled pattern/scope pairs of an arbitrary finite instance
as clauses. The classical enumeration order has no mathematical significance;
this is not an implementation or a complexity certificate. -/
noncomputable def formulaOfInstance {variableCount : ℕ}
    (input : Instance language variableCount) : SAT.Formula (Fin variableCount) := by
  classical
  exact ((Finset.univ : Finset ((Fin 3 → Bool) × (Fin 3 → Fin variableCount))).filter
    (fun constraint => input.RelMap ⟨constraint.1, rfl⟩ constraint.2)).toList.map
      (fun constraint position => (constraint.2 position, constraint.1 position))

/-- Converting an instance to clauses and back preserves every relation
application, rather than only preserving satisfiability. -/
theorem instanceOfFormula_formulaOfInstance_relMap {variableCount : ℕ}
    (input : Instance language variableCount) (arity : ℕ)
    (symbol : language.Relations arity) (tuple : Fin arity → Fin variableCount) :
    (instanceOfFormula (formulaOfInstance input)).RelMap symbol tuple ↔ input.RelMap symbol tuple := by
  classical
  rcases symbol with ⟨pattern, equality⟩
  subst arity
  change (∃ clause ∈ formulaOfInstance input,
    clause.falsifyingPattern = pattern ∧ tuple = clause.scope) ↔ _
  constructor
  · rintro ⟨clause, member, pattern_eq, scope_eq⟩
    obtain ⟨⟨sourcePattern, sourceScope⟩, enabled, clause_eq⟩ := List.mem_map.mp member
    have holds : input.RelMap ⟨sourcePattern, rfl⟩ sourceScope :=
      (Finset.mem_filter.mp (Finset.mem_toList.mp enabled)).2
    subst clause
    change sourcePattern = pattern at pattern_eq
    change tuple = sourceScope at scope_eq
    subst sourcePattern
    subst sourceScope
    exact holds
  · intro enabled
    refine ⟨fun position => (tuple position, pattern position), ?_, rfl, rfl⟩
    apply List.mem_map.mpr
    refine ⟨(pattern, tuple), ?_, rfl⟩
    apply Finset.mem_toList.mpr
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, enabled⟩

/-- Every finite instance of the template is equivalent to a three-literal
CNF formula on the same variables, with no new assignment choices. -/
theorem formulaOfInstance_satisfiable_iff {variableCount : ℕ}
    (input : Instance language variableCount) :
    SAT.Formula.Satisfiable (formulaOfInstance input) ↔ Instance.Satisfiable language input Bool := by
  rw [← satisfiable_iff, Instance.satisfiable_iff_exists_assignment,
    Instance.satisfiable_iff_exists_assignment]
  apply exists_congr
  intro assignment
  apply forall_congr'
  intro arity
  apply forall_congr'
  intro symbol
  apply forall_congr'
  intro tuple
  rw [instanceOfFormula_formulaOfInstance_relMap]

end Polytime2.CSP.ThreeSAT
