import Mathlib.ModelTheory.Basic

/-! # Relational CSP instances and solutions

For a fixed relational template on `Carrier`, an instance is a structure in
the same language on its variables. A solution is a Mathlib homomorphism from
the instance to the template. `Satisfiable` asserts existence of a solution;
it makes no claim about an algorithm or its complexity.

The mathematical characterization works for arbitrary carriers. Fixed-template
finite CSP specializes it to a finite template, finitely many total relation
symbols, and `Instance L variableCount`, whose variables are `Fin variableCount`.
Instances impose no reflexivity or symmetry conditions; tuples may repeat
variables. Nullary relations are included, even for zero variables.

`Instance` reuses Mathlib's structure type rather than defining a new carrier.
Its relations are mathematical predicates. Canonical Boolean-table encodings
and polynomial-time realizations are separate later obligations.
-/

namespace Polytime2.CSP

open FirstOrder FirstOrder.Language

universe languageLevel instanceLevel carrierLevel

variable (L : Language.{languageLevel, languageLevel}) [L.IsRelational]

/-- All relation symbols, retaining their mathematical arities. Total
finiteness is the fixed-signature hypothesis for finite-template CSP. -/
abbrev RelationSymbol := Σ arity : ℕ, L.Relations arity

/-- The homomorphism decision predicate for an instance and a fixed template.
No finiteness or decidability assumption is needed to state satisfiability. -/
def Satisfiable (Variables : Type instanceLevel) (Carrier : Type carrierLevel)
    [L.Structure Variables] [L.Structure Carrier] : Prop :=
  Nonempty (Variables →[L] Carrier)

/-- Satisfiability is exactly existence of an assignment preserving all enabled
relation tuples, including nullary relations. No function-symbol obligations
remain because the language is relational. -/
theorem satisfiable_iff_exists_assignment
    (Variables : Type instanceLevel) (Carrier : Type carrierLevel)
    [L.Structure Variables] [L.Structure Carrier] :
    Satisfiable L Variables Carrier ↔
      ∃ assignment : Variables → Carrier,
        ∀ (arity : ℕ) (symbol : L.Relations arity) (tuple : Fin arity → Variables),
          Structure.RelMap symbol tuple → Structure.RelMap symbol (assignment ∘ tuple) := by
  constructor
  · rintro ⟨homomorphism⟩
    exact ⟨homomorphism, fun _ symbol tuple => homomorphism.map_rel symbol tuple⟩
  · rintro ⟨assignment, preserves⟩
    exact ⟨{
      toFun := assignment
      map_fun' := fun symbol => isEmptyElim symbol
      map_rel' := fun symbol tuple => preserves _ symbol tuple }⟩

/-- A finite instance has exactly `variableCount` variables and interprets the
fixed language on `Fin variableCount`. This is the mathematical carrier for
future encoded domains; it does not prescribe an encoding. -/
abbrev Instance (variableCount : ℕ) := L.Structure (Fin variableCount)

/-- Satisfiability with the input structure passed as ordinary mathematical
data. The template interpretation remains fixed through its typeclass. -/
def Instance.Satisfiable {variableCount : ℕ} (input : Instance L variableCount)
    (Carrier : Type carrierLevel) [L.Structure Carrier] : Prop :=
  letI : L.Structure (Fin variableCount) := input
  CSP.Satisfiable L (Fin variableCount) Carrier

/-- The explicit-instance interface has the same assignment contract as the
general homomorphism predicate. Each enabled tuple is tested in the template. -/
theorem Instance.satisfiable_iff_exists_assignment
    {variableCount : ℕ} (input : Instance L variableCount)
    (Carrier : Type carrierLevel) [L.Structure Carrier] :
    Instance.Satisfiable L input Carrier ↔
      ∃ assignment : Fin variableCount → Carrier,
        ∀ (arity : ℕ) (symbol : L.Relations arity) (tuple : Fin arity → Fin variableCount),
          input.RelMap symbol tuple → Structure.RelMap symbol (assignment ∘ tuple) := by
  let _ : L.Structure (Fin variableCount) := input
  exact CSP.satisfiable_iff_exists_assignment L (Fin variableCount) Carrier

/-- With no variables, the unique empty assignment is a solution precisely
when every asserted nullary relation holds in the template. This also applies
to empty templates and requires no artificial inhabitant for the assignment. -/
theorem satisfiable_iff_nullary_of_isEmpty
    (Variables : Type instanceLevel) (Carrier : Type carrierLevel)
    [IsEmpty Variables] [L.Structure Variables] [L.Structure Carrier] :
    Satisfiable L Variables Carrier ↔
      ∀ symbol : L.Relations 0,
        Structure.RelMap symbol (Fin.elim0 : Fin 0 → Variables) →
          Structure.RelMap symbol (Fin.elim0 : Fin 0 → Carrier) := by
  rw [satisfiable_iff_exists_assignment]
  constructor
  · rintro ⟨assignment, preserves⟩ symbol enabled
    have mapped := preserves 0 symbol Fin.elim0 enabled
    simpa only [Subsingleton.elim (assignment ∘ Fin.elim0) Fin.elim0] using mapped
  · intro nullary
    refine ⟨isEmptyElim, ?_⟩
    intro arity symbol tuple enabled
    cases arity with
    | zero =>
      have enabledEmpty : Structure.RelMap symbol (Fin.elim0 : Fin 0 → Variables) := by
        simpa only [Subsingleton.elim tuple Fin.elim0] using enabled
      simpa only [Subsingleton.elim (isEmptyElim ∘ tuple) Fin.elim0] using
        nullary symbol enabledEmpty
    | succ arity => exact isEmptyElim (tuple 0)

end Polytime2.CSP
