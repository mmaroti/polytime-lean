import Polytime2.CSP.PrimitivePositive
import Mathlib.Data.Fintype.EquivFin

/-! # The finite Inv–Pol theorem

A finite-arity relation on a finite template is primitive-positive definable
exactly when every template polymorphism preserves it. Operation arity zero is
included, so the equivalence also covers empty relations without adjoining a
falsehood symbol. Neither carrier inhabitance nor signature finiteness is
required.

The proof follows Brady, *Notes on CSPs and Polymorphisms*, section 1.1:
describe the finite operation table by a finite conjunction of preservation
constraints, then existentially quantify that table and identify its values on
the columns of an enumeration of the desired relation.
-/

namespace Polytime2.CSP

open FirstOrder FirstOrder.Language

universe languageLevel carrierLevel variableLevel

variable {L : Language.{languageLevel, languageLevel}} [L.IsRelational]
variable {Carrier : Type carrierLevel} [L.Structure Carrier]

section OperationTables

private theorem exists_separating_atom {arity : ℕ}
    {operation : (Fin arity → Carrier) → Carrier}
    (fails : ¬ IsPolymorphism L Carrier operation) :
    ∃ formula : L.Formula (Fin arity → Carrier),
      IsPrimitivePositive formula ∧
      (∀ other, IsPolymorphism L Carrier other → formula.Realize other) ∧
      ¬ formula.Realize operation := by
  classical
  simp only [IsPolymorphism, not_forall] at fails
  obtain ⟨relationArity, symbol, tuples, fails⟩ := fails
  obtain ⟨related, violated⟩ := fails
  refine ⟨symbol.formula (fun coordinate => Term.var (fun index => tuples index coordinate)),
    .atomic (.rel _ _), ?_, ?_⟩
  · intro other preserves
    exact preserves relationArity symbol tuples related
  · exact violated

/-- A finite conjunction of atomic constraints describes exactly the
polymorphism operation tables of a fixed arity. The signature may be infinite:
one failed atomic constraint per non-polymorphism suffices. -/
theorem exists_polymorphism_formula [Finite Carrier] (arity : ℕ) :
    ∃ formula : L.Formula (Fin arity → Carrier), IsPrimitivePositive formula ∧
      ∀ operation, formula.Realize operation ↔ IsPolymorphism L Carrier operation := by
  classical
  let Bad := {operation : (Fin arity → Carrier) → Carrier // ¬ IsPolymorphism L Carrier operation}
  have separation (bad : Bad) := exists_separating_atom bad.property
  choose formula positive accepts rejects using separation
  refine ⟨Formula.iInf formula, IsPrimitivePositive.iInf formula positive, ?_⟩
  intro operation
  rw [Formula.realize_iInf]
  constructor
  · intro satisfies
    by_contra fails
    exact rejects ⟨operation, fails⟩ (satisfies ⟨operation, fails⟩)
  · intro preserves bad
    exact accepts bad operation preserves

end OperationTables

section Definability

variable {Variables : Type variableLevel} [Finite Variables] [Finite Carrier]

/-- Finite Inv–Pol, with all natural-number operation arities. Enumerating the
relation also handles the empty relation: its table has operation arity zero.
The output is an actual parameter-free Mathlib formula over the given language. -/
theorem IsPolymorphismInvariant.ppDefinable {relation : Set (Variables → Carrier)}
    (invariant : IsPolymorphismInvariant L relation) : IsPPDefinable L relation := by
  classical
  let _ := Fintype.ofFinite relation
  let arity := Fintype.card relation
  let enumeration : Fin arity ≃ relation := (Fintype.equivFin relation).symm
  let rows : Fin arity → Variables → Carrier := fun index => (enumeration index).val
  obtain ⟨diagram, diagramPositive, diagramCorrect⟩ :=
    exists_polymorphism_formula (L := L) (Carrier := Carrier) arity
  let equations : L.Formula (Variables ⊕ (Fin arity → Carrier)) := Formula.iInf
    (fun coordinate => (Term.var (Sum.inl coordinate)).equal
      (Term.var (Sum.inr (fun index => rows index coordinate))))
  have equationsPositive : IsPrimitivePositive equations :=
    IsPrimitivePositive.iInf _ (fun _ => .atomic (.equal _ _))
  let body : L.Formula (Variables ⊕ (Fin arity → Carrier)) :=
    diagram.relabel Sum.inr ⊓ equations
  have bodyPositive : IsPrimitivePositive body :=
    (diagramPositive.relabel (Sum.inl ∘ Sum.inr)).inf equationsPositive
  refine ⟨body.iExs (Fin arity → Carrier), bodyPositive.iExs, ?_⟩
  intro values
  simp only [Formula.realize_iExs, body, Formula.realize_inf, Formula.realize_relabel,
    equations, Formula.realize_iInf, Formula.realize_equal, Term.realize_var,
    Function.comp_def, Sum.elim_inr, Sum.elim_inl]
  constructor
  · rintro ⟨operation, satisfies, equalities⟩
    have member := invariant arity operation ((diagramCorrect operation).mp satisfies)
      rows (fun index => (enumeration index).property)
    have equal : values = fun coordinate => operation (fun index => rows index coordinate) :=
      funext equalities
    exact equal ▸ member
  · intro member
    obtain ⟨index, indexEqual⟩ := enumeration.surjective ⟨values, member⟩
    refine ⟨fun tuple => tuple index, (diagramCorrect _).mpr (isPolymorphism_projection index), ?_⟩
    intro coordinate
    exact congrArg (fun tuple : relation => tuple.val coordinate) indexEqual.symm

/-- On a finite carrier, finite-arity pp-definability is exactly preservation
by all polymorphisms, including nullary ones. This includes empty relations,
nullary relations, and empty carriers. -/
theorem isPPDefinable_iff_invariant (relation : Set (Variables → Carrier)) :
    IsPPDefinable L relation ↔ IsPolymorphismInvariant L relation :=
  ⟨IsPPDefinable.invariant, IsPolymorphismInvariant.ppDefinable⟩

/-- The empty relation is pp-definable precisely when there is no nullary
polymorphism. Positive-arity preservation alone would miss this condition. -/
theorem isPPDefinable_empty_iff :
    IsPPDefinable L (∅ : Set (Variables → Carrier)) ↔
      ¬ ∃ operation : (Fin 0 → Carrier) → Carrier, IsPolymorphism L Carrier operation := by
  rw [isPPDefinable_iff_invariant]
  constructor
  · intro invariant
    rintro ⟨operation, preserves⟩
    exact invariant 0 operation preserves Fin.elim0 Fin.elim0
  · intro noNullary arity operation preserves tuples related
    cases arity with
    | zero => exact (noNullary ⟨operation, preserves⟩).elim
    | succ arity => exact (related 0).elim

/-- A nullary relation is a truth value. The true one is always pp-definable;
the false one requires the absence of nullary polymorphisms. -/
theorem isPPDefinable_nullary_iff (relation : Set (Fin 0 → Carrier)) :
    IsPPDefinable L relation ↔ (default : Fin 0 → Carrier) ∈ relation ∨
      ¬ ∃ operation : (Fin 0 → Carrier) → Carrier, IsPolymorphism L Carrier operation := by
  classical
  by_cases holds : (default : Fin 0 → Carrier) ∈ relation
  · constructor
    · intro _; exact Or.inl holds
    · intro _
      refine ⟨⊤, .top, ?_⟩
      intro values
      have member : values ∈ relation := (Subsingleton.elim (default : Fin 0 → Carrier) values) ▸ holds
      simp only [Formula.realize_top, member]
  · have empty : relation = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro values member
      exact holds ((Subsingleton.elim values (default : Fin 0 → Carrier)) ▸ member)
    simpa only [empty, Set.mem_empty_iff_false, false_or] using
      (isPPDefinable_empty_iff (L := L) (Carrier := Carrier) (Variables := Fin 0))

end Definability

end Polytime2.CSP
