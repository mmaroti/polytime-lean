import Polytime2.CSP.Polymorphism
import Mathlib.ModelTheory.Complexity

/-! # Primitive-positive formulas

Primitive-positive formulas use atomic formulas (including equality), truth,
finite conjunction, and existential quantification. They use Mathlib syntax
and semantics, with no falsehood constructor. Preservation includes nullary
operations and empty carriers.

Mathematical provenance: Brady, *Notes on CSPs and Polymorphisms*, section 1.1.
-/

namespace Polytime2.CSP

open FirstOrder FirstOrder.Language

universe functionLevel relationLevel languageLevel variableLevel otherVariableLevel
  boundVariableLevel conjunctionLevel carrierLevel targetLevel indexLevel

section Syntax

variable {L : Language.{functionLevel, relationLevel}} {Variables : Type variableLevel}

/-- The positive existential conjunctive fragment of Mathlib's formulas.
Truth permits empty conjunctions; falsehood is deliberately absent. -/
inductive IsPrimitivePositive : {bound : ℕ} → L.BoundedFormula Variables bound → Prop
  | atomic {bound} {formula : L.BoundedFormula Variables bound}
      (proof : formula.IsAtomic) : IsPrimitivePositive formula
  | top {bound} : IsPrimitivePositive (⊤ : L.BoundedFormula Variables bound)
  | inf {bound} {first second : L.BoundedFormula Variables bound}
      (left : IsPrimitivePositive first) (right : IsPrimitivePositive second) :
      IsPrimitivePositive (first ⊓ second)
  | ex {bound} {formula : L.BoundedFormula Variables (bound + 1)}
      (body : IsPrimitivePositive formula) : IsPrimitivePositive formula.ex

namespace IsPrimitivePositive

theorem relabel {OtherVariables : Type otherVariableLevel} {bound extra : ℕ}
    {formula : L.BoundedFormula Variables bound} (positive : IsPrimitivePositive formula)
    (rename : Variables → OtherVariables ⊕ Fin extra) :
    IsPrimitivePositive (formula.relabel rename) := by
  induction positive with
  | atomic proof => exact atomic (proof.relabel rename)
  | top => exact top
  | inf _ _ left right => exact left.inf right
  | ex _ body => simpa only [BoundedFormula.relabel_ex] using body.ex

theorem exs {bound : ℕ} {formula : L.BoundedFormula Variables bound}
    (positive : IsPrimitivePositive formula) : IsPrimitivePositive formula.exs := by
  induction bound with
  | zero => exact positive
  | succ bound hypothesis => exact hypothesis positive.ex

theorem iExs {BoundVariables : Type boundVariableLevel} [Finite BoundVariables]
    {formula : L.Formula (Variables ⊕ BoundVariables)} (positive : IsPrimitivePositive formula) :
    IsPrimitivePositive (formula.iExs BoundVariables) := by
  exact (positive.relabel _).exs

theorem iInf {Index : Type conjunctionLevel} [Finite Index] {bound : ℕ}
    (formulas : Index → L.BoundedFormula Variables bound)
    (positive : ∀ index, IsPrimitivePositive (formulas index)) :
    IsPrimitivePositive (BoundedFormula.iInf formulas) := by
  classical
  let _ := Fintype.ofFinite Index
  dsimp only [BoundedFormula.iInf]
  generalize (Finset.univ : Finset Index).toList = indices
  induction indices with
  | nil => exact top
  | cons index indices hypothesis => exact (positive index).inf hypothesis

end IsPrimitivePositive

end Syntax

section Semantics

variable {L : Language.{functionLevel, relationLevel}} {Variables : Type variableLevel}
variable {Carrier : Type carrierLevel} [L.Structure Carrier]
variable {Target : Type targetLevel} [L.Structure Target]

/-- Homomorphisms preserve primitive-positive formulas, without injectivity or
inhabitance hypotheses. -/
theorem IsPrimitivePositive.map {bound : ℕ} {formula : L.BoundedFormula Variables bound}
    (positive : IsPrimitivePositive formula) (homomorphism : Carrier →[L] Target)
    {values : Variables → Carrier} {boundValues : Fin bound → Carrier}
    (satisfies : formula.Realize values boundValues) :
    formula.Realize (homomorphism ∘ values) (homomorphism ∘ boundValues) := by
  induction positive with
  | atomic proof =>
    cases proof with
    | equal first second =>
      simpa only [BoundedFormula.realize_bdEqual, ← Sum.comp_elim, HomClass.realize_term]
        using congrArg homomorphism satisfies
    | rel symbol terms =>
      simp only [BoundedFormula.realize_rel, ← Sum.comp_elim, HomClass.realize_term]
      exact homomorphism.map_rel symbol _ satisfies
  | top => trivial
  | inf _ _ left right =>
    rw [BoundedFormula.realize_inf] at satisfies ⊢
    exact ⟨left satisfies.1, right satisfies.2⟩
  | ex _ body =>
    obtain ⟨witness, witnessProof⟩ := BoundedFormula.realize_ex.mp satisfies
    apply BoundedFormula.realize_ex.mpr
    refine ⟨homomorphism witness, ?_⟩
    simpa only [Fin.comp_snoc] using body witnessProof

private theorem term_realize_power_coordinate {bound : ℕ} {Index : Type indexLevel}
    (term : L.Term (Variables ⊕ Fin bound)) (values : Variables → Index → Carrier)
    (boundValues : Fin bound → Index → Carrier) (index : Index) :
    term.realize (Sum.elim (fun coordinate => values coordinate index)
      (fun coordinate => boundValues coordinate index)) =
      term.realize (Sum.elim values boundValues) index := by
  have environment : Sum.elim (fun coordinate => values coordinate index)
      (fun coordinate => boundValues coordinate index) =
      (powerProjection (L := L) (Carrier := Carrier) index) ∘ Sum.elim values boundValues := by
    funext name
    cases name <;> rfl
  rw [environment]
  exact HomClass.realize_term (powerProjection (L := L) (Carrier := Carrier) index)

/-- Realization in an ordinary power is coordinatewise for this fragment,
including empty powers. Existential witnesses are chosen coordinatewise. -/
theorem IsPrimitivePositive.realize_power {bound : ℕ}
    {formula : L.BoundedFormula Variables bound} (positive : IsPrimitivePositive formula)
    {Index : Type indexLevel} {values : Variables → Index → Carrier}
    {boundValues : Fin bound → Index → Carrier} :
    formula.Realize values boundValues ↔
      ∀ index, formula.Realize (fun coordinate => values coordinate index)
        (fun coordinate => boundValues coordinate index) := by
  classical
  induction positive with
  | atomic proof =>
    cases proof with
    | equal first second =>
      simp only [BoundedFormula.realize_bdEqual]
      simp_rw [term_realize_power_coordinate]
      exact funext_iff
    | rel symbol terms =>
      simp only [BoundedFormula.realize_rel]
      simp_rw [term_realize_power_coordinate]
      rfl
  | top => simp
  | inf _ _ left right => simp only [BoundedFormula.realize_inf, left, right, forall_and]
  | ex _ body =>
    simp only [BoundedFormula.realize_ex, body]
    have tupleAt (witness : Index → Carrier) (index : Index) :=
      Fin.comp_snoc (fun tuple : Index → Carrier => tuple index) boundValues witness
    dsimp only [Function.comp_def] at tupleAt
    constructor
    · rintro ⟨witness, proof⟩ index
      refine ⟨witness index, ?_⟩
      have atIndex := proof index
      rw [tupleAt] at atIndex
      exact atIndex
    · intro proof
      choose witness witnessProof using proof
      refine ⟨witness, fun index => ?_⟩
      rw [tupleAt]
      exact witnessProof index

/-- The formula-level homomorphism rule hides the empty bound-variable tuple. -/
theorem IsPrimitivePositive.map_formula {formula : L.Formula Variables}
    (positive : IsPrimitivePositive formula) (homomorphism : Carrier →[L] Target)
    {values : Variables → Carrier} (satisfies : formula.Realize values) :
    formula.Realize (homomorphism ∘ values) := by
  have mapped := positive.map homomorphism satisfies
  have empty : homomorphism ∘ (default : Fin 0 → Carrier) = (default : Fin 0 → Target) :=
    Subsingleton.elim _ _
  rw [empty] at mapped
  exact mapped

/-- Formula realization commutes with arbitrary powers, including the empty one. -/
theorem IsPrimitivePositive.realize_formula_power {formula : L.Formula Variables}
    (positive : IsPrimitivePositive formula) {Index : Type indexLevel}
    {values : Variables → Index → Carrier} :
    formula.Realize values ↔
      ∀ index, formula.Realize (fun coordinate => values coordinate index) := by
  rw [Formula.Realize, positive.realize_power]
  apply forall_congr'
  intro index
  have empty : (fun coordinate : Fin 0 => (default : Fin 0 → Index → Carrier) coordinate index) =
      (default : Fin 0 → Carrier) := Subsingleton.elim _ _
  rw [empty]
  rfl

end Semantics

section Relations

variable {L : Language.{languageLevel, languageLevel}} [L.IsRelational]
variable {Carrier : Type carrierLevel} [L.Structure Carrier]
variable {Variables : Type variableLevel}

/-- A relation has a primitive-positive definition over the template, using
no parameters or additional relation symbols. -/
def IsPPDefinable (L : Language.{languageLevel, languageLevel}) [L.IsRelational] {Carrier : Type carrierLevel}
    [L.Structure Carrier] {Variables : Type variableLevel}
    (relation : Set (Variables → Carrier)) : Prop :=
  ∃ formula : L.Formula Variables, IsPrimitivePositive formula ∧
    ∀ values, formula.Realize values ↔ values ∈ relation

/-- Invariance under all template polymorphisms, including operation arity
zero. For an empty relation that case says there is no nullary polymorphism. -/
def IsPolymorphismInvariant (L : Language.{languageLevel, languageLevel}) [L.IsRelational] {Carrier : Type carrierLevel}
    [L.Structure Carrier] {Variables : Type variableLevel}
    (relation : Set (Variables → Carrier)) : Prop :=
  ∀ arity (operation : (Fin arity → Carrier) → Carrier), IsPolymorphism L Carrier operation →
    ∀ tuples : Fin arity → Variables → Carrier, (∀ index, tuples index ∈ relation) →
      (fun coordinate => operation (fun index => tuples index coordinate)) ∈ relation

theorem IsPPDefinable.invariant {relation : Set (Variables → Carrier)}
    (definable : IsPPDefinable L relation) : IsPolymorphismInvariant L relation := by
  obtain ⟨formula, positive, defines⟩ := definable
  intro arity operation preserves tuples related
  apply (defines _).mp
  have satisfied : formula.Realize (fun coordinate index => tuples index coordinate) := by
    apply positive.realize_formula_power.mpr
    intro index
    exact (defines _).mpr (related index)
  exact positive.map_formula (Polymorphism.ofOperation operation preserves) satisfied

end Relations

end Polytime2.CSP
