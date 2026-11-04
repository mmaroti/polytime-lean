import Polytime2.CSP.BooleanGadgets
import Polytime2.CSP.GadgetGluing

/-! # Mathematical expansion of three-SAT by fixed relational gadgets

Every source variable receives a domain gadget and every clause occurrence a
fresh clause gadget. Boundary variables are glued to the corresponding tuple
blocks. The canonical relational gadgets realize the fixed pp definitions;
their size can be large but depends only on the template. This module contains
no machine, codec, runtime, or realization infrastructure.
-/

namespace Polytime2.CSP.GadgetExpansion

open FirstOrder FirstOrder.Language

universe languageLevel carrierLevel

variable {L : Language.{languageLevel, languageLevel}} [L.IsRelational]
variable {Carrier : Type carrierLevel} [L.Structure Carrier] [Finite Carrier]
variable {dimension : ℕ}

section Construction

/-- Domain gadgets and the eight excluded-pattern clause gadgets. -/
abbrev Kind := Unit ⊕ (Fin 3 → Bool)

def BoundaryVariables (dimension : ℕ) : Kind → Type
  | .inl _ => Fin dimension
  | .inr _ => Fin 3 × Fin dimension

instance boundaryFintype (kind : Kind) : Fintype (BoundaryVariables dimension kind) := by
  cases kind <;> dsimp only [BoundaryVariables] <;> infer_instance

variable (domainFormula : L.Formula (Fin dimension))
variable (clauseFormulas : (Fin 3 → Bool) → L.Formula (Fin 3 × Fin dimension))

def relation : (kind : Kind) → Set (BoundaryVariables dimension kind → Carrier)
  | .inl _ => {values | domainFormula.Realize values}
  | .inr pattern => {values | (clauseFormulas pattern).Realize values}

abbrev Host (kind : Kind) := CanonicalGadget (relation (Carrier := Carrier) domainFormula clauseFormulas kind)

noncomputable def boundary (kind : Kind) : BoundaryVariables dimension kind → Host (Carrier := Carrier) domainFormula clauseFormulas kind :=
  canonicalBoundary (relation (Carrier := Carrier) domainFormula clauseFormulas kind)

theorem local_extends_iff (domainPositive : IsPrimitivePositive domainFormula)
    (clausePositive : ∀ pattern, IsPrimitivePositive (clauseFormulas pattern))
    (kind : Kind) (values : BoundaryVariables dimension kind → Carrier) :
    (∃ homomorphism : Host (Carrier := Carrier) domainFormula clauseFormulas kind →[L] Carrier,
      ∀ coordinate, homomorphism (boundary (Carrier := Carrier) domainFormula clauseFormulas kind coordinate) = values coordinate) ↔
      values ∈ relation (Carrier := Carrier) domainFormula clauseFormulas kind := by
  apply IsPPDefinable.canonicalGadget_extends_iff
  cases kind with
  | inl _unitValue => exact (show IsPPDefinable L {values | domainFormula.Realize values} from
      ⟨domainFormula, domainPositive, fun _ => Iff.rfl⟩)
  | inr pattern => exact (show IsPPDefinable L {values | (clauseFormulas pattern).Realize values} from
      ⟨clauseFormulas pattern, clausePositive pattern, fun _ => Iff.rfl⟩)

def occurrenceKind {variableCount : ℕ} (formula : SAT.Formula (Fin variableCount)) :
    Fin variableCount ⊕ Fin formula.length → Kind
  | .inl _ => .inl ()
  | .inr index => .inr (formula.get index).falsifyingPattern

def scope {variableCount : ℕ} (formula : SAT.Formula (Fin variableCount)) :
    (occurrence : Fin variableCount ⊕ Fin formula.length) →
      BoundaryVariables dimension (occurrenceKind formula occurrence) → Fin variableCount × Fin dimension
  | .inl variableIndex => fun coordinate => (variableIndex, coordinate)
  | .inr index => fun position => ((formula.get index).scope position.1, position.2)

noncomputable def occurrenceBoundary {variableCount : ℕ} (formula : SAT.Formula (Fin variableCount))
    (occurrence : Fin variableCount ⊕ Fin formula.length) :=
  boundary (Carrier := Carrier) domainFormula clauseFormulas (occurrenceKind formula occurrence)

/-- The target variables are fresh gadget copies with their boundary equations
identified. This mathematical quotient needs no arbitrary numbering of variables. -/
abbrev ExpandedVariables {variableCount : ℕ} (formula : SAT.Formula (Fin variableCount)) :=
  GluedVariables (occurrenceBoundary (Carrier := Carrier) domainFormula clauseFormulas formula) (scope formula)

noncomputable def shared {variableCount : ℕ} (formula : SAT.Formula (Fin variableCount))
    (position : Fin variableCount × Fin dimension) : ExpandedVariables (Carrier := Carrier) domainFormula clauseFormulas formula :=
  sharedVariable (occurrenceBoundary (Carrier := Carrier) domainFormula clauseFormulas formula) (scope formula) position

/-- The expansion has precisely the conjunction of the domain and clause
gadget contracts on the supplied shared tuple blocks. -/
theorem extends_iff {variableCount : ℕ} (formula : SAT.Formula (Fin variableCount))
    (domainPositive : IsPrimitivePositive domainFormula)
    (clausePositive : ∀ pattern, IsPrimitivePositive (clauseFormulas pattern))
    (blocks : (Fin variableCount × Fin dimension) → Carrier) :
    (∃ homomorphism : ExpandedVariables (Carrier := Carrier) domainFormula clauseFormulas formula →[L] Carrier,
      ∀ position, homomorphism (shared domainFormula clauseFormulas formula position) = blocks position) ↔
    (∀ variableIndex, domainFormula.Realize (fun coordinate => blocks (variableIndex, coordinate))) ∧
      ∀ index : Fin formula.length, ((clauseFormulas (formula.get index).falsifyingPattern).Realize
        (fun position => blocks ((formula.get index).scope position.1, position.2))) := by
  simp only [shared]
  rw [glued_extends_iff]
  constructor
  · intro extensions
    exact ⟨fun variableIndex => (local_extends_iff domainFormula clauseFormulas domainPositive clausePositive _ _).mp
      (extensions (.inl variableIndex)),
      fun index => (local_extends_iff domainFormula clauseFormulas domainPositive clausePositive _ _).mp
        (extensions (.inr index))⟩
  · rintro ⟨domains, clauses⟩ occurrence
    cases occurrence with
    | inl variableIndex =>
      exact (local_extends_iff domainFormula clauseFormulas domainPositive clausePositive _ _).mpr
        (domains variableIndex)
    | inr index =>
      exact (local_extends_iff domainFormula clauseFormulas domainPositive clausePositive _ _).mpr
        (clauses index)

end Construction

section Correctness

variable {subalgebra : (polymorphismLanguage L Carrier).Substructure (Fin dimension → Carrier)}
variable {quotient : subalgebra → Bool}
variable {domainFormula : L.Formula (Fin dimension)}
variable {equalityFormula : L.Formula (Fin 2 × Fin dimension)}
variable {clauseFormulas : (Fin 3 → Bool) → L.Formula (Fin 3 × Fin dimension)}
variable (family : IsBooleanGadgetFamily subalgebra quotient domainFormula equalityFormula clauseFormulas)

include family

/-- For any choice of blocks representing a Boolean assignment, extension to
a target homomorphism is equivalent to satisfaction of the original formula. -/
theorem extends_iff_satisfied {variableCount : ℕ} (formula : SAT.Formula (Fin variableCount))
    (assignment : Fin variableCount → Bool) (blocks : (Fin variableCount × Fin dimension) → Carrier)
    (represented : ∀ variableIndex, Represents subalgebra quotient
      (fun coordinate => blocks (variableIndex, coordinate)) (assignment variableIndex)) :
    (∃ homomorphism : ExpandedVariables (Carrier := Carrier) domainFormula clauseFormulas formula →[L] Carrier,
      ∀ position, homomorphism (shared domainFormula clauseFormulas formula position) = blocks position) ↔
      SAT.Formula.Satisfied assignment formula := by
  rw [extends_iff domainFormula clauseFormulas formula family.1 family.2.2.1]
  have domains : ∀ variableIndex, domainFormula.Realize (fun coordinate => blocks (variableIndex, coordinate)) :=
    fun variableIndex => (family.domain _).mpr ⟨assignment variableIndex, represented variableIndex⟩
  rw [iff_true_intro domains, true_and]
  rw [SAT.Formula.Satisfied, List.forall_mem_iff_get]
  apply forall_congr'
  intro index
  exact (family.2.2.2.2.2 (formula.get index).falsifyingPattern _).trans
    ((liftedRelation_iff_of_represents _ _ (assignment ∘ (formula.get index).scope)
      (fun argument => represented ((formula.get index).scope argument))).trans
      (SAT.Clause.satisfied_iff_ne_falsifyingPattern assignment (formula.get index)).symm)

/-- Boolean assignments admit representative blocks and an extending target
homomorphism exactly when they satisfy the source formula. -/
theorem assignment_extends_iff (representatives : Bool → subalgebra)
    (sectionLaw : Function.RightInverse representatives quotient)
    {variableCount : ℕ} (formula : SAT.Formula (Fin variableCount)) (assignment : Fin variableCount → Bool) :
    (∃ blocks : (Fin variableCount × Fin dimension) → Carrier,
      (∀ variableIndex, Represents subalgebra quotient
        (fun coordinate => blocks (variableIndex, coordinate)) (assignment variableIndex)) ∧
      ∃ homomorphism : ExpandedVariables (Carrier := Carrier) domainFormula clauseFormulas formula →[L] Carrier,
        ∀ position, homomorphism (shared domainFormula clauseFormulas formula position) = blocks position) ↔
      SAT.Formula.Satisfied assignment formula := by
  constructor
  · rintro ⟨blocks, represented, extension⟩
    exact (extends_iff_satisfied family formula assignment blocks represented).mp extension
  · intro satisfied
    let blocks (position : Fin variableCount × Fin dimension) :=
      (representatives (assignment position.1)).val position.2
    have represented variableIndex : Represents subalgebra quotient
        (fun coordinate => blocks (variableIndex, coordinate)) (assignment variableIndex) :=
      ⟨representatives (assignment variableIndex), rfl, sectionLaw (assignment variableIndex)⟩
    exact ⟨blocks, represented, (extends_iff_satisfied family formula assignment blocks represented).mpr satisfied⟩

/-- The target is an actual relational structure. Repeated literals, repeated
clauses, unused variables, and empty formulas require no side conditions. -/
theorem satisfiable_iff (representatives : Bool → subalgebra)
    (sectionLaw : Function.RightInverse representatives quotient)
    {variableCount : ℕ} (formula : SAT.Formula (Fin variableCount)) :
    Satisfiable L (ExpandedVariables (Carrier := Carrier) domainFormula clauseFormulas formula) Carrier ↔
      SAT.Formula.Satisfiable formula := by
  classical
  constructor
  · rintro ⟨homomorphism⟩
    let blocks position := homomorphism (shared domainFormula clauseFormulas formula position)
    have extension : ∃ hom : ExpandedVariables (Carrier := Carrier) domainFormula clauseFormulas formula →[L] Carrier,
        ∀ position, hom (shared domainFormula clauseFormulas formula position) = blocks position :=
      ⟨homomorphism, fun _ => rfl⟩
    have domains := ((extends_iff domainFormula clauseFormulas formula family.1 family.2.2.1 blocks).mp extension).1
    have values variableIndex := (family.domain _).mp (domains variableIndex)
    choose assignment represented using values
    exact ⟨assignment, (extends_iff_satisfied family formula assignment blocks represented).mp extension⟩
  · rintro ⟨assignment, satisfied⟩
    obtain ⟨blocks, represented, homomorphism, agrees⟩ :=
      (assignment_extends_iff family representatives sectionLaw formula assignment).mpr satisfied
    exact ⟨homomorphism⟩

end Correctness

end Polytime2.CSP.GadgetExpansion
