import Polytime2.CSP.QuotientRelation
import Polytime2.CSP.ThreeSAT

/-! # A fixed family of Boolean pp gadgets

Brady, *Notes on CSPs and Polymorphisms*, sections 1.1 and 1.3. The finite
projection witness gives one domain formula, one quotient-equality formula,
and eight clause formulas indexed by their excluded Boolean triple. All are
parameter-free Mathlib primitive-positive formulas in the original language.
The family and Boolean representatives depend only on the fixed template.
-/

namespace Polytime2.CSP

open FirstOrder FirstOrder.Language

universe languageLevel carrierLevel

variable {L : Language.{languageLevel, languageLevel}} [L.IsRelational]
variable {Carrier : Type carrierLevel} [L.Structure Carrier] {dimension : ℕ}

section Contracts

/-- The ten fixed gadgets and their exact contracts on arbitrary blocks.
Equality compares represented Boolean values, not the raw representative
tuples. Every lifted constraint requires its blocks to lie in the domain. -/
def IsBooleanGadgetFamily
    (subalgebra : (polymorphismLanguage L Carrier).Substructure (Fin dimension → Carrier))
    (quotient : subalgebra → Bool)
    (domainFormula : L.Formula (Fin dimension))
    (equalityFormula : L.Formula (Fin 2 × Fin dimension))
    (clauseFormulas : (Fin 3 → Bool) → L.Formula (Fin 3 × Fin dimension)) : Prop :=
  IsPrimitivePositive domainFormula ∧ IsPrimitivePositive equalityFormula ∧
    (∀ pattern, IsPrimitivePositive (clauseFormulas pattern)) ∧
    (∀ block, domainFormula.Realize block ↔ block ∈ subalgebra) ∧
    (∀ blocks, equalityFormula.Realize blocks ↔
      blocks ∈ liftedRelation subalgebra quotient {values | values 0 = values 1}) ∧
    ∀ pattern blocks, (clauseFormulas pattern).Realize blocks ↔
      blocks ∈ liftedRelation subalgebra quotient {values | values ≠ pattern}

variable {subalgebra : (polymorphismLanguage L Carrier).Substructure (Fin dimension → Carrier)}
variable {quotient : subalgebra → Bool}
variable {domainFormula : L.Formula (Fin dimension)}
variable {equalityFormula : L.Formula (Fin 2 × Fin dimension)}
variable {clauseFormulas : (Fin 3 → Bool) → L.Formula (Fin 3 × Fin dimension)}

theorem IsBooleanGadgetFamily.domain
    (family : IsBooleanGadgetFamily subalgebra quotient domainFormula equalityFormula clauseFormulas)
    (block : Fin dimension → Carrier) :
    domainFormula.Realize block ↔ ∃ value, Represents subalgebra quotient block value :=
  (family.2.2.2.1 block).trans (represents_some_iff block).symm

/-- Any pair of representatives satisfies the equality gadget exactly when
its members belong to the same quotient class. -/
theorem IsBooleanGadgetFamily.equality
    (family : IsBooleanGadgetFamily subalgebra quotient domainFormula equalityFormula clauseFormulas)
    (representatives : Fin 2 → subalgebra) :
    equalityFormula.Realize (fun position => (representatives position.1).val position.2) ↔
      quotient (representatives 0) = quotient (representatives 1) := by
  rw [family.2.2.2.2.1 _, liftedRelation_on_representatives _ representatives]
  rfl

/-- The clause contract for arbitrary quotient representatives. The relation
is exactly the excluded-pattern relation of the existing Three-SAT template. -/
theorem IsBooleanGadgetFamily.clause
    (family : IsBooleanGadgetFamily subalgebra quotient domainFormula equalityFormula clauseFormulas)
    (pattern : Fin 3 → Bool) (representatives : Fin 3 → subalgebra) :
    (clauseFormulas pattern).Realize (fun position => (representatives position.1).val position.2) ↔
      Structure.RelMap (L := ThreeSAT.language) ⟨pattern, rfl⟩
        (fun argument => quotient (representatives argument)) := by
  rw [family.2.2.2.2.2 pattern _, liftedRelation_on_representatives _ representatives]
  rfl

/-- Choosing representatives from a section realizes exactly the intended
Boolean clause, independently of which section was selected. -/
theorem IsBooleanGadgetFamily.clause_on_section
    (family : IsBooleanGadgetFamily subalgebra quotient domainFormula equalityFormula clauseFormulas)
    (representatives : Bool → subalgebra) (sectionLaw : Function.RightInverse representatives quotient)
    (pattern values : Fin 3 → Bool) :
    (clauseFormulas pattern).Realize
        (fun position => (representatives (values position.1)).val position.2) ↔ values ≠ pattern := by
  rw [family.2.2.2.2.2 pattern _, liftedRelation_on_section representatives sectionLaw]
  rfl

end Contracts

section Construction

variable [Finite Carrier]
variable (subalgebra : (polymorphismLanguage L Carrier).Substructure (Fin dimension → Carrier))
variable [booleanStructure : (polymorphismLanguage L Carrier).Structure Bool]
variable (projections : ∀ arity (symbol : (polymorphismLanguage L Carrier).Functions arity),
  ∃ coordinate : Fin arity, ∀ values : Fin arity → Bool,
    Structure.funMap symbol values = values coordinate)
variable (quotient : subalgebra →[polymorphismLanguage L Carrier] Bool)

include projections in
/-- Apply finite Inv–Pol to the domain, quotient equality, and the eight
Boolean clauses. The resulting formulas use no added relation symbols. -/
theorem exists_boolean_gadget_family :
    ∃ domainFormula : L.Formula (Fin dimension),
      ∃ equalityFormula : L.Formula (Fin 2 × Fin dimension),
        ∃ clauseFormulas : (Fin 3 → Bool) → L.Formula (Fin 3 × Fin dimension),
          IsBooleanGadgetFamily subalgebra quotient domainFormula equalityFormula clauseFormulas := by
  classical
  obtain ⟨domainFormula, domainPositive, domainCorrect⟩ := subalgebra_ppDefinable subalgebra
  obtain ⟨equalityFormula, equalityPositive, equalityCorrect⟩ :=
    liftedRelation_ppDefinable subalgebra projections quotient {values : Fin 2 → Bool | values 0 = values 1}
  have clauseDefinitions (pattern : Fin 3 → Bool) :=
    liftedRelation_ppDefinable subalgebra projections quotient {values | values ≠ pattern}
  choose clauseFormulas clausePositive clauseCorrect using clauseDefinitions
  exact ⟨domainFormula, equalityFormula, clauseFormulas, domainPositive, equalityPositive,
    clausePositive, domainCorrect, equalityCorrect, clauseCorrect⟩

end Construction

section Template

/-- A finite rigid core without a Taylor polymorphism admits a fixed family
of ten Boolean pp gadgets and representatives for both Boolean values. The
block dimension is `|Carrier|²`; all data is fixed before any input formula.
No finite-signature or additional inhabitance hypothesis is required here. -/
theorem exists_boolean_gadgets_of_noTaylorPolymorphism [Finite Carrier]
    (rigid : IsRigidCore L Carrier) (noTaylor : ¬ HasTaylorPolymorphism L Carrier) :
    ∃ choices : ∀ arity, (polymorphismLanguage L Carrier).Functions arity → Fin arity,
      let _ : (polymorphismLanguage L Carrier).Structure Bool := projectionStructure choices Bool
      ∃ subalgebra : (polymorphismLanguage L Carrier).Substructure (Fin (Nat.card Carrier ^ 2) → Carrier),
        ∃ quotient : subalgebra →[polymorphismLanguage L Carrier] Bool,
          Function.Surjective quotient ∧
          ∃ representatives : Bool → subalgebra, Function.RightInverse representatives quotient ∧
            ∃ domainFormula : L.Formula (Fin (Nat.card Carrier ^ 2)),
              ∃ equalityFormula : L.Formula (Fin 2 × Fin (Nat.card Carrier ^ 2)),
                ∃ clauseFormulas : (Fin 3 → Bool) → L.Formula (Fin 3 × Fin (Nat.card Carrier ^ 2)),
                  IsBooleanGadgetFamily subalgebra quotient domainFormula equalityFormula clauseFormulas := by
  classical
  obtain ⟨choices, witness⟩ := exists_finite_projection_witness_of_noTaylorPolymorphism rigid noTaylor
  let _ : (polymorphismLanguage L Carrier).Structure Bool := projectionStructure choices Bool
  dsimp only at witness
  obtain ⟨subalgebra, quotient, surjective⟩ := witness
  obtain ⟨domainFormula, equalityFormula, clauseFormulas, family⟩ :=
    exists_boolean_gadget_family subalgebra
      (fun arity symbol => ⟨choices arity symbol, fun _ => rfl⟩) quotient
  refine ⟨choices, ?_⟩
  dsimp only
  exact ⟨subalgebra, quotient, surjective, Function.surjInv surjective,
    Function.rightInverse_surjInv surjective, domainFormula, equalityFormula, clauseFormulas, family⟩

end Template

end Polytime2.CSP
