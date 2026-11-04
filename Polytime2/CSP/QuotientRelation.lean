import Polytime2.CSP.InvPol
import Polytime2.CSP.ProjectionWitness

/-! # Relations lifted through a projection quotient

Brady, *Notes on CSPs and Polymorphisms*, sections 1.1 and 1.3: lift a relation
through a quotient of a subalgebra of a power, then apply finite Inv–Pol.
Blocks are ordinary tuples; representation is a mathematical relation, with
no storage, encoding, or algorithm conventions.
-/

namespace Polytime2.CSP

open FirstOrder FirstOrder.Language

universe languageLevel carrierLevel

variable {L : Language.{languageLevel, languageLevel}} [L.IsRelational]
variable {Carrier : Type carrierLevel} [L.Structure Carrier] {dimension : ℕ}

section Representation

/-- A block represents a Boolean if it is in the chosen subalgebra and its
quotient value is that Boolean. -/
def Represents (subalgebra : (polymorphismLanguage L Carrier).Substructure (Fin dimension → Carrier))
    (quotient : subalgebra → Bool) (block : Fin dimension → Carrier) (value : Bool) : Prop :=
  ∃ representative : subalgebra, representative.val = block ∧ quotient representative = value

variable {subalgebra : (polymorphismLanguage L Carrier).Substructure (Fin dimension → Carrier)}
variable {quotient : subalgebra → Bool}

theorem represents_subtype_iff (representative : subalgebra) (value : Bool) :
    Represents subalgebra quotient representative.val value ↔ quotient representative = value := by
  constructor
  · rintro ⟨other, equal, image⟩
    have same : other = representative := Subtype.ext equal
    exact same ▸ image
  · intro image
    exact ⟨representative, rfl, image⟩

theorem Represents.unique {block : Fin dimension → Carrier} {first second : Bool}
    (left : Represents subalgebra quotient block first)
    (right : Represents subalgebra quotient block second) : first = second := by
  obtain ⟨representative, rfl, image⟩ := left
  exact image.symm.trans ((represents_subtype_iff representative second).mp right)

theorem represents_some_iff (block : Fin dimension → Carrier) :
    (∃ value, Represents subalgebra quotient block value) ↔ block ∈ subalgebra := by
  constructor
  · rintro ⟨value, representative, equal, image⟩
    exact equal ▸ representative.property
  · intro member
    exact ⟨quotient ⟨block, member⟩, ⟨block, member⟩, rfl, rfl⟩

/-- Pull back a Boolean relation through the quotient, requiring every block
to belong to the subalgebra. The free variables are argument/coordinate pairs. -/
def liftedRelation (subalgebra : (polymorphismLanguage L Carrier).Substructure (Fin dimension → Carrier))
    (quotient : subalgebra → Bool) {arity : ℕ} (relation : Set (Fin arity → Bool)) :
    Set ((Fin arity × Fin dimension) → Carrier) :=
  {blocks | ∃ values : Fin arity → Bool,
    (∀ argument, Represents subalgebra quotient (fun coordinate => blocks (argument, coordinate)) (values argument)) ∧
      values ∈ relation}

/-- Once the represented values of the blocks are known, membership in a
lifted relation is exactly membership of those values in the Boolean relation. -/
theorem liftedRelation_iff_of_represents {arity : ℕ} (relation : Set (Fin arity → Bool))
    (blocks : (Fin arity × Fin dimension) → Carrier) (values : Fin arity → Bool)
    (represented : ∀ argument, Represents subalgebra quotient
      (fun coordinate => blocks (argument, coordinate)) (values argument)) :
    blocks ∈ liftedRelation subalgebra quotient relation ↔ values ∈ relation := by
  constructor
  · rintro ⟨other, otherRepresented, related⟩
    have equal : other = values := funext (fun argument =>
      (otherRepresented argument).unique (represented argument))
    exact equal ▸ related
  · intro related
    exact ⟨values, represented, related⟩

/-- On actual representatives, lifting has exactly the original relation's
semantics. Different representatives with the same quotient value agree. -/
theorem liftedRelation_on_representatives {arity : ℕ} (relation : Set (Fin arity → Bool))
    (representatives : Fin arity → subalgebra) :
    (fun position => (representatives position.1).val position.2) ∈ liftedRelation subalgebra quotient relation ↔
      (fun argument => quotient (representatives argument)) ∈ relation := by
  constructor
  · rintro ⟨values, represented, related⟩
    have equal : values = fun argument => quotient (representatives argument) := by
      funext argument
      exact ((represents_subtype_iff (representatives argument) (values argument)).mp (represented argument)).symm
    exact equal ▸ related
  · intro related
    exact ⟨fun argument => quotient (representatives argument),
      fun argument => ⟨representatives argument, rfl, rfl⟩, related⟩

/-- A section of the quotient realizes every Boolean tuple, with exactly the
prescribed lifted-relation behavior. -/
theorem liftedRelation_on_section (representatives : Bool → subalgebra)
    (sectionLaw : Function.RightInverse representatives quotient)
    {arity : ℕ} (relation : Set (Fin arity → Bool)) (values : Fin arity → Bool) :
    (fun position => (representatives (values position.1)).val position.2) ∈
        liftedRelation subalgebra quotient relation ↔ values ∈ relation := by
  rw [liftedRelation_on_representatives relation (fun argument => representatives (values argument))]
  have equal : (fun argument => quotient (representatives (values argument))) = values :=
    funext (fun argument => sectionLaw (values argument))
  rw [equal]

end Representation

section Preservation

variable (subalgebra : (polymorphismLanguage L Carrier).Substructure (Fin dimension → Carrier))

/-- The witness subalgebra is invariant under all template polymorphisms. -/
theorem subalgebra_polymorphismInvariant : IsPolymorphismInvariant L (subalgebra : Set (Fin dimension → Carrier)) := by
  intro arity operation preserves tuples related
  exact subalgebra.fun_mem (Polymorphism.ofOperation operation preserves) tuples related

theorem subalgebra_ppDefinable [Finite Carrier] :
    IsPPDefinable L (subalgebra : Set (Fin dimension → Carrier)) :=
  (subalgebra_polymorphismInvariant subalgebra).ppDefinable

variable [booleanStructure : (polymorphismLanguage L Carrier).Structure Bool]
variable (projections : ∀ arity (symbol : (polymorphismLanguage L Carrier).Functions arity),
  ∃ coordinate : Fin arity, ∀ values : Fin arity → Bool,
    Structure.funMap symbol values = values coordinate)
variable (quotient : subalgebra →[polymorphismLanguage L Carrier] Bool)

include projections in
/-- Every Boolean relation is invariant in a projection algebra. Its pullback
through a homomorphic image of a subalgebra of a power is therefore invariant
under the original template polymorphisms. Nullary arities are included. -/
theorem liftedRelation_polymorphismInvariant {relationArity : ℕ}
    (relation : Set (Fin relationArity → Bool)) :
    IsPolymorphismInvariant L (liftedRelation subalgebra quotient relation) := by
  classical
  intro arity operation preserves tuples related
  choose values represented relatedValues using related
  have representations (row : Fin arity) (argument : Fin relationArity) :
      ∃ representative : subalgebra,
        representative.val = (fun coordinate => tuples row (argument, coordinate)) ∧
          quotient representative = values row argument := represented row argument
  choose representatives sameBlock image using representations
  let symbol : (polymorphismLanguage L Carrier).Functions arity := Polymorphism.ofOperation operation preserves
  obtain ⟨coordinate, projectionLaw⟩ := projections arity symbol
  let combined (argument : Fin relationArity) : subalgebra :=
    Structure.funMap symbol (fun row => representatives row argument)
  refine ⟨fun argument => quotient (combined argument), ?_, ?_⟩
  · intro argument
    refine ⟨combined argument, ?_, rfl⟩
    funext coordinate
    change operation (fun row => (representatives row argument).val coordinate) =
      operation (fun row => tuples row (argument, coordinate))
    congr 1
    funext row
    exact congrFun (sameBlock row argument) coordinate
  · have selected : (fun argument => quotient (combined argument)) = values coordinate := by
      funext argument
      exact (quotient.map_fun symbol (fun row => representatives row argument)).trans
        ((projectionLaw (fun row => quotient (representatives row argument))).trans (image coordinate argument))
    exact selected ▸ relatedValues coordinate

include projections in
theorem liftedRelation_ppDefinable [Finite Carrier] {relationArity : ℕ}
    (relation : Set (Fin relationArity → Bool)) :
    IsPPDefinable L (liftedRelation subalgebra quotient relation) :=
  (liftedRelation_polymorphismInvariant subalgebra projections quotient relation).ppDefinable

end Preservation

end Polytime2.CSP
