import Polytime2.CSP.Basic
import Mathlib.ModelTheory.Substructures
import Mathlib.ModelTheory.Semantics

/-! # Polymorphisms, powers, and the full polymorphism algebra

Powers have coordinatewise functions and relations. A polymorphism is a
Mathlib homomorphism from a finite power to the template; the equivalence
with `IsPolymorphism` includes zero operation arity and nullary relations.
The algebra has one function symbol for every such polymorphism, with no
assumption that this signature is finite. Its terms give exactly the
polymorphisms. Rigidity makes all these operations idempotent.

Mathematical provenance: Brady, *Notes on CSPs and Polymorphisms*, sections
1.1 (clones and preservation) and 1.4 (cores and idempotent reducts).
-/

namespace Polytime2.CSP

open FirstOrder FirstOrder.Language

universe functionLevel relationLevel languageLevel carrierLevel indexLevel sourceLevel

section Powers

variable {L : Language.{functionLevel, relationLevel}}
variable {Carrier : Type carrierLevel} [L.Structure Carrier]

/-- The ordinary power, including the empty product. A relation holds exactly
when it holds in every coordinate. Empty powers satisfy every relation, even
nullary ones. -/
instance powerStructure (Index : Type indexLevel) : L.Structure (Index → Carrier) where
  funMap symbol arguments index := Structure.funMap symbol (fun argument => arguments argument index)
  RelMap symbol arguments := ∀ index, Structure.RelMap symbol (fun argument => arguments argument index)

/-- A coordinate projection is a structure homomorphism. -/
def powerProjection {Index : Type indexLevel} (index : Index) : (Index → Carrier) →[L] Carrier where
  toFun values := values index
  map_fun' _ _ := rfl
  map_rel' _ _ related := related index

/-- The diagonal map preserves every function and relation. -/
def diagonalHom (Index : Type indexLevel) : Carrier →[L] (Index → Carrier) where
  toFun value _ := value
  map_fun' _ _ := rfl
  map_rel' _ _ related _ := related

/-- Bundle homomorphisms with a common source into the ordinary power. -/
def homTuple {Index : Type indexLevel} {Source : Type sourceLevel} [L.Structure Source]
    (family : Index → Source →[L] Carrier) : Source →[L] (Index → Carrier) where
  toFun value index := family index value
  map_fun' symbol arguments := by funext index; exact (family index).map_fun symbol arguments
  map_rel' symbol arguments related index := (family index).map_rel symbol arguments related

end Powers

section Relational

variable {L : Language.{languageLevel, languageLevel}} [L.IsRelational]
variable {Carrier : Type carrierLevel} [L.Structure Carrier]

/-- A polymorphism of operation arity `arity` is a homomorphism from the
coordinatewise relational power to the template. -/
abbrev Polymorphism (L : Language.{languageLevel, languageLevel}) [L.IsRelational]
    (Carrier : Type carrierLevel) [L.Structure Carrier] (arity : ℕ) :=
  (Fin arity → Carrier) →[L] Carrier

namespace Polymorphism

/-- Turn relation preservation into a Mathlib homomorphism. -/
def ofOperation {arity : ℕ} (operation : (Fin arity → Carrier) → Carrier)
    (preserves : IsPolymorphism L Carrier operation) : Polymorphism L Carrier arity where
  toFun := operation
  map_fun' symbol := isEmptyElim symbol
  map_rel' symbol arguments related := preserves _ symbol (fun index coordinate => arguments coordinate index) related

/-- The homomorphism and relation-preservation presentations agree. -/
theorem isPolymorphism {arity : ℕ} (operation : Polymorphism L Carrier arity) :
    IsPolymorphism L Carrier operation := by
  intro relationArity symbol tuples related
  exact operation.map_rel symbol (fun coordinate index => tuples index coordinate) related

end Polymorphism

theorem isPolymorphism_iff_exists_hom {arity : ℕ} (operation : (Fin arity → Carrier) → Carrier) :
    IsPolymorphism L Carrier operation ↔
      ∃ homomorphism : Polymorphism L Carrier arity, (homomorphism : (Fin arity → Carrier) → Carrier) = operation := by
  constructor
  · intro preserves; exact ⟨Polymorphism.ofOperation operation preserves, rfl⟩
  · rintro ⟨homomorphism, rfl⟩; exact homomorphism.isPolymorphism

theorem isPolymorphism_projection {arity : ℕ} (coordinate : Fin arity) :
    IsPolymorphism L Carrier (fun values : Fin arity → Carrier => values coordinate) :=
  Polymorphism.isPolymorphism (powerProjection (L := L) (Carrier := Carrier) coordinate)

/-- Closure under simultaneous composition, with arbitrary inner and outer
arities. This also covers empty families and nullary relations. -/
theorem IsPolymorphism.comp {outerArity innerArity : ℕ}
    {outer : (Fin outerArity → Carrier) → Carrier}
    {inner : Fin outerArity → (Fin innerArity → Carrier) → Carrier}
    (outerPreserves : IsPolymorphism L Carrier outer)
    (innerPreserves : ∀ index, IsPolymorphism L Carrier (inner index)) :
    IsPolymorphism L Carrier (fun values => outer (fun index => inner index values)) :=
  Polymorphism.isPolymorphism ((Polymorphism.ofOperation outer outerPreserves).comp
    (homTuple (fun index => Polymorphism.ofOperation (inner index) (innerPreserves index))))

/-- Diagonal composition is an endomorphism, so rigidity forces idempotence.
Neither finiteness nor an inhabited carrier nor positive arity is needed. -/
theorem IsPolymorphism.apply_const_of_rigidCore {arity : ℕ}
    {operation : (Fin arity → Carrier) → Carrier} (preserves : IsPolymorphism L Carrier operation)
    (rigid : IsRigidCore L Carrier) (value : Carrier) : operation (fun _ => value) = value :=
  rigid ((Polymorphism.ofOperation operation preserves).comp (diagonalHom (Fin arity))) value

/-- The full operation signature of the template, including nullary
polymorphisms when they exist. No new algebra or signature hierarchy is used. -/
def polymorphismLanguage (L : Language.{languageLevel, languageLevel}) [L.IsRelational]
    (Carrier : Type carrierLevel) [L.Structure Carrier] : Language.{carrierLevel, 0} where
  Functions := Polymorphism L Carrier
  Relations _ := Empty

instance polymorphismLanguage_isAlgebraic : (polymorphismLanguage L Carrier).IsAlgebraic :=
  fun _ => (inferInstance : IsEmpty Empty)

/-- Interpret every operation symbol by its underlying homomorphism. -/
instance polymorphismAlgebra : (polymorphismLanguage L Carrier).Structure Carrier where
  funMap {arity} operation arguments := (show Polymorphism L Carrier arity from operation) arguments
  RelMap symbol := Empty.elim (show Empty from symbol)

/-- Every basic operation in the full algebra is idempotent on a rigid core. -/
theorem polymorphismAlgebra_idempotent (rigid : IsRigidCore L Carrier) {arity : ℕ}
    (operation : (polymorphismLanguage L Carrier).Functions arity) (value : Carrier) :
    Structure.funMap operation (fun _ => value) = value :=
  operation.isPolymorphism.apply_const_of_rigidCore rigid value

/-- Each template relation is a Mathlib substructure of a power of the full
polymorphism algebra. This is the algebraic meaning of relation preservation. -/
def relationSubstructure {arity : ℕ} (symbol : L.Relations arity) :
    (polymorphismLanguage L Carrier).Substructure (Fin arity → Carrier) where
  carrier := {tuple | Structure.RelMap symbol tuple}
  fun_mem operation tuples related := operation.isPolymorphism _ symbol tuples related

/-- Closure of term operations follows from projections and simultaneous
composition, using Mathlib's terms and their realization. -/
theorem term_isPolymorphism {arity : ℕ}
    (term : (polymorphismLanguage L Carrier).Term (Fin arity)) :
    IsPolymorphism L Carrier (fun values => term.realize values) := by
  induction term with
  | var coordinate => exact isPolymorphism_projection coordinate
  | func operation terms hypothesis => exact operation.isPolymorphism.comp hypothesis

/-- Every polymorphism occurs as a basic term operation, and every term
operation preserves the original relations. -/
theorem isPolymorphism_iff_term {arity : ℕ} (operation : (Fin arity → Carrier) → Carrier) :
    IsPolymorphism L Carrier operation ↔
      ∃ term : (polymorphismLanguage L Carrier).Term (Fin arity),
        (fun values : Fin arity → Carrier => term.realize values) = operation := by
  constructor
  · intro preserves
    let symbol : (polymorphismLanguage L Carrier).Functions arity := Polymorphism.ofOperation operation preserves
    exact ⟨symbol.term, rfl⟩
  · rintro ⟨term, rfl⟩
    exact term_isPolymorphism term

theorem term_realize_const_of_rigidCore (rigid : IsRigidCore L Carrier) {arity : ℕ}
    (term : (polymorphismLanguage L Carrier).Term (Fin arity)) (value : Carrier) :
    term.realize (fun _ => value) = value :=
  (term_isPolymorphism term).apply_const_of_rigidCore rigid value

/-- Taylor polymorphisms are exactly Taylor term operations of the full
polymorphism algebra. This supplies the semantic interface for step 10. -/
theorem hasTaylorPolymorphism_iff_term : HasTaylorPolymorphism L Carrier ↔
    ∃ arity : ℕ, ∃ term : (polymorphismLanguage L Carrier).Term (Fin arity),
      IsTaylorOperation (fun values : Fin arity → Carrier => term.realize values) := by
  constructor
  · rintro ⟨arity, operation, taylor, preserves⟩
    obtain ⟨term, rfl⟩ := (isPolymorphism_iff_term operation).mp preserves
    exact ⟨arity, term, taylor⟩
  · rintro ⟨arity, term, taylor⟩
    exact ⟨arity, _, taylor, term_isPolymorphism term⟩

end Relational

end Polytime2.CSP
