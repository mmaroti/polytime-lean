import Mathlib.ModelTheory.Basic

/-! # Mathematical contract for fixed-template CSP hardness

The target theorem is the following, to be formalized after the complexity
interface exists. Fix a relational language `L` with
`Finite (Σ arity, L.Relations arity)` and a nonempty finite carrier `Carrier`
with an `L.Structure`. If `IsRigidCore L Carrier` and
`¬ HasTaylorPolymorphism L Carrier`, then the language of finite structures
admitting a homomorphism to `Carrier` is NP-complete under polynomial-time
many-one reductions. The reduction and its polynomial may depend on the fixed
template, but must work for all input structures. This module does not assert
NP-completeness or postulate a complexity predicate.

Instances have carrier `Fin variableCount` and arbitrary interpretations of the
same relation symbols. A solution is a Mathlib structure homomorphism. Relations
have arbitrary fixed natural-number arities, including zero, with no symmetry
or reflexivity assumptions. A nullary relation is a truth value: an instance
asserting a nullary symbol false in the template is unsatisfiable, even with no
variables. An empty instance has its unique empty assignment precisely when
all its asserted nullary relations hold in the template.

The future encoding uses the dense tables specified in `EXAMPLES.md`, including
one bit per nullary symbol (`variableCount ^ 0 = 1`). Total relation-symbol
finiteness, not merely finiteness at each arity, gives a fixed maximum arity.
The serialized input includes unary variable-count headers; complexity is
measured in the full serialized input length. No encoding or machine is needed
for the mathematical predicates below.

The rigid-core hypothesis means every endomorphism is the identity; adding all
singleton unary relations suffices. Reflexivity instead gives constant
solutions, as `constantHom_of_reflexive` shows. The implementation target uses
rigidity in place of the originally requested reflexivity.

Mathematical source: Zarathustra Brady, *Notes on CSPs and Polymorphisms*,
sections 1.4 (cores and idempotent reducts) and 1.5 (Taylor algebras), especially
Theorem 1.5.2 and Corollary 1.5.7. See `Polytime2/tasks/csp-taylor-hardness.md`
for the TeX source and remaining proof obligations.
-/

namespace Polytime2.CSP

open FirstOrder FirstOrder.Language

universe languageLevel carrierLevel instanceLevel

/-- A Taylor operation has positive arity, is idempotent, and satisfies a
two-variable identity for each coordinate whose two patterns differ there.
The Boolean patterns select mathematical variables, not encoded storage. -/
def IsTaylorOperation {Carrier : Type carrierLevel} {arity : ℕ}
    (operation : (Fin arity → Carrier) → Carrier) : Prop :=
  0 < arity ∧
    (∀ value, operation (fun _ => value) = value) ∧
    ∀ coordinate : Fin arity, ∃ left right : Fin arity → Bool,
      left coordinate ≠ right coordinate ∧
      ∀ first second : Carrier,
        operation (fun index => if left index then first else second) =
          operation (fun index => if right index then first else second)

/-- Coordinatewise preservation of every template relation. Relation arities
include zero. Operation arity is unrestricted here; Taylor operations below
are required to have positive arity. -/
def IsPolymorphism (L : Language.{languageLevel, languageLevel})
    [L.IsRelational] (Carrier : Type carrierLevel) [L.Structure Carrier] {arity : ℕ}
    (operation : (Fin arity → Carrier) → Carrier) : Prop :=
  ∀ (relationArity : ℕ) (symbol : L.Relations relationArity)
    (tuples : Fin arity → Fin relationArity → Carrier),
    (∀ index, Structure.RelMap symbol (tuples index)) →
      Structure.RelMap symbol (fun coordinate => operation (fun index => tuples index coordinate))

/-- The template has a positive-arity Taylor operation preserving all its
relations. Finiteness and rigidity are separate hypotheses of the target
hardness theorem, not part of the meaning of a Taylor polymorphism. -/
def HasTaylorPolymorphism (L : Language.{languageLevel, languageLevel})
    [L.IsRelational] (Carrier : Type carrierLevel) [L.Structure Carrier] : Prop :=
  ∃ arity : ℕ, ∃ operation : (Fin arity → Carrier) → Carrier,
    IsTaylorOperation operation ∧ IsPolymorphism L Carrier operation

/-- A coordinate projection on a nontrivial carrier cannot satisfy the Taylor
identity for that coordinate. This is the obstruction used by the algebraic
hardness argument. -/
theorem not_isTaylorOperation_projection
    {Carrier : Type carrierLevel} [Nontrivial Carrier] {arity : ℕ}
    (coordinate : Fin arity) :
    ¬ IsTaylorOperation (fun tuple : Fin arity → Carrier => tuple coordinate) := by
  rintro ⟨_, _, identities⟩
  obtain ⟨left, right, different, identity⟩ := identities coordinate
  obtain ⟨first, second, distinct⟩ := exists_pair_ne Carrier
  have equality := identity first second
  cases leftValue : left coordinate <;> cases rightValue : right coordinate <;>
    simp_all

/-- A rigid core has only the identity endomorphism. Merely requiring all
endomorphisms to be automorphisms would specify a core, not a rigid core. -/
def IsRigidCore (L : Language.{languageLevel, languageLevel})
    (Carrier : Type carrierLevel) [L.Structure Carrier] : Prop :=
  ∀ endomorphism : Carrier →[L] Carrier, ∀ value, endomorphism value = value

/-- Named singleton unary relations force every endomorphism to be the
identity. The relation symbols may depend on the element being named. -/
theorem isRigidCore_of_singletonRelations
    {L : Language.{languageLevel, languageLevel}}
    {Carrier : Type carrierLevel} [L.Structure Carrier]
    (singletons : ∀ value : Carrier, ∃ symbol : L.Relations 1,
      ∀ tuple : Fin 1 → Carrier, Structure.RelMap symbol tuple ↔ tuple 0 = value) :
    IsRigidCore L Carrier := by
  intro endomorphism value
  obtain ⟨symbol, singleton⟩ := singletons value
  exact (singleton _).mp (endomorphism.map_rel symbol (fun _ => value)
    ((singleton _).mpr rfl))

/-- If all constant tuples satisfy every template relation, every instance
admits a constant homomorphism. For nullary symbols this hypothesis requires
truth in the template as well. No finiteness or instance reflexivity is needed. -/
def constantHom_of_reflexive
    {L : Language.{languageLevel, languageLevel}} [L.IsRelational]
    {Carrier : Type carrierLevel} [L.Structure Carrier]
    (reflexive : ∀ (arity : ℕ) (symbol : L.Relations arity) (value : Carrier),
      Structure.RelMap symbol (fun _ => value))
    (value : Carrier) (Instance : Type instanceLevel) [L.Structure Instance] :
    Instance →[L] Carrier where
  toFun := fun _ => value
  map_fun' symbol := isEmptyElim symbol
  map_rel' symbol _ _ := reflexive _ symbol value

end Polytime2.CSP
