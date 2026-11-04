import Polytime2.CSP.TaylorCriterion
import Mathlib.SetTheory.Cardinal.NatCard

/-! # The finite-power Birkhoff construction

Brady, *Notes on CSPs and Polymorphisms*, section 1.3, Theorem 1.3.1.
If finite algebras `Carrier` and `Target` satisfy the identity implication from
the former to the latter, a subalgebra of a finite power of `Carrier` surjects
onto `Target`. The power has `|Carrier| ^ |Target|` coordinates. No finiteness
of the operation signature or inhabitance of either carrier is required.

The construction uses tables of term evaluations on all assignments. Equality
of tables is an identity in the source and hence in the target, so evaluation
at an enumeration of the target factors through the table subalgebra.
-/

namespace Polytime2.CSP

open FirstOrder FirstOrder.Language

universe functionLevel relationLevel carrierLevel targetLevel indexLevel

variable {L : Language.{functionLevel, relationLevel}}
variable {Carrier : Type carrierLevel} [L.Structure Carrier]
variable {Target : Type targetLevel} [L.Structure Target]

section TermTables

variable {arity : ℕ} {Index : Type indexLevel}

/-- A term's table on the supplied family of source assignments. -/
def termTable (samples : Index → Fin arity → Carrier) (term : L.Term (Fin arity)) :
    Index → Carrier := fun index => term.realize (samples index)

/-- The term tables form a Mathlib substructure of the coordinatewise power.
No signature enumeration is needed to prove closure under its operations. -/
def termTableSubstructure (samples : Index → Fin arity → Carrier) :
    L.Substructure (Index → Carrier) where
  carrier := Set.range (termTable samples)
  fun_mem symbol arguments related := by
    classical
    choose terms equal using related
    refine ⟨Term.func symbol terms, ?_⟩
    funext index
    change Structure.funMap symbol (fun position => (terms position).realize (samples index)) =
      Structure.funMap symbol (fun position => arguments position index)
    congr 1
    funext position
    exact congrFun (equal position) index

private noncomputable def representative (samples : Index → Fin arity → Carrier)
    (table : termTableSubstructure (L := L) samples) : L.Term (Fin arity) :=
  Classical.choose table.property

private theorem representative_correct (samples : Index → Fin arity → Carrier)
    (table : termTableSubstructure (L := L) samples) :
    termTable samples (representative samples table) = table.val :=
  Classical.choose_spec table.property

private theorem equal_evaluations_of_equal_tables
    (samples : Index → Fin arity → Carrier) (covers : Function.Surjective samples)
    (identities : ∀ identity : AlgebraIdentity L,
      SatisfiesIdentity Carrier identity → SatisfiesIdentity Target identity)
    {first second : L.Term (Fin arity)} (equal : termTable samples first = termTable samples second)
    (values : Fin arity → Target) : first.realize values = second.realize values := by
  apply identities ⟨arity, first, second⟩ _ values
  intro assignment
  obtain ⟨index, rfl⟩ := covers assignment
  exact congrFun equal index

variable [L.IsAlgebraic]

/-- Evaluation in an algebra satisfying the source identities factors through
the source term tables whenever the samples cover all source assignments. -/
noncomputable def termTableHom (samples : Index → Fin arity → Carrier)
    (covers : Function.Surjective samples)
    (identities : ∀ identity : AlgebraIdentity L,
      SatisfiesIdentity Carrier identity → SatisfiesIdentity Target identity)
    (values : Fin arity → Target) : termTableSubstructure (L := L) samples →[L] Target where
  toFun table := (representative samples table).realize values
  map_fun' symbol arguments := by
    change (representative samples (Structure.funMap symbol arguments)).realize values =
      (Term.func symbol (fun position => representative samples (arguments position))).realize values
    apply equal_evaluations_of_equal_tables samples covers identities
    exact (representative_correct samples (Structure.funMap symbol arguments)).trans (by
      funext index
      change Structure.funMap symbol (fun position => (arguments position).val index) =
        Structure.funMap symbol (fun position => (representative samples (arguments position)).realize (samples index))
      congr 1
      funext position
      exact (congrFun (representative_correct samples (arguments position)) index).symm)
  map_rel' symbol := isEmptyElim symbol

/-- The factored evaluation agrees with evaluation of every representative. -/
theorem termTableHom_apply (samples : Index → Fin arity → Carrier)
    (covers : Function.Surjective samples)
    (identities : ∀ identity : AlgebraIdentity L,
      SatisfiesIdentity Carrier identity → SatisfiesIdentity Target identity)
    (values : Fin arity → Target) (term : L.Term (Fin arity)) :
    termTableHom samples covers identities values ⟨termTable samples term, ⟨term, rfl⟩⟩ =
      term.realize values :=
  equal_evaluations_of_equal_tables samples covers identities
    (representative_correct samples ⟨termTable samples term, ⟨term, rfl⟩⟩) values

theorem termTableHom_surjective (samples : Index → Fin arity → Carrier)
    (covers : Function.Surjective samples)
    (identities : ∀ identity : AlgebraIdentity L,
      SatisfiesIdentity Carrier identity → SatisfiesIdentity Target identity)
    (values : Fin arity → Target) (generates : Function.Surjective values) :
    Function.Surjective (termTableHom samples covers identities values) := by
  intro value
  obtain ⟨coordinate, rfl⟩ := generates value
  exact ⟨⟨termTable samples (Term.var coordinate), ⟨Term.var coordinate, rfl⟩⟩,
    termTableHom_apply samples covers identities values (Term.var coordinate)⟩

end TermTables

section FinitePower

variable [L.IsAlgebraic]

/-- The finite single-source Birkhoff theorem. The witness is an actual
Mathlib substructure and a surjective Mathlib homomorphism, not an abstract
membership assertion about a class of algebras. The dimension is independent
of the size of the signature, which may be infinite. -/
theorem exists_finite_power_surjective_hom [Finite Carrier] [Finite Target]
    (identities : ∀ identity : AlgebraIdentity L,
      SatisfiesIdentity Carrier identity → SatisfiesIdentity Target identity) :
    ∃ subalgebra : L.Substructure (Fin (Nat.card Carrier ^ Nat.card Target) → Carrier),
      ∃ homomorphism : subalgebra →[L] Target, Function.Surjective homomorphism := by
  classical
  let _ := Fintype.ofFinite Carrier
  let _ := Fintype.ofFinite Target
  let arity := Nat.card Target
  have assignmentsCard : Nat.card (Fin arity → Carrier) = Nat.card Carrier ^ Nat.card Target := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, arity]
  let enumeration : Fin arity → Target := (Finite.equivFin Target).symm
  let samples : Fin (Nat.card Carrier ^ Nat.card Target) → Fin arity → Carrier :=
    (Finite.equivFinOfCardEq assignmentsCard).symm
  have covers : Function.Surjective samples := (Finite.equivFinOfCardEq assignmentsCard).symm.surjective
  refine ⟨termTableSubstructure samples, termTableHom samples covers identities enumeration, ?_⟩
  exact termTableHom_surjective samples covers identities enumeration (Finite.equivFin Target).symm.surjective

end FinitePower

end Polytime2.CSP
