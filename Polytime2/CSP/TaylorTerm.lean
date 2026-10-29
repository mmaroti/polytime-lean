import Polytime2.CSP.Polymorphism
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Idempotent terms and star composition

Mathematical provenance: Brady, *Notes on CSPs and Polymorphisms*, section 1.5,
Taylor's theorem and the star-composition construction in its proof. All
operations and terms use Mathlib's first-order structures and syntax.
-/

namespace Polytime2.CSP

open FirstOrder FirstOrder.Language

universe functionLevel relationLevel carrierLevel variableLevel

variable {L : Language.{functionLevel, relationLevel}}
variable {Carrier : Type carrierLevel} [L.Structure Carrier]

/-- Every basic operation fixes constant tuples, including nullary operations
if the carrier permits them. No finiteness assumption is imposed. -/
def IsIdempotentAlgebra (L : Language.{functionLevel, relationLevel})
    (Carrier : Type carrierLevel) [L.Structure Carrier] : Prop :=
  ∀ arity (symbol : L.Functions arity) (value : Carrier),
    Structure.funMap symbol (fun _ => value) = value

/-- A Taylor term, with the positive-arity convention of `IsTaylorOperation`. -/
def HasTaylorTerm (L : Language.{functionLevel, relationLevel})
    (Carrier : Type carrierLevel) [L.Structure Carrier] : Prop :=
  ∃ arity, ∃ term : L.Term (Fin arity),
    IsTaylorOperation (fun values : Fin arity → Carrier => term.realize values)

theorem hasTaylorTerm_of_subsingleton [Subsingleton Carrier] : HasTaylorTerm L Carrier := by
  refine ⟨1, Term.var 0, by decide, (fun _ => rfl), ?_⟩
  intro coordinate
  exact ⟨fun _ => true, fun _ => false, by change true ≠ false; decide,
    fun _ _ => Subsingleton.elim _ _⟩

theorem nontrivial_of_not_hasTaylorTerm (noTaylor : ¬ HasTaylorTerm L Carrier) : Nontrivial Carrier := by
  classical
  rcases subsingleton_or_nontrivial Carrier with subsingleton | nontrivial
  · let _ := subsingleton
    exact (noTaylor hasTaylorTerm_of_subsingleton).elim
  · exact nontrivial

/-- Nullary operations in an idempotent algebra force its carrier to have at
most one element. They therefore cannot occur in the non-Taylor case. -/
theorem IsIdempotentAlgebra.isEmpty_constants [Nontrivial Carrier]
    (idempotent : IsIdempotentAlgebra L Carrier) : IsEmpty (L.Functions 0) := by
  refine ⟨fun symbol => ?_⟩
  obtain ⟨first, second, different⟩ := exists_pair_ne Carrier
  have firstEqual := idempotent 0 symbol first
  have secondEqual := idempotent 0 symbol second
  rw [Subsingleton.elim (fun _ : Fin 0 => first) (fun _ : Fin 0 => second)] at firstEqual
  exact different (firstEqual.symm.trans secondEqual)

theorem IsIdempotentAlgebra.term_realize_const (idempotent : IsIdempotentAlgebra L Carrier)
    {Variables : Type variableLevel} (term : L.Term Variables) (value : Carrier) :
    term.realize (fun _ => value) = value := by
  induction term with
  | var coordinate => rfl
  | func symbol arguments hypothesis =>
    change Structure.funMap symbol (fun index => (arguments index).realize (fun _ => value)) = value
    simpa only [hypothesis] using idempotent _ symbol value

/-- A coordinate that is consistent with all binary identities of an
operation. A non-Taylor idempotent operation of positive arity has one. -/
def RespectsBinaryIdentities {arity : ℕ} (operation : (Fin arity → Carrier) → Carrier)
    (coordinate : Fin arity) : Prop :=
  ∀ left right : Fin arity → Bool,
    (∀ first second : Carrier,
      operation (fun index => if left index then first else second) =
        operation (fun index => if right index then first else second)) →
      left coordinate = right coordinate

theorem exists_coordinate_of_not_hasTaylorTerm
    (idempotent : IsIdempotentAlgebra L Carrier) (noTaylor : ¬ HasTaylorTerm L Carrier)
    {arity : ℕ} (positive : 0 < arity) (term : L.Term (Fin arity)) :
    ∃ coordinate, RespectsBinaryIdentities (fun values : Fin arity → Carrier => term.realize values) coordinate := by
  classical
  by_contra noCoordinate
  apply noTaylor
  refine ⟨arity, term, positive, idempotent.term_realize_const term, ?_⟩
  intro coordinate
  have fails : ¬ RespectsBinaryIdentities
      (fun values : Fin arity → Carrier => term.realize values) coordinate :=
    fun respects => noCoordinate ⟨coordinate, respects⟩
  simp only [RespectsBinaryIdentities, not_forall] at fails
  obtain ⟨left, right, equal, different⟩ := fails
  exact ⟨left, right, different, equal⟩

/-- Substitute one copy of `inner` into every variable of `outer`, using the
ordinary product of their coordinate sets, numbered by Mathlib's equivalence. -/
def starTerm {outerArity innerArity : ℕ}
    (outer : L.Term (Fin outerArity)) (inner : L.Term (Fin innerArity)) :
    L.Term (Fin (outerArity * innerArity)) :=
  outer.subst (fun first => inner.relabel (fun second => finProdFinEquiv (first, second)))

theorem starTerm_realize {outerArity innerArity : ℕ}
    (outer : L.Term (Fin outerArity)) (inner : L.Term (Fin innerArity))
    (values : Fin (outerArity * innerArity) → Carrier) :
    (starTerm outer inner).realize values =
      outer.realize (fun first => inner.realize (fun second => values (finProdFinEquiv (first, second)))) := by
  simp only [starTerm, Term.realize_subst, Term.realize_relabel, Function.comp_def]

theorem starTerm_minor_left (idempotent : IsIdempotentAlgebra L Carrier)
    {outerArity innerArity : ℕ} (outer : L.Term (Fin outerArity)) (inner : L.Term (Fin innerArity))
    (values : Fin outerArity → Carrier) :
    (starTerm outer inner).realize (fun index => values (finProdFinEquiv.symm index).1) =
      outer.realize values := by
  simp only [starTerm_realize, Equiv.symm_apply_apply, idempotent.term_realize_const]

theorem starTerm_minor_right (idempotent : IsIdempotentAlgebra L Carrier)
    {outerArity innerArity : ℕ} (outer : L.Term (Fin outerArity)) (inner : L.Term (Fin innerArity))
    (values : Fin innerArity → Carrier) :
    (starTerm outer inner).realize (fun index => values (finProdFinEquiv.symm index).2) =
      inner.realize values := by
  simp only [starTerm_realize, Equiv.symm_apply_apply, idempotent.term_realize_const]

/-- Finitely many positive-arity terms are all minors of one positive-arity
term in an idempotent algebra. This is the finite common-star construction. -/
theorem IsIdempotentAlgebra.exists_common_term
    (idempotent : IsIdempotentAlgebra L Carrier)
    (terms : List (Σ arity : ℕ, L.Term (Fin (arity + 1)))) :
    ∃ arity, ∃ common : L.Term (Fin arity), 0 < arity ∧
      ∀ term ∈ terms, ∃ coordinates : Fin arity → Fin (term.1 + 1),
        ∀ values : Fin (term.1 + 1) → Carrier,
          common.realize (values ∘ coordinates) = term.2.realize values := by
  induction terms with
  | nil => exact ⟨1, .var 0, by decide, by simp⟩
  | cons head tail hypothesis =>
    obtain ⟨arity, common, positive, realizes⟩ := hypothesis
    refine ⟨(head.1 + 1) * arity, starTerm head.2 common, Nat.mul_pos (Nat.zero_lt_succ _) positive, ?_⟩
    intro term member
    rcases List.mem_cons.mp member with equal | member
    · subst term
      exact ⟨fun index => (finProdFinEquiv.symm index).1, starTerm_minor_left idempotent head.2 common⟩
    · obtain ⟨coordinates, correct⟩ := realizes term member
      refine ⟨fun index => coordinates (finProdFinEquiv.symm index).2, ?_⟩
      intro values
      exact (starTerm_minor_right idempotent head.2 common (values ∘ coordinates)).trans (correct values)

end Polytime2.CSP
