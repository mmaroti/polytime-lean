import Polytime2.CSP.InvPol
import Polytime2.CSP.Instance
import Mathlib.SetTheory.Cardinal.NatCard

/-! # Finite relational gadgets for invariant relations

Brady, *Notes on CSPs and Polymorphisms*, section 1.1, the operation-table
construction in the finite Inv–Pol proof. The gadget is the relational power
indexed by all tuples of the relation. Its boundary columns need not be
distinct: repeated columns express equality by identifying variables.

This is a mathematical construction. Fixed-template gadgets may be large;
no algorithm, encoding, or runtime certificate is asserted here.
-/

namespace Polytime2.CSP

open FirstOrder FirstOrder.Language

universe languageLevel carrierLevel variableLevel

variable {L : Language.{languageLevel, languageLevel}} [L.IsRelational]
variable {Carrier : Type carrierLevel} [L.Structure Carrier] [Finite Carrier]
variable {Variables : Type variableLevel} [Finite Variables]

/-- The variables of the canonical relational-power gadget. -/
abbrev CanonicalGadget (relation : Set (Variables → Carrier)) :=
  Fin (Nat.card relation) → Carrier

/-- The column corresponding to a free variable, after enumerating the rows
of the relation. Boundary variables can coincide. -/
noncomputable def canonicalBoundary (relation : Set (Variables → Carrier))
    (coordinate : Variables) : CanonicalGadget relation :=
  fun index => ((Finite.equivFin relation).symm index).val coordinate

/-- An assignment extends to a homomorphism from the canonical gadget exactly
when it belongs to the invariant relation. This includes the empty relation. -/
theorem canonicalGadget_extends_iff (relation : Set (Variables → Carrier))
    (invariant : IsPolymorphismInvariant L relation) (values : Variables → Carrier) :
    (∃ homomorphism : CanonicalGadget relation →[L] Carrier,
      ∀ coordinate, homomorphism (canonicalBoundary relation coordinate) = values coordinate) ↔
      values ∈ relation := by
  classical
  constructor
  · rintro ⟨homomorphism, agrees⟩
    have member := invariant (Nat.card relation) homomorphism
      (Polymorphism.isPolymorphism homomorphism)
      (fun index => ((Finite.equivFin relation).symm index).val)
      (fun index => ((Finite.equivFin relation).symm index).property)
    have equal : (fun coordinate => homomorphism (canonicalBoundary relation coordinate)) = values :=
      funext agrees
    exact equal ▸ member
  · intro member
    let index := (Finite.equivFin relation) ⟨values, member⟩
    refine ⟨powerProjection (L := L) index, ?_⟩
    intro coordinate
    change ((Finite.equivFin relation).symm ((Finite.equivFin relation) ⟨values, member⟩)).val coordinate = _
    rw [Equiv.symm_apply_apply]

/-- In particular, every pp definition has a finite relational gadget with
the same boundary-assignment contract, without normalizing formula syntax. -/
theorem IsPPDefinable.canonicalGadget_extends_iff {relation : Set (Variables → Carrier)}
    (definable : IsPPDefinable L relation) (values : Variables → Carrier) :
    (∃ homomorphism : CanonicalGadget relation →[L] Carrier,
      ∀ coordinate, homomorphism (canonicalBoundary relation coordinate) = values coordinate) ↔
      values ∈ relation :=
  CSP.canonicalGadget_extends_iff relation definable.invariant values

end Polytime2.CSP
