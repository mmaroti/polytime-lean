import Polytime2.CSP.FiniteBirkhoff

/-! # A finite projection witness for Taylor hardness

Brady, *Notes on CSPs and Polymorphisms*, Theorem 1.3.1 (finite Birkhoff) and
Theorem 1.5.2 (Taylor's criterion). The full polymorphism algebra of a finite
rigid core without a Taylor polymorphism has a two-element projection algebra
as a homomorphic image of a subalgebra of a finite power. Its operation
signature may be infinite.

The choices here depend only on the fixed template. These are mathematical
existence proofs, with no instance-dependent computation or cost claims.
-/

namespace Polytime2.CSP

open FirstOrder FirstOrder.Language

universe languageLevel carrierLevel

variable {L : Language.{languageLevel, languageLevel}} [L.IsRelational]
variable {Carrier : Type carrierLevel} [L.Structure Carrier] [Finite Carrier]

/-- The finite HSP witness needed for the hardness gadgets. Every operation on
`Bool` is a coordinate projection, and a subalgebra of the `|Carrier|²`-fold
power of the full polymorphism algebra surjects onto it. No finiteness of the
signature or additional nonemptiness hypothesis is needed. -/
theorem exists_finite_projection_witness_of_noTaylorPolymorphism
    (rigid : IsRigidCore L Carrier) (noTaylor : ¬ HasTaylorPolymorphism L Carrier) :
    ∃ choices : ∀ arity, (polymorphismLanguage L Carrier).Functions arity → Fin arity,
      let _ : (polymorphismLanguage L Carrier).Structure Bool := projectionStructure choices Bool
      ∃ subalgebra : (polymorphismLanguage L Carrier).Substructure
          (Fin (Nat.card Carrier ^ 2) → Carrier),
        ∃ homomorphism : subalgebra →[polymorphismLanguage L Carrier] Bool,
          Function.Surjective homomorphism := by
  obtain ⟨choices, identities⟩ := hasProjectionModel_of_noTaylorPolymorphism rigid noTaylor
  refine ⟨choices, ?_⟩
  let _ : (polymorphismLanguage L Carrier).Structure Bool := projectionStructure choices Bool
  dsimp only
  have boolCard : Nat.card Bool = 2 := by simp [Nat.card_eq_fintype_card]
  have witness := exists_finite_power_surjective_hom identities
  rw [boolCard] at witness
  exact witness

end Polytime2.CSP
