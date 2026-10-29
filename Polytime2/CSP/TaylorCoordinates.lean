import Polytime2.CSP.TaylorTerm
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions
import Mathlib.Topology.Separation.Hausdorff

/-! # Consistent projection coordinates

Brady, *Notes on CSPs and Polymorphisms*, section 1.5, Taylor's theorem.
For an idempotent algebra without a Taylor term, finite common-star terms
provide consistent projection coordinates for any finite collection of binary
minor identities. Compactness then supplies coordinates for all terms at once.
No finiteness of the carrier or operation signature is assumed.
-/

namespace Polytime2.CSP

open FirstOrder FirstOrder.Language

universe functionLevel relationLevel carrierLevel variableLevel

variable {L : Language.{functionLevel, relationLevel}}
variable {Carrier : Type carrierLevel} [L.Structure Carrier]

/-- A Mathlib term together with its positive number of variables. -/
abbrev PositiveTerm (L : Language.{functionLevel, relationLevel}) :=
  Σ arity : ℕ, L.Term (Fin (arity + 1))

/-- A choice of one coordinate per term respects binary minor identities when
equal binary specializations always select the same Boolean variable. -/
def RespectsMinorIdentities (coordinates : (term : PositiveTerm L) → Fin (term.1 + 1)) : Prop :=
  ∀ (first second : PositiveTerm L) (left : Fin (first.1 + 1) → Bool)
    (right : Fin (second.1 + 1) → Bool),
    (∀ firstValue secondValue : Carrier,
      first.2.realize (fun index => if left index then firstValue else secondValue) =
        second.2.realize (fun index => if right index then firstValue else secondValue)) →
      left (coordinates first) = right (coordinates second)

section Compactness

private abbrev BinaryMinor (L : Language.{functionLevel, relationLevel}) :=
  Σ first : PositiveTerm L, Σ second : PositiveTerm L,
    (Fin (first.1 + 1) → Bool) × (Fin (second.1 + 1) → Bool)

private def BinaryMinor.Holds (minor : BinaryMinor L) : Prop :=
  ∀ firstValue secondValue : Carrier,
    minor.1.2.realize (fun index => if minor.2.2.1 index then firstValue else secondValue) =
      minor.2.1.2.realize (fun index => if minor.2.2.2 index then firstValue else secondValue)

/-- The compactness step in Taylor's criterion. Each coordinate set is finite
and nonempty; the finite intersection property comes from common star terms. -/
theorem exists_coordinates_of_not_hasTaylorTerm
    (idempotent : IsIdempotentAlgebra L Carrier) (noTaylor : ¬ HasTaylorTerm L Carrier) :
    ∃ coordinates : (term : PositiveTerm L) → Fin (term.1 + 1),
      RespectsMinorIdentities (Carrier := Carrier) coordinates := by
  classical
  let ValidMinor := {minor : BinaryMinor L // minor.Holds (Carrier := Carrier)}
  let Choices := (term : PositiveTerm L) → Fin (term.1 + 1)
  let condition (minor : ValidMinor) : Set Choices :=
    {coordinates | minor.val.2.2.1 (coordinates minor.val.1) =
      minor.val.2.2.2 (coordinates minor.val.2.1)}
  let finTopology (arity : ℕ) : TopologicalSpace (Fin arity) := ⊥
  let finDiscrete (arity : ℕ) : DiscreteTopology (Fin arity) := ⟨rfl⟩
  let : TopologicalSpace Bool := ⊥
  let : DiscreteTopology Bool := ⟨rfl⟩
  have closed (minor : ValidMinor) : IsClosed (condition minor) := by
    apply isClosed_eq
    · exact continuous_of_discreteTopology.comp (continuous_apply minor.val.1)
    · exact continuous_of_discreteTopology.comp (continuous_apply minor.val.2.1)
  have finiteConsistency (constraints : Finset ValidMinor) :
      (⋂ minor ∈ constraints, condition minor).Nonempty := by
    let terms := constraints.toList.flatMap (fun minor => [minor.val.1, minor.val.2.1])
    obtain ⟨arity, common, positive, realizes⟩ := idempotent.exists_common_term terms
    obtain ⟨coordinate, good⟩ := exists_coordinate_of_not_hasTaylorTerm idempotent noTaylor positive common
    let coordinates (term : PositiveTerm L) : Fin (term.1 + 1) :=
      if member : term ∈ terms then (Classical.choose (realizes term member)) coordinate else 0
    refine ⟨coordinates, ?_⟩
    simp only [Set.mem_iInter]
    intro minor member
    have firstMember : minor.val.1 ∈ terms :=
      List.mem_flatMap.mpr ⟨minor, Finset.mem_toList.mpr member, by simp⟩
    have secondMember : minor.val.2.1 ∈ terms :=
      List.mem_flatMap.mpr ⟨minor, Finset.mem_toList.mpr member, by simp⟩
    change minor.val.2.2.1 (coordinates minor.val.1) = minor.val.2.2.2 (coordinates minor.val.2.1)
    dsimp only [coordinates]
    rw [dite_eq_left firstMember, dite_eq_left secondMember]
    apply good (minor.val.2.2.1 ∘ Classical.choose (realizes minor.val.1 firstMember))
      (minor.val.2.2.2 ∘ Classical.choose (realizes minor.val.2.1 secondMember))
    intro firstValue secondValue
    have firstCorrect := Classical.choose_spec (realizes minor.val.1 firstMember)
      (fun index => if minor.val.2.2.1 index then firstValue else secondValue)
    have secondCorrect := Classical.choose_spec (realizes minor.val.2.1 secondMember)
      (fun index => if minor.val.2.2.2 index then firstValue else secondValue)
    exact firstCorrect.trans ((minor.property firstValue secondValue).trans secondCorrect.symm)
  obtain ⟨coordinates, satisfies⟩ := CompactSpace.iInter_nonempty closed finiteConsistency
  refine ⟨coordinates, ?_⟩
  intro first second left right holds
  exact Set.mem_iInter.mp satisfies ⟨⟨first, second, left, right⟩, holds⟩

end Compactness

section Identities

variable {coordinates : (term : PositiveTerm L) → Fin (term.1 + 1)}

/-- Binary substitutions separate any two variable names, so respecting binary
minor identities also respects identities with arbitrary variable sets. -/
theorem RespectsMinorIdentities.identity {Variables : Type variableLevel}
    (respects : RespectsMinorIdentities (Carrier := Carrier) coordinates)
    (first second : PositiveTerm L) (left : Fin (first.1 + 1) → Variables)
    (right : Fin (second.1 + 1) → Variables)
    (holds : ∀ values : Variables → Carrier,
      first.2.realize (values ∘ left) = second.2.realize (values ∘ right)) :
    left (coordinates first) = right (coordinates second) := by
  classical
  by_contra different
  have chosen := respects first second
    (fun index => decide (left index = left (coordinates first)))
    (fun index => decide (right index = left (coordinates first))) (by
      intro firstValue secondValue
      simpa only [Bool.decide_iff, Function.comp_def] using
        holds (fun name => if name = left (coordinates first) then firstValue else secondValue))
  simp [Ne.symm different] at chosen

end Identities

end Polytime2.CSP
