import Polytime2.CSP.TaylorCoordinates

/-! # Taylor's algebraic criterion

Brady, *Notes on CSPs and Polymorphisms*, section 1.5, Theorem 1.5.2.
An idempotent algebra without a Taylor term admits a two-element projection
algebra satisfying all its identities. Terms, interpretations, and identity
satisfaction are mathematical; no algorithm or encoding is involved.
-/

namespace Polytime2.CSP

open FirstOrder FirstOrder.Language

universe functionLevel relationLevel carrierLevel variableLevel

variable {L : Language.{functionLevel, relationLevel}}
variable {Carrier : Type carrierLevel} [L.Structure Carrier]

section SelectedCoordinates

private def positiveNumbering {arity : ℕ} (positive : 0 < arity) :
    Fin arity ≃ Fin (arity - 1 + 1) :=
  finCongr (Nat.sub_add_cancel (Nat.succ_le_of_lt positive)).symm

private def numberedTerm {arity : ℕ} (positive : 0 < arity) (term : L.Term (Fin arity)) :
    PositiveTerm L := ⟨arity - 1, term.relabel (positiveNumbering positive)⟩

private def selectedCoordinate (coordinates : (term : PositiveTerm L) → Fin (term.1 + 1))
    {arity : ℕ} (positive : 0 < arity) (term : L.Term (Fin arity)) : Fin arity :=
  (positiveNumbering positive).symm (coordinates (numberedTerm positive term))

variable {coordinates : (term : PositiveTerm L) → Fin (term.1 + 1)}

private theorem selectedCoordinate_identity {Variables : Type variableLevel}
    (respects : RespectsMinorIdentities (Carrier := Carrier) coordinates)
    {firstArity secondArity : ℕ} (firstPositive : 0 < firstArity) (secondPositive : 0 < secondArity)
    (first : L.Term (Fin firstArity)) (second : L.Term (Fin secondArity))
    (left : Fin firstArity → Variables) (right : Fin secondArity → Variables)
    (holds : ∀ values : Variables → Carrier,
      first.realize (values ∘ left) = second.realize (values ∘ right)) :
    left (selectedCoordinate coordinates firstPositive first) =
      right (selectedCoordinate coordinates secondPositive second) := by
  apply respects.identity (numberedTerm firstPositive first) (numberedTerm secondPositive second)
    (left ∘ (positiveNumbering firstPositive).symm) (right ∘ (positiveNumbering secondPositive).symm)
  intro values
  simpa only [numberedTerm, Term.realize_relabel, Function.comp_def, Equiv.symm_apply_apply] using holds values

private theorem selectedCoordinate_minor
    (respects : RespectsMinorIdentities (Carrier := Carrier) coordinates)
    {firstArity secondArity : ℕ} (firstPositive : 0 < firstArity) (secondPositive : 0 < secondArity)
    (first : L.Term (Fin firstArity)) (second : L.Term (Fin secondArity))
    (rename : Fin firstArity → Fin secondArity)
    (holds : ∀ values : Fin secondArity → Carrier,
      first.realize (values ∘ rename) = second.realize values) :
    rename (selectedCoordinate coordinates firstPositive first) =
      selectedCoordinate coordinates secondPositive second :=
  selectedCoordinate_identity respects firstPositive secondPositive first second rename id holds

private theorem selectedCoordinate_variable
    (respects : RespectsMinorIdentities (Carrier := Carrier) coordinates)
    {arity : ℕ} (positive : 0 < arity) (coordinate : Fin arity) :
    selectedCoordinate coordinates positive (Term.var coordinate) = coordinate :=
  selectedCoordinate_identity respects positive (by decide) (Term.var coordinate) (Term.var (0 : Fin 1))
    id (fun _ => coordinate) (fun _ => rfl)

/-- Combining all inner terms by a common star term turns substitution into
minor identities. Thus consistent minor coordinates respect composition. -/
private theorem selectedCoordinate_subst
    (idempotent : IsIdempotentAlgebra L Carrier)
    (respects : RespectsMinorIdentities (Carrier := Carrier) coordinates)
    {outerArity innerArity : ℕ} (outer : L.Term (Fin (outerArity + 1)))
    (inner : Fin (outerArity + 1) → L.Term (Fin (innerArity + 1))) :
    selectedCoordinate coordinates (Nat.succ_pos _) (outer.subst inner) =
      selectedCoordinate coordinates (Nat.succ_pos _)
        (inner (selectedCoordinate coordinates (Nat.succ_pos _) outer)) := by
  classical
  obtain ⟨arity, common, positive, realizes⟩ := idempotent.exists_common_term
    (List.ofFn (fun index => (⟨innerArity, inner index⟩ : PositiveTerm L)))
  have innerMinor (index : Fin (outerArity + 1)) := realizes ⟨innerArity, inner index⟩
    (List.mem_ofFn.mpr ⟨index, rfl⟩)
  choose maps mapsCorrect using innerMinor
  let combined := starTerm outer common
  have combinedPositive : 0 < (outerArity + 1) * arity := Nat.mul_pos (Nat.succ_pos _) positive
  let chosen := selectedCoordinate coordinates combinedPositive combined
  let first := (finProdFinEquiv.symm chosen).1
  let second := (finProdFinEquiv.symm chosen).2
  have firstCorrect : first = selectedCoordinate coordinates (Nat.succ_pos _) outer :=
    selectedCoordinate_minor respects combinedPositive (Nat.succ_pos _) combined outer
      (fun index => (finProdFinEquiv.symm index).1) (starTerm_minor_left idempotent outer common)
  have innerCorrect (index : Fin (outerArity + 1)) :
      maps index second = selectedCoordinate coordinates (Nat.succ_pos _) (inner index) := by
    apply selectedCoordinate_minor respects combinedPositive (Nat.succ_pos _) combined (inner index)
      (fun position => maps index (finProdFinEquiv.symm position).2)
    intro values
    exact (starTerm_minor_right idempotent outer common (values ∘ maps index)).trans (mapsCorrect index values)
  have compositeCorrect : maps first second =
      selectedCoordinate coordinates (Nat.succ_pos _) (outer.subst inner) := by
    apply selectedCoordinate_minor respects combinedPositive (Nat.succ_pos _) combined (outer.subst inner)
      (fun position => maps (finProdFinEquiv.symm position).1 (finProdFinEquiv.symm position).2)
    intro values
    simp only [combined, starTerm_realize, Function.comp_def, Equiv.symm_apply_apply, Term.realize_subst]
    congr 1
    funext index
    convert mapsCorrect index values using 1
    congr 1
    funext second
    rw [Equiv.symm_apply_apply]
    rfl
  exact compositeCorrect.symm.trans ((innerCorrect first).trans (congrArg
    (fun index => selectedCoordinate coordinates (Nat.succ_pos _) (inner index)) firstCorrect))

end SelectedCoordinates

section ProjectionModels

variable [L.IsAlgebraic]

/-- Interpret each basic symbol as its chosen coordinate projection. -/
@[instance_reducible]
def projectionStructure (choices : ∀ arity, L.Functions arity → Fin arity)
    (Target : Type variableLevel) : L.Structure Target where
  funMap {arity} symbol values := values (choices arity symbol)
  RelMap symbol := isEmptyElim symbol

/-- An equation between two Mathlib terms in a finite common variable set. -/
abbrev AlgebraIdentity (L : Language.{functionLevel, relationLevel}) :=
  Σ arity : ℕ, L.Term (Fin arity) × L.Term (Fin arity)

/-- Satisfaction of an identity means equality under every assignment. -/
def SatisfiesIdentity (Carrier : Type carrierLevel) [L.Structure Carrier]
    (identity : AlgebraIdentity L) : Prop :=
  ∀ values : Fin identity.1 → Carrier, identity.2.1.realize values = identity.2.2.realize values

/-- A two-element projection algebra satisfying the whole equational theory
of the original algebra. The signature need not be finite. -/
def HasProjectionModel (L : Language.{functionLevel, relationLevel}) [L.IsAlgebraic]
    (Carrier : Type carrierLevel) [L.Structure Carrier] : Prop :=
  ∃ choices : ∀ arity, L.Functions arity → Fin arity,
    let _ : L.Structure Bool := projectionStructure choices Bool
    ∀ identity : AlgebraIdentity L, SatisfiesIdentity Carrier identity → SatisfiesIdentity Bool identity

private noncomputable def projectionChoices
    (coordinates : (term : PositiveTerm L) → Fin (term.1 + 1))
    (noConstants : IsEmpty (L.Functions 0)) : ∀ arity, L.Functions arity → Fin arity
  | 0, symbol => (noConstants.false symbol).elim
  | arity + 1, symbol => selectedCoordinate coordinates (Nat.succ_pos arity) symbol.term

private theorem projectionChoices_realize
    (idempotent : IsIdempotentAlgebra L Carrier)
    {coordinates : (term : PositiveTerm L) → Fin (term.1 + 1)}
    (respects : RespectsMinorIdentities (Carrier := Carrier) coordinates)
    (noConstants : IsEmpty (L.Functions 0)) {arity : ℕ} (term : L.Term (Fin (arity + 1)))
    (values : Fin (arity + 1) → Bool) :
    let _ : L.Structure Bool := projectionStructure (projectionChoices coordinates noConstants) Bool
    term.realize values = values (selectedCoordinate coordinates (Nat.succ_pos _) term) := by
  let _ : L.Structure Bool := projectionStructure (projectionChoices coordinates noConstants) Bool
  induction term with
  | var coordinate =>
    rw [selectedCoordinate_variable respects]
    rfl
  | @func count symbol arguments hypothesis =>
    cases count with
    | zero => exact (noConstants.false symbol).elim
    | succ count =>
      change (arguments (selectedCoordinate coordinates (Nat.succ_pos _) symbol.term)).realize values = _
      rw [hypothesis]
      congr 1
      exact (selectedCoordinate_subst idempotent respects symbol.term arguments).symm

omit [L.IsAlgebraic] in
private theorem isEmpty_terms_zero (noConstants : IsEmpty (L.Functions 0)) :
    IsEmpty (L.Term (Fin 0)) := by
  refine ⟨fun term => ?_⟩
  induction term with
  | var coordinate => exact coordinate.elim0
  | @func count symbol arguments hypothesis =>
    cases count with
    | zero => exact noConstants.false symbol
    | succ count => exact hypothesis 0

/-- Contrapositive form of Taylor's criterion: an idempotent non-Taylor
algebra has a projection model of all its identities, on the carrier `Bool`. -/
theorem hasProjectionModel_of_not_hasTaylorTerm
    (idempotent : IsIdempotentAlgebra L Carrier) (noTaylor : ¬ HasTaylorTerm L Carrier) :
    HasProjectionModel L Carrier := by
  classical
  let _ := nontrivial_of_not_hasTaylorTerm noTaylor
  have noConstants := idempotent.isEmpty_constants
  obtain ⟨coordinates, respects⟩ := exists_coordinates_of_not_hasTaylorTerm idempotent noTaylor
  refine ⟨projectionChoices coordinates noConstants, ?_⟩
  dsimp only
  intro identity holds
  obtain ⟨arity, first, second⟩ := identity
  cases arity with
  | zero => exact ((isEmpty_terms_zero noConstants).false first).elim
  | succ arity =>
    intro values
    rw [projectionChoices_realize idempotent respects noConstants,
      projectionChoices_realize idempotent respects noConstants]
    congr 1
    exact selectedCoordinate_identity respects (Nat.succ_pos _) (Nat.succ_pos _)
      first second id id holds

/-- An idempotent algebra whose identities cannot hold in a projection algebra
has a Taylor term. This allows arbitrary carriers and infinite signatures. -/
theorem hasTaylorTerm_of_not_hasProjectionModel
    (idempotent : IsIdempotentAlgebra L Carrier) (noProjection : ¬ HasProjectionModel L Carrier) :
    HasTaylorTerm L Carrier := by
  classical
  by_contra noTaylor
  exact noProjection (hasProjectionModel_of_not_hasTaylorTerm idempotent noTaylor)

/-- The criterion for an explicitly supplied set of identities: if all hold
in the idempotent algebra and no assignment of projections satisfies them all,
the algebra has a Taylor term. The identity set need not be finite. -/
theorem hasTaylorTerm_of_nontrivial_identities
    (idempotent : IsIdempotentAlgebra L Carrier) (identities : Set (AlgebraIdentity L))
    (valid : ∀ identity ∈ identities, SatisfiesIdentity Carrier identity)
    (noProjections : ∀ choices : ∀ arity, L.Functions arity → Fin arity,
      let _ : L.Structure Bool := projectionStructure choices Bool
      ∃ identity ∈ identities, ¬ SatisfiesIdentity Bool identity) : HasTaylorTerm L Carrier := by
  apply hasTaylorTerm_of_not_hasProjectionModel idempotent
  rintro ⟨choices, model⟩
  obtain ⟨identity, member, fails⟩ := noProjections choices
  exact fails (model identity (valid identity member))

end ProjectionModels

section PolymorphismAlgebra

variable {RelationalLanguage : Language.{functionLevel, functionLevel}} [RelationalLanguage.IsRelational]
variable [RelationalLanguage.Structure Carrier]

/-- The full polymorphism algebra of a rigid core is idempotent. -/
theorem polymorphismAlgebra_isIdempotent (rigid : IsRigidCore RelationalLanguage Carrier) :
    IsIdempotentAlgebra (polymorphismLanguage RelationalLanguage Carrier) Carrier :=
  fun _ operation value => polymorphismAlgebra_idempotent rigid operation value

/-- The projection-model conclusion needed for the subsequent finite HSP step.
It applies to the full, possibly infinite, polymorphism signature. -/
theorem hasProjectionModel_of_noTaylorPolymorphism
    (rigid : IsRigidCore RelationalLanguage Carrier)
    (noTaylor : ¬ HasTaylorPolymorphism RelationalLanguage Carrier) :
    HasProjectionModel (polymorphismLanguage RelationalLanguage Carrier) Carrier := by
  apply hasProjectionModel_of_not_hasTaylorTerm (polymorphismAlgebra_isIdempotent rigid)
  intro taylor
  exact noTaylor (hasTaylorPolymorphism_iff_term.mpr taylor)

end PolymorphismAlgebra

end Polytime2.CSP
