import Polytime2.CSP.InstanceProgram
import Polytime2.CSP.QuotientScope
import Polytime2.CSP.QuotientInstanceMath

/-! # Canonically encoded dense quotient instances

Relation images are assembled from the certified scope operation. The caller
supplies the actual output class count as a mathematical size parameter;
computed-size preparation will supply that count from equation classes.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.CSP

open EncodedDomain Polytime2.Computation

variable (L : FirstOrder.Language.{0, 0}) [L.IsRelational] [Fintype (RelationSymbol L)]
variable {Parameter : Type} [Fintype Parameter]

noncomputable def quotientInstanceInputs (vertices classes : MvPolynomial Parameter ℕ) :
    Option Bool → EncodedDomain Parameter
  | none => (instanceDomain L).substitute (fun _ => vertices)
  | some false => (boundedIndex vertices).arrayOfLength vertices
  | some true => (boundedIndex vertices).arrayOfLength classes

omit [Fintype (RelationSymbol L)] in
/-- The canonical tables of mathematical relation images are precisely the
existential scope queries used by the compiler. -/
theorem instanceImage_tables {vertices classes : ℕ} (input : Instance L vertices)
    (labels : Fin vertices → Fin vertices) (representatives : Fin classes → Fin vertices) :
    instanceTablesEquiv L classes (instanceImage input labels representatives) =
      fun symbol tuple => decide (∃ original,
        instanceTablesEquiv L vertices input symbol original = true ∧
          ∀ coordinate, labels (original coordinate) = representatives (tuple coordinate)) := by
  classical
  funext symbol tuple
  apply Bool.eq_iff_iff.mpr
  simp only [instanceTablesEquiv, Equiv.coe_fn_mk, instanceImage, decide_eq_true_eq]

/-- Build the relation images of an instance using labels and representatives.
The result has exactly the supplied number of classes and the canonical dense
instance encoding. -/
noncomputable def quotientInstanceProgram (vertices classes : MvPolynomial Parameter ℕ) :
    Computation Parameter (Option Bool) := by
  classical
  exact instanceTabulate L (quotientInstanceInputs L vertices classes) classes
    (fun sizes arguments symbol tuple => decide (∃ original,
      instanceTablesEquiv L (MvPolynomial.eval sizes vertices) (arguments none) symbol original = true ∧
        ∀ coordinate, arguments (some false) (original coordinate) =
          arguments (some true) (tuple coordinate)))

theorem quotientInstanceProgram_realizable (vertices classes : MvPolynomial Parameter ℕ) :
    (quotientInstanceProgram L vertices classes).Realizable := by
  classical
  apply instanceTabulate_of_tables_realizable
  intro symbol
  let inputs := quotientInstanceInputs L vertices classes
  have projected := (instanceRelation_realizable L vertices symbol).onArguments inputs (fun _ _ => True)
    (fun _ => none) (by intros; rfl) (by intros; trivial)
  have assembled := (quotientScope_realizable vertices classes symbol.1).onResults inputs (fun _ _ => True)
    (fun name sizes arguments => match name with
      | none => instanceTablesEquiv L (MvPolynomial.eval sizes vertices) (arguments.val none) symbol
      | some false => arguments.val (some false)
      | some true => arguments.val (some true)) (by intros; trivial) (by
        intro name
        cases name with
        | none => exact projected.withSpecification (fun _ _ => True) _ (by intros; trivial) (by intros; rfl)
        | some choice =>
          cases choice
          · exact Realizable.argument inputs (some false) (fun _ _ => True)
          · exact Realizable.argument inputs (some true) (fun _ _ => True))
  exact assembled.withSpecification (fun _ _ => True) _ (by intros; trivial) (by intros; rfl)

/-- When the supplied labels come from equations, the program computes the
mathematical quotient relation images exactly. -/
theorem quotientInstanceProgram_compute (vertices classes : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ) (input : Instance L (MvPolynomial.eval sizes vertices))
    (equations : List (Fin (MvPolynomial.eval sizes vertices) × Fin (MvPolynomial.eval sizes vertices)))
    (representatives : Fin (MvPolynomial.eval sizes classes) → Fin (MvPolynomial.eval sizes vertices)) :
    (quotientInstanceProgram L vertices classes).compute sizes
      ⟨(fun name => match name with
        | none => input
        | some false => ArrayQuotient.labels equations
        | some true => representatives), trivial⟩ =
      quotientInstance input equations representatives := by
  classical
  apply (instanceTablesEquiv L (MvPolynomial.eval sizes classes)).injective
  funext symbol tuple
  simp only [quotientInstanceProgram, instanceTabulate, Equiv.apply_symm_apply]
  apply Bool.eq_iff_iff.mpr
  simp only [instanceTablesEquiv, Equiv.coe_fn_mk, decide_eq_true_eq, quotientInstance, instanceImage]

/-- The certified dense output preserves precisely the original solutions
that respect the boundary equations. -/
theorem quotientInstanceProgram_satisfiable_iff (vertices classes : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ) (input : Instance L (MvPolynomial.eval sizes vertices))
    (equations : List (Fin (MvPolynomial.eval sizes vertices) × Fin (MvPolynomial.eval sizes vertices)))
    (representatives : Fin (MvPolynomial.eval sizes classes) ≃
      {value : Fin (MvPolynomial.eval sizes vertices) // ArrayQuotient.labels equations value = value})
    (Carrier : Type) [L.Structure Carrier] :
    Instance.Satisfiable L
      ((quotientInstanceProgram L vertices classes).compute sizes
        ⟨(fun name => match name with
          | none => input
          | some false => ArrayQuotient.labels equations
          | some true => fun index => (representatives index).val), trivial⟩) Carrier ↔
      ∃ assignment : Fin (MvPolynomial.eval sizes vertices) → Carrier,
        (∀ arity (symbol : L.Relations arity) (tuple : Fin arity → Fin (MvPolynomial.eval sizes vertices)),
          input.RelMap symbol tuple → FirstOrder.Language.Structure.RelMap symbol (assignment ∘ tuple)) ∧
        ∀ equation ∈ equations, assignment equation.1 = assignment equation.2 := by
  rw [quotientInstanceProgram_compute]
  exact quotientInstance_satisfiable_iff input equations representatives Carrier

end Polytime2.CSP
