import Polytime2.CSP.QuotientAtCount
import Polytime2.Arrays.QuotientNumbering

/-! # Certified quotient compilation from a dense instance and equations

Compute equation classes, retain their actual representatives, and construct
the dense relation images at the computed class count. The equation capacity
is a specialization-fixed polynomial in the original vertex count.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.CSP

open EncodedDomain Polytime2.Computation

variable (L : FirstOrder.Language.{0, 0}) [L.IsRelational] [Fintype (RelationSymbol L)]

noncomputable def quotientCompilerInputs (equations : MvPolynomial Unit ℕ) : Bool → EncodedDomain Unit
  | false => instanceDomain L
  | true => ((boundedIndex (MvPolynomial.X ())).prod (boundedIndex (MvPolynomial.X ()))).arrayOfLength equations

private noncomputable def prepare (equations : MvPolynomial Unit ℕ) : Computation Unit Bool where
  inputDomains := quotientCompilerInputs L equations
  outputDomain := quotientStoredInput L
  precondition _ _ := True
  compute sizes arguments :=
    ((arguments.val false,
      (quotientLabels (MvPolynomial.X ()) equations).compute sizes ⟨fun _ => arguments.val true, trivial⟩),
      (quotientRepresentatives (MvPolynomial.X ()) equations).compute sizes
        ⟨fun _ => arguments.val true, trivial⟩)

private theorem prepare_realizable (equations : MvPolynomial Unit ℕ) :
    (prepare L equations).Realizable := by
  let inputs := quotientCompilerInputs L equations
  have labels := (quotientLabels_realizable (MvPolynomial.X ()) equations).onArguments inputs
    (fun _ _ => True) (fun _ => true) (by intros; rfl) (by intros; trivial)
  have representatives := (quotientRepresentatives_realizable (MvPolynomial.X ()) equations).onArguments inputs
    (fun _ _ => True) (fun _ => true) (by intros; rfl) (by intros; trivial)
  have combined := ((Realizable.argument inputs false (fun _ _ => True)).prodMk labels).prodMk representatives
  exact combined.withSpecification (fun _ _ => True) (prepare L equations).compute
    (by intros; trivial) (by intros; rfl)

/-- Identify all equation classes and return their exact count and dense
relational instance. No quotient count or representatives are caller inputs. -/
noncomputable def quotientCompiler (equations : MvPolynomial Unit ℕ) : Computation Unit Bool :=
  (prepare L equations).followedBy (quotientAtCount L) rfl (by intros; trivial)

theorem quotientCompiler_realizable (equations : MvPolynomial Unit ℕ) :
    (quotientCompiler L equations).Realizable :=
  (prepare_realizable L equations).followedBy (quotientAtCount_realizable L) rfl (by intros; trivial)

/-- The retained output size is the actual mathematical quotient cardinality. -/
theorem quotientCompiler_count (equations : MvPolynomial Unit ℕ) (sizes : Unit → ℕ)
    (input : (quotientCompiler L equations).Arguments sizes) :
    (((quotientCompiler L equations).compute sizes ⟨input, trivial⟩).1 ()).val =
      Nat.card (Quot (ArrayQuotient.equationRelation (List.ofFn (input true)))) := by
  change (((quotientAtCount L).compute sizes
    ⟨fun _ => (prepare L equations).compute sizes ⟨input, trivial⟩, trivial⟩).1 ()).val = _
  rw [quotientAtCount_count]
  exact quotientRepresentatives_count (MvPolynomial.X ()) equations sizes (input true)

/-- The computed instance is the mathematical quotient with its stable
increasing representatives. The heterogeneous equality only transports the
equal finite variable bounds. -/
theorem quotientCompiler_compute_heq (equations : MvPolynomial Unit ℕ) (sizes : Unit → ℕ)
    (input : (quotientCompiler L equations).Arguments sizes) :
    let equationList := List.ofFn (input true)
    let flags := ArrayQuotient.representativeFlags equationList
    HEq ((quotientCompiler L equations).compute sizes ⟨input, trivial⟩).2
      (quotientInstance
        (cast (congrArg (Instance L) (MvPolynomial.eval_X (f := sizes) ()).symm) (input false))
        equationList (fun index => (ArrayPacking.selection flags index).val)) := by
  let equationList : List (Fin (MvPolynomial.eval sizes (MvPolynomial.X ())) ×
      Fin (MvPolynomial.eval sizes (MvPolynomial.X ()))) := List.ofFn (input true)
  dsimp only
  change HEq ((quotientAtCount L).compute sizes
    ⟨fun _ => (prepare L equations).compute sizes ⟨input, trivial⟩, trivial⟩).2 _
  rw [quotientAtCount_compute]
  dsimp only [prepare]
  rw [quotientRepresentatives_compute]
  dsimp only [storedInstanceImage, quotientLabels, unaryMap, quotientInstance]
  apply instanceImage_heq
  · exact (MvPolynomial.eval_X (f := sizes) ()).symm
  · rfl
  · exact (cast_heq _ _).symm
  · intro leftIndex rightIndex same
    change (ArrayQuotient.labels equationList _).val = (ArrayQuotient.labels equationList _).val
    apply congrArg (fun index => (ArrayQuotient.labels equationList index).val)
    exact Fin.ext same
  · intro leftIndex rightIndex same
    change (ArrayPacking.selection _ _).val.val = (ArrayPacking.selection _ _).val.val
    congr 3
    exact Fin.ext same

/-- Solutions of the compiled dense instance are exactly assignments to the
original variables preserving all original relations and all input equations.
The source cast only identifies polynomial evaluation of the named size with
that same mathematical variable count. -/
theorem quotientCompiler_satisfiable_iff (equations : MvPolynomial Unit ℕ) (sizes : Unit → ℕ)
    (input : (quotientCompiler L equations).Arguments sizes) (Carrier : Type) [L.Structure Carrier] :
    Instance.Satisfiable L ((quotientCompiler L equations).compute sizes ⟨input, trivial⟩).2 Carrier ↔
      let source := cast (congrArg (Instance L) (MvPolynomial.eval_X (f := sizes) ()).symm) (input false)
      ∃ assignment : Fin (MvPolynomial.eval sizes (MvPolynomial.X ())) → Carrier,
        (∀ arity (symbol : L.Relations arity)
          (tuple : Fin arity → Fin (MvPolynomial.eval sizes (MvPolynomial.X ()))),
          source.RelMap symbol tuple → FirstOrder.Language.Structure.RelMap symbol (assignment ∘ tuple)) ∧
        ∀ equation ∈ List.ofFn (input true), assignment equation.1 = assignment equation.2 := by
  let equationList : List (Fin (MvPolynomial.eval sizes (MvPolynomial.X ())) ×
      Fin (MvPolynomial.eval sizes (MvPolynomial.X ()))) := List.ofFn (input true)
  let flags := ArrayQuotient.representativeFlags equationList
  let source : Instance L (MvPolynomial.eval sizes (MvPolynomial.X ())) :=
    cast (congrArg (Instance L) (MvPolynomial.eval_X (f := sizes) ()).symm) (input false)
  let representatives : Fin (ArrayPacking.count flags) ≃
      {value // ArrayQuotient.labels equationList value = value} :=
    (ArrayPacking.selection flags).toEquiv.trans
      (Equiv.subtypeEquivRight (fun _ => by simp only [flags, ArrayQuotient.representativeFlags, decide_eq_true_eq]))
  have count := (quotientCompiler_count L equations sizes input).trans
    (ArrayQuotient.numbering_count equationList)
  have solutions := Instance.satisfiable_heq L count
    (quotientCompiler_compute_heq L equations sizes input) Carrier
  exact solutions.trans (quotientInstance_satisfiable_iff source equationList representatives Carrier)

end Polytime2.CSP
