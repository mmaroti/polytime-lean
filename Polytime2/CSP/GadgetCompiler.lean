import Polytime2.CSP.GadgetRawInstance
import Polytime2.CSP.GadgetEquationArrays
import Polytime2.CSP.QuotientCompiler
import Polytime2.Encoding.ConstructorSubstitution

/-! # Composition of the fixed relational gadget compiler

Construct the exact dense raw tables and allocation equations from the source
clause array, then invoke the existing equation-class compiler at the raw
allocation size. No quotient size or numbering is supplied by the caller.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.CSP.GadgetExpansion

open FirstOrder FirstOrder.Language EncodedDomain Polytime2.Computation GadgetAllocation

variable {L : Language.{0, 0}} [L.IsRelational] [Fintype (RelationSymbol L)]
variable {Carrier : Type} [L.Structure Carrier] [Finite Carrier] [Nonempty Carrier]
variable {dimension poolSize : ℕ}
variable (domainFormula : L.Formula (Fin dimension))
variable (clauseFormulas : (Fin 3 → Bool) → L.Formula (Fin 3 × Fin dimension))
variable (enumeration : Pool (Carrier := Carrier) domainFormula clauseFormulas ≃ Fin poolSize)
variable {Parameter : Type} [Fintype Parameter]

private noncomputable def quotientCallee (wires clauses : MvPolynomial Parameter ℕ) : Computation Parameter Bool :=
  (quotientCompiler L (MvPolynomial.X () * MvPolynomial.C (1 + 3 * dimension))).substitute
    (fun _ => allocationSize wires clauses dimension poolSize)

omit [Finite Carrier] in
private theorem rawDomain_eq (wires clauses : MvPolynomial Parameter ℕ) :
    (gadgetRawInstance domainFormula clauseFormulas enumeration wires clauses).outputDomain =
      (quotientCallee (L := L) (dimension := dimension) (poolSize := poolSize) wires clauses).inputDomains false := rfl

private theorem equationDomain_eq (wires clauses : MvPolynomial Parameter ℕ) :
    (gadgetEquationArray domainFormula clauseFormulas enumeration wires clauses).outputDomain =
      (quotientCallee (L := L) (dimension := dimension) (poolSize := poolSize) wires clauses).inputDomains true := by
  change ((boundedIndex (allocationSize wires clauses dimension poolSize)).prod
    (boundedIndex (allocationSize wires clauses dimension poolSize))).arrayOfLength
      (equationArraySize wires clauses dimension poolSize) =
    ((((boundedIndex (MvPolynomial.X ())).prod (boundedIndex (MvPolynomial.X ()))).arrayOfLength
      (MvPolynomial.X () * MvPolynomial.C (1 + 3 * dimension))).substitute
        (fun _ => allocationSize wires clauses dimension poolSize))
  have index : SizeSubstitution.polynomial
      (fun _ : Unit => allocationSize wires clauses dimension poolSize) (MvPolynomial.X ()) =
        allocationSize wires clauses dimension poolSize := by simp [SizeSubstitution.polynomial]
  have count : SizeSubstitution.polynomial
      (fun _ : Unit => allocationSize wires clauses dimension poolSize)
      (MvPolynomial.X () * MvPolynomial.C (1 + 3 * dimension)) =
        allocationSize wires clauses dimension poolSize * MvPolynomial.C (1 + 3 * dimension) := by
    change (MvPolynomial.eval₂Hom MvPolynomial.C
      (fun _ : Unit => allocationSize wires clauses dimension poolSize)) _ = _
    rw [map_mul, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_C]
  rw [arrayOfLength_substitute, prod_substitute, boundedIndex_substitute, index, count, equationArraySize_eq]

/-- Prepare one mathematical input of the quotient compiler from source clauses. -/
noncomputable def gadgetQuotientArgument (wires clauses : MvPolynomial Parameter ℕ) (name : Bool) :
    Computation Parameter Unit where
  inputDomains _ := (SAT.clauseDomain wires).arrayOfLength clauses
  outputDomain := (quotientCallee (L := L) (dimension := dimension) (poolSize := poolSize) wires clauses).inputDomains name
  precondition _ _ := True
  compute sizes arguments := by
    cases name
    · exact cast (congrArg (fun domain : EncodedDomain Parameter => domain.Carrier sizes)
        (rawDomain_eq domainFormula clauseFormulas enumeration wires clauses))
        ((gadgetRawInstance domainFormula clauseFormulas enumeration wires clauses).compute sizes arguments)
    · exact cast (congrArg (fun domain : EncodedDomain Parameter => domain.Carrier sizes)
        (equationDomain_eq domainFormula clauseFormulas enumeration wires clauses))
        ((gadgetEquationArray domainFormula clauseFormulas enumeration wires clauses).compute sizes arguments)

theorem gadgetQuotientArgument_realizable (wires clauses : MvPolynomial Parameter ℕ) (name : Bool) :
    (gadgetQuotientArgument domainFormula clauseFormulas enumeration wires clauses name).Realizable := by
  cases name
  · exact (gadgetRawInstance_realizable domainFormula clauseFormulas enumeration wires clauses).castOutput _
      (rawDomain_eq domainFormula clauseFormulas enumeration wires clauses)
  · exact (gadgetEquationArray_realizable domainFormula clauseFormulas enumeration wires clauses).castOutput _
      (equationDomain_eq domainFormula clauseFormulas enumeration wires clauses)

/-- Build the fixed gadgets, identify their boundary variables, and return the
actual quotient size with its canonical dense relational instance. The internal
result frame retains no extra mathematical variables. -/
noncomputable def gadgetCompiler (wires clauses : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  (quotientCallee (L := L) (dimension := dimension) (poolSize := poolSize) wires clauses).onResults
    (fun _ : Unit => (SAT.clauseDomain wires).arrayOfLength clauses) (fun _ _ => True)
    (fun name sizes arguments =>
      (gadgetQuotientArgument domainFormula clauseFormulas enumeration wires clauses name).compute sizes arguments)
    (by intros; trivial)

theorem gadgetCompiler_realizable (wires clauses : MvPolynomial Parameter ℕ) :
    (gadgetCompiler domainFormula clauseFormulas enumeration wires clauses).Realizable := by
  apply ((quotientCompiler_realizable L (MvPolynomial.X () * MvPolynomial.C (1 + 3 * dimension))).substitute
    (fun _ => allocationSize wires clauses dimension poolSize)).onResults
  intro name
  exact gadgetQuotientArgument_realizable domainFormula clauseFormulas enumeration wires clauses name


private theorem ofFn_heq {First Second : Type} {firstCount secondCount : ℕ}
    (types : First = Second) (counts : firstCount = secondCount)
    {first : Fin firstCount → First} {second : Fin secondCount → Second}
    (same : HEq first second) : HEq (List.ofFn first) (List.ofFn second) := by
  cases types
  cases counts
  cases eq_of_heq same
  rfl

private theorem quotientEquations_heq (wires clauses : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (input : ((SAT.clauseDomain wires).arrayOfLength clauses).Carrier sizes) :
    HEq (List.ofFn ((gadgetQuotientArgument domainFormula clauseFormulas enumeration wires clauses true).compute sizes
      ⟨fun _ => input, trivial⟩))
      (List.ofFn ((gadgetEquationArray domainFormula clauseFormulas enumeration wires clauses).compute sizes
        ⟨fun _ => input, trivial⟩)) := by
  let actual := SizeSubstitution.assignment (fun _ : Unit => allocationSize wires clauses dimension poolSize) sizes
  apply ofFn_heq
    (congrArg (fun count => Fin count × Fin count) (MvPolynomial.eval_X (f := actual) ()))
    (show MvPolynomial.eval actual (MvPolynomial.X () * MvPolynomial.C (1 + 3 * dimension)) =
      MvPolynomial.eval sizes (equationArraySize wires clauses dimension poolSize) from by
        rw [equationArraySize_eq]
        simp only [map_mul, MvPolynomial.eval_X, MvPolynomial.eval_C]
        rfl)
  exact cast_heq (congrArg (fun domain : EncodedDomain Parameter => domain.Carrier sizes)
    (equationDomain_eq domainFormula clauseFormulas enumeration wires clauses))
    ((gadgetEquationArray domainFormula clauseFormulas enumeration wires clauses).compute sizes ⟨fun _ => input, trivial⟩)

omit [L.IsRelational] [Fintype (RelationSymbol L)] [Finite Carrier] [Nonempty Carrier] in
private theorem equationSolutions_heq {firstCount secondCount : ℕ}
    {first : Instance L firstCount} {second : Instance L secondCount}
    {firstEquations : List (Fin firstCount × Fin firstCount)}
    {secondEquations : List (Fin secondCount × Fin secondCount)}
    (counts : firstCount = secondCount) (instances : HEq first second)
    (equations : HEq firstEquations secondEquations) :
    (∃ assignment : Fin firstCount → Carrier,
      (∀ arity (symbol : L.Relations arity) (tuple : Fin arity → Fin firstCount),
        first.RelMap symbol tuple → Structure.RelMap symbol (assignment ∘ tuple)) ∧
      ∀ equation ∈ firstEquations, assignment equation.1 = assignment equation.2) ↔
    (∃ assignment : Fin secondCount → Carrier,
      (∀ arity (symbol : L.Relations arity) (tuple : Fin arity → Fin secondCount),
        second.RelMap symbol tuple → Structure.RelMap symbol (assignment ∘ tuple)) ∧
      ∀ equation ∈ secondEquations, assignment equation.1 = assignment equation.2) := by
  cases counts
  cases eq_of_heq instances
  cases eq_of_heq equations
  rfl

/-- Solutions of the composed compiler are exactly assignments preserving the
raw gadget relations and every generated equation. Counts, padding, and codec
transports impose no additional conditions on an assignment. -/
theorem gadgetCompiler_satisfiable_iff_raw (wires clauses : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (input : ((SAT.clauseDomain wires).arrayOfLength clauses).Carrier sizes) :
    Instance.Satisfiable L
      ((gadgetCompiler domainFormula clauseFormulas enumeration wires clauses).compute sizes ⟨fun _ => input, trivial⟩).2
      Carrier ↔
    ∃ assignment : Fin (MvPolynomial.eval sizes (allocationSize wires clauses dimension poolSize)) → Carrier,
      (∀ arity (symbol : L.Relations arity)
        (tuple : Fin arity → Fin (MvPolynomial.eval sizes (allocationSize wires clauses dimension poolSize))),
        ((gadgetRawInstance domainFormula clauseFormulas enumeration wires clauses).compute sizes
          ⟨fun _ => input, trivial⟩).RelMap symbol tuple → Structure.RelMap symbol (assignment ∘ tuple)) ∧
      ∀ equation ∈ List.ofFn ((gadgetEquationArray domainFormula clauseFormulas enumeration wires clauses).compute sizes
        ⟨fun _ => input, trivial⟩), assignment equation.1 = assignment equation.2 := by
  let vertices := allocationSize wires clauses dimension poolSize
  let actual := SizeSubstitution.assignment (fun _ : Unit => vertices) sizes
  let arguments := fun name =>
    (gadgetQuotientArgument domainFormula clauseFormulas enumeration wires clauses name).compute sizes ⟨fun _ => input, trivial⟩
  have correct := quotientCompiler_satisfiable_iff L
    (MvPolynomial.X () * MvPolynomial.C (1 + 3 * dimension)) actual arguments Carrier
  refine correct.trans ?_
  apply equationSolutions_heq (Carrier := Carrier)
    (show MvPolynomial.eval actual (MvPolynomial.X ()) = MvPolynomial.eval sizes vertices from MvPolynomial.eval_X ())
  · exact cast_heq _ (arguments false)
  · exact quotientEquations_heq domainFormula clauseFormulas enumeration wires clauses sizes input

private theorem equationQuotient_card_heq {firstCount secondCount : ℕ}
    {first : List (Fin firstCount × Fin firstCount)} {second : List (Fin secondCount × Fin secondCount)}
    (counts : firstCount = secondCount) (same : HEq first second) :
    Nat.card (Quot (ArrayQuotient.equationRelation first)) =
      Nat.card (Quot (ArrayQuotient.equationRelation second)) := by
  cases counts
  cases eq_of_heq same
  rfl

/-- The computed variable count is exactly the number of equation classes,
with no contribution from the computation's padded result storage. -/
theorem gadgetCompiler_count (wires clauses : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (input : ((SAT.clauseDomain wires).arrayOfLength clauses).Carrier sizes) :
    ((((gadgetCompiler domainFormula clauseFormulas enumeration wires clauses).compute sizes
      ⟨fun _ => input, trivial⟩).1 ()).val) =
      Nat.card (Quot (ArrayQuotient.equationRelation (List.ofFn
        ((gadgetEquationArray domainFormula clauseFormulas enumeration wires clauses).compute sizes
          ⟨fun _ => input, trivial⟩)))) := by
  let vertices := allocationSize wires clauses dimension poolSize
  let actual := SizeSubstitution.assignment (fun _ : Unit => vertices) sizes
  let arguments := fun name =>
    (gadgetQuotientArgument domainFormula clauseFormulas enumeration wires clauses name).compute sizes ⟨fun _ => input, trivial⟩
  have count := quotientCompiler_count L (MvPolynomial.X () * MvPolynomial.C (1 + 3 * dimension)) actual arguments
  refine count.trans (equationQuotient_card_heq (MvPolynomial.eval_X (f := actual) ()) ?_)
  exact quotientEquations_heq domainFormula clauseFormulas enumeration wires clauses sizes input

end Polytime2.CSP.GadgetExpansion
