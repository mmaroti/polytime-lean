import Polytime2.CSP.GadgetCompilerCardinality
import Polytime2.CSP.WordVerifier
import Polytime2.Complexity.Realizable

/-! # Native result and source-word bounds for gadget compilation

The mathematical result is the actual quotient size and its dense instance.
Its native instance word has polynomial length in the complete serialized
source input, including all unary size headers. Native-word machine extraction
is a separate obligation from these length bounds.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.CSP.GadgetExpansion

open FirstOrder FirstOrder.Language EncodedDomain Polytime2.Computation GadgetAllocation

variable {L : FirstOrder.Language.{0, 0}} [L.IsRelational] [Fintype (RelationSymbol L)]
variable {Carrier : Type} [L.Structure Carrier] [Finite Carrier] [Nonempty Carrier]
variable {dimension poolSize : ℕ}
variable (domainFormula : L.Formula (Fin dimension))
variable (clauseFormulas : (Fin 3 → Bool) → L.Formula (Fin 3 × Fin dimension))
variable (enumeration : Pool (Carrier := Carrier) domainFormula clauseFormulas ≃ Fin poolSize)
variable {Parameter : Type} [Fintype Parameter]

/-- Observe the actual mathematical output, forgetting its private count
capacity and padded dependent frame. -/
noncomputable def gadgetCompilerInstance (wires clauses : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (input : ((SAT.clauseDomain wires).arrayOfLength clauses).Carrier sizes) : SizedInstance L :=
  let output := (gadgetCompiler domainFormula clauseFormulas enumeration wires clauses).compute sizes ⟨fun _ => input, trivial⟩
  ⟨(output.1 ()).val, output.2⟩

/-- The observed result has exactly the mathematical expansion's variables. -/
theorem gadgetCompilerInstance_count (wires clauses : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (input : ((SAT.clauseDomain wires).arrayOfLength clauses).Carrier sizes) :
    (gadgetCompilerInstance domainFormula clauseFormulas enumeration wires clauses sizes input).1 =
      Nat.card (ExpandedVariables (Carrier := Carrier) domainFormula clauseFormulas (List.ofFn input)) :=
  gadgetCompiler_count_expansion domainFormula clauseFormulas enumeration wires clauses sizes input

/-- The ordinary mathematical result preserves the represented Boolean SAT
problem; no frame or storage capacity appears in this solution contract. -/
theorem gadgetCompilerInstance_satisfiable_iff
    {subalgebra : (polymorphismLanguage L Carrier).Substructure (Fin dimension → Carrier)}
    {quotient : subalgebra → Bool} {equalityFormula : L.Formula (Fin 2 × Fin dimension)}
    (family : IsBooleanGadgetFamily subalgebra quotient domainFormula equalityFormula clauseFormulas)
    (representatives : Bool → subalgebra) (sectionLaw : Function.RightInverse representatives quotient)
    (wires clauses : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (input : ((SAT.clauseDomain wires).arrayOfLength clauses).Carrier sizes) :
    Instance.Satisfiable L
      (gadgetCompilerInstance domainFormula clauseFormulas enumeration wires clauses sizes input).2 Carrier ↔
      SAT.Formula.Satisfiable (List.ofFn input) :=
  gadgetCompiler_satisfiable_iff domainFormula clauseFormulas enumeration family representatives sectionLaw wires clauses sizes input

/-- The mathematical quotient has at most the number of raw allocated slots. -/
theorem gadgetCompilerInstance_count_le (wires clauses : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (input : ((SAT.clauseDomain wires).arrayOfLength clauses).Carrier sizes) :
    (gadgetCompilerInstance domainFormula clauseFormulas enumeration wires clauses sizes input).1 ≤
      MvPolynomial.eval sizes (allocationSize wires clauses dimension poolSize) := by
  change (((gadgetCompiler domainFormula clauseFormulas enumeration wires clauses).compute sizes
    ⟨fun _ => input, trivial⟩).1 ()).val ≤ _
  rw [gadgetCompiler_count]
  let equations : List (Fin (MvPolynomial.eval sizes (allocationSize wires clauses dimension poolSize)) ×
      Fin (MvPolynomial.eval sizes (allocationSize wires clauses dimension poolSize))) := List.ofFn ((gadgetEquationArray domainFormula clauseFormulas enumeration wires clauses).compute sizes
    ⟨fun _ => input, trivial⟩)
  have bound := Nat.card_le_card_of_surjective (Quot.mk (ArrayQuotient.equationRelation equations)) (by
    intro value
    refine Quot.inductionOn value ?_
    intro representative
    exact ⟨representative, rfl⟩)
  simpa only [Nat.card_fin] using bound

/-- Header, separator, and dense table widths at the maximum raw count. -/
noncomputable def gadgetWordLengthBound (wires clauses : MvPolynomial Parameter ℕ) (dimension poolSize : ℕ) :
    MvPolynomial Parameter ℕ :=
  let vertices := allocationSize wires clauses dimension poolSize
  vertices + 1 + SizeSubstitution.polynomial (fun _ : Unit => vertices) (instanceDomain L).widthPolynomial

/-- Native output length is bounded at the source sizes, including its unary
quotient-count header and every dense relation table. -/
theorem gadgetCompilerInstance_word_length (wires clauses : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (input : ((SAT.clauseDomain wires).arrayOfLength clauses).Carrier sizes) :
    (instanceWord L (gadgetCompilerInstance domainFormula clauseFormulas enumeration wires clauses sizes input)).length ≤
      MvPolynomial.eval sizes (gadgetWordLengthBound (L := L) wires clauses dimension poolSize) := by
  let output := gadgetCompilerInstance domainFormula clauseFormulas enumeration wires clauses sizes input
  have count := gadgetCompilerInstance_count_le domainFormula clauseFormulas enumeration wires clauses sizes input
  have tables := SizeSubstitution.eval_mono (instanceDomain L).widthPolynomial (fun _ : Unit => count)
  change (instanceWord L output).length ≤ _
  simp only [instanceWord, List.length_append, List.length_replicate, List.length_cons, word_length]
  change output.1 + (MvPolynomial.eval (fun _ => output.1) (instanceDomain L).widthPolynomial + 1) ≤ _
  have bound := Nat.add_le_add count (Nat.add_le_add_right tables 1)
  have lengthBound : MvPolynomial.eval sizes (gadgetWordLengthBound (L := L) wires clauses dimension poolSize) =
      MvPolynomial.eval sizes (allocationSize wires clauses dimension poolSize) + 1 +
        MvPolynomial.eval (fun _ : Unit => MvPolynomial.eval sizes (allocationSize wires clauses dimension poolSize))
          (instanceDomain L).widthPolynomial := by
    simp only [gadgetWordLengthBound, map_add, map_one, SizeSubstitution.polynomial_eval]
    rfl
  rw [lengthBound]
  exact (Nat.add_assoc _ _ _).symm ▸ (by simpa only [Nat.add_comm 1] using bound)

/-- The native instance word has polynomial length in the whole serialized
source, rather than in externally supplied capacities or the quotient count. -/
theorem gadgetCompilerInstance_word_length_polynomial (wires clauses : MvPolynomial Parameter ℕ) :
    ∃ bound : Polynomial ℕ, ∀ sizes
      (input : ((SAT.clauseDomain wires).arrayOfLength clauses).Carrier sizes),
      (instanceWord L (gadgetCompilerInstance domainFormula clauseFormulas enumeration wires clauses sizes input)).length ≤
        bound.eval ((gadgetCompiler domainFormula clauseFormulas enumeration wires clauses).inputWord
          ⟨sizes, ⟨fun _ => input, trivial⟩⟩).length := by
  refine ⟨Complexity.Internal.diagonal (gadgetWordLengthBound (L := L) wires clauses dimension poolSize), ?_⟩
  intro sizes input
  refine (gadgetCompilerInstance_word_length domainFormula clauseFormulas enumeration wires clauses sizes input).trans ?_
  rw [Complexity.Internal.diagonal_eval]
  exact SizeSubstitution.eval_mono _
    ((gadgetCompiler domainFormula clauseFormulas enumeration wires clauses).size_le_inputWord_length
      ⟨sizes, ⟨fun _ => input, trivial⟩⟩)

end Polytime2.CSP.GadgetExpansion
