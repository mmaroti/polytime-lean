import Polytime2.CSP.GadgetExport
import Polytime2.Complexity.WordArrays

/-! # Total clause-constructor translations through fixed Boolean gadgets

Every raw input word is sent through a certified clause constructor and then
the fixed-gadget compiler. The exact native output is an instance of
the target template, with satisfiability equal to that of the constructed
formula. No intermediate relational-instance parser is required.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.CSP.GadgetExpansion

open EncodedDomain Complexity Polytime2.Computation GadgetAllocation

variable {L : FirstOrder.Language.{0, 0}} [L.IsRelational] [Fintype (RelationSymbol L)]
variable {Carrier : Type} [L.Structure Carrier] [Finite Carrier] [Nonempty Carrier]
variable {dimension poolSize : ℕ}
variable (domainFormula : L.Formula (Fin dimension))
variable (clauseFormulas : (Fin 3 → Bool) → L.Formula (Fin 3 × Fin dimension))
variable (enumeration : Pool (Carrier := Carrier) domainFormula clauseFormulas ≃ Fin poolSize)
variable (wires clauses : MvPolynomial Unit ℕ)
variable (construct : ∀ sizes : Unit → ℕ,
  {_arguments : Unit → Fin (sizes ()) → Letter // True} →
    ((SAT.clauseDomain wires).arrayOfLength clauses).Carrier sizes)

private noncomputable def sourceProgram : Computation Unit Unit :=
  Computation.mk (fun _ => letterDomain.array ())
    ((SAT.clauseDomain wires).arrayOfLength clauses) (fun _ _ => True) construct

private noncomputable def streamProgram : Computation Unit Unit :=
  (sourceProgram wires clauses construct).followedBy
    (gadgetWordCompiler domainFormula clauseFormulas enumeration wires clauses) rfl (by intros; trivial)

private theorem streamProgram_realizable
    (ready : (sourceProgram wires clauses construct).Realizable) :
    (streamProgram domainFormula clauseFormulas enumeration wires clauses construct).Realizable :=
  ready.followedBy (gadgetWordCompiler_realizable domainFormula clauseFormulas enumeration wires clauses)
    rfl (by intros; trivial)

/-- Compile a total word-to-clause constructor to an actual target instance. -/
noncomputable def formulaGadgetInstance (word : Word) : SizedInstance L :=
  gadgetCompilerInstance domainFormula clauseFormulas enumeration wires clauses (fun _ => word.length)
    (construct (fun _ => word.length) ⟨fun _ index => word[index], trivial⟩)

/-- The native target word, defined for every raw source word. -/
noncomputable def formulaGadgetWord (word : Word) : Word :=
  instanceWord L (formulaGadgetInstance domainFormula clauseFormulas enumeration wires clauses construct word)

private theorem streamProgram_list (word : Word) :
    ∃ padding : List (Option Letter),
      List.ofFn ((streamProgram domainFormula clauseFormulas enumeration wires clauses construct).compute
        (fun _ => word.length) ⟨fun _ index => word[index], trivial⟩) =
      (formulaGadgetWord domainFormula clauseFormulas enumeration wires clauses construct word).map some ++
        none :: padding := by
  dsimp only [streamProgram, sourceProgram, followedBy,
    formulaGadgetWord, formulaGadgetInstance, gadgetCompilerInstance]
  exact gadgetWordCompiler_list domainFormula clauseFormulas enumeration wires clauses
    (fun _ => word.length) (fun _ => construct (fun _ => word.length)
      ⟨fun _ index => word[index], trivial⟩)

/-- A certified total clause constructor composes with the gadget compiler.
Raw preparation, native output, and padding erasure enter the word-length bound. -/
theorem formulaGadgetWord_polynomialTime
    (ready : (Computation.mk (fun _ : Unit => letterDomain.array ())
      ((SAT.clauseDomain wires).arrayOfLength clauses) (fun _ _ => True) construct).Realizable) :
    PolynomialTime id id (formulaGadgetWord domainFormula clauseFormulas enumeration wires clauses construct) := by
  let computation := streamProgram domainFormula clauseFormulas enumeration wires clauses construct
  let operation (size : ℕ) (input : Fin size → Letter) :=
    computation.compute (fun _ => size) ⟨fun _ => input, trivial⟩
  have raw := Computation.Realizable.onWordResult computation.outputDomain computation.compute
    (streamProgram_realizable domainFormula clauseFormulas enumeration wires clauses construct ready)
  let substitution : Unit → MvPolynomial Unit ℕ := fun _ => allocationSize wires clauses dimension poolSize
  let capacity := SizeSubstitution.polynomial (fun _ : Unit => (MvPolynomial.X () : MvPolynomial Unit ℕ))
    (nativeStreamLength (MvPolynomial.X ()) (instanceDomain L))
  let values (word : Word) : (codedLetterDomain.arrayOfLength capacity).Carrier
      (SizeSubstitution.assignment substitution (fun _ => word.length)) :=
    operation word.length (fun index => word[index])
  have stream (word : Word) : ∃ padding : List (Option Letter),
      List.ofFn (values word) =
        (formulaGadgetWord domainFormula clauseFormulas enumeration wires clauses construct word).map some ++
          none :: padding :=
    streamProgram_list domainFormula clauseFormulas enumeration wires clauses construct word
  have decoded := codedArray_substitute_polynomialTime capacity substitution
    (fun word : Word => fun _ => word.length) values
    (formulaGadgetWord domainFormula clauseFormulas enumeration wires clauses construct) stream
  exact decoded.comp raw.encodedResult

/-- The strict target decoder accepts the exact constructed instance.
Its satisfiability is that of the clause constructor's mathematical formula. -/
theorem formulaGadgetWord_mem
    {subalgebra : (polymorphismLanguage L Carrier).Substructure (Fin dimension → Carrier)}
    {quotient : subalgebra → Bool} {equalityFormula : L.Formula (Fin 2 × Fin dimension)}
    (family : IsBooleanGadgetFamily subalgebra quotient domainFormula equalityFormula clauseFormulas)
    (representatives : Bool → subalgebra) (sectionLaw : Function.RightInverse representatives quotient)
    (word : Word) :
    formulaGadgetWord domainFormula clauseFormulas enumeration wires clauses construct word ∈
      CSP.language L Carrier ↔
      SAT.Formula.Satisfiable (SAT.formulaValue
        (construct (fun _ => word.length) ⟨fun _ index => word[index], trivial⟩)) := by
  change (∃ input, decodeInstanceWord L (instanceWord L _) = some input ∧
    Instance.Satisfiable L input.2 Carrier) ↔ _
  rw [decodeInstanceWord_instanceWord]
  simp only [Option.some.injEq, exists_eq_left']
  exact (gadgetCompilerInstance_satisfiable_iff domainFormula clauseFormulas enumeration family
    representatives sectionLaw _ _ _ _).trans (SAT.formulaValue_satisfiable _).symm

end Polytime2.CSP.GadgetExpansion
