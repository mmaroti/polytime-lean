import Polytime2.CSP.GadgetCompiler
import Polytime2.CSP.QuotientWordCompiler
import Polytime2.Complexity.CodedArrayOutput

/-! # Certified native-word streams for fixed-gadget compilation

Reuse the original raw-instance and equation preparation. Only the quotient
consumer changes: it constructs the exact native output stream internally.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.CSP.GadgetExpansion

open EncodedDomain Polytime2.Computation GadgetAllocation Complexity

variable {L : FirstOrder.Language.{0, 0}} [L.IsRelational] [Fintype (RelationSymbol L)]
variable {Carrier : Type} [L.Structure Carrier] [Finite Carrier] [Nonempty Carrier]
variable {dimension poolSize : ℕ}
variable (domainFormula : L.Formula (Fin dimension))
variable (clauseFormulas : (Fin 3 → Bool) → L.Formula (Fin 3 × Fin dimension))
variable (enumeration : Pool (Carrier := Carrier) domainFormula clauseFormulas ≃ Fin poolSize)
variable {Parameter : Type} [Fintype Parameter]

/-- Compile the same gadgets into a sentinel-terminated native output stream. -/
noncomputable def gadgetWordCompiler (wires clauses : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  ((quotientWordCompiler L (MvPolynomial.X () * MvPolynomial.C (1 + 3 * dimension))).substitute
    (fun _ => allocationSize wires clauses dimension poolSize)).onResults
    (fun _ : Unit => (SAT.clauseDomain wires).arrayOfLength clauses) (fun _ _ => True)
    (fun name sizes arguments =>
      (gadgetQuotientArgument domainFormula clauseFormulas enumeration wires clauses name).compute sizes arguments)
    (by intros; trivial)

theorem gadgetWordCompiler_realizable (wires clauses : MvPolynomial Parameter ℕ) :
    (gadgetWordCompiler domainFormula clauseFormulas enumeration wires clauses).Realizable := by
  apply ((quotientWordCompiler_realizable L (MvPolynomial.X () * MvPolynomial.C (1 + 3 * dimension))).substitute
    (fun _ => allocationSize wires clauses dimension poolSize)).onResults
  intro name
  exact gadgetQuotientArgument_realizable domainFormula clauseFormulas enumeration wires clauses name

/-- Live letters encode the original compiler's exact quotient result. -/
theorem gadgetWordCompiler_list (wires clauses : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (gadgetWordCompiler domainFormula clauseFormulas enumeration wires clauses).Arguments sizes) :
    ∃ padding : List (Option Letter),
      List.ofFn ((gadgetWordCompiler domainFormula clauseFormulas enumeration wires clauses).compute sizes
        ⟨arguments, trivial⟩) =
      (instanceWord L
        ⟨(((gadgetCompiler domainFormula clauseFormulas enumeration wires clauses).compute sizes
          ⟨arguments, trivial⟩).1 ()).val,
          ((gadgetCompiler domainFormula clauseFormulas enumeration wires clauses).compute sizes
            ⟨arguments, trivial⟩).2⟩).map some ++ none :: padding := by
  exact quotientWordCompiler_list L (MvPolynomial.X () * MvPolynomial.C (1 + 3 * dimension))
    (SizeSubstitution.assignment (fun _ => allocationSize wires clauses dimension poolSize) sizes)
    (fun name => (gadgetQuotientArgument domainFormula clauseFormulas enumeration wires clauses name).compute sizes
      ⟨arguments, trivial⟩)

/-- Standalone native-word compilation includes the complete source headers. -/
theorem gadgetWordCompiler_polynomialTime (wires clauses : MvPolynomial Parameter ℕ) :
    PolynomialTime (gadgetWordCompiler domainFormula clauseFormulas enumeration wires clauses).inputWord id
      (fun input => instanceWord L
        ⟨(((gadgetCompiler domainFormula clauseFormulas enumeration wires clauses).compute input.1
          ⟨input.2.val, trivial⟩).1 ()).val,
          ((gadgetCompiler domainFormula clauseFormulas enumeration wires clauses).compute input.1
            ⟨input.2.val, trivial⟩).2⟩) := by
  let computation := gadgetWordCompiler domainFormula clauseFormulas enumeration wires clauses
  let substitution : Unit → MvPolynomial Parameter ℕ := fun _ => allocationSize wires clauses dimension poolSize
  let capacity := SizeSubstitution.polynomial (fun _ : Unit => (MvPolynomial.X () : MvPolynomial Unit ℕ))
    (nativeStreamLength (MvPolynomial.X ()) (instanceDomain L))
  let operation := fun input : computation.AdmissibleInput => instanceWord L
    ⟨(((gadgetCompiler domainFormula clauseFormulas enumeration wires clauses).compute input.1
      ⟨input.2.val, trivial⟩).1 ()).val,
      ((gadgetCompiler domainFormula clauseFormulas enumeration wires clauses).compute input.1
        ⟨input.2.val, trivial⟩).2⟩
  have decoded := codedArray_polynomialTime capacity
    (fun input : computation.AdmissibleInput => SizeSubstitution.assignment substitution input.1)
    (fun input => computation.compute input.1 input.2) operation
    (fun input => gadgetWordCompiler_list domainFormula clauseFormulas enumeration wires clauses input.1 input.2.val)
  have encoded : (fun input : computation.AdmissibleInput =>
      (codedLetterDomain.arrayOfLength capacity).word
        (SizeSubstitution.assignment substitution input.1) (computation.compute input.1 input.2)) =
      computation.outputWord ∘ computation.result := by
    funext input
    change _ = (ArrayEncoding.bits (((codedLetterDomain.arrayOfLength capacity).substitute substitution).encode
      input.1 (computation.compute input.1 input.2))).map Sum.inl
    exact (substitute_word (codedLetterDomain.arrayOfLength capacity) substitution input.1
      (computation.compute input.1 input.2)).symm
  rw [encoded] at decoded
  exact decoded.comp (gadgetWordCompiler_realizable domainFormula clauseFormulas enumeration wires clauses).polynomialTime.encodedResult

end Polytime2.CSP.GadgetExpansion
