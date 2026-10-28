import Polytime2.Complexity.FixedWitness
import Polytime2.Complexity.CookLevin.InstancePrefix
import Polytime2.Complexity.CookLevin.PrefixFormula
import Polytime2.Complexity.CookLevin.Tseitin
import Polytime2.SAT.FormulaSubstitution
import Polytime2.SAT.FixedInputsProgram

/-! # Certified construction of prefix-fixed verifier formulas

The sole public size is the instance length. The full framed verifier-input
length and its time allowance are fixed polynomials derived internally from
the witness length and verifier certificate. Canonical Tseitin clauses and
fixed-instance unit clauses use the same clause codec.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Complexity.CookLevin

open Turing Circuit EncodedDomain Polytime2.Computation

variable {Symbol State : Type} [Inhabited Symbol] [Inhabited State]
variable [Fintype Symbol] [Fintype State]

/-- The framed verifier word consists of its pair prefix and fixed-length witness. -/
noncomputable def verifierPairLength (witnessLength : Polynomial ℕ) : Polynomial ℕ :=
  2 * Polynomial.X + witnessLength + 1

private noncomputable def fixedFormulaSizes (timeBound witnessLength : Polynomial ℕ) : Bool → MvPolynomial Unit ℕ :=
  fun isLength => if isLength then (verifierPairLength witnessLength).toMvPolynomial ()
    else (timeBound.comp (verifierPairLength witnessLength)).toMvPolynomial ()

private theorem fixedFormulaSizes_length (timeBound witnessLength : Polynomial ℕ) (sizes : Unit → ℕ) :
    SizeSubstitution.assignment (fixedFormulaSizes timeBound witnessLength) sizes true =
      2 * sizes () + witnessLength.eval (sizes ()) + 1 := by
  simp [SizeSubstitution.assignment, fixedFormulaSizes, verifierPairLength, MvPolynomial.eval_toMvPolynomial]

private theorem fixedFormulaSizes_time (timeBound witnessLength : Polynomial ℕ) (sizes : Unit → ℕ) :
    SizeSubstitution.assignment (fixedFormulaSizes timeBound witnessLength) sizes false =
      timeBound.eval (2 * sizes () + witnessLength.eval (sizes ()) + 1) := by
  simp [SizeSubstitution.assignment, fixedFormulaSizes, verifierPairLength, MvPolynomial.eval_toMvPolynomial,
    Polynomial.eval_comp]

private noncomputable def sourceWires (Symbol State : Type) [Fintype Symbol] [Fintype State] : MvPolynomial Bool ℕ :=
  verifierInputBits + checkedWordGateCount Symbol State

private noncomputable def sourceClauses (Symbol State : Type) [Fintype Symbol] [Fintype State] : MvPolynomial Bool ℕ :=
  checkedWordGateCount Symbol State * 3 + 1

/-- Actual finite variable count of the constructed verifier formula. -/
noncomputable def fixedFormulaWireCount (Symbol State : Type) [Fintype Symbol] [Fintype State]
    (timeBound witnessLength : Polynomial ℕ) : MvPolynomial Unit ℕ :=
  SizeSubstitution.polynomial (fixedFormulaSizes timeBound witnessLength) (sourceWires Symbol State)

private noncomputable def fixedClauses (Symbol State : Type) [Fintype Symbol] [Fintype State]
    (timeBound witnessLength : Polynomial ℕ) : MvPolynomial Unit ℕ :=
  SizeSubstitution.polynomial (fixedFormulaSizes timeBound witnessLength) (sourceClauses Symbol State)

private noncomputable def prefixBitCount : MvPolynomial Unit ℕ :=
  instancePrefixLength * MvPolynomial.C (Fintype.card Letter)

/-- Total clause count, including all fixed-instance unit clauses. -/
noncomputable def fixedFormulaClauseCount (Symbol State : Type) [Fintype Symbol] [Fintype State]
    (timeBound witnessLength : Polynomial ℕ) : MvPolynomial Unit ℕ :=
  fixedClauses Symbol State timeBound witnessLength + prefixBitCount

omit [Inhabited Symbol] [Inhabited State] in
private theorem prefix_fits (timeBound witnessLength : Polynomial ℕ) (sizes : Unit → ℕ) :
    MvPolynomial.eval sizes prefixBitCount ≤ MvPolynomial.eval sizes (fixedFormulaWireCount Symbol State timeBound witnessLength) := by
  have prefixBound : MvPolynomial.eval sizes instancePrefixLength ≤
      SizeSubstitution.assignment (fixedFormulaSizes timeBound witnessLength) sizes true := by
    simp only [instancePrefixLength, map_add, map_one, MvPolynomial.eval_X, fixedFormulaSizes_length]
    omega
  calc
    MvPolynomial.eval sizes prefixBitCount = MvPolynomial.eval sizes instancePrefixLength * Fintype.card Letter := by
      simp [prefixBitCount]
    _ ≤ SizeSubstitution.assignment (fixedFormulaSizes timeBound witnessLength) sizes true * Fintype.card Letter :=
      Nat.mul_le_mul_right _ prefixBound
    _ = MvPolynomial.eval (SizeSubstitution.assignment (fixedFormulaSizes timeBound witnessLength) sizes) verifierInputBits := by
      simp [verifierInputBits]
    _ ≤ MvPolynomial.eval (SizeSubstitution.assignment (fixedFormulaSizes timeBound witnessLength) sizes) (sourceWires Symbol State) := by
      simp only [sourceWires, map_add]
      omega
    _ = MvPolynomial.eval sizes (fixedFormulaWireCount Symbol State timeBound witnessLength) :=
      (SizeSubstitution.polynomial_eval _ _ _).symm

private noncomputable def specializedFormula (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) (timeBound witnessLength : Polynomial ℕ) : Computation Unit Empty :=
  ((verifierFormulaProgram machine entry letters).substitute (fixedFormulaSizes timeBound witnessLength)).followedBy
    (SAT.formulaSubstitution (sourceWires Symbol State) (sourceClauses Symbol State)
      (fixedFormulaSizes timeBound witnessLength)) rfl (by intros; trivial)

private theorem specializedFormula_realizable (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) (timeBound witnessLength : Polynomial ℕ) :
    (specializedFormula machine entry letters timeBound witnessLength).Realizable :=
  ((verifierFormulaProgram_realizable machine entry letters).substitute (fixedFormulaSizes timeBound witnessLength)).followedBy
    (SAT.formulaSubstitution_realizable (sourceWires Symbol State) (sourceClauses Symbol State)
      (fixedFormulaSizes timeBound witnessLength)) rfl (by intros; trivial)

private theorem specializedFormula_correct (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) (timeBound witnessLength : Polynomial ℕ) (sizes : Unit → ℕ)
    (arguments : (specializedFormula machine entry letters timeBound witnessLength).Arguments sizes) :
    SAT.formulaValue ((specializedFormula machine entry letters timeBound witnessLength).compute sizes ⟨arguments, trivial⟩) =
      SAT.tseitin ((2 * sizes () + witnessLength.eval (sizes ()) + 1) * Fintype.card Letter)
        (checkedWordCircuit machine entry letters (timeBound.eval (2 * sizes () + witnessLength.eval (sizes ()) + 1))
          (2 * sizes () + witnessLength.eval (sizes ()) + 1)) := by
  simp only [specializedFormula, followedBy]
  rw [SAT.formulaSubstitution_correct]
  have correct := verifierFormulaProgram_correct machine entry letters
    (SizeSubstitution.assignment (fixedFormulaSizes timeBound witnessLength) sizes) arguments
  simpa only [Computation.substitute, fixedFormulaSizes_time, fixedFormulaSizes_length] using correct

private noncomputable def formulaOnInput (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) (timeBound witnessLength : Polynomial ℕ) : Computation Unit Unit :=
  (specializedFormula machine entry letters timeBound witnessLength).onResults
    instancePrefixBits.inputDomains (fun _ _ => True) (fun empty => nomatch empty) (by intros; trivial)

private theorem formulaOnInput_realizable (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) (timeBound witnessLength : Polynomial ℕ) :
    (formulaOnInput machine entry letters timeBound witnessLength).Realizable :=
  (specializedFormula_realizable machine entry letters timeBound witnessLength).onResults
    instancePrefixBits.inputDomains (fun _ _ => True) (fun empty => nomatch empty) (by intros; trivial)
    (fun empty => nomatch empty)

/-- Construct exactly the verifier formula with the framed instance prefix fixed. -/
noncomputable def fixedFormulaProgram (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) (timeBound witnessLength : Polynomial ℕ) : Computation Unit Unit :=
  (SAT.fixInputsProgram prefixBitCount (fixedFormulaWireCount Symbol State timeBound witnessLength)
    (fixedClauses Symbol State timeBound witnessLength) (prefix_fits timeBound witnessLength)).onResults
    instancePrefixBits.inputDomains (fun _ _ => True)
    (fun name sizes arguments => match name with
      | false => (formulaOnInput machine entry letters timeBound witnessLength).compute sizes arguments
      | true => instancePrefixBits.compute sizes arguments) (by intros; trivial)

theorem fixedFormulaProgram_realizable (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) (timeBound witnessLength : Polynomial ℕ) :
    (fixedFormulaProgram machine entry letters timeBound witnessLength).Realizable := by
  apply (SAT.fixInputsProgram_realizable prefixBitCount (fixedFormulaWireCount Symbol State timeBound witnessLength)
    (fixedClauses Symbol State timeBound witnessLength) (prefix_fits timeBound witnessLength)).onResults
  intro name
  cases name
  · exact formulaOnInput_realizable machine entry letters timeBound witnessLength
  · exact instancePrefixBits_realizable

theorem fixedFormulaProgram_outputDomain (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) (timeBound witnessLength : Polynomial ℕ) :
    (fixedFormulaProgram machine entry letters timeBound witnessLength).outputDomain =
      (SAT.clauseDomain (fixedFormulaWireCount Symbol State timeBound witnessLength)).arrayOfLength
        (fixedFormulaClauseCount Symbol State timeBound witnessLength) := rfl

/-- The complete output has exactly the intended mathematical clauses. -/
theorem fixedFormulaProgram_correct (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) (timeBound witnessLength : Polynomial ℕ) (sizes : Unit → ℕ)
    (arguments : (fixedFormulaProgram machine entry letters timeBound witnessLength).Arguments sizes) :
    SAT.formulaValue ((fixedFormulaProgram machine entry letters timeBound witnessLength).compute sizes ⟨arguments, trivial⟩) =
      fixedVerifierFormula machine entry letters
        (timeBound.eval (2 * (List.ofFn (arguments ())).length + witnessLength.eval (List.ofFn (arguments ())).length + 1))
        (2 * (List.ofFn (arguments ())).length + witnessLength.eval (List.ofFn (arguments ())).length + 1)
        (encodePair (List.ofFn (arguments ()), [])) := by
  simp only [fixedFormulaProgram, onResults]
  rw [SAT.fixInputsProgram_correct, instancePrefixBits_correct]
  simp only [formulaOnInput, onResults]
  rw [specializedFormula_correct]
  simp only [fixedVerifierFormula, List.length_ofFn, MvPolynomial.eval_X]

/-- The complete constructed formula is satisfiable exactly for an accepting
witness of the specified polynomial length. -/
theorem fixedFormulaProgram_satisfiable (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) (timeBound witnessLength : Polynomial ℕ) (verify : Word → Bool)
    (runs : ∀ word, Internal.Runs machine entry letters word [Sum.inl (verify word)] (timeBound.eval word.length))
    (sizes : Unit → ℕ)
    (arguments : (fixedFormulaProgram machine entry letters timeBound witnessLength).Arguments sizes) :
    SAT.Formula.Satisfiable (SAT.formulaValue
      ((fixedFormulaProgram machine entry letters timeBound witnessLength).compute sizes ⟨arguments, trivial⟩)) ↔
        ∃ witness : Word, witness.length = witnessLength.eval (List.ofFn (arguments ())).length ∧
          verify (encodePair (List.ofFn (arguments ()), witness)) = true := by
  rw [fixedFormulaProgram_correct]
  apply fixedVerifierFormula_pair
  intro word
  simpa only [List.length_ofFn] using runs (List.ofFn word)

/-- Includes instance-prefix construction, internal size preparation, verifier
circuit construction, Tseitin conversion, unit clauses, and serialization. -/
theorem fixedFormulaProgram_polynomialTime (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) (timeBound witnessLength : Polynomial ℕ) :
    PolynomialTime (fixedFormulaProgram machine entry letters timeBound witnessLength).inputWord
      (fixedFormulaProgram machine entry letters timeBound witnessLength).outputWord
      (fixedFormulaProgram machine entry letters timeBound witnessLength).result :=
  (fixedFormulaProgram_realizable machine entry letters timeBound witnessLength).polynomialTime

/-- Every NP language has a certified uniform three-CNF constructor whose
satisfiability is exactly membership of the original word. The word-language
reduction additionally requires a framed SAT output word. -/
theorem np_formulas_uniform (language : Language Letter) (membership : InNP language) :
    ∃ (Symbol : Type) (finiteSymbols : Fintype Symbol) (inhabitedSymbols : Inhabited Symbol),
      let _ : Fintype Symbol := finiteSymbols
      let _ : Inhabited Symbol := inhabitedSymbols
      ∃ (State : Type) (finiteStates : Fintype State) (inhabitedStates : Inhabited State),
        let _ : Fintype State := finiteStates
        let _ : Inhabited State := inhabitedStates
        ∃ (letters : Letter ↪ Symbol) (machine : TM0.Machine Symbol State) (entry : State)
            (timeBound witnessLength : Polynomial ℕ),
          (fixedFormulaProgram machine entry letters timeBound witnessLength).Realizable ∧
          ∀ (sizes : Unit → ℕ)
              (arguments : (fixedFormulaProgram machine entry letters timeBound witnessLength).Arguments sizes),
            List.ofFn (arguments ()) ∈ language ↔
              SAT.Formula.Satisfiable (SAT.formulaValue
                ((fixedFormulaProgram machine entry letters timeBound witnessLength).compute sizes ⟨arguments, trivial⟩)) := by
  obtain ⟨verify, witnessLength, ready, _rejects, correct⟩ := membership.fixedWitness
  obtain ⟨Symbol, finiteSymbols, inhabitedSymbols, State, finiteStates, inhabitedStates,
    letters, machine, entry, timeBound, _nonblank, executes⟩ := ready
  let _ : Fintype Symbol := finiteSymbols
  let _ : Inhabited Symbol := inhabitedSymbols
  let _ : Fintype State := finiteStates
  let _ : Inhabited State := inhabitedStates
  refine ⟨Symbol, finiteSymbols, inhabitedSymbols, State, finiteStates, inhabitedStates,
    letters, machine, entry, timeBound, witnessLength,
    fixedFormulaProgram_realizable machine entry letters timeBound witnessLength, ?_⟩
  intro sizes arguments
  rw [correct]
  apply (fixedFormulaProgram_satisfiable machine entry letters timeBound witnessLength verify ?_ sizes arguments).symm
  intro word
  simpa only [id_eq, encodeBool] using (executes word).1

end Polytime2.Complexity.CookLevin
