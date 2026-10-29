import Polytime2.Complexity.CookLevin.CheckedWordGates

/-! # Canonical construction and serialization of checked verifier circuits

The answer is exactly the existing mathematical checked-word circuit. Its
letter-code predicate rejects every noncanonical one-hot input assignment.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Complexity.CookLevin

open Turing Circuit EncodedDomain Polytime2.Computation

variable {Symbol State : Type} [Inhabited Symbol] [Inhabited State]
variable [Fintype Symbol] [Fintype State]

/-- Final output reference after all guard copies and joining gates. -/
noncomputable def checkedWordOutput (Symbol State : Type) [Fintype Symbol] [Fintype State] : MvPolynomial Bool ℕ :=
  wordCircuitWires Symbol State + 3 * wordGuardGateCount + 4

private theorem checkedWordCircuit_output (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) (sizes : Bool → ℕ) :
    (checkedWordCircuit machine entry letters (sizes false) (sizes true)).2 =
      MvPolynomial.eval sizes (checkedWordOutput Symbol State) := by
  let expression := Expression.select (wordGuardExpression (sizes true))
    (.wire (wordCircuit machine entry letters (sizes false) (sizes true)).2) (.constant false)
  have count : expression.gateCount = 3 * (wordGuardExpression (sizes true)).gateCount + 5 := by
    simp only [expression, Expression.select, Expression.gateCount]
    omega
  have result := Expression.compile_output expression (MvPolynomial.eval sizes (wordCircuitWires Symbol State))
    (by rw [count]; omega)
  rw [count] at result
  simp only [checkedWordCircuit, Circuit.guard, wordCircuit_base]
  change (expression.compile (MvPolynomial.eval sizes (wordCircuitWires Symbol State))).2 = _
  simp only [checkedWordOutput, map_add, map_mul, map_ofNat, wordGuardGateCount_eval]
  omega

/-- Exact number of simulation, input-preparation, and guard gates. -/
noncomputable def checkedWordGateCount (Symbol State : Type) [Fintype Symbol] [Fintype State] : MvPolynomial Bool ℕ :=
  (2 + wordCoreGateCount Symbol State) +
    (((wordGuardGateCount + 1) + (wordGuardGateCount + wordGuardGateCount)) + 4)

/-- Canonical complete gate-array and actual output-coordinate codec. -/
noncomputable def checkedWordCircuitDomain (Symbol State : Type) [Fintype Symbol] [Fintype State] : EncodedDomain Bool :=
  ((gateDomain (checkedGuardWires (wordCircuitWires Symbol State))).arrayOfLength
    (checkedWordGateCount Symbol State)).prod
    (arrayPosition (checkedGuardWires (wordCircuitWires Symbol State)))

/-- Observe the checked circuit as an ordinary mathematical network. -/
noncomputable def checkedWordProgramNetwork (Symbol State : Type) [Fintype Symbol] [Fintype State]
    (sizes : Bool → ℕ) (program : (checkedWordCircuitDomain Symbol State).Carrier sizes) : Network :=
  programValue program

private theorem output_fits (sizes : Bool → ℕ) :
    MvPolynomial.eval sizes (checkedWordOutput Symbol State) <
      MvPolynomial.eval sizes (checkedGuardWires (wordCircuitWires Symbol State)) := by
  simp only [checkedWordOutput, checkedGuardWires, map_add, map_mul, map_ofNat]
  omega

private noncomputable def checkedWordImplementation (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) : Computation Bool Empty where
  inputDomains := Empty.elim
  outputDomain := checkedWordCircuitDomain Symbol State
  precondition _ _ := True
  compute sizes arguments := ((checkedWordGateProgram machine entry letters).compute sizes arguments,
    ⟨MvPolynomial.eval sizes (checkedWordOutput Symbol State), output_fits sizes⟩)

private theorem checkedWordImplementation_realizable (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) : (checkedWordImplementation machine entry letters).Realizable := by
  have output := (positionPolynomial_realizable (checkedWordOutput Symbol State)
    (checkedGuardWires (wordCircuitWires Symbol State))).onResults
      (Empty.elim : Empty → EncodedDomain Bool) (fun _ _ => True) (fun empty => nomatch empty)
      (by intro sizes arguments; exact output_fits sizes) (fun empty => nomatch empty)
  exact (checkedWordGateProgram_realizable machine entry letters).prodMk output

private theorem checkedWordImplementation_correct (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) (sizes : Bool → ℕ)
    (arguments : {arguments : (checkedWordImplementation machine entry letters).Arguments sizes // True}) :
    checkedWordProgramNetwork Symbol State sizes ((checkedWordImplementation machine entry letters).compute sizes arguments) =
      checkedWordCircuit machine entry letters (sizes false) (sizes true) := by
  rcases arguments with ⟨arguments, accepted⟩
  have unique : arguments = (fun empty => nomatch empty) := by funext empty; cases empty
  subst arguments
  apply Prod.ext
  · exact checkedWordGateProgram_value machine entry letters sizes ⟨(fun empty => nomatch empty), trivial⟩
  · exact (checkedWordCircuit_output machine entry letters sizes).symm

private theorem checkedWordCircuit_fits (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) (sizes : Bool → ℕ)
    (arguments : {arguments : ∀ name : Empty, (Empty.elim name : EncodedDomain.{0, 0} Bool).Carrier sizes // True}) :
    ∃ result : (checkedWordCircuitDomain Symbol State).Carrier sizes,
      checkedWordProgramNetwork Symbol State sizes result = checkedWordCircuit machine entry letters (sizes false) (sizes true) :=
  ⟨(checkedWordImplementation machine entry letters).compute sizes arguments,
    checkedWordImplementation_correct machine entry letters sizes arguments⟩

/-- Construct the complete verifier circuit, including letter-code guards.
The mathematical specification is the ordinary `checkedWordCircuit` network. -/
noncomputable def checkedWordProgram (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) : Computation Bool Empty :=
  specificationBy Empty.elim (checkedWordCircuitDomain Symbol State) (fun _ _ => True)
    (checkedWordProgramNetwork Symbol State)
    (fun sizes _ => checkedWordCircuit machine entry letters (sizes false) (sizes true))
    (checkedWordCircuit_fits machine entry letters)

theorem checkedWordProgram_realizable (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) : (checkedWordProgram machine entry letters).Realizable := by
  apply (checkedWordImplementation_realizable machine entry letters).specificationBy
    (checkedWordProgramNetwork Symbol State)
    (fun sizes _ => checkedWordCircuit machine entry letters (sizes false) (sizes true))
    (checkedWordCircuit_fits machine entry letters) (fun _ => programValue_injective)
  intro sizes arguments allowed
  exact checkedWordImplementation_correct machine entry letters sizes ⟨arguments, allowed⟩

theorem checkedWordProgram_correct (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) (sizes : Bool → ℕ) (arguments : (checkedWordProgram machine entry letters).Arguments sizes) :
    checkedWordProgramNetwork Symbol State sizes ((checkedWordProgram machine entry letters).compute sizes ⟨arguments, trivial⟩) =
      checkedWordCircuit machine entry letters (sizes false) (sizes true) := by
  simp only [checkedWordProgram, specificationBy_correct]

/-- Includes canonical size-input preparation, TM0 execution, and serialized
output extraction for every mathematical time allowance and word length. -/
theorem checkedWordProgram_polynomialTime (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) :
    PolynomialTime (checkedWordProgram machine entry letters).inputWord (checkedWordProgram machine entry letters).outputWord
      (checkedWordProgram machine entry letters).result :=
  (checkedWordProgram_realizable machine entry letters).polynomialTime

/-- Exact number of external one-hot word-input bits. -/
noncomputable def verifierInputBits : MvPolynomial Bool ℕ :=
  MvPolynomial.X true * MvPolynomial.C (Fintype.card Letter)

omit [Inhabited Symbol] [Inhabited State] in
theorem checkedWord_wireCount :
    verifierInputBits + checkedWordGateCount Symbol State = checkedGuardWires (wordCircuitWires Symbol State) := by
  simp only [verifierInputBits, checkedWordGateCount, checkedGuardWires, wordCircuitWires, wordPreparedWires]
  ring

omit [Inhabited Symbol] [Inhabited State] in
/-- The checked constructor and ordinary evaluator share one circuit codec. -/
theorem checkedWordCircuitDomain_equal :
    Circuit.networkDomain verifierInputBits (checkedWordGateCount Symbol State) = checkedWordCircuitDomain Symbol State := by
  simp only [Circuit.networkDomain, checkedWordCircuitDomain, checkedWord_wireCount]

end Polytime2.Complexity.CookLevin
