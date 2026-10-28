import Polytime2.Complexity.CookLevin.WordGateProgram

/-! # Canonical construction and serialization of word-input circuits

The public answer is the ordinary mathematical network. The canonical output
contains the complete gate array and the actual output wire coordinate.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Complexity.CookLevin

open Turing Circuit EncodedDomain Polytime2.Computation

variable {Symbol State : Type} [Inhabited Symbol] [Inhabited State]
variable [Fintype Symbol] [Fintype State]

/-- Offset of the acceptance output after the prepared word-input wires. -/
noncomputable def wordCoreOutputOffset (Symbol State : Type) [Fintype Symbol] [Fintype State] :
    MvPolynomial Bool ℕ :=
  MvPolynomial.rename (fun _ : Unit => false)
    (MvPolynomial.X () * layoutLayerGates Symbol State + 5 * observationCount State)

private theorem coreGateCount_eq : wordCoreGateCount Symbol State = wordCoreOutputOffset Symbol State + 1 := by
  simp only [wordCoreGateCount, wordCoreOutputOffset, disjunctionGateCount, map_add, map_mul, map_one, map_ofNat]
  ring

/-- Exact output reference of the mathematical word-input circuit. -/
theorem wordCircuit_output (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) (sizes : Bool → ℕ) :
    (wordCircuit machine entry letters (sizes false) (sizes true)).2 =
      MvPolynomial.eval sizes (wordPreparedWires + wordCoreOutputOffset Symbol State) := by
  have original := acceptanceCircuit_output machine (letters (Sum.inl true)) (sizes ∘ (fun _ : Unit => false))
  dsimp only [Function.comp_apply] at original
  have outputEqual : (acceptanceCircuit machine (letters (Sum.inl true)) (sizes false)).2 =
      (2 * (2 * sizes false) + 1) * cellWidth Symbol State +
        MvPolynomial.eval sizes (wordCoreOutputOffset Symbol State) := by
    rw [original]
    simp only [wordCoreOutputOffset, MvPolynomial.eval_rename, layoutWires, layoutWidth, layoutPositions,
      map_add, map_mul, map_ofNat, map_one, MvPolynomial.eval_X, MvPolynomial.eval_C, Function.comp_apply]
    ring
  change spliceNames ((2 * (2 * sizes false) + 1) * cellWidth Symbol State)
    (sizes true * Fintype.card Letter + 2)
    (wiringLayer (sizes true * Fintype.card Letter)
      (initialChoices (2 * sizes false) (sizes true) entry letters)).2
    (acceptanceCircuit machine (letters (Sum.inl true)) (sizes false)).2 = _
  rw [outputEqual]
  unfold spliceNames
  rw [dif_neg (by omega)]
  simp only [wordPreparedWires, map_add, map_mul, map_ofNat, MvPolynomial.eval_X, MvPolynomial.eval_C]
  omega

/-- Canonical complete gate array and output reference for the word circuit. -/
noncomputable def wordCircuitDomain (Symbol State : Type) [Fintype Symbol] [Fintype State] : EncodedDomain Bool :=
  ((gateDomain (wordPreparedWires + wordCoreGateCount Symbol State)).arrayOfLength
    (2 + wordCoreGateCount Symbol State)).prod
    (arrayPosition (wordPreparedWires + wordCoreGateCount Symbol State))

/-- Forget only canonical storage bounds, retaining the actual mathematical network. -/
noncomputable def wordProgramNetwork (Symbol State : Type) [Fintype Symbol] [Fintype State]
    (sizes : Bool → ℕ) (program : (wordCircuitDomain Symbol State).Carrier sizes) : Network :=
  programValue program

theorem wordCircuitOutput_fits (sizes : Bool → ℕ) :
    MvPolynomial.eval sizes (wordPreparedWires + wordCoreOutputOffset Symbol State) <
      MvPolynomial.eval sizes (wordPreparedWires + wordCoreGateCount Symbol State) := by
  rw [coreGateCount_eq]
  simp only [map_add, map_one]
  omega


private noncomputable def wordImplementation (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) : Computation Bool Empty where
  inputDomains := Empty.elim
  outputDomain := wordCircuitDomain Symbol State
  precondition _ _ := True
  compute sizes arguments := ((wordGateProgram machine entry letters).compute sizes arguments,
    ⟨MvPolynomial.eval sizes (wordPreparedWires + wordCoreOutputOffset Symbol State), wordCircuitOutput_fits sizes⟩)

private theorem wordImplementation_realizable (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) : (wordImplementation machine entry letters).Realizable := by
  have output := (wirePolynomial_realizable (wordPreparedWires + wordCoreOutputOffset Symbol State)
    (wordPreparedWires + wordCoreGateCount Symbol State)).onResults
      (Empty.elim : Empty → EncodedDomain Bool) (fun _ _ => True) (fun empty => nomatch empty)
      (by intro sizes arguments; exact wordCircuitOutput_fits sizes) (fun empty => nomatch empty)
  exact (wordGateProgram_realizable machine entry letters).prodMk output

private theorem wordImplementation_correct (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) (sizes : Bool → ℕ)
    (arguments : {arguments : (wordImplementation machine entry letters).Arguments sizes // True}) :
    wordProgramNetwork Symbol State sizes ((wordImplementation machine entry letters).compute sizes arguments) =
      wordCircuit machine entry letters (sizes false) (sizes true) := by
  rcases arguments with ⟨arguments, accepted⟩
  have unique : arguments = (fun empty => nomatch empty) := by funext empty; cases empty
  subst arguments
  apply Prod.ext
  · exact wordGateProgram_value machine entry letters sizes ⟨(fun empty => nomatch empty), trivial⟩
  · exact (wordCircuit_output machine entry letters sizes).symm

private theorem wordCircuit_fits (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) (sizes : Bool → ℕ)
    (arguments : {arguments : ∀ name : Empty, (Empty.elim name : EncodedDomain.{0, 0} Bool).Carrier sizes // True}) :
    ∃ result : (wordCircuitDomain Symbol State).Carrier sizes,
      wordProgramNetwork Symbol State sizes result = wordCircuit machine entry letters (sizes false) (sizes true) :=
  ⟨(wordImplementation machine entry letters).compute sizes arguments,
    wordImplementation_correct machine entry letters sizes arguments⟩

/-- Construct the full word-input circuit, specified as an ordinary network. -/
noncomputable def wordProgram (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) : Computation Bool Empty :=
  specificationBy Empty.elim (wordCircuitDomain Symbol State) (fun _ _ => True)
    (wordProgramNetwork Symbol State) (fun sizes _ => wordCircuit machine entry letters (sizes false) (sizes true))
    (wordCircuit_fits machine entry letters)

theorem wordProgram_realizable (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) : (wordProgram machine entry letters).Realizable := by
  apply (wordImplementation_realizable machine entry letters).specificationBy
    (wordProgramNetwork Symbol State) (fun sizes _ => wordCircuit machine entry letters (sizes false) (sizes true))
    (wordCircuit_fits machine entry letters) (fun _ => programValue_injective)
  intro sizes arguments allowed
  exact wordImplementation_correct machine entry letters sizes ⟨arguments, allowed⟩

theorem wordProgram_correct (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) (sizes : Bool → ℕ) (arguments : (wordProgram machine entry letters).Arguments sizes) :
    wordProgramNetwork Symbol State sizes ((wordProgram machine entry letters).compute sizes ⟨arguments, trivial⟩) =
      wordCircuit machine entry letters (sizes false) (sizes true) := by
  simp only [wordProgram, specificationBy_correct]

/-- Word-level construction includes canonical size preparation, execution,
and extraction of the complete serialized circuit. -/
theorem wordProgram_polynomialTime (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) :
    PolynomialTime (wordProgram machine entry letters).inputWord (wordProgram machine entry letters).outputWord
      (wordProgram machine entry letters).result :=
  (wordProgram_realizable machine entry letters).polynomialTime

end Polytime2.Complexity.CookLevin
