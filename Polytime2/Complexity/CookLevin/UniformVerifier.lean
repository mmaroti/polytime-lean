import Polytime2.Complexity.CookLevin.CheckedWordProgram
import Polytime2.Complexity.CookLevin.VerifierCircuit
import Polytime2.Computation.Substitution
import Mathlib.Algebra.MvPolynomial.Equiv

/-! # Uniform polynomial-time construction of verifier circuits

The sole public size is word length. A fixed verifier's polynomial time bound
is substituted internally into the checked-word constructor. Canonical size
preparation, machine execution, and serialized output extraction are included.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Complexity.CookLevin

open Turing Circuit EncodedDomain Polytime2.Computation

variable {Symbol State : Type} [Inhabited Symbol] [Inhabited State]
variable [Fintype Symbol] [Fintype State]

/-- The verifier time allowance and word length, both polynomial in length. -/
noncomputable def verifierSizePolynomials (timeBound : Polynomial ℕ) : Bool → MvPolynomial Unit ℕ :=
  fun isLength => if isLength then MvPolynomial.X () else timeBound.toMvPolynomial ()

theorem verifierSizes_time (timeBound : Polynomial ℕ) (sizes : Unit → ℕ) :
    SizeSubstitution.assignment (verifierSizePolynomials timeBound) sizes false = timeBound.eval (sizes ()) := by
  simp [SizeSubstitution.assignment, verifierSizePolynomials, MvPolynomial.eval_toMvPolynomial]

theorem verifierSizes_length (timeBound : Polynomial ℕ) (sizes : Unit → ℕ) :
    SizeSubstitution.assignment (verifierSizePolynomials timeBound) sizes true = sizes () := by
  simp [SizeSubstitution.assignment, verifierSizePolynomials]

/-- Construct a fixed verifier's checked circuit at the given word length. -/
noncomputable def verifierProgram (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) (timeBound : Polynomial ℕ) : Computation Unit Empty :=
  ((checkedWordProgram machine entry letters).substitute (verifierSizePolynomials timeBound)).onResults
    Empty.elim (fun _ _ => True) (fun empty => nomatch empty) (by intros; trivial)

/-- The canonical checked-circuit codec with its time parameter substituted. -/
theorem verifierProgram_outputDomain (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) (timeBound : Polynomial ℕ) :
    (verifierProgram machine entry letters timeBound).outputDomain =
      (checkedWordCircuitDomain Symbol State).substitute (verifierSizePolynomials timeBound) := rfl

/-- Read the ordinary network from the substituted canonical circuit codec. -/
noncomputable def verifierProgramNetwork (Symbol State : Type) [Fintype Symbol] [Fintype State]
    (timeBound : Polynomial ℕ) (sizes : Unit → ℕ)
    (program : ((checkedWordCircuitDomain Symbol State).substitute (verifierSizePolynomials timeBound)).Carrier sizes) : Network :=
  checkedWordProgramNetwork Symbol State (SizeSubstitution.assignment (verifierSizePolynomials timeBound) sizes) program

theorem verifierProgram_realizable (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) (timeBound : Polynomial ℕ) : (verifierProgram machine entry letters timeBound).Realizable := by
  exact ((checkedWordProgram_realizable machine entry letters).substitute (verifierSizePolynomials timeBound)).onResults
    Empty.elim (fun _ _ => True) (fun empty => nomatch empty) (by intros; trivial) (fun empty => nomatch empty)

/-- The emitted network is exactly the checked circuit at the verifier's
polynomial allowance and the supplied mathematical word length. -/
theorem verifierProgram_correct (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) (timeBound : Polynomial ℕ) (sizes : Unit → ℕ)
    (arguments : (verifierProgram machine entry letters timeBound).Arguments sizes) :
    verifierProgramNetwork Symbol State timeBound sizes
      ((verifierProgram machine entry letters timeBound).compute sizes ⟨arguments, trivial⟩) =
      checkedWordCircuit machine entry letters (timeBound.eval (sizes ())) (sizes ()) := by
  have correct := checkedWordProgram_correct machine entry letters
    (SizeSubstitution.assignment (verifierSizePolynomials timeBound) sizes) (fun empty => nomatch empty)
  calc
    verifierProgramNetwork Symbol State timeBound sizes
        ((verifierProgram machine entry letters timeBound).compute sizes ⟨arguments, trivial⟩) =
      checkedWordProgramNetwork Symbol State (SizeSubstitution.assignment (verifierSizePolynomials timeBound) sizes)
        ((checkedWordProgram machine entry letters).compute
          (SizeSubstitution.assignment (verifierSizePolynomials timeBound) sizes)
          ⟨(fun empty => nomatch empty), trivial⟩) := by
      apply congrArg (checkedWordProgramNetwork Symbol State
        (SizeSubstitution.assignment (verifierSizePolynomials timeBound) sizes))
      apply congrArg ((checkedWordProgram machine entry letters).compute
        (SizeSubstitution.assignment (verifierSizePolynomials timeBound) sizes))
      apply Subtype.ext
      funext name
      cases name
    _ = checkedWordCircuit machine entry letters (timeBound.eval (sizes ())) (sizes ()) := by
      simpa only [verifierSizes_time, verifierSizes_length] using correct

/-- Word-level execution includes preparation of the single unary length
parameter and extraction of the canonical serialized checked circuit. -/
theorem verifierProgram_polynomialTime (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) (timeBound : Polynomial ℕ) :
    PolynomialTime (verifierProgram machine entry letters timeBound).inputWord
      (verifierProgram machine entry letters timeBound).outputWord
      (verifierProgram machine entry letters timeBound).result :=
  (verifierProgram_realizable machine entry letters timeBound).polynomialTime

/-- Every polynomial-time word verifier admits a certified uniform circuit
constructor in the canonical codec. Its polynomial gate bound and acceptance
contract cover every Boolean assignment, including invalid letter codes. -/
theorem verifier_circuits_uniform (verify : Word → Bool) (ready : PolynomialTime id encodeBool verify) :
    ∃ (Symbol : Type) (finiteSymbols : Fintype Symbol) (inhabitedSymbols : Inhabited Symbol),
      let _ : Fintype Symbol := finiteSymbols
      let _ : Inhabited Symbol := inhabitedSymbols
      ∃ (State : Type) (finiteStates : Fintype State) (inhabitedStates : Inhabited State),
        let _ : Fintype State := finiteStates
        let _ : Inhabited State := inhabitedStates
        ∃ (letters : Letter ↪ Symbol) (machine : TM0.Machine Symbol State) (entry : State)
            (timeBound gateBound : Polynomial ℕ),
          (verifierProgram machine entry letters timeBound).Realizable ∧
          PolynomialTime (verifierProgram machine entry letters timeBound).inputWord
            (verifierProgram machine entry letters timeBound).outputWord
            (verifierProgram machine entry letters timeBound).result ∧
          ∀ (sizes : Unit → ℕ) (arguments : (verifierProgram machine entry letters timeBound).Arguments sizes),
            let circuit := verifierProgramNetwork Symbol State timeBound sizes
              ((verifierProgram machine entry letters timeBound).compute sizes ⟨arguments, trivial⟩)
            Circuit.Valid (sizes () * Fintype.card Letter) circuit ∧
            circuit.1.length ≤ gateBound.eval (sizes ()) ∧
            ∀ assignment : Fin (sizes () * Fintype.card Letter) → Bool,
              evaluate (sizes () * Fintype.card Letter) circuit assignment = true ↔
                ∃ word : Fin (sizes ()) → Letter,
                  encodeWordBits word = assignment ∧ verify (List.ofFn word) = true := by
  obtain ⟨Symbol, finiteSymbols, inhabitedSymbols, State, finiteStates, inhabitedStates,
    letters, machine, entry, timeBound, _nonblank, runs⟩ := ready
  let _ : Fintype Symbol := finiteSymbols
  let _ : Inhabited Symbol := inhabitedSymbols
  let _ : Fintype State := finiteStates
  let _ : Inhabited State := inhabitedStates
  refine ⟨Symbol, finiteSymbols, inhabitedSymbols, State, finiteStates, inhabitedStates,
    letters, machine, entry, timeBound,
    (circuitSizePolynomial (cellWidth Symbol State)).comp timeBound + wordGuardSizePolynomial,
    verifierProgram_realizable machine entry letters timeBound,
    verifierProgram_polynomialTime machine entry letters timeBound, ?_⟩
  intro sizes arguments
  dsimp only
  rw [verifierProgram_correct]
  refine ⟨checkedWordCircuit_valid machine entry letters _ _, ?_, ?_⟩
  · simp only [Polynomial.eval_add, Polynomial.eval_comp, circuitSizePolynomial_eval,
      wordGuardSizePolynomial, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one]
    exact checkedWordCircuit_bound machine entry letters _ _
  · apply checkedWordCircuit_correct
    intro word
    simpa only [id_eq, List.length_ofFn, encodeBool] using (runs (List.ofFn word)).1

end Polytime2.Complexity.CookLevin
