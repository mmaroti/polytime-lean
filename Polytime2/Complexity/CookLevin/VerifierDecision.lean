import Polytime2.Complexity.CookLevin.VerifierEvaluation
import Polytime2.Complexity.CookLevin.UniformVerifier
import Polytime2.Complexity.CookLevin.WordAssignment

/-! # High-level execution of a polynomially bounded word verifier

The input is an ordinary external-letter array. Its one-hot assignment is
prepared using finite tests, and the existing uniform circuit constructor and
array evaluator return the verifier answer. The allowance is derived from a
fixed polynomial internally.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Complexity.CookLevin

open Turing Circuit EncodedDomain Polytime2.Computation

variable {Symbol State : Type} [Inhabited Symbol] [Inhabited State]
variable [Fintype Symbol] [Fintype State]

private noncomputable def inputBitCount : MvPolynomial Unit ℕ :=
  MvPolynomial.X () * MvPolynomial.C (Fintype.card Letter)

private theorem inputBitCount_equal (timeBound : Polynomial ℕ) (sizes : Unit → ℕ) :
    MvPolynomial.eval (SizeSubstitution.assignment (verifierSizePolynomials timeBound) sizes) verifierInputBits =
      MvPolynomial.eval sizes inputBitCount := by
  simp [verifierInputBits, inputBitCount, verifierSizes_length]

private noncomputable def uniformBitEvaluation (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) (timeBound : Polynomial ℕ) : Computation Unit Unit :=
  (((verifierEvaluation machine entry letters).substitute (verifierSizePolynomials timeBound)).reinterpretInputs
    (fun _ => booleans.arrayOfLength inputBitCount)
    (fun _ sizes bits index => bits (index.cast (inputBitCount_equal timeBound sizes)))
    (fun _ _ => True) (by intros; trivial)).reinterpretOutput booleans (fun _ value => value)

private theorem uniformBitEvaluation_realizable (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) (timeBound : Polynomial ℕ) :
    (uniformBitEvaluation machine entry letters timeBound).Realizable := by
  have prepared := ((verifierEvaluation_realizable machine entry letters).substitute
    (verifierSizePolynomials timeBound)).reinterpretInputs (fun _ => booleans.arrayOfLength inputBitCount)
    (fun _ sizes bits index => bits (index.cast (inputBitCount_equal timeBound sizes)))
    (by
      intro name sizes
      simp [Computation.substitute, verifierEvaluation_inputDomains, width, substitute_width,
        verifierInputBits, inputBitCount, verifierSizes_length])
    (by
      intro name sizes bits
      simp only [Computation.substitute, verifierEvaluation_inputDomains]
      rw [substitute_encode_bits, WordBits.boolean_arrayOfLength_bits, WordBits.boolean_arrayOfLength_bits]
      exact List.ofFn_congr (inputBitCount_equal timeBound sizes).symm bits)
    (fun _ _ => True) (by intros; trivial)
  apply prepared.reinterpretOutput booleans (fun _ value => value)
  · intro sizes
    simp [reinterpretInputs, Computation.substitute, verifierEvaluation_outputDomain, width, substitute_width]
  · intro sizes value
    simp only [reinterpretInputs, Computation.substitute, verifierEvaluation_outputDomain]
    simp [substitute_encode_bits, WordBits.boolean_bits]

/-- Run the bounded verifier on an ordinary letter array at its actual length. -/
noncomputable def verifierDecision (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) (timeBound : Polynomial ℕ) : Computation Unit Unit :=
  (wordAssignment (MvPolynomial.X ())).followedBy
    (uniformBitEvaluation machine entry letters timeBound) rfl (by intros; trivial)

theorem verifierDecision_realizable (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) (timeBound : Polynomial ℕ) :
    (verifierDecision machine entry letters timeBound).Realizable :=
  (wordAssignment_realizable (MvPolynomial.X ())).followedBy
    (uniformBitEvaluation_realizable machine entry letters timeBound) rfl (by intros; trivial)

/-- The high-level computation returns the original verifier's answer on every
letter array, including the empty word. The runtime allowance is internal. -/
theorem verifierDecision_correct (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) (timeBound : Polynomial ℕ) (verify : Word → Bool)
    (runs : ∀ word, Internal.Runs machine entry letters word [Sum.inl (verify word)] (timeBound.eval word.length))
    (sizes : Unit → ℕ) (arguments : (verifierDecision machine entry letters timeBound).Arguments sizes) :
    (verifierDecision machine entry letters timeBound).compute sizes ⟨arguments, trivial⟩ =
      verify (List.ofFn (arguments ())) := by
  let actual := SizeSubstitution.assignment (verifierSizePolynomials timeBound) sizes
  have sameLength : MvPolynomial.eval sizes (MvPolynomial.X ()) = actual true := by
    simp [actual, verifierSizes_length]
  let word : Fin (actual true) → Letter := fun position => arguments () (position.cast sameLength.symm)
  have actualRuns : ∀ source : Fin (actual true) → Letter,
      Internal.Runs machine entry letters (List.ofFn source) [Sum.inl (verify (List.ofFn source))] (actual false) := by
    intro source
    simpa only [List.length_ofFn, actual, verifierSizes_time, verifierSizes_length] using runs (List.ofFn source)
  have accepted := verifierEvaluation_onWord machine entry letters actual verify actualRuns word
  change (verifierEvaluation machine entry letters).compute actual
    ⟨(fun _ index => (wordAssignment (MvPolynomial.X ())).compute sizes ⟨arguments, trivial⟩
      (index.cast (inputBitCount_equal timeBound sizes))), trivial⟩ = _
  have sameBits : (fun _ : Unit => fun index : Fin (MvPolynomial.eval actual verifierInputBits) =>
      (wordAssignment (MvPolynomial.X ())).compute sizes ⟨arguments, trivial⟩
        (index.cast (inputBitCount_equal timeBound sizes))) =
      (fun _ : Unit => fun index : Fin (MvPolynomial.eval actual verifierInputBits) =>
        encodeWordBits word (index.cast (by simp [verifierInputBits]))) := by
    funext singleton index
    rw [wordAssignment_correct]
    change @Eq Bool _ _
    have transported := (encodeWordBits_cast sameLength (arguments ())
      (index.cast (by simp [verifierInputBits]))).symm
    refine Eq.trans ?_ transported
    apply congrArg (encodeWordBits (arguments ()))
    apply Fin.ext
    rfl
  rw [sameBits]
  exact accepted.trans (congrArg verify (List.ofFn_congr sameLength (arguments ())).symm)

/-- A polynomial-time word verifier can be called as a total high-level
computation on ordinary letter arrays, using the existing canonical codec. -/
theorem wordVerifier_realizable (verify : Word → Bool) (ready : PolynomialTime id encodeBool verify) :
    (Computation.mk (fun _ : Unit => letterDomain.array ()) booleans (fun _ _ => True)
      (fun _ arguments => verify (List.ofFn (arguments.val ())))).Realizable := by
  obtain ⟨Symbol, finiteSymbols, inhabitedSymbols, State, finiteStates, inhabitedStates,
    letters, machine, entry, timeBound, _nonblank, executes⟩ := ready
  let _ : Fintype Symbol := finiteSymbols
  let _ : Inhabited Symbol := inhabitedSymbols
  let _ : Fintype State := finiteStates
  let _ : Inhabited State := inhabitedStates
  have runs : ∀ word, Internal.Runs machine entry letters word [Sum.inl (verify word)] (timeBound.eval word.length) := by
    intro word
    simpa only [id_eq, encodeBool] using (executes word).1
  have source := (verifierDecision_realizable machine entry letters timeBound).reinterpretInputs
    (fun _ : Unit => letterDomain.array ()) (fun _ sizes => arrayParameterEquiv letterDomain () sizes)
    (by intros; rfl) (fun _ sizes value => array_X_encode_bits letterDomain () sizes value)
    (fun _ _ => True) (by intros; trivial)
  apply source.withSpecification (fun _ _ => True) _ (by intros; trivial)
  intro sizes arguments accepted
  change (verifierDecision machine entry letters timeBound).compute sizes
    ⟨(fun _ => arrayParameterEquiv letterDomain () sizes (arguments ())), trivial⟩ = _
  rw [verifierDecision_correct machine entry letters timeBound verify runs]
  exact congrArg verify (List.ofFn_congr (MvPolynomial.eval_X (f := sizes) ()).symm (arguments ())).symm

end Polytime2.Complexity.CookLevin
