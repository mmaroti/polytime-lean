import Polytime2.Complexity.CookLevin.CheckedWordProgram
import Polytime2.Circuit.EvaluateCircuit

/-! # Calling a bounded word verifier through its certified circuit

The input is an ordinary Boolean assignment in the word circuit's one-hot
input dimensions. Construction and evaluation are composed through their
shared network codec; neither tape layout nor scratch appears in this API.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Complexity.CookLevin

open Turing Circuit EncodedDomain Polytime2.Computation

variable {Symbol State : Type} [Inhabited Symbol] [Inhabited State]
variable [Fintype Symbol] [Fintype State]

private noncomputable def evaluationContinuation : Computation Bool (Unit ⊕ Unit) :=
  (evaluateCircuit verifierInputBits (checkedWordGateCount Symbol State)).onResults
    (Sum.elim (fun _ => booleans.arrayOfLength verifierInputBits)
      (fun _ => networkDomain verifierInputBits (checkedWordGateCount Symbol State))) (fun _ _ => True)
    (fun name _ arguments => match name with | false => arguments.val (.inr ()) | true => arguments.val (.inl ()))
    (by intros; trivial)

omit [Inhabited Symbol] [Inhabited State] in
private theorem evaluationContinuation_realizable : (evaluationContinuation (Symbol := Symbol) (State := State)).Realizable := by
  let context : Unit ⊕ Unit → EncodedDomain Bool :=
    Sum.elim (fun _ => booleans.arrayOfLength verifierInputBits)
      (fun _ => networkDomain verifierInputBits (checkedWordGateCount Symbol State))
  apply (evaluateCircuit_realizable verifierInputBits (checkedWordGateCount Symbol State)).onResults
  intro name
  cases name
  · exact Realizable.argument context (.inr ()) (fun _ _ => True)
  · exact Realizable.argument context (.inl ()) (fun _ _ => True)

private noncomputable def evaluationConstructor (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) : Computation Bool Unit where
  inputDomains _ := booleans.arrayOfLength verifierInputBits
  outputDomain := checkedWordCircuitDomain Symbol State
  precondition _ _ := True
  compute sizes _ := (checkedWordProgram machine entry letters).compute sizes
    ⟨(fun empty => nomatch empty), trivial⟩

private theorem evaluationConstructor_realizable (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) : (evaluationConstructor machine entry letters).Realizable := by
  have ready := (checkedWordProgram_realizable machine entry letters).onResults
    (fun _ : Unit => booleans.arrayOfLength verifierInputBits) (fun _ _ => True)
    (fun empty => nomatch empty) (by intros; trivial) (fun empty => nomatch empty)
  apply ready.withSpecification (fun _ _ => True) _ (by intros; trivial)
  intro sizes arguments accepted
  apply congrArg ((checkedWordProgram machine entry letters).compute sizes)
  apply Subtype.ext
  funext empty
  cases empty

/-- Construct and evaluate the checked verifier circuit on supplied input bits. -/
noncomputable def verifierEvaluation (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) : Computation Bool Unit :=
  (evaluationConstructor machine entry letters).letThen
    (evaluationContinuation (Symbol := Symbol) (State := State)) (by intros; rfl)
    checkedWordCircuitDomain_equal (by intros; trivial)

theorem verifierEvaluation_realizable (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) : (verifierEvaluation machine entry letters).Realizable :=
  (evaluationConstructor_realizable machine entry letters).letThen
    evaluationContinuation_realizable (by intros; rfl) checkedWordCircuitDomain_equal (by intros; trivial)

theorem verifierEvaluation_inputDomains (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) : (verifierEvaluation machine entry letters).inputDomains =
      fun _ => booleans.arrayOfLength verifierInputBits := rfl

theorem verifierEvaluation_outputDomain (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) : (verifierEvaluation machine entry letters).outputDomain = booleans := rfl

/-- The result is exactly the mathematical checked circuit on the supplied bits. -/
theorem verifierEvaluation_correct (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) (sizes : Bool → ℕ)
    (arguments : (verifierEvaluation machine entry letters).Arguments sizes) :
    (verifierEvaluation machine entry letters).compute sizes ⟨arguments, trivial⟩ =
      evaluate (sizes true * Fintype.card Letter)
        (checkedWordCircuit machine entry letters (sizes false) (sizes true))
        (fun index => arguments () (index.cast (by simp [verifierInputBits]))) := by
  let program : (checkedWordCircuitDomain Symbol State).Carrier sizes :=
    (checkedWordProgram machine entry letters).compute sizes ⟨(fun empty => nomatch empty), trivial⟩
  let converted : (networkDomain verifierInputBits (checkedWordGateCount Symbol State)).Carrier sizes :=
    (checkedWordCircuitDomain_equal (Symbol := Symbol) (State := State)).symm ▸ program
  change (evaluateCircuit verifierInputBits (checkedWordGateCount Symbol State)).compute sizes
    ⟨(fun name => match name with | false => converted | true => arguments ()), trivial⟩ = _
  rw [evaluateCircuit_correct]
  have castValue : programValue converted = programValue program :=
    programValue_transport sizes _ _ _ (checkedWord_wireCount (Symbol := Symbol) (State := State)).symm program
  rw [castValue]
  have correct := checkedWordProgram_correct machine entry letters sizes (fun empty => nomatch empty)
  change programValue program = _ at correct
  rw [correct]
  have castInputs (first second : ℕ) (same : first = second) (circuit : Network)
      (assignment : Fin first → Bool) :
      evaluate first circuit assignment = evaluate second circuit (fun index => assignment (index.cast same.symm)) := by
    cases same
    rfl
  exact castInputs _ _ (by simp [verifierInputBits]) _ (arguments ())

/-- On a canonical one-hot word, bounded circuit evaluation returns exactly
its certified verifier answer. -/
theorem verifierEvaluation_onWord (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) (sizes : Bool → ℕ) (verify : Word → Bool)
    (runs : ∀ word : Fin (sizes true) → Letter,
      Internal.Runs machine entry letters (List.ofFn word) [Sum.inl (verify (List.ofFn word))] (sizes false))
    (word : Fin (sizes true) → Letter) :
    (verifierEvaluation machine entry letters).compute sizes
      ⟨(fun _ index => encodeWordBits word (index.cast (by simp [verifierInputBits]))), trivial⟩ =
      verify (List.ofFn word) := by
  apply Bool.eq_iff_iff.mpr
  rw [verifierEvaluation_correct]
  simp only [Fin.cast_cast, Fin.cast_eq_self]
  rw [checkedWordCircuit_correct machine entry letters _ _ verify runs]
  constructor
  · rintro ⟨other, encoded, accepted⟩
    have same : other = word := encodeWordBits_injective encoded
    simpa only [same] using accepted
  · intro accepted
    exact ⟨word, rfl, accepted⟩

end Polytime2.Complexity.CookLevin
