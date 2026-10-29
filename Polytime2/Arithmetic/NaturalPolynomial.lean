import Polytime2.Arrays.PositionArithmetic
import Polytime2.Arithmetic.SignedMultiplyAdd
import Polytime2.Computation.RecordArguments

/-! # Bounded natural polynomial evaluation

A fixed Mathlib polynomial reads mathematical sizes and bounded runtime natural
coordinates. The result is its exact natural value in a requested interval;
admissibility is only membership in that interval. Intermediate signed words
and their polynomial widths are derived privately from the expression.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain Realizable.Internal

variable {Parameter Argument : Type} [Fintype Parameter] [Fintype Argument]

/-- Evaluate a fixed natural polynomial. Left variables are mathematical sizes;
right variables are runtime coordinates in their given intervals. The sole
precondition says that the exact polynomial value fits the output interval. -/
noncomputable def polynomialPosition (bounds : Argument → MvPolynomial Parameter ℕ)
    (expression : MvPolynomial (Parameter ⊕ Argument) ℕ) (limit : MvPolynomial Parameter ℕ) :
    Computation Parameter Argument where
  inputDomains name := arrayPosition (bounds name)
  outputDomain := arrayPosition limit
  precondition sizes arguments :=
    MvPolynomial.eval (Sum.elim sizes (fun name => (arguments name).val)) expression < MvPolynomial.eval sizes limit
  compute sizes arguments := ⟨MvPolynomial.eval (Sum.elim sizes (fun name => (arguments.val name).val)) expression,
    arguments.property⟩

private def Certified (inputs : Argument → EncodedDomain Parameter)
    (value : ∀ sizes, (∀ name, (inputs name).Carrier sizes) → ℕ) : Prop :=
  ∃ (width : MvPolynomial Parameter ℕ)
    (compute : ∀ sizes, {_arguments : ∀ name, (inputs name).Carrier sizes // True} →
      (binaryIntegers width).Carrier sizes),
    (Computation.mk inputs (binaryIntegers width) (fun _ _ => True) compute).Realizable ∧
      ∀ sizes arguments, (compute sizes ⟨arguments, trivial⟩).val = (value sizes arguments : ℤ)

private theorem certified_size (inputs : Argument → EncodedDomain Parameter)
    (value : MvPolynomial Parameter ℕ) : Certified inputs (fun sizes _ => MvPolynomial.eval sizes value) := by
  let computation := (polynomialIntegerSize value).onResults inputs (fun _ _ => True)
    (fun empty => nomatch empty) (by intros; trivial)
  have ready : computation.Realizable := (polynomialIntegerSize_realizable value).onResults
    inputs (fun _ _ => True) (fun empty => nomatch empty) (by intros; trivial) (fun empty => nomatch empty)
  exact ⟨value + 1, computation.compute, ready, by intros; rfl⟩

private theorem certified_multiplyAdd (inputs : Argument → EncodedDomain Parameter)
    (first coefficient second : ∀ sizes, (∀ name, (inputs name).Carrier sizes) → ℕ)
    (firstReady : Certified inputs first) (coefficientReady : Certified inputs coefficient)
    (secondReady : Certified inputs second) :
    Certified inputs (fun sizes arguments => first sizes arguments + coefficient sizes arguments * second sizes arguments) := by
  obtain ⟨firstWidth, firstValue, firstReady, firstCorrect⟩ := firstReady
  obtain ⟨coefficientWidth, coefficientValue, coefficientReady, coefficientCorrect⟩ := coefficientReady
  obtain ⟨secondWidth, secondValue, secondReady, secondCorrect⟩ := secondReady
  let width := firstWidth + coefficientWidth + secondWidth
  have first := firstReady.followedBy (integerWidenTo_realizable firstWidth (coefficientWidth + secondWidth) width
    (by dsimp [width]; ring)) rfl (by intros; trivial)
  have coefficient := coefficientReady.followedBy (integerWidenTo_realizable coefficientWidth (firstWidth + secondWidth) width
    (by dsimp [width]; ring)) rfl (by intros; trivial)
  have second := secondReady.followedBy (integerWidenTo_realizable secondWidth (firstWidth + coefficientWidth) width
    (by dsimp [width]; ring)) rfl (by intros; trivial)
  let values (name : Fin 3) sizes (arguments : {arguments : ∀ name, (inputs name).Carrier sizes // True}) :
      (binaryIntegers width).Carrier sizes := match name with
    | 0 => (integerWidenTo firstWidth (coefficientWidth + secondWidth) width (by dsimp [width]; ring)).compute
        sizes ⟨(fun _ => firstValue sizes arguments), trivial⟩
    | 1 => (integerWidenTo coefficientWidth (firstWidth + secondWidth) width (by dsimp [width]; ring)).compute
        sizes ⟨(fun _ => coefficientValue sizes arguments), trivial⟩
    | 2 => (integerWidenTo secondWidth (firstWidth + coefficientWidth) width (by dsimp [width]; ring)).compute
        sizes ⟨(fun _ => secondValue sizes arguments), trivial⟩
  let computation := (integerMultiplyAdd width).onResults inputs (fun _ _ => True) values (by intros; trivial)
  have ready : computation.Realizable := (integerMultiplyAdd_realizable width).onResults
    inputs (fun _ _ => True) values (by intros; trivial) (by intro name; fin_cases name; exact first; exact coefficient; exact second)
  refine ⟨2 * width + 1, computation.compute, ready, ?_⟩
  intro sizes arguments
  change (firstValue sizes ⟨arguments, trivial⟩).val +
    (coefficientValue sizes ⟨arguments, trivial⟩).val * (secondValue sizes ⟨arguments, trivial⟩).val = _
  rw [firstCorrect, coefficientCorrect, secondCorrect, Nat.cast_add, Nat.cast_mul]

private theorem certified_eval (bounds : Argument → MvPolynomial Parameter ℕ)
    (expression : MvPolynomial (Parameter ⊕ Argument) ℕ) :
    Certified (fun name => arrayPosition (bounds name))
      (fun sizes arguments => MvPolynomial.eval (Sum.elim sizes (fun name => (arguments name).val)) expression) := by
  let inputs := fun name => arrayPosition (bounds name)
  have variableReady (name : Parameter ⊕ Argument) : Certified inputs
      (fun sizes arguments => Sum.elim sizes (fun name => (arguments name).val) name) := by
    cases name with
    | inl parameter => simpa using certified_size inputs (MvPolynomial.X parameter)
    | inr argument =>
      let computation := (positionInteger (bounds argument) 0 (bounds argument + 1) (by ring)).onResults
        inputs (fun _ _ => True) (fun _ _ arguments => arguments.val argument) (by intros; trivial)
      have ready : computation.Realizable := (positionInteger_realizable (bounds argument) 0 (bounds argument + 1)
        (by ring)).onResults inputs (fun _ _ => True) (fun _ _ arguments => arguments.val argument)
          (by intros; trivial) (fun _ => Realizable.argument inputs argument (fun _ _ => True))
      exact ⟨bounds argument + 1, computation.compute, ready, by intros; rfl⟩
  induction expression using MvPolynomial.induction_on with
  | C constant => simpa using certified_size inputs (MvPolynomial.C constant)
  | add first second firstReady secondReady =>
    simpa only [map_add, map_one, one_mul] using certified_multiplyAdd inputs _ _ _
      firstReady (certified_size inputs 1) secondReady
  | mul_X expression name ready =>
    simpa only [map_mul, MvPolynomial.eval_X, map_zero, zero_add] using certified_multiplyAdd inputs _ _ _
      (certified_size inputs 0) ready (variableReady name)

theorem polynomialPosition_realizable (bounds : Argument → MvPolynomial Parameter ℕ)
    (expression : MvPolynomial (Parameter ⊕ Argument) ℕ) (limit : MvPolynomial Parameter ℕ) :
    (polynomialPosition bounds expression limit).Realizable := by
  obtain ⟨width, value, ready, correct⟩ := certified_eval bounds expression
  let computation := polynomialPosition bounds expression limit
  have widened := ready.followedBy (integerWiden_realizable width (limit + 1)) rfl (by intros; trivial)
  have allowed := widened.withPrecondition computation.precondition (by intros; trivial)
  have narrowed := allowed.followedBy (integerNarrowAtWidths_realizable (width + (limit + 1)) (limit + 1)
    (by intro sizes; simp only [map_add]; omega)) rfl (by
      intro sizes arguments fits
      change (value sizes ⟨arguments, trivial⟩).val.natAbs < 2 ^ MvPolynomial.eval sizes (limit + 1)
      rw [correct, Int.natAbs_natCast]
      simp only [map_add, map_one]
      exact fits.trans_le ((Nat.le_succ _).trans Nat.lt_two_pow_self.le))
  have magnitude := narrowed.followedBy (integerMagnitude_realizable (limit + 1)) rfl (by intros; trivial)
  exact magnitude.withEncodedOutput computation.outputDomain computation.compute (by intros; rfl) (by
    intro sizes arguments
    apply congrArg CallingConvention.tape
    apply arrayPosition_binary_bits limit sizes
    change (value sizes ⟨arguments.val, trivial⟩).val.natAbs = _
    rw [correct, Int.natAbs_natCast]
    rfl)

end Polytime2.Computation
