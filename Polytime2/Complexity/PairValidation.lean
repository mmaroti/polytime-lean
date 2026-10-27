import Polytime2.Complexity.HeaderValidation
import Polytime2.Arrays.PositionArithmetic
import Polytime2.Arithmetic.SignedAddition

/-! # Payload bounds for self-delimiting word pairs

A unary header of length k consumes k + 1 letters. Its announced input field
fits precisely when 2 * k < the complete word length. All arithmetic widths
are internal and the missing-boundary scan count is rejected by the same test.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Complexity

open EncodedDomain Polytime2.Computation
open Polytime2.Computation.Realizable.Internal

private noncomputable def countFitsPair : Computation Unit Unit where
  inputDomains _ := bitVectors (MvPolynomial.X () + 1)
  outputDomain := booleans
  precondition _ _ := True
  compute sizes arguments := decide (2 * (arguments.val ()).toNat < sizes ())

private theorem countFitsPair_realizable : countFitsPair.Realizable := by
  let width : MvPolynomial Unit ℕ := MvPolynomial.X () + 1
  let computation := countFitsPair
  let magnitude := (integerOfMagnitude width).reinterpretInputs computation.inputDomains
    (fun _ _ value => value.toFin) (fun _ _ => True) (by intros; trivial)
  have magnitudeReady : magnitude.Realizable := (integerOfMagnitude_realizable width).reinterpretInputs
    computation.inputDomains (fun _ _ value => value.toFin)
    (by intros; rfl) (by intros; rfl) (fun _ _ => True) (by intros; trivial)
  let double := (integerAdd width).onResults (fun _ : Unit => binaryIntegers width)
    (fun _ _ => True) (fun _ _ arguments => arguments.val ()) (by intros; trivial)
  have doubleReady : double.Realizable := (integerAdd_realizable width).onArguments
    (fun _ : Unit => binaryIntegers width) (fun _ _ => True) (fun _ => ())
    (by intros; rfl) (by intros; trivial)
  let doubled := magnitude.followedBy double rfl (by intros; trivial)
  have doubledReady : doubled.Realizable := magnitudeReady.followedBy doubleReady rfl (by intros; trivial)
  let limit := (polynomialIntegerSize (MvPolynomial.X ())).followedBy
    (integerWidenTo width 1 (width + 1) rfl) rfl (by intros; trivial)
  have limitReady : limit.Realizable := (polynomialIntegerSize_realizable (MvPolynomial.X ())).followedBy
    (integerWidenTo_realizable width 1 (width + 1) rfl) rfl (by intros; trivial)
  have limitOnInputs := limitReady.onResults computation.inputDomains computation.precondition
    (fun empty => empty.elim) (by intros; trivial) (fun empty => empty.elim)
  have compared := (integerLess_realizable (width + 1)).onResults computation.inputDomains
    computation.precondition
    (fun choice sizes arguments => match choice with
      | false => doubled.compute sizes arguments
      | true => limit.compute sizes ⟨(fun empty => empty.elim), trivial⟩)
    (by intros; trivial) (by intro choice; cases choice; exact doubledReady; exact limitOnInputs)
  apply compared.withSpecification computation.precondition computation.compute (by intros; trivial)
  intro sizes arguments valid
  apply Bool.eq_iff_iff.mpr
  simp only [onResults, integerLess, decide_eq_true_eq]
  change ((arguments ()).toNat : ℤ) + (arguments ()).toNat <
      (MvPolynomial.eval sizes (MvPolynomial.X ()) : ℤ) ↔
    decide (2 * (arguments ()).toNat < sizes ()) = true
  simp only [MvPolynomial.eval_X, decide_eq_true_eq]
  omega

/-- Test whether the input field announced by the unary count fits in the
remaining word. A missing boundary fails, even before checking its letter. -/
noncomputable def pairPayloadFits : Computation Unit Unit where
  inputDomains := unaryHeaderBoundary.inputDomains
  outputDomain := booleans
  precondition _ _ := True
  compute sizes arguments := by
    classical
    exact decide (2 * (List.ofFn (arguments.val ())).findIdx
      (fun letter => decide (letter ≠ .inr 1)) < sizes ())

theorem pairPayloadFits_realizable : pairPayloadFits.Realizable := by
  let predicate : Letter → Bool := fun letter => decide (letter = .inr 1)
  have mapped := unaryCountFlags_realizable
  have counted := mapped.followedBy (firstFalse_realizable (MvPolynomial.X ())) rfl (by intros; trivial)
  have tested := counted.followedBy countFitsPair_realizable rfl (by intros; trivial)
  apply tested.withSpecification (fun _ _ => True) pairPayloadFits.compute (by intros; trivial)
  intro sizes arguments valid
  change decide (2 * ((firstFalse (MvPolynomial.X ())).compute sizes
    ⟨(fun _ index => predicate (arguments () index)), trivial⟩).toNat < sizes ()) = _
  rw [firstFalse_correct]
  have mapped : List.ofFn (fun index => predicate (arguments () index)) =
      (List.ofFn (arguments ())).map predicate := by rw [List.map_ofFn]; rfl
  rw [mapped, List.findIdx_map]
  apply Bool.eq_iff_iff.mpr
  simp only [pairPayloadFits, decide_eq_true_eq]
  have predicates : ((fun bit => !bit) ∘ predicate) =
      (fun letter : Letter => decide (letter ≠ .inr 1)) := by
    funext letter
    apply Bool.eq_iff_iff.mpr
    simp [predicate]
  rw [predicates]
  apply Iff.of_eq
  congr
  funext letter
  apply Bool.eq_iff_iff.mpr
  simp

/-- Decide whether the complete word is a valid input/witness pair. Header
letters, separators, and announced input length are all checked. -/
noncomputable def pairValid : Computation Unit Unit where
  inputDomains := unaryHeaderBoundary.inputDomains
  outputDomain := booleans
  precondition _ _ := True
  compute _ arguments := (decodePair (List.ofFn (arguments.val ()))).isSome

theorem pairValid_realizable : pairValid.Realizable := by
  let inputs := pairValid.inputDomains
  have combined := (booleanOperation_realizable (Parameter := Unit) (Argument := Bool)
    (fun flags => flags false && flags true)).onResults inputs (fun _ _ => True)
    (fun choice sizes arguments => match choice with
    | false => unaryHeaderValid.compute sizes arguments
    | true => pairPayloadFits.compute sizes arguments)
    (by intros; trivial) (by
      intro choice
      cases choice
      · exact unaryHeaderValid_realizable
      · exact pairPayloadFits_realizable)
  apply combined.withSpecification (fun _ _ => True) pairValid.compute (by intros; trivial)
  intro sizes arguments valid
  change (unaryHeaderValid.compute sizes ⟨arguments, trivial⟩ &&
    pairPayloadFits.compute sizes ⟨arguments, trivial⟩) = (decodePair (List.ofFn (arguments ()))).isSome
  have argumentsEta : arguments = fun _ => arguments () := by
    funext name
    cases name
    rfl
  rw [argumentsEta, unaryHeaderValid_correct]
  rw [decodePair_isSome]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [pairPayloadFits, decide_eq_true_eq, List.length_ofFn]
  apply Iff.of_eq
  congr <;> first
  | (funext letter; apply Bool.eq_iff_iff.mpr; simp)
  | simp

/-- Pair framing and announced payload bounds are checked in polynomial time
on every word, including truncated and malformed inputs. -/
theorem decodePair_isSome_polynomialTime :
    PolynomialTime id encodeBool (fun word => (decodePair word).isSome) :=
  pairValid_realizable.onWordDecision (fun word => (decodePair word).isSome)

end Polytime2.Complexity
