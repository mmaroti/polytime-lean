import Polytime2.Complexity.RawWords
import Polytime2.Computation.RecordArguments
import Polytime2.Arrays.Tabulate
import Polytime2.Arrays.Operations
import Polytime2.Primitives.FiniteOperations

/-! # Total word execution on ordinary letter arrays

Application parsers receive ordinary finite arrays of external letters. The
three physical Boolean tracks are decoded here using a fixed finite operation
and certified array lookup and tabulation. No application tape convention is
introduced.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Complexity

open EncodedDomain Polytime2.Computation

/-- Canonical fixed alphabet codec, lifted to runtime word lengths. -/
noncomputable def letterDomain : EncodedDomain Unit :=
  (fixed (Parameter := Empty) (Fintype.equivFin Letter)).constant

/-- Apply a specialization-fixed Boolean test to an external letter. -/
noncomputable def letterTest (test : Letter → Bool) : Computation Unit Unit :=
  unaryMap letterDomain booleans (fun _ _ => True) (fun _ letter => test letter.val)

/-- A letter test is a finite table, independent of the runtime word length. -/
theorem letterTest_realizable (test : Letter → Bool) : (letterTest test).Realizable := by
  have raw := (finitePredicate_realizable (fixed (Fintype.equivFin Letter)) test).withConstantSizes
    (Parameter := Unit)
  exact raw.reinterpretOutput (booleans : EncodedDomain Unit) (fun _ value => value)
    (by intros; simp [withConstantSizes, finitePredicate, finiteOperation, booleans, width])
    (by intros; simp [withConstantSizes, finitePredicate, finiteOperation, constant_encode_bits,
      booleans, fixed_encode_bits])

private def decodeBits (bits : Fin 3 → Bool) : Letter :=
  if bits 2 then .inr 2 else
    if bits 1 then (if bits 0 then .inr 1 else .inr 0) else .inl (bits 0)

private theorem decodeBits_letterBits (letter : Letter) :
    decodeBits (letterBits letter) = letter := by
  revert letter
  decide

private noncomputable def lettersFromBits : Computation Unit (Fin 3) where
  inputDomains _ := booleans.array ()
  outputDomain := letterDomain.array ()
  precondition _ _ := True
  compute _ arguments index := decodeBits (fun bit => arguments.val bit index)

private theorem lettersFromBits_realizable : lettersFromBits.Realizable := by
  classical
  have raw := (finiteOperation_realizable (fun _ : Fin 3 => (booleans : EncodedDomain Empty))
    (fixed (Fintype.equivFin Letter)) decodeBits).withConstantSizes (Parameter := Unit)
  have normalized := raw.reinterpretInputs (fun _ : Fin 3 => (booleans : EncodedDomain Unit))
    (fun _ _ value => value)
    (by intros; simp [withConstantSizes, finiteOperation, booleans, width])
    (by intros; simp [withConstantSizes, finiteOperation, constant_encode_bits, booleans, fixed_encode_bits])
    (fun _ _ => True) (by intros; trivial)
  let length : MvPolynomial Unit ℕ := MvPolynomial.X ()
  let inputs := fun _ : Fin 3 => (booleans : EncodedDomain Unit).arrayOfLength length
  let operation (sizes : Unit → ℕ) (arguments : ∀ name, (inputs name).Carrier sizes)
      (index : Fin (MvPolynomial.eval sizes length)) := decodeBits (fun bit => arguments bit index)
  let step := arrayTransformStep inputs (arrayPosition length) letterDomain operation
  have lookup (bit : Fin 3) :=
    (Realizable.Internal.arrayLookupWithIndex_realizable booleans (arrayPosition length)
      (fun _ index => index.val) (arrayPosition_value length) length).onArguments
      step.inputDomains (fun _ _ => True)
      (fun choice => match choice with | false => .inr () | true => .inl bit)
      (by intro choice; cases choice <;> rfl)
      (by intro sizes arguments; exact (arguments.val (.inr ())).isLt)
  have stepReady : step.Realizable := normalized.onResults step.inputDomains (fun _ _ => True)
    (fun bit _ arguments => arguments.val (.inl bit) (arguments.val (.inr ())))
    (by intros; trivial) lookup
  have tabulated := arrayTabulate_realizable inputs letterDomain length operation stepReady
  have prepared := tabulated.reinterpretInputs lettersFromBits.inputDomains
    (fun _ sizes => arrayParameterEquiv booleans () sizes)
    (by intros; rfl)
    (fun _ sizes value => array_X_encode_bits booleans () sizes value)
    (fun _ _ => True) (by intros; trivial)
  exact prepared.reinterpretOutput (letterDomain.array ())
    (fun sizes => (arrayParameterEquiv letterDomain () sizes).symm)
    (arrayParameter_width letterDomain ())
    (fun sizes value => array_X_encode_bits letterDomain () sizes _)

end Polytime2.Complexity

namespace Polytime2.Computation.Realizable

open EncodedDomain Complexity

/-- Execute on ordinary letter arrays on every raw word and format the output
bits with fixed finite memory, without an input framing precondition. -/
theorem onWordFormattedOutput {Memory : Type} [Fintype Memory] (outputDomain : EncodedDomain Unit)
    (operation : (size : ℕ) → (Fin size → Letter) → outputDomain.Carrier (fun _ => size))
    (format : Memory → Bool → Memory × Letter) (initialMemory : Memory)
    (ready : (Computation.mk (fun _ : Unit => letterDomain.array ()) outputDomain
      (fun _ _ => True) (fun sizes arguments => operation (sizes ()) (arguments.val ()))).Realizable) :
    PolynomialTime id id (fun word =>
      formatBits format initialMemory (ArrayEncoding.bits (outputDomain.encode (fun _ => word.length)
        (operation word.length (fun index => word[index]))))) := by
  have composed := Complexity.lettersFromBits_realizable.followedBy ready rfl (by intros; trivial)
  have raw := onRawWordFormattedOutput outputDomain
    (fun size arrays => operation size (fun index => Complexity.decodeBits (fun bit => arrays bit index)))
    format initialMemory composed
  convert raw using 1
  funext word
  congr 4
  funext index
  exact (Complexity.decodeBits_letterBits word[index]).symm

/-- Canonical binary output specializes the finite-memory formatter. -/
theorem onWordOutput (outputDomain : EncodedDomain Unit)
    (operation : (size : ℕ) → (Fin size → Letter) → outputDomain.Carrier (fun _ => size))
    (ready : (Computation.mk (fun _ : Unit => letterDomain.array ()) outputDomain
      (fun _ _ => True) (fun sizes arguments => operation (sizes ()) (arguments.val ()))).Realizable) :
    PolynomialTime id id (fun word =>
      (ArrayEncoding.bits (outputDomain.encode (fun _ => word.length)
        (operation word.length (fun index => word[index])))).map Sum.inl) := by
  have formatted := onWordFormattedOutput outputDomain operation
    (fun _ : Unit => fun bit => ((), Sum.inl bit)) () ready
  simpa only [formatBits_binary] using formatted

/-- A certified total decision on ordinary arrays of external letters yields a
polynomial-time decision on every word, with no input framing precondition. -/
theorem onWordArrays
    (operation : (size : ℕ) → (Fin size → Letter) → Bool)
    (ready : (Computation.mk (fun _ : Unit => letterDomain.array ()) booleans
      (fun _ _ => True) (fun sizes arguments => operation (sizes ()) (arguments.val ()))).Realizable) :
    PolynomialTime id encodeBool
      (fun word => operation word.length (fun index => word[index])) := by
  have raw := onWordOutput booleans operation ready
  simpa only [WordBits.boolean_bits, List.map_singleton, PolynomialTime, encodeBool, id_eq] using raw

/-- Export a total word decision specified on the ordinary list of letters.
The polynomial-array and named-array codecs are transported here once, so
parsers need no array-length casts in their exported word theorem. -/
theorem onWordDecision (decision : Word → Bool)
    (ready : (Computation.mk
      (fun _ : Unit => letterDomain.arrayOfLength (MvPolynomial.X ())) booleans
      (fun _ _ => True) (fun _ arguments => decision (List.ofFn (arguments.val ())))).Realizable) :
    PolynomialTime id encodeBool decision := by
  have prepared := ready.reinterpretInputs (fun _ : Unit => letterDomain.array ())
    (fun _ sizes => arrayParameterEquiv letterDomain () sizes)
    (by intros; rfl) (fun _ sizes value => array_X_encode_bits letterDomain () sizes value)
    (fun _ _ => True) (by intros; trivial)
  have specified := prepared.withSpecification (fun _ _ => True)
    (fun _ arguments => decision (List.ofFn (arguments.val ()))) (by intros; trivial) (by
      intro sizes arguments valid
      have sameLetters : List.ofFn (arrayParameterEquiv letterDomain () sizes (arguments ())) =
          List.ofFn (arguments ()) :=
        (List.ofFn_congr (MvPolynomial.eval_X (f := sizes) ()).symm (arguments ())).symm
      exact congrArg decision sameLetters)
  have raw := specified.onWordArrays (fun _ letters => decision (List.ofFn letters))
  have same (word : Word) : List.ofFn (fun index : Fin word.length => word[index]) = word := by simp
  simpa only [same] using raw

end Polytime2.Computation.Realizable
