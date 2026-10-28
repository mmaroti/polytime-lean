import Polytime2.Complexity.WordArrays
import Polytime2.Complexity.WitnessEndpoints
import Polytime2.Complexity.WitnessMask
import Polytime2.Arrays.PrefixIntervalFlags

/-! # Certified stable selection of a nested witness

The input supplies the original word and the two mathematical field lengths.
The fitting precondition is checked separately by the pair parsers. Retain
only the outer prefix and the inner witness, with the original host capacity.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Complexity

open EncodedDomain Polytime2.Computation

private noncomputable def selectionInputs (capacity : MvPolynomial Unit ℕ) : Option Bool → EncodedDomain Unit :=
  fun name => match name with
    | none => letterDomain.arrayOfLength capacity
    | some _ => boundedIndex (capacity + 1)

private def selectionAllowed (capacity : MvPolynomial Unit ℕ) (sizes : Unit → ℕ)
    (arguments : ∀ name, (selectionInputs capacity name).Carrier sizes) : Prop :=
  2 * (arguments (some false)).val + 2 * (arguments (some true)).val + 2 ≤ MvPolynomial.eval sizes capacity

private noncomputable def selectionFlags (capacity : MvPolynomial Unit ℕ) : Computation Unit (Option Bool) :=
  (arrayPrefixIntervalFlags capacity).onResults (selectionInputs capacity) (selectionAllowed capacity)
    (fun index sizes arguments => (witnessEndpoints capacity).compute sizes
      ⟨(fun name => arguments.val (some name)), arguments.property⟩ index) (by intros; trivial)

private theorem selectionFlags_realizable (capacity : MvPolynomial Unit ℕ) : (selectionFlags capacity).Realizable := by
  have endpoints := (witnessEndpoints_realizable capacity).onArguments (selectionInputs capacity) (selectionAllowed capacity)
    (fun name => some name) (by intros; rfl) (by intro sizes arguments; exact arguments.property)
  apply (arrayPrefixIntervalFlags_realizable capacity).onResults
  intro index
  exact endpoints.followedBy (recordProjection_realizable 3 (fun _ => arrayPosition (capacity + 1)) index)
    rfl (by intros; trivial)

/-- Select the normalized word while retaining exactly its actual letters. -/
noncomputable def selectNestedWitness (capacity : MvPolynomial Unit ℕ) : Computation Unit (Option Bool) :=
  (arrayPack letterDomain capacity).onResults (selectionInputs capacity) (selectionAllowed capacity)
    (fun name sizes arguments => match name with
      | false => (selectionFlags capacity).compute sizes arguments
      | true => arguments.val none) (by intros; trivial)

theorem selectNestedWitness_realizable (capacity : MvPolynomial Unit ℕ) : (selectNestedWitness capacity).Realizable := by
  apply (arrayPack_realizable letterDomain capacity).onResults
  intro name
  cases name
  · exact selectionFlags_realizable capacity
  · exact Realizable.argument _ none (selectionAllowed capacity)

/-- The exact stored output is the outer prefix followed by the witness
interval. Neither the inner header nor trailing capacity padding is retained. -/
theorem selectNestedWitness_correct (capacity : MvPolynomial Unit ℕ) (sizes : Unit → ℕ)
    (arguments : (selectNestedWitness capacity).Arguments sizes)
    (valid : (selectNestedWitness capacity).precondition sizes arguments) :
    List.ofFn ((selectNestedWitness capacity).compute sizes ⟨arguments, valid⟩).2 =
      (List.ofFn (arguments none)).take (2 * (arguments (some false)).val + 1) ++
        ((List.ofFn (arguments none)).drop
          (2 * (arguments (some false)).val + (arguments (some true)).val + 2)).take
            (arguments (some true)).val := by
  change List.ofFn (ArrayPacking.pack ((selectionFlags capacity).compute sizes ⟨arguments, valid⟩)
    (arguments none)) = _
  have flags : (selectionFlags capacity).compute sizes ⟨arguments, valid⟩ =
      ArrayPacking.prefixIntervalFlags (2 * (arguments (some false)).val + 1)
        (2 * (arguments (some false)).val + (arguments (some true)).val + 2)
        (arguments (some true)).val := by
    funext index
    simp only [selectionFlags, onResults, arrayPrefixIntervalFlags_correct, witnessEndpoints,
      ArrayPacking.prefixIntervalFlags]
    apply Bool.decide_congr
    omega
  rw [flags]
  apply ArrayPacking.pack_prefix_interval_ofFn
  · omega
  · change 2 * (arguments (some false)).val + 2 * (arguments (some true)).val + 2 ≤ _ at valid
    omega

/-- Correctly parsed lengths select precisely the unpadded verifier input. -/
theorem selectNestedWitness_normalizes (capacity : MvPolynomial Unit ℕ) (sizes : Unit → ℕ)
    (arguments : (selectNestedWitness capacity).Arguments sizes)
    (valid : (selectNestedWitness capacity).precondition sizes arguments)
    (input witness padding : Word)
    (source : List.ofFn (arguments none) = encodePair (input, encodePair (witness, padding)))
    (inputLength : (arguments (some false)).val = input.length)
    (witnessLength : (arguments (some true)).val = witness.length) :
    List.ofFn ((selectNestedWitness capacity).compute sizes ⟨arguments, valid⟩).2 = encodePair (input, witness) := by
  rw [selectNestedWitness_correct, inputLength, witnessLength, source]
  exact nestedPair_slices input witness padding

end Polytime2.Complexity
