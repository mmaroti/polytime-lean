import Polytime2.Complexity.WitnessPadding
import Polytime2.Arrays.PackingIntervals

/-! # Removing nested witness framing by stable selection

Retain the outer pair's header and input, then the actual witness inside the
inner pair. Skip its header and trailing padding. These are word identities;
certifying the mask computation and its guards is separate.
-/

namespace Polytime2.Complexity

/-- The retained prefix and witness interval form exactly the original pair. -/
theorem nestedPair_slices (input witness padding : Word) :
    (encodePair (input, encodePair (witness, padding))).take (2 * input.length + 1) ++
      ((encodePair (input, encodePair (witness, padding))).drop
        (2 * input.length + witness.length + 2)).take witness.length = encodePair (input, witness) := by
  let outer := encodePair (input, [])
  let innerHeader : Word := List.replicate witness.length (.inr 1) ++ [.inr 0]
  have outerLength : outer.length = 2 * input.length + 1 := by simp [outer]
  have headerLength : (outer ++ innerHeader).length = 2 * input.length + witness.length + 2 := by
    simp only [List.length_append, innerHeader, List.length_replicate, List.length_singleton, outerLength]
    omega
  have first : (encodePair (input, encodePair (witness, padding))).take (2 * input.length + 1) = outer := by
    have source : encodePair (input, encodePair (witness, padding)) = outer ++ encodePair (witness, padding) := by
      simp [outer, encodePair, List.append_assoc]
    rw [source, ← outerLength, List.take_left]
  have second : ((encodePair (input, encodePair (witness, padding))).drop
      (2 * input.length + witness.length + 2)).take witness.length = witness := by
    have source : encodePair (input, encodePair (witness, padding)) =
        (outer ++ innerHeader) ++ (witness ++ padding) := by
      simp [encodePair, outer, innerHeader, List.append_assoc]
    rw [source, ← headerLength, List.drop_left, List.take_left]
  rw [first, second]
  simp [outer, encodePair, List.append_assoc]

/-- Stable selection removes exactly the inner header and padding. -/
theorem pack_nestedPair (input witness padding : Word) :
    List.ofFn (ArrayPacking.pack
      (ArrayPacking.prefixIntervalFlags (2 * input.length + 1)
        (2 * input.length + witness.length + 2) witness.length)
      (encodePair (input, encodePair (witness, padding))).get) = encodePair (input, witness) := by
  have bounded : 2 * input.length + witness.length + 2 + witness.length ≤
      (encodePair (input, encodePair (witness, padding))).length := by
    simp only [encodePair_length]
    omega
  rw [ArrayPacking.pack_prefix_interval_list _ _ _ _ (by omega) bounded]
  exact nestedPair_slices input witness padding

end Polytime2.Complexity
