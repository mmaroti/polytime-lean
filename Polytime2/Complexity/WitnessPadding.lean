import Polytime2.Complexity.Languages

/-! # Fixed-length witnesses through the existing pair encoding

A witness of length at most a capacity is paired with padding to obtain length
exactly twice the capacity plus one. A total normalizer removes the inner
framing and padding before the original verifier runs. Malformed framing maps
to the empty word, which every NP verifier rejects by its existing contract.
These are mathematical word identities; execution certification is separate.
-/

namespace Polytime2.Complexity

/-- A self-delimiting witness with enough padding for the fixed target length. -/
def padWitness (capacity : ℕ) (witness : Word) : Word :=
  encodePair (witness, List.replicate (2 * (capacity - witness.length)) (.inl false))

theorem padWitness_length (capacity : ℕ) (witness : Word) (bounded : witness.length ≤ capacity) :
    (padWitness capacity witness).length = 2 * capacity + 1 := by
  simp only [padWitness, encodePair_length, List.length_replicate]
  omega

/-- Remove the inner witness framing and ignore its padding. Rejected parses
map to an ordinary malformed pair, so an NP verifier will reject them. -/
def normalizePaddedPair (word : Word) : Word :=
  match decodePair word with
  | none => []
  | some (input, padded) => match decodePair padded with
    | none => []
    | some (witness, _padding) => encodePair (input, witness)

/-- Padding and normalization preserve the original verifier input exactly. -/
@[simp] theorem normalizePaddedPair_encode (input witness : Word) (capacity : ℕ) :
    normalizePaddedPair (encodePair (input, padWitness capacity witness)) = encodePair (input, witness) := by
  simp [normalizePaddedPair, padWitness]

theorem normalizePaddedPair_length (word : Word) : (normalizePaddedPair word).length ≤ word.length := by
  cases outer : decodePair word with
  | none => simp [normalizePaddedPair, outer]
  | some pair =>
    rcases pair with ⟨input, padded⟩
    cases inner : decodePair padded with
    | none => simp [normalizePaddedPair, outer, inner]
    | some fields =>
      rcases fields with ⟨witness, padding⟩
      have outerLength := decodePair_length outer
      have innerLength := decodePair_length inner
      simp only [normalizePaddedPair, outer, inner, encodePair_length]
      dsimp only at outerLength innerLength ⊢
      omega

/-- The full padded verifier input has a length determined only by the input
length and capacity, even when the actual witness is shorter or empty. -/
theorem paddedVerifierInput_length (input witness : Word) (capacity : ℕ) (bounded : witness.length ≤ capacity) :
    (encodePair (input, padWitness capacity witness)).length = 2 * input.length + 2 * capacity + 2 := by
  rw [encodePair_length, padWitness_length capacity witness bounded]
  dsimp only
  omega

/-- Fixed-length padded witnesses and bounded original witnesses give exactly
the same accepting possibilities. Padding contents need not be canonical. -/
theorem paddedWitness_iff (verify : Word → Bool) (rejectEmpty : verify [] = false)
    (input : Word) (capacity : ℕ) :
    (∃ padded : Word, padded.length = 2 * capacity + 1 ∧
      verify (normalizePaddedPair (encodePair (input, padded))) = true) ↔
    ∃ witness : Word, witness.length ≤ capacity ∧ verify (encodePair (input, witness)) = true := by
  constructor
  · rintro ⟨padded, length, accepted⟩
    cases parsed : decodePair padded with
    | none => simp [normalizePaddedPair, parsed, rejectEmpty] at accepted
    | some fields =>
      rcases fields with ⟨witness, padding⟩
      have decodedLength := decodePair_length parsed
      dsimp only at decodedLength
      refine ⟨witness, by omega, ?_⟩
      simpa only [normalizePaddedPair, decodePair_encodePair, parsed] using accepted
  · rintro ⟨witness, bounded, accepted⟩
    exact ⟨padWitness capacity witness, padWitness_length capacity witness bounded, by simpa using accepted⟩

end Polytime2.Complexity
