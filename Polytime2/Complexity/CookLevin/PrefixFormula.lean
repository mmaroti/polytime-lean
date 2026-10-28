import Polytime2.Complexity.Languages
import Polytime2.Complexity.CookLevin.WordPrefix
import Polytime2.Complexity.CookLevin.WordGuard
import Polytime2.SAT.FixedInputs

/-! # Fixing the instance prefix of a checked verifier formula

The remaining letters are existential. Fixing one-hot blocks is equivalent
to fixing the mathematical word prefix; checked circuits reject every invalid
letter code. The result uses the shared three-literal formula definition.
-/

namespace Polytime2.Complexity.CookLevin

open Turing Circuit

variable {Symbol State : Type} [Inhabited Symbol] [Inhabited State]
variable [Fintype Symbol] [Fintype State]

/-- Tseitin clauses for the checked verifier, with all supplied prefix letters fixed. -/
noncomputable def fixedVerifierFormula (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) (steps length : ℕ) (fixedWord : Word) : SAT.Formula ℕ :=
  SAT.fixInputs (List.ofFn (encodeWordBits fixedWord.get))
    (SAT.tseitin (length * Fintype.card Letter) (checkedWordCircuit machine entry letters steps length))

/-- The formula is satisfiable exactly when an accepted word of the specified
length begins with the supplied prefix. No alphabet-code assumptions remain. -/
theorem fixedVerifierFormula_correct (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) (steps length : ℕ) (fixedWord : Word) (bounded : fixedWord.length ≤ length)
    (verify : Word → Bool)
    (runs : ∀ word : Fin length → Letter,
      Internal.Runs machine entry letters (List.ofFn word) [Sum.inl (verify (List.ofFn word))] steps) :
    SAT.Formula.Satisfiable (fixedVerifierFormula machine entry letters steps length fixedWord) ↔
      ∃ word : Word, word.length = length ∧ word.take fixedWord.length = fixedWord ∧ verify word = true := by
  rw [fixedVerifierFormula, SAT.fixInputs_ofFn_tseitin _ _ _
    (checkedWordCircuit_valid machine entry letters steps length) _ (Nat.mul_le_mul_right _ bounded)]
  constructor
  · rintro ⟨assignment, accepted, fixed⟩
    obtain ⟨word, encoded, answer⟩ :=
      (checkedWordCircuit_correct machine entry letters steps length verify runs assignment).mp accepted
    subst assignment
    have prefixLetters := (encodeWordBits_prefix_iff bounded word fixedWord.get).mp fixed
    have prefixList := (word_prefix_take_iff bounded word fixedWord.get).mp prefixLetters
    exact ⟨List.ofFn word, List.length_ofFn, by simpa only [List.ofFn_get] using prefixList, answer⟩
  · rintro ⟨word, lengthEqual, prefixList, answer⟩
    subst length
    refine ⟨encodeWordBits word.get, ?_, ?_⟩
    · apply (checkedWordCircuit_correct machine entry letters steps word.length verify runs _).mpr
      exact ⟨word.get, rfl, by simpa only [List.ofFn_get] using answer⟩
    · apply (encodeWordBits_prefix_iff bounded word.get fixedWord.get).mpr
      apply (word_prefix_take_iff bounded word.get fixedWord.get).mpr
      simpa only [List.ofFn_get] using prefixList

/-- Fixing the framed instance leaves precisely an existential witness of the
requested length. All letters in the instance and witness are unrestricted. -/
theorem fixedVerifierFormula_pair (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) (steps witnessLength : ℕ) (input : Word) (verify : Word → Bool)
    (runs : ∀ word : Fin (2 * input.length + witnessLength + 1) → Letter,
      Internal.Runs machine entry letters (List.ofFn word) [Sum.inl (verify (List.ofFn word))] steps) :
    SAT.Formula.Satisfiable (fixedVerifierFormula machine entry letters steps
      (2 * input.length + witnessLength + 1) (encodePair (input, []))) ↔
      ∃ witness : Word, witness.length = witnessLength ∧ verify (encodePair (input, witness)) = true := by
  rw [fixedVerifierFormula_correct machine entry letters steps _ _
    (by simp only [encodePair_length, List.length_nil]; omega) verify runs]
  constructor
  · rintro ⟨word, lengthEqual, prefixEqual, accepted⟩
    refine ⟨word.drop (encodePair (input, [])).length, ?_, ?_⟩
    · simp only [List.length_drop, encodePair_length, List.length_nil]
      omega
    · have split : encodePair (input, []) ++ word.drop (encodePair (input, [])).length = word := by
        exact (congrArg (fun front => front ++ word.drop (encodePair (input, [])).length)
          prefixEqual).symm.trans (List.take_append_drop _ word)
      have same : encodePair (input, word.drop (encodePair (input, [])).length) = word := by
        simpa only [encodePair, List.append_nil, List.append_assoc] using split
      simpa only [same] using accepted
  · rintro ⟨witness, lengthEqual, accepted⟩
    refine ⟨encodePair (input, witness), ?_, ?_, accepted⟩
    · simp only [encodePair_length, lengthEqual]
    · have split : encodePair (input, witness) = encodePair (input, []) ++ witness := by
        simp only [encodePair, List.append_nil, List.append_assoc]
      rw [split, List.take_left]

/-- The fixed prefix adds exactly one unit clause per one-hot input bit. -/
theorem fixedVerifierFormula_length (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) (steps length : ℕ) (fixedWord : Word) :
    (fixedVerifierFormula machine entry letters steps length fixedWord).length =
      3 * (checkedWordCircuit machine entry letters steps length).1.length + 1 +
        fixedWord.length * Fintype.card Letter := by
  simp only [fixedVerifierFormula, SAT.fixInputs_length, SAT.tseitin_length, List.length_ofFn]

end Polytime2.Complexity.CookLevin
