import Polytime2.Complexity.PaddedVerifier

/-! # Every NP language has polynomially fixed witness lengths

The existing NP contract permits witnesses up to a polynomial bound. Nested
pair framing pads them to one exact polynomial length. The certified total
padded verifier removes that framing before invoking the original verifier.
-/

namespace Polytime2.Complexity

open Turing

/-- Replace a bounded witness length by one exact polynomial length, retaining
an all-word polynomial-time verifier and malformed-pair rejection. -/
theorem InNP.fixedWitness {language : Language Letter} (membership : InNP language) :
    ∃ (verify : Word → Bool) (witnessLength : Polynomial ℕ),
      PolynomialTime id encodeBool verify ∧
      (∀ word, decodePair word = none → verify word = false) ∧
      ∀ input, input ∈ language ↔
        ∃ witness : Word, witness.length = witnessLength.eval input.length ∧
          verify (encodePair (input, witness)) = true := by
  obtain ⟨verify, bound, ready, rejects, correct⟩ := membership
  have rejectEmpty : verify [] = false := rejects [] (by rfl)
  refine ⟨(fun word => verify (normalizePaddedPair word)), 2 * bound + 1,
    paddedVerifier_polynomialTime verify ready rejectEmpty, ?_, ?_⟩
  · intro word malformed
    simp only [normalizePaddedPair, malformed, rejectEmpty]
  · intro input
    rw [correct input]
    simpa only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one] using
      (paddedWitness_iff verify rejectEmpty input (bound.eval input.length)).symm

end Polytime2.Complexity
