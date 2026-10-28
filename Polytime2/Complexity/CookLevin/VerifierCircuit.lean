import Polytime2.Complexity.CookLevin.WordGuard
import Polytime2.Complexity.Languages

/-! # Polynomial gate bounds for word-verifier circuits

Every certified polynomial-time word verifier has one explicit circuit per
input length, with a single polynomial gate bound and correctness on every
Boolean assignment. Noncanonical letter encodings reject. This mathematical
circuit-family theorem supplies the size bound used by `UniformVerifier.lean`,
which also certifies construction and canonical input/output serialization.
-/

namespace Polytime2.Complexity.CookLevin

open Turing Circuit

/-- Gate bound as a polynomial in the time allowance, including initial
wiring and final acceptance observation. The cell alphabet is fixed. -/
noncomputable def circuitSizePolynomial (cellBits : ℕ) : Polynomial ℕ :=
  2 + (Polynomial.X * ((4 * Polynomial.X + 1) * Polynomial.C cellBits) *
    Polynomial.C (5 * 2 ^ (3 * cellBits)) +
      (5 * ((4 * Polynomial.X + 1) * Polynomial.C cellBits) + 1))

theorem circuitSizePolynomial_eval (cellBits steps : ℕ) :
    (circuitSizePolynomial cellBits).eval steps =
      2 + (steps * ((2 * (2 * steps) + 1) * cellBits) * (5 * 2 ^ (3 * cellBits)) +
        (5 * ((2 * (2 * steps) + 1) * cellBits) + 1)) := by
  simp [circuitSizePolynomial]
  ring

/-- Gate cost of the linear-size input-code guard. -/
noncomputable def wordGuardSizePolynomial : Polynomial ℕ :=
  3 * (3 * (Polynomial.X * Polynomial.C letterExpression.gateCount) + 5 * Polynomial.X + 1) + 5

/-- One fixed certified verifier supplies circuits correct on every Boolean
assignment, with polynomially many gates. An accepted assignment encodes an
actual accepted word; invalid one-hot blocks reject. -/
theorem verifier_circuits (verify : Word → Bool) (ready : PolynomialTime id encodeBool verify) :
    ∃ (circuits : ℕ → Network) (gateBound : Polynomial ℕ),
      ∀ length, Circuit.Valid (length * Fintype.card Letter) (circuits length) ∧
        (circuits length).1.length ≤ gateBound.eval length ∧
        ∀ assignment : Fin (length * Fintype.card Letter) → Bool,
          evaluate (length * Fintype.card Letter) (circuits length) assignment = true ↔
            ∃ word : Fin length → Letter,
              encodeWordBits word = assignment ∧ verify (List.ofFn word) = true := by
  obtain ⟨Symbol, finiteSymbols, inhabitedSymbols, State, finiteStates, inhabitedStates,
    letters, machine, entry, timeBound, _nonblank, runs⟩ := ready
  let _ : Fintype Symbol := finiteSymbols
  let _ : Inhabited Symbol := inhabitedSymbols
  let _ : Fintype State := finiteStates
  let _ : Inhabited State := inhabitedStates
  refine ⟨fun length => checkedWordCircuit machine entry letters (timeBound.eval length) length,
    (circuitSizePolynomial (cellWidth Symbol State)).comp timeBound + wordGuardSizePolynomial, ?_⟩
  intro length
  refine ⟨checkedWordCircuit_valid machine entry letters _ length, ?_, ?_⟩
  · simp only [Polynomial.eval_add, Polynomial.eval_comp, circuitSizePolynomial_eval,
      wordGuardSizePolynomial, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one]
    exact checkedWordCircuit_bound machine entry letters _ length
  · apply checkedWordCircuit_correct
    intro word
    simpa only [id_eq, List.length_ofFn, encodeBool] using (runs (List.ofFn word)).1

end Polytime2.Complexity.CookLevin
