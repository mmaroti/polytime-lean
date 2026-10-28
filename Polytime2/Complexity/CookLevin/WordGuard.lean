import Polytime2.Complexity.CookLevin.WordInput
import Polytime2.Circuit.Guard

/-! # Rejecting noncanonical one-hot word inputs

SAT assignments are arbitrary Boolean vectors. The verifier circuit must
therefore test that each external letter block is a valid one-hot code.
This guard has linear expression size and accepts precisely encoded words.
-/

namespace Polytime2.Complexity.CookLevin

open Turing Circuit

attribute [local instance] Classical.propDecidable

noncomputable def canonicalLetter (bits : Fin (Fintype.card Letter) → Bool) : Bool :=
  decide (∃ letter : Letter, ∀ bit, bits bit = decide (letter = (Fintype.equivFin Letter).symm bit))

noncomputable def letterExpression := Expression.truthTable (Fintype.card Letter) 0 canonicalLetter

noncomputable def wordLetterExpression (length : ℕ) (position : Fin length) : Expression :=
  letterExpression.rename (fun wire => if bounded : wire < Fintype.card Letter then
    (finProdFinEquiv (position, ⟨wire, bounded⟩)).val else 0)

noncomputable def wordGuardExpression (length : ℕ) : Expression :=
  Expression.allExpressions (List.ofFn (wordLetterExpression length))

theorem wordLetterExpression_valid (length : ℕ) (position : Fin length) :
    (wordLetterExpression length position).Valid (length * Fintype.card Letter) := by
  apply Expression.rename_valid (Expression.truthTable_valid (Fintype.card Letter) 0 (Fintype.card Letter) canonicalLetter (by omega))
  intro wire bounded
  simp only [dite_eq_left bounded]
  exact (finProdFinEquiv (position, ⟨wire, bounded⟩)).isLt

theorem wordGuardExpression_valid (length : ℕ) :
    (wordGuardExpression length).Valid (length * Fintype.card Letter) := by
  apply Expression.allExpressions_valid
  intro expression member
  obtain ⟨position, equal⟩ := List.mem_ofFn.mp member
  subst expression
  exact wordLetterExpression_valid length position

theorem wordGuardExpression_gateCount (length : ℕ) :
    (wordGuardExpression length).gateCount =
      3 * (length * letterExpression.gateCount) + 5 * length + 1 := by
  simp [wordGuardExpression, Expression.allExpressions_gateCount, wordLetterExpression,
    Expression.rename_gateCount, List.sum_ofFn]

theorem wordLetterExpression_eval (length : ℕ) (position : Fin length)
    (assignment : Fin (length * Fintype.card Letter) → Bool) :
    (wordLetterExpression length position).eval (inputValues assignment) =
      canonicalLetter (fun bit => assignment (finProdFinEquiv (position, bit))) := by
  simp only [wordLetterExpression, Expression.rename_eval, letterExpression, Expression.truthTable_eval,
    Function.comp_apply, Nat.zero_add]
  congr 1
  funext bit
  simp only [dite_eq_left bit.isLt]
  change inputValues assignment (finProdFinEquiv (position, bit)).val = _
  simp only [inputValues, dite_eq_left (finProdFinEquiv (position, bit)).isLt]

theorem wordGuardExpression_eval (length : ℕ) (assignment : Fin (length * Fintype.card Letter) → Bool) :
    (wordGuardExpression length).eval (inputValues assignment) = true ↔
      ∃ word : Fin length → Letter, encodeWordBits word = assignment := by
  have localTests : (wordGuardExpression length).eval (inputValues assignment) = true ↔
      ∀ position : Fin length, canonicalLetter (fun bit => assignment (finProdFinEquiv (position, bit))) = true := by
    simp only [wordGuardExpression, Expression.allExpressions_eval, List.all_eq_true]
    constructor
    · intro all position
      exact (wordLetterExpression_eval length position assignment) ▸ all _ (by simp)
    · intro all expression member
      obtain ⟨position, equal⟩ := List.mem_ofFn.mp member
      subst expression
      rw [wordLetterExpression_eval]
      exact all position
  rw [localTests]
  simp only [canonicalLetter, decide_eq_true_eq]
  constructor
  · intro localWords
    choose word correct using localWords
    refine ⟨word, ?_⟩
    funext index
    have bit := correct (finProdFinEquiv.symm index).1 (finProdFinEquiv.symm index).2
    have flat : finProdFinEquiv ((finProdFinEquiv.symm index).1, (finProdFinEquiv.symm index).2) = index := by
      change finProdFinEquiv (finProdFinEquiv.symm index) = index
      exact Equiv.apply_symm_apply _ _
    rw [flat] at bit
    exact bit.symm
  · rintro ⟨word, rfl⟩ position
    refine ⟨word position, ?_⟩
    intro bit
    simp only [encodeWordBits, Equiv.symm_apply_apply]

variable {Symbol State : Type} [Inhabited Symbol] [Inhabited State]
variable [Fintype Symbol] [Fintype State]

/-- The word simulation with rejection of every invalid letter block. -/
noncomputable def checkedWordCircuit (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) (steps length : ℕ) : Network :=
  guard (length * Fintype.card Letter) (wordCircuit machine entry letters steps length)
    (wordGuardExpression length)

theorem checkedWordCircuit_valid (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) (steps length : ℕ) :
    Circuit.Valid (length * Fintype.card Letter) (checkedWordCircuit machine entry letters steps length) :=
  guard_valid (wordCircuit_valid machine entry letters steps length) (wordGuardExpression_valid length)

theorem checkedWordCircuit_bound (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) (steps length : ℕ) :
    (checkedWordCircuit machine entry letters steps length).1.length ≤
      2 + (steps * ((2 * (2 * steps) + 1) * cellWidth Symbol State) *
        (5 * 2 ^ (3 * cellWidth Symbol State)) + (5 * ((2 * (2 * steps) + 1) * cellWidth Symbol State) + 1)) +
          (3 * (3 * (length * letterExpression.gateCount) + 5 * length + 1) + 5) := by
  dsimp only [checkedWordCircuit]
  rw [guard_length, wordGuardExpression_gateCount]
  exact Nat.add_le_add_right (wordCircuit_bound machine entry letters steps length) _

/-- Correctness on every Boolean assignment: invalid letter blocks reject,
and every accepted assignment encodes a word accepted by the verifier. -/
theorem checkedWordCircuit_correct (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) (steps length : ℕ) (verify : Word → Bool)
    (runs : ∀ word : Fin length → Letter,
      Internal.Runs machine entry letters (List.ofFn word) [Sum.inl (verify (List.ofFn word))] steps)
    (assignment : Fin (length * Fintype.card Letter) → Bool) :
    evaluate (length * Fintype.card Letter) (checkedWordCircuit machine entry letters steps length)
        assignment = true ↔
      ∃ word : Fin length → Letter, encodeWordBits word = assignment ∧ verify (List.ofFn word) = true := by
  dsimp only [checkedWordCircuit]
  rw [guard_correct (wordCircuit_valid machine entry letters steps length) (wordGuardExpression_valid length),
    Bool.and_eq_true, wordGuardExpression_eval]
  constructor
  · rintro ⟨⟨word, equal⟩, accepted⟩
    refine ⟨word, equal, ?_⟩
    rw [← equal, wordCircuit_runs machine entry letters steps length word _ (runs word)] at accepted
    exact accepted
  · rintro ⟨word, equal, accepted⟩
    refine ⟨⟨word, equal⟩, ?_⟩
    rw [← equal, wordCircuit_runs machine entry letters steps length word _ (runs word)]
    exact accepted

end Polytime2.Complexity.CookLevin
