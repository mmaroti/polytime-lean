import Polytime2.Circuit.TruthTable
import Polytime2.Circuit.Observe
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Polynomial circuits for bounded local Boolean dynamics

Each output bit reads `arity` selected bits of the preceding configuration.
The truth table may depend on the output position. Unrolling for `steps`
transitions uses at most `steps * width * (5 * 2 ^ arity)` gates. For a fixed
machine, `arity` is fixed by its finite local alphabet; the configuration
width and time bound may grow with the input. Applying a truth table to the
whole configuration instead would not give the required polynomial bound.

This module proves the circuit simulation and bound for local Boolean
dynamics. Connecting those dynamics to Mathlib TM0 and certifying the circuit
constructor are separate obligations.
-/

namespace Polytime2.Circuit

/-- One expression for each output bit of a local transition. -/
def localExpressions (width arity : ℕ) (sources : Fin width → Fin arity → Fin width)
    (tables : Fin width → (Fin arity → Bool) → Bool) : Fin width → Expression :=
  fun output => (Expression.truthTable arity 0 (tables output)).rename
    (fun wire => if bound : wire < arity then (sources output ⟨wire, bound⟩).val else 0)

theorem localExpressions_valid (width arity : ℕ)
    (sources : Fin width → Fin arity → Fin width)
    (tables : Fin width → (Fin arity → Bool) → Bool) (output : Fin width) :
    (localExpressions width arity sources tables output).Valid width := by
  apply Expression.rename_valid (Expression.truthTable_valid arity 0 arity _ (by omega))
  intro wire bound
  simp [bound]

/-- The Boolean expression implements exactly the selected finite local
transition table, on arbitrary bit configurations. -/
theorem localExpressions_eval (width arity : ℕ)
    (sources : Fin width → Fin arity → Fin width)
    (tables : Fin width → (Fin arity → Bool) → Bool)
    (assignment : Fin width → Bool) (output : Fin width) :
    transition (localExpressions width arity sources tables) assignment output =
      tables output (fun argument => assignment (sources output argument)) := by
  simp only [transition, localExpressions, Expression.rename_eval, Expression.truthTable_eval]
  congr 1
  funext argument
  simp [inputValues, argument.isLt, (sources output argument).isLt]

theorem localExpressions_gateCount (width arity : ℕ)
    (sources : Fin width → Fin arity → Fin width)
    (tables : Fin width → (Fin arity → Bool) → Bool) (output : Fin width) :
    (localExpressions width arity sources tables output).gateCount ≤ 5 * 2 ^ arity := by
  simp only [localExpressions, Expression.rename_gateCount]
  have count := Expression.truthTable_gateCount arity 0 (tables output)
  omega

theorem local_unroll_length (width arity steps : ℕ)
    (sources : Fin width → Fin arity → Fin width)
    (tables : Fin width → (Fin arity → Bool) → Bool) :
    (unroll (localExpressions width arity sources tables) steps).1.length ≤
      steps * width * (5 * 2 ^ arity) := by
  have sumBound : (∑ position, (localExpressions width arity sources tables position).gateCount) ≤
      width * (5 * 2 ^ arity) := by
    calc
      _ ≤ ∑ _position : Fin width, 5 * 2 ^ arity :=
        Finset.sum_le_sum (fun position _ => localExpressions_gateCount width arity sources tables position)
      _ = _ := by simp
  rw [unroll_length, Nat.mul_assoc]
  exact Nat.mul_le_mul_left steps sumBound

/-- Compile local dynamics followed by a final mathematical observation. -/
def localObservationCircuit (width arity steps : ℕ)
    (sources : Fin width → Fin arity → Fin width)
    (tables : Fin width → (Fin arity → Bool) → Bool) (observation : Expression) : Network :=
  observeLayer width (unroll (localExpressions width arity sources tables) steps) observation

/-- Observe the entire final configuration without duplicating its circuit.
The observer contributes only its own gate count. -/
theorem localObservationCircuit_spec (width arity steps : ℕ)
    (sources : Fin width → Fin arity → Fin width)
    (tables : Fin width → (Fin arity → Bool) → Bool)
    (observation : Expression) (observationValid : observation.Valid width) :
    Valid width (localObservationCircuit width arity steps sources tables observation) ∧
      (localObservationCircuit width arity steps sources tables observation).1.length ≤
        steps * width * (5 * 2 ^ arity) + observation.gateCount ∧
      ∀ assignment, evaluate width (localObservationCircuit width arity steps sources tables observation)
        assignment = observation.eval (inputValues
        ((fun current position => tables position (fun argument => current (sources position argument)))^[steps]
          assignment)) := by
  dsimp only [localObservationCircuit]
  let expressions := localExpressions width arity sources tables
  let program := unroll expressions steps
  have valid := localExpressions_valid width arity sources tables
  have programValid := unroll_valid expressions valid steps
  change Valid width (observeLayer width program observation) ∧ _
  refine ⟨observeLayer_valid programValid.1 programValid.2 observationValid, ?_, ?_⟩
  · rw [observeLayer_length]
    exact Nat.add_le_add_right (local_unroll_length width arity steps sources tables) _
  · intro assignment
    rw [observeLayer_correct program programValid.2 observationValid]
    have transitionEqual : transition expressions =
        (fun current position => tables position (fun argument => current (sources position argument))) := by
      funext current position
      exact localExpressions_eval width arity sources tables current position
    have outputs : (fun index => run width program.1 (inputValues assignment) (program.2 index)) =
        ((transition expressions)^[steps] assignment) := by
      funext index
      exact unroll_correct expressions valid steps assignment index
    rw [outputs, transitionEqual]

end Polytime2.Circuit
