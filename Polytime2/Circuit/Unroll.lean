import Polytime2.Circuit.Layer
import Mathlib.Logic.Function.Iterate

/-! # Unrolling Boolean transitions with shared wires

A transition is a finite family of expressions over the current state bits.
Each time step appends a fresh circuit layer and refers to the preceding
layer's wires. Correctness is stated against ordinary function iteration.
The exact gate count is the number of steps times the one-step gate count;
expression substitution across time steps, which could grow exponentially,
is avoided.
-/

namespace Polytime2.Circuit

/-- Extend a finite assignment to numbered wires. -/
def inputValues {width : ℕ} (assignment : Fin width → Bool) : ℕ → Bool :=
  fun wire => if bound : wire < width then assignment ⟨wire, bound⟩ else false

/-- Extend a finite family of wire names. Only names below `width` are read
by a valid transition expression. -/
def layerNames {width : ℕ} (outputs : Fin width → ℕ) : ℕ → ℕ :=
  fun wire => if bound : wire < width then outputs ⟨wire, bound⟩ else 0

/-- The mathematical state transition described by one expression per bit. -/
def transition {width : ℕ} (expressions : Fin width → Expression)
    (assignment : Fin width → Bool) : Fin width → Bool :=
  fun index => (expressions index).eval (inputValues assignment)

/-- Starting with the input wires, append one fresh layer per time step. -/
def unroll {width : ℕ} (expressions : Fin width → Expression) : ℕ → Layer width
  | 0 => ([], fun index => index.val)
  | steps + 1 =>
    let previous := unroll expressions steps
    let next := compileLayer width (width + previous.1.length)
      (fun index => (expressions index).rename (layerNames previous.2))
    (previous.1 ++ next.1, next.2)

theorem unroll_length {width : ℕ} (expressions : Fin width → Expression) (steps : ℕ) :
    (unroll expressions steps).1.length = steps * ∑ index, (expressions index).gateCount := by
  induction steps with
  | zero => simp [unroll]
  | succ steps induction =>
    simp only [unroll, List.length_append, compileLayer_length, Expression.rename_gateCount,
      induction, Nat.succ_mul]

theorem unroll_valid {width : ℕ} (expressions : Fin width → Expression)
    (valid : ∀ index, (expressions index).Valid width) (steps : ℕ) :
    WellFormed width (unroll expressions steps).1 ∧
      ∀ index, (unroll expressions steps).2 index < width + (unroll expressions steps).1.length := by
  induction steps with
  | zero => exact ⟨trivial, fun index => index.isLt⟩
  | succ steps induction =>
    let previous := unroll expressions steps
    have renamed : ∀ index, ((expressions index).rename (layerNames previous.2)).Valid
        (width + previous.1.length) := by
      intro index
      apply Expression.rename_valid (valid index)
      intro wire bound
      simpa [layerNames, bound] using induction.2 ⟨wire, bound⟩
    have next := compileLayer_valid width _ renamed (Nat.le_refl _)
    constructor
    · exact (wellFormed_append _ _ _).mpr ⟨induction.1, next.1⟩
    · intro index
      simpa only [unroll, List.length_append, Nat.add_assoc] using next.2 index

/-- The selected output wires contain exactly the iterated mathematical
transition, including zero steps and zero state bits. -/
theorem unroll_correct {width : ℕ} (expressions : Fin width → Expression)
    (valid : ∀ index, (expressions index).Valid width) (steps : ℕ)
    (assignment : Fin width → Bool) (index : Fin width) :
    run width (unroll expressions steps).1 (inputValues assignment)
      ((unroll expressions steps).2 index) =
        ((transition expressions)^[steps] assignment) index := by
  induction steps generalizing index with
  | zero => simp [unroll, run, inputValues, index.isLt]
  | succ steps induction =>
    let previous := unroll expressions steps
    let values := run width previous.1 (inputValues assignment)
    have previousValid := unroll_valid expressions valid steps
    have renamed : ∀ position, ((expressions position).rename (layerNames previous.2)).Valid
        (width + previous.1.length) := by
      intro position
      apply Expression.rename_valid (valid position)
      intro wire bound
      simpa [layerNames, bound] using previousValid.2 ⟨wire, bound⟩
    change run width (previous.1 ++ _) (inputValues assignment)
      ((compileLayer width (width + previous.1.length)
        (fun position => (expressions position).rename (layerNames previous.2))).2 index) = _
    rw [run_append, compileLayer_correct width _ renamed (Nat.le_refl _), Expression.rename_eval]
    rw [Function.iterate_succ_apply']
    apply Expression.eval_eq_of_agree (valid index)
    intro wire bound
    simp only [Function.comp_apply, layerNames, dite_eq_left bound, inputValues]
    simpa [bound] using induction ⟨wire, bound⟩

end Polytime2.Circuit
