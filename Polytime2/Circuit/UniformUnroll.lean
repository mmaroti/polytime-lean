import Polytime2.Circuit.UniformLayer
import Polytime2.Circuit.Unroll

/-! # Directly indexed blocks of a bounded circuit simulation

Uniform local gate counts give closed arithmetic formulas for every layer
input and block offset. The complete unrolled program is a flattened array
of those blocks. This exposes the tabulation needed by the uniform constructor
without requiring recursive reconstruction of earlier circuit layers.
-/

namespace Polytime2.Circuit

def stepInputWire (width blockSize : ℕ) : ℕ → Fin width → ℕ
  | 0, index => index.val
  | steps + 1, index => width + steps * (width * blockSize) + (index.val + 1) * blockSize - 1

theorem unroll_uniform_length {width : ℕ} (expressions : Fin width → Expression)
    (blockSize : ℕ) (uniform : ∀ index, (expressions index).gateCount = blockSize) (steps : ℕ) :
    (unroll expressions steps).1.length = steps * (width * blockSize) := by
  rw [unroll_length]
  simp only [uniform, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

theorem unroll_uniform_output {width : ℕ} (expressions : Fin width → Expression)
    (blockSize : ℕ) (uniform : ∀ index, (expressions index).gateCount = blockSize)
    (positive : 0 < blockSize) (steps : ℕ) (index : Fin width) :
    (unroll expressions steps).2 index = stepInputWire width blockSize steps index := by
  cases steps with
  | zero => rfl
  | succ steps =>
    have output := compileLayer_uniform_output width (width + (unroll expressions steps).1.length)
      blockSize (fun index => (expressions index).rename (layerNames (unroll expressions steps).2))
      (fun index => by rw [Expression.rename_gateCount, uniform]) positive index
    rw [unroll_uniform_length expressions blockSize uniform] at output
    dsimp only [unroll, stepInputWire]
    rw [unroll_uniform_length expressions blockSize uniform]
    omega

/-- Each time/cell block is compiled at a directly computed offset and reads
directly computed predecessor wires. Earlier layers need not be rebuilt. -/
theorem unroll_uniform_gates {width : ℕ} (expressions : Fin width → Expression)
    (blockSize : ℕ) (uniform : ∀ index, (expressions index).gateCount = blockSize)
    (positive : 0 < blockSize) (steps : ℕ) :
    (unroll expressions steps).1 =
      (List.ofFn (fun time : Fin steps =>
        (List.ofFn (fun index : Fin width =>
          (((expressions index).rename (layerNames (stepInputWire width blockSize time.val))).compile
            (width + time.val * (width * blockSize) + index.val * blockSize)).1)).flatten)).flatten := by
  induction steps with
  | zero => rfl
  | succ steps induction =>
    have outputs : (unroll expressions steps).2 = stepInputWire width blockSize steps := by
      funext index
      exact unroll_uniform_output expressions blockSize uniform positive steps index
    simp only [unroll]
    rw [compileLayer_uniform_gates width _ blockSize _ (fun index => by
      rw [Expression.rename_gateCount, uniform])]
    rw [unroll_uniform_length expressions blockSize uniform, outputs, induction, List.ofFn_succ']
    simp only [List.concat_eq_append, List.flatten_append, List.flatten_cons, List.flatten_nil,
      List.append_nil, Fin.val_castSucc, Fin.val_last]

end Polytime2.Circuit
