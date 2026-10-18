/-
Copyright (c) 2026 Miklos Maroti <mmaroti@math.u-szeged.hu>
SPDX-License-Identifier: Apache-2.0

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Polytime2.StandardGaussJordanEliminationInitialization

/-! # Complete standard-convention Gauss–Jordan elimination -/

namespace Polytime2.StandardGaussJordanElimination

open MultiTape CallingConvention StandardMatrixRows

variable {Scalar : Type} [Field Scalar] {cardinality : ℕ}

abbrev AlgorithmState (scalarWidth : ℕ) :=
  Sum InitializationState (LoopState scalarWidth)

noncomputable instance algorithmStatesFinite (scalarWidth : ℕ) :
    Fintype (AlgorithmState scalarWidth) := by
  letI : Fintype (LoopState scalarWidth) := inferInstance
  dsimp only [AlgorithmState]
  infer_instance

noncomputable def algorithm (enumeration : Scalar ≃ Fin cardinality) :
    Machine Alphabet (AlgorithmState
      ((FieldRow.scalarDomain enumeration).width Empty.elim)) :=
  MultiTape.sequence initialization (loop enumeration)
    (loopEntry
      ((FieldRow.scalarDomain enumeration).width Empty.elim))

def entry (scalarWidth : ℕ) : AlgorithmState scalarWidth :=
  .inl (initializationEntry)

def exit (scalarWidth : ℕ) : AlgorithmState scalarWidth :=
  .inr (loopExit scalarWidth)

@[simp] theorem halt (enumeration : Scalar ≃ Fin cardinality) (symbols : Symbols Alphabet) :
    algorithm enumeration (exit
      ((FieldRow.scalarDomain enumeration).width Empty.elim)) symbols = none := rfl

theorem runs [DecidableEq Scalar] (enumeration : Scalar ≃ Fin cardinality) :
    ∃ bound : MvPolynomial (Fin 3) ℕ, ∀ (sizes : Fin 3 → ℕ) (initial : Tapes Alphabet)
      (matrix : Matrix (Fin (sizes 1)) (Fin (sizes 2)) Scalar),
      sizes 1 < 2 ^ sizes 0 → sizes 2 < 2 ^ sizes 0 → sizes 1 * sizes 2 ≤ 2 ^ sizes 0 →
      initial inputTape = encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes matrix →
      (∀ parameter, initial (sizeTape parameter) = unary (sizes parameter)) →
      (∀ name, Region ((domains enumeration name).width sizes) 0 (initial name)) →
      ∃ ticks final, ticks ≤ MvPolynomial.eval sizes bound ∧
        Runs (fun name => (domains enumeration name).width sizes) readOnly (algorithm enumeration) ticks
          (entry
            ((FieldRow.scalarDomain enumeration).width Empty.elim)) (fun _ => 0) initial
          (exit
            ((FieldRow.scalarDomain enumeration).width Empty.elim)) (fun _ => 0) final ∧
        final workingTape = encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes
          (GaussJordan.eliminate (Scalar := Scalar) matrix) := by
  obtain ⟨initBound, executeInit⟩ := initialization_runs enumeration
  obtain ⟨loopBound, executeLoop⟩ := mathematical_loop_runs enumeration
  refine ⟨initBound + loopBound + 1, ?_⟩
  intro sizes initial matrix rowsFit columnsFit capacity inputEq headers regions
  obtain ⟨initTicks, prepared, initCost, initTrace, matrixEq, pivotEq, columnEq, limitEq⟩ :=
    executeInit sizes initial matrix columnsFit inputEq headers regions
  let zero : Fin (2 ^ sizes 0) := ⟨0, by positivity⟩
  obtain ⟨loopTicks, final, finalPivot, loopCost, loopTrace, resultEq, finalPivotEq,
      finalPivotValue, finalColumnEq⟩ :=
    executeLoop sizes prepared zero matrix (by simp [zero]) rowsFit columnsFit capacity
      pivotEq columnEq matrixEq limitEq
      (fun parameter => (initTrace.readOnly_tape (sizeTape parameter)
        (by fin_cases parameter <;> decide)).trans (headers parameter))
      (fun name => initTrace.region name (regions name))
  have complete := initTrace.sequence (loop enumeration)
    (loopEntry
      ((FieldRow.scalarDomain enumeration).width Empty.elim))
    initialization_halt loopTrace
  refine ⟨initTicks + loopTicks + 1, final, ?_, ?_, ?_⟩
  · simp only [map_add, map_one]
    omega
  · simpa only [algorithm, entry, exit] using complete
  · simpa only [GaussJordan.eliminate, zero] using resultEq

/-- The working matrix is the sole declared result; every other writable tape
is private and has no encoding obligation at return. -/
def outputTapes : Unit ↪ TapeName := MultiTape.oneTape workingTape

/-- Immutable unary sizes and a separate immutable input matrix suffice.
All output and private tapes may initially contain arbitrary symbols. -/
theorem contract [DecidableEq Scalar] (enumeration : Scalar ≃ Fin cardinality) :
    CallingConvention.Realizes (domains enumeration) readOnly sizeTapes outputTapes (algorithm enumeration)
      (entry
        ((FieldRow.scalarDomain enumeration).width Empty.elim))
      (exit
        ((FieldRow.scalarDomain enumeration).width Empty.elim))
      (fun sizes _ => sizes 1 < 2 ^ sizes 0 ∧ sizes 2 < 2 ^ sizes 0 ∧ sizes 1 * sizes 2 ≤ 2 ^ sizes 0)
      (fun sizes input output =>
        (matrixEquiv (Carrier := Scalar) sizes).symm (output ()) =
          GaussJordan.eliminate (Scalar := Scalar)
            ((matrixEquiv (Carrier := Scalar) sizes).symm (input ⟨inputTape, rfl⟩))) := by
  classical
  obtain ⟨bound, execute⟩ := runs enumeration
  refine ⟨(by intro parameter; fin_cases parameter <;> rfl), (by intro name; cases name; decide), halt enumeration, bound, ?_⟩
  intro sizes input initial valid represented headers
  let matrix := (matrixEquiv (Carrier := Scalar) sizes).symm (input ⟨inputTape, rfl⟩)
  have matrixEq : initial inputTape = encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes matrix := by
    change initial inputTape = encoded (domains enumeration inputTape) sizes (matrixEquiv sizes matrix)
    exact (represented.1 inputTape rfl).trans
      (congrArg (encoded (domains enumeration inputTape) sizes)
        ((matrixEquiv (Carrier := Scalar) sizes).apply_symm_apply (input ⟨inputTape, rfl⟩))).symm
  obtain ⟨ticks, final, cost, trace, resultEq⟩ :=
    execute sizes initial matrix valid.1 valid.2.1 valid.2.2 matrixEq headers represented.region
  let output : Outputs (domains enumeration) outputTapes sizes := fun _ =>
    matrixEquiv (Carrier := Scalar) sizes (GaussJordan.eliminate (Scalar := Scalar) matrix)
  refine ⟨ticks, output, final, cost, trace,
    Equiv.symm_apply_apply (matrixEquiv (Carrier := Scalar) sizes)
      (GaussJordan.eliminate (Scalar := Scalar) matrix), ?_⟩
  intro name
  cases name
  exact resultEq

end Polytime2.StandardGaussJordanElimination
