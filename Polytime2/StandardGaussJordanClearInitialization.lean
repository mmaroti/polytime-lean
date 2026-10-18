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

import Polytime2.StandardGaussJordanClearTraversal
import Polytime2.Initialization

/-! # Initialization of live values for pivot-column clearing -/

namespace Polytime2.StandardGaussJordanClear

open MultiTape CallingConvention

variable {Scalar : Type} {cardinality : ℕ}

def initCommand (stage : Fin 3) : Initialization.Command TapeName :=
  if stage = 0 then .copy originalTape workingTape (by decide)
  else if stage = 1 then .clear (sizeTape 0) (dataTape 1) (by decide)
  else .copy (dataTape 0) limitTape (by decide)

abbrev InitializationState := Pipeline.State (fun stage => (initCommand stage).State)

noncomputable def initialization : Machine Alphabet InitializationState := Initialization.machine initCommand

def initializationEntry : InitializationState := Pipeline.position (fun stage => (initCommand stage).entry) 0
def initializationExit : InitializationState := none

@[simp] theorem initialization_halt (symbols : Symbols Alphabet) :
    initialization initializationExit symbols = none := rfl

/-- Only the working matrix, target counter, and interval limit are initialized.
All other private contents may be arbitrary, including for empty intervals. -/
theorem initialization_runs (enumeration : Scalar ≃ Fin cardinality) :
    ∃ bound : MvPolynomial (Fin 3) ℕ, ∀ (sizes : Fin 3 → ℕ) (initial : Tapes Alphabet)
      (pivot : Fin (2 ^ sizes 0))
      (matrix : ((FieldRow.scalarDomain enumeration).constant.arrayOfLength
        StandardMatrixEntry.length).Carrier sizes),
      initial (dataTape 0) = encoded (EncodedDomain.binaryNaturals 0) sizes pivot →
      initial originalTape = encoded (domains enumeration originalTape) sizes matrix →
      (∀ parameter, initial (sizeTape parameter) = unary (sizes parameter)) →
      (∀ name, Region ((domains enumeration name).width sizes) 0 (initial name)) →
      ∃ ticks final, ticks ≤ MvPolynomial.eval sizes bound ∧
        Runs (fun name => (domains enumeration name).width sizes) readOnly
          initialization ticks initializationEntry (fun _ => 0) initial initializationExit (fun _ => 0) final ∧
        final workingTape = encoded (domains enumeration workingTape) sizes matrix ∧
        final (dataTape 1) = encoded (EncodedDomain.binaryNaturals 0) sizes
          (⟨0, by positivity⟩ : Fin (2 ^ sizes 0)) ∧
        final limitTape = encoded (EncodedDomain.binaryNaturals 0) sizes pivot := by
  let domain := (FieldRow.scalarDomain enumeration).constant.arrayOfLength StandardMatrixEntry.length
  refine ⟨3 * (2 * domain.widthPolynomial + 2 * MvPolynomial.X 0 + 3), ?_⟩
  intro sizes initial pivot matrix pivotEq matrixEq headers regions
  let words (name : TapeName) : List Bool :=
    if name = originalTape then List.ofFn (fun index : Fin (domain.width sizes) =>
      (domain.encode sizes matrix).getLsbD index.val)
    else if name = dataTape 0 then EncodedDomain.ArrayEncoding.bits
      ((EncodedDomain.binaryNaturals (0 : Fin 3)).encode sizes pivot)
    else List.replicate (sizes 0) true
  have matrixWidth : (domains enumeration originalTape).width sizes = domain.width sizes := rfl
  have workWidth : (domains enumeration workingTape).width sizes = domain.width sizes := rfl
  have sourceWidth : (domains enumeration (dataTape 0)).width sizes = sizes 0 := EncodedDomain.binaryNaturals_width 0 sizes
  have targetWidth : (domains enumeration (dataTape 1)).width sizes = sizes 0 := EncodedDomain.binaryNaturals_width 0 sizes
  have limitWidth : (domains enumeration limitTape).width sizes = sizes 0 := EncodedDomain.binaryNaturals_width 0 sizes
  have headerWidth : (domains enumeration (sizeTape 0)).width sizes = sizes 0 := by
    change (EncodedDomain.unary.{0, 0} (0 : Fin 3)).width sizes = sizes 0
    simp [EncodedDomain.unary, EncodedDomain.ofCodec]
  have headerMatrix : sizeTape 0 ≠ originalTape := by decide
  have headerPivot : sizeTape 0 ≠ dataTape 0 := by decide
  have pivotMatrix : dataTape 0 ≠ originalTape := by decide
  obtain ⟨ticks, final, cost, trace, outputs⟩ := Initialization.runs initCommand words
    (fun name => (domains enumeration name).width sizes) readOnly
    (2 * domain.width sizes + 2 * sizes 0 + 2)
    (by intro first second equal; fin_cases first <;> fin_cases second <;>
      first | rfl | exact absurd equal (by decide))
    (by intro stage; fin_cases stage <;> decide)
    (by intro stage name source; fin_cases stage <;>
      norm_num [initCommand, Initialization.Command.source] at source <;> subst name <;> rfl)
    (by
      intro stage name source
      fin_cases stage <;> norm_num [initCommand, Initialization.Command.source] at source <;> subst name
      all_goals simp [words, headerMatrix, headerPivot, pivotMatrix, EncodedDomain.ArrayEncoding.bits, matrixWidth, sourceWidth, headerWidth])
    (by intro stage; fin_cases stage <;> norm_num [initCommand, Initialization.Command.target,
      Initialization.Command.word, words, headerMatrix, headerPivot, pivotMatrix, EncodedDomain.ArrayEncoding.bits, workWidth, targetWidth, limitWidth])
    (by intro stage; fin_cases stage <;> simp [initCommand, Initialization.Command.cost,
      Initialization.Command.word, words, headerMatrix, headerPivot, pivotMatrix, EncodedDomain.ArrayEncoding.bits] <;> omega)
    initial
    (by
      intro stage name source
      fin_cases stage <;> norm_num [initCommand, Initialization.Command.source] at source <;> subst name
      all_goals first | exact matrixEq | exact headers 0 | simpa only [words, ite_eq_right pivotMatrix, ite_eq_left rfl, ite_true, encoded, tape, buffer] using pivotEq)
    regions
  refine ⟨ticks, final, ?_, trace, outputs 0, ?_, ?_⟩
  · simp only [map_mul, map_add, map_ofNat, MvPolynomial.eval_X]
    simp only [EncodedDomain.width] at cost
    omega
  · have zeroWord : (initCommand 1).word words = List.replicate (sizes 0) false := by
      simp [initCommand, Initialization.Command.word, words, headerMatrix, headerPivot]
    have counterResult := outputs 1
    rw [zeroWord] at counterResult
    exact counterResult.trans (by simpa only [Binary.value_replicate_false] using
      (encoded_binaryNaturals (0 : Fin 3) sizes (List.replicate (sizes 0) false) (by simp)).symm)
  · exact outputs 2

end Polytime2.StandardGaussJordanClear
