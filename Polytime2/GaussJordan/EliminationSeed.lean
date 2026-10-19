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

import Polytime2.GaussJordan.EliminationMath
import Polytime2.Primitives.Initialization

/-! # Seeding the outer elimination frame -/

namespace Polytime2.StandardGaussJordanElimination

open MultiTape CallingConvention StandardMatrixRows
open Binary (word)

variable {Scalar : Type} {cardinality : ℕ}

def seedTarget (stage : Fin 3) : TapeName := match stage.val with
  | 0 => workingTape | 1 => pivotTape | _ => columnTape

theorem seedTarget_injective : Function.Injective seedTarget := by
  intro first second equal
  fin_cases first <;> fin_cases second <;> first | rfl | exact absurd equal (by decide)

def seedCommand (stage : Fin 3) : Initialization.Command TapeName :=
  if stage = 0 then .copy inputTape (seedTarget stage) (by fin_cases stage <;> decide)
  else .clear (sizeTape 0) (seedTarget stage) (by fin_cases stage <;> decide)

@[simp] theorem seedCommand_target (stage : Fin 3) : (seedCommand stage).target = seedTarget stage := by
  unfold seedCommand
  split_ifs <;> rfl

abbrev SeedStageState (stage : Fin 3) := (seedCommand stage).State
abbrev seedEntry (stage : Fin 3) := (seedCommand stage).entry

noncomputable def seed : Machine Alphabet (Pipeline.State SeedStageState) :=
  Initialization.machine seedCommand

noncomputable def seedDefault (enumeration : Scalar ≃ Fin cardinality) (sizes : Fin 3 → ℕ)
    (matrix : Matrix (Fin (sizes 1)) (Fin (sizes 2)) Scalar) (stage : Fin 3) :
    Turing.Tape Binary.Symbol :=
  if stage = 0 then encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes matrix
  else encoded (EncodedDomain.binaryNaturals 0) sizes (⟨0, by positivity⟩ : Fin (2 ^ sizes 0))

/-- Copy the caller's matrix and initialize all outer counters except the
column limit, which will be read from its unary size tape. -/
theorem seed_runs (enumeration : Scalar ≃ Fin cardinality) :
    ∃ bound : MvPolynomial (Fin 3) ℕ, ∀ (sizes : Fin 3 → ℕ) (initial : Tapes Alphabet)
      (matrix : Matrix (Fin (sizes 1)) (Fin (sizes 2)) Scalar),
      initial inputTape = encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes matrix →
      initial (sizeTape 0) = unary (sizes 0) →
      (∀ name, Region ((domains enumeration name).width sizes) 0 (initial name)) →
      ∃ ticks final, ticks ≤ MvPolynomial.eval sizes bound ∧
        Runs (fun name => (domains enumeration name).width sizes) readOnly seed ticks
          (Pipeline.position seedEntry 0) (fun _ => 0) initial none (fun _ => 0) final ∧
        (∀ stage, final (seedTarget stage) = seedDefault enumeration sizes matrix stage) := by
  let matrixBound := (matrixDomain (FieldRow.scalarDomain enumeration)).widthPolynomial
  refine ⟨3 * (2 * matrixBound + 2 * MvPolynomial.X 0 + 3), ?_⟩
  intro sizes initial matrix inputEq header regions
  let words (name : TapeName) : List Bool :=
    if name = inputTape then List.ofFn (fun index : Fin ((matrixDomain (FieldRow.scalarDomain enumeration)).width sizes) =>
      ((matrixDomain (FieldRow.scalarDomain enumeration)).encode sizes matrix).getLsbD index.val)
    else List.replicate (sizes 0) true
  have headerDistinct : sizeTape 0 ≠ inputTape := by decide
  have inputWidth : (domains enumeration inputTape).width sizes =
      (matrixDomain (FieldRow.scalarDomain enumeration)).width sizes := rfl
  have matrixWidth : (domains enumeration workingTape).width sizes =
      (matrixDomain (FieldRow.scalarDomain enumeration)).width sizes := rfl
  have headerWidth : (domains enumeration (sizeTape 0)).width sizes = sizes 0 := by
    change (EncodedDomain.unary.{0, 0} (0 : Fin 3)).width sizes = sizes 0
    simp [EncodedDomain.unary, EncodedDomain.ofCodec]
  have pivotWidth : (domains enumeration pivotTape).width sizes = sizes 0 := EncodedDomain.binaryNaturals_width 0 sizes
  have columnWidth : (domains enumeration columnTape).width sizes = sizes 0 := EncodedDomain.binaryNaturals_width 0 sizes
  have expected (stage : Fin 3) :
      buffer (word ((seedCommand stage).word words)) = seedDefault enumeration sizes matrix stage := by
    fin_cases stage
    · rfl
    all_goals
      have chosen (stage : Fin 3) (nonzero : stage ≠ 0) :
          (seedCommand stage).word words = List.replicate (sizes 0) false := by
        simp [seedCommand, nonzero, Initialization.Command.word, words, headerDistinct]
      rw [chosen _ (by decide)]
      change buffer (word (List.replicate (sizes 0) false)) =
        encoded (EncodedDomain.binaryNaturals 0) sizes (⟨0, by positivity⟩ : Fin (2 ^ sizes 0))
      simpa only [Binary.value_replicate_false] using
        (encoded_binaryNaturals (0 : Fin 3) sizes (List.replicate (sizes 0) false) (by simp)).symm
  obtain ⟨ticks, final, cost, trace, outputs⟩ := Initialization.runs seedCommand words
    (fun name => (domains enumeration name).width sizes) readOnly
    (2 * (matrixDomain (FieldRow.scalarDomain enumeration)).width sizes + 2 * sizes 0 + 2)
    (by simpa only [seedCommand_target] using seedTarget_injective)
    (by intro stage; fin_cases stage <;> decide)
    (by intro stage name source; fin_cases stage <;>
      norm_num [seedCommand, Initialization.Command.source] at source <;>
      subst name <;> decide)
    (by
      intro stage name source
      fin_cases stage <;>
        norm_num [seedCommand, Initialization.Command.source] at source <;>
        subst name
      all_goals simp [words, headerDistinct, inputWidth, headerWidth])
    (by intro stage; fin_cases stage <;> norm_num [seedCommand, Initialization.Command.target,
      Initialization.Command.word, words, headerDistinct, seedTarget, matrixWidth, pivotWidth, columnWidth])
    (by intro stage; fin_cases stage <;> simp [seedCommand, Initialization.Command.cost, Initialization.Command.word, words, headerDistinct] <;> omega)
    initial
    (by
      intro stage name source
      fin_cases stage <;>
        norm_num [seedCommand, Initialization.Command.source] at source <;>
        subst name
      · exact inputEq
      all_goals exact header)
    regions
  refine ⟨ticks, final, ?_, trace, ?_⟩
  · simp only [matrixBound, map_mul, map_add, map_ofNat, MvPolynomial.eval_X]
    omega
  · intro stage
    have result := (outputs stage).trans (expected stage)
    rw [seedCommand_target] at result
    exact result

end Polytime2.StandardGaussJordanElimination
