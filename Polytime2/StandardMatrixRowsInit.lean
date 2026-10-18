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

import Polytime2.StandardMatrixRows
import Polytime2.Initialization

/-! # Initializing the live matrix-row workspace -/

namespace Polytime2.StandardMatrixRows

open MultiTape CallingConvention

/-- Copy the working and result matrices, and initialize the column counter.
No other private tape needs a valid encoding before the loop. -/
def initCommand (stage : Fin 3) : Initialization.Command TapeName :=
  if stage = 2 then .clear (sizeTape 0) (dataTape 2) (by decide)
  else .copy inputTape (if stage = 0 then dataTape 4 else dataTape 5) (by
    split_ifs <;> decide)

abbrev InitStageState (stage : Fin 3) := (initCommand stage).State
abbrev initEntry (stage : Fin 3) := (initCommand stage).entry

noncomputable def initialization : Machine Alphabet (Pipeline.State InitStageState) :=
  Initialization.machine initCommand

theorem initialization_runs (scalar : EncodedDomain.{0, 0} Empty) (sizes : Fin 3 → ℕ)
    (array : (scalar.constant.arrayOfLength StandardMatrixEntry.length).Carrier sizes)
    (initial : Tapes Alphabet)
    (matrixEq : initial inputTape = encoded (scalar.constant.arrayOfLength StandardMatrixEntry.length) sizes array)
    (header : initial (sizeTape 0) = unary (sizes 0))
    (regions : ∀ name, Region ((domains scalar name).width sizes) 0 (initial name)) :
    ∃ ticks final, ticks ≤ 3 * (2 * (scalar.constant.arrayOfLength StandardMatrixEntry.length).width sizes +
        2 * sizes 0 + 3) ∧
      Runs (fun name => (domains scalar name).width sizes) readOnly initialization ticks
        (Pipeline.position initEntry 0) (fun _ => 0) initial none (fun _ => 0) final ∧
      final (dataTape 4) = encoded (scalar.constant.arrayOfLength StandardMatrixEntry.length) sizes array ∧
      final (dataTape 5) = encoded (scalar.constant.arrayOfLength StandardMatrixEntry.length) sizes array ∧
      final (dataTape 2) = encoded (EncodedDomain.binaryNaturals 0) sizes
        (⟨0, by positivity⟩ : Fin (2 ^ sizes 0)) := by
  let domain := scalar.constant.arrayOfLength StandardMatrixEntry.length
  let words (name : TapeName) : List Bool :=
    if name = inputTape then List.ofFn (fun index : Fin (domain.width sizes) =>
      (domain.encode sizes array).getLsbD index.val)
    else List.replicate (sizes 0) true
  have headerDistinct : sizeTape 0 ≠ inputTape := by decide
  have matrixWidth (index : Fin 18) (valid : index = 4 ∨ index = 5) :
      (domains scalar (dataTape index)).width sizes = domain.width sizes := by
    rcases valid with rfl | rfl <;> rfl
  have inputWidth : (domains scalar inputTape).width sizes = domain.width sizes := rfl
  have headerWidth : (domains scalar (sizeTape 0)).width sizes = sizes 0 := by
    change (EncodedDomain.unary.{0, 0} (0 : Fin 3)).width sizes = sizes 0
    simp [EncodedDomain.unary, EncodedDomain.ofCodec]
  have counterWidth : (domains scalar (dataTape 2)).width sizes = sizes 0 := EncodedDomain.binaryNaturals_width 0 sizes
  obtain ⟨ticks, final, cost, trace, outputs⟩ := Initialization.runs initCommand words
    (fun name => (domains scalar name).width sizes) readOnly
    (2 * domain.width sizes + 2 * sizes 0 + 2)
    (by intro first second equal; fin_cases first <;> fin_cases second <;>
      first | rfl | exact absurd equal (by decide))
    (by intro stage; fin_cases stage <;> decide)
    (by intro stage name source; fin_cases stage <;>
      norm_num [initCommand, Initialization.Command.source] at source <;> subst name <;> rfl)
    (by
      intro stage name source
      fin_cases stage <;> norm_num [initCommand, Initialization.Command.source] at source <;> subst name
      all_goals simp [words, headerDistinct, inputWidth, headerWidth])
    (by intro stage; fin_cases stage <;> norm_num [initCommand, Initialization.Command.target,
      Initialization.Command.word, words, headerDistinct, matrixWidth _ (Or.inl rfl),
      matrixWidth _ (Or.inr rfl), counterWidth])
    (by intro stage; fin_cases stage <;> simp [initCommand, Initialization.Command.cost,
      Initialization.Command.word, words, headerDistinct] <;> omega)
    initial
    (by
      intro stage name source
      fin_cases stage <;> norm_num [initCommand, Initialization.Command.source] at source <;> subst name
      all_goals first | exact matrixEq | exact header)
    regions
  refine ⟨ticks, final, cost, trace, outputs 0, outputs 1, ?_⟩
  have zeroWord : (initCommand 2).word words = List.replicate (sizes 0) false := by
    simp [initCommand, Initialization.Command.word, words, headerDistinct]
  have zeroEncoding := encoded_binaryNaturals (0 : Fin 3) sizes (List.replicate (sizes 0) false) (by simp)
  have counterResult := outputs 2
  rw [zeroWord] at counterResult
  exact counterResult.trans (by simpa only [Binary.value_replicate_false] using zeroEncoding.symm)

end Polytime2.StandardMatrixRows
