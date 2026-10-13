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

/-! # Initializing every private tape of a matrix row traversal

Each of the nineteen writable tapes is overwritten once. Copies derive their
extent from immutable mathematical inputs; binary clearing uses the unary
capacity. Boolean outputs need no prepared source. Empty matrices are included.
-/

namespace Polytime2.StandardMatrixRows

open MultiTape CallingConvention

def initTarget (stage : Fin 19) : TapeName := match stage.val with
  | 0 => dataTape 4 | 1 => dataTape 5 | 2 => dataTape 6
  | 3 => dataTape 7 | 4 => dataTape 8 | 5 => dataTape 9 | 6 => dataTape 10
  | 7 => dataTape 2 | 8 => dataTape 11 | 9 => dataTape 12 | 10 => dataTape 13
  | 11 => dataTape 14 | 12 => dataTape 15 | 13 => nextTape | 14 => limitTape
  | 15 => differenceTape | 16 => dataTape 16 | 17 => dataTape 17 | _ => guardTape

theorem initTarget_injective : Function.Injective initTarget := by
  let ordinal : TapeName → ℕ := fun name => match name with
    | .inl (.inl (.inr name)) => match name.val with
      | 4 => 0 | 5 => 1 | 6 => 2 | 7 => 3 | 8 => 4 | 9 => 5 | 10 => 6
      | 2 => 7 | 11 => 8 | 12 => 9 | 13 => 10 | 14 => 11 | 15 => 12
      | 16 => 16 | _ => 17
    | .inl (.inr _) => 13
    | .inr name => match name.val with | 0 => 14 | 1 => 15 | _ => 18
    | _ => 0
  have inverse (stage : Fin 19) : ordinal (initTarget stage) = stage.val := by fin_cases stage <;> rfl
  intro first second equal
  exact Fin.ext ((inverse first).symm.trans ((congrArg ordinal equal).trans (inverse second)))

theorem initTarget_writable (stage : Fin 19) : readOnly (initTarget stage) = false := by
  fin_cases stage <;> rfl

theorem writable_initTarget (name : TapeName) (writable : readOnly name = false) :
    ∃ stage, initTarget stage = name := by
  fin_cases name <;> first
    | contradiction
    | exact ⟨0, rfl⟩ | exact ⟨1, rfl⟩ | exact ⟨2, rfl⟩ | exact ⟨3, rfl⟩ | exact ⟨4, rfl⟩
    | exact ⟨5, rfl⟩ | exact ⟨6, rfl⟩ | exact ⟨7, rfl⟩ | exact ⟨8, rfl⟩ | exact ⟨9, rfl⟩
    | exact ⟨10, rfl⟩ | exact ⟨11, rfl⟩ | exact ⟨12, rfl⟩ | exact ⟨13, rfl⟩ | exact ⟨14, rfl⟩
    | exact ⟨15, rfl⟩ | exact ⟨16, rfl⟩ | exact ⟨17, rfl⟩ | exact ⟨18, rfl⟩

def initSource (stage : Fin 19) : TapeName := if stage.val < 3 then inputTape else dataTape 3

theorem initSource_distinct (stage : Fin 19) : initSource stage ≠ initTarget stage := by
  fin_cases stage <;> simp [initSource, initTarget, dataTape, inputTape, nextTape,
    limitTape, differenceTape, guardTape]

theorem initCapacity_distinct (stage : Fin 19) : sizeTape 0 ≠ initTarget stage := by
  fin_cases stage <;> simp [initTarget, dataTape, sizeTape, nextTape, limitTape, differenceTape, guardTape]

def InitStageState (stage : Fin 19) : Type :=
  if stage.val < 7 then Fin 3 else if stage.val < 16 then StandardBinaryScan.State Unit else Bool

instance initStageFinite (stage : Fin 19) : Fintype (InitStageState stage) := by
  unfold InitStageState
  split_ifs <;> infer_instance

noncomputable def initStage (stage : Fin 19) : Machine Alphabet (InitStageState stage) := by
  unfold InitStageState
  split_ifs with copyStage clearStage
  · exact StandardTapeCommands.copy (initSource stage) (initTarget stage) (initSource_distinct stage)
  · exact StandardTapeCommands.clear (sizeTape 0) (initTarget stage) (initCapacity_distinct stage)
  · exact StandardTapeCommands.setBoolean (initTarget stage) false

def initEntry (stage : Fin 19) : InitStageState stage := by
  unfold InitStageState
  split_ifs
  · exact 0
  · exact .inl ()
  · exact false

def initExit (stage : Fin 19) : InitStageState stage := by
  unfold InitStageState
  split_ifs
  · exact 2
  · exact .inr ((), true)
  · exact true

noncomputable def initialization : Machine Alphabet (Pipeline.State InitStageState) :=
  Pipeline.machine initStage initEntry

theorem initStage_halt (stage : Fin 19) (symbols : Symbols Alphabet) : initStage stage (initExit stage) symbols = none := by
  fin_cases stage <;> rfl

noncomputable def initDefault (scalar : EncodedDomain.{0, 0} Empty) (sizes : Fin 3 → ℕ)
    (coefficient : scalar.Carrier Empty.elim)
    (array : (scalar.constant.arrayOfLength StandardMatrixEntry.length).Carrier sizes)
    (stage : Fin 19) : Turing.Tape Binary.Symbol :=
  if stage.val < 3 then encoded (scalar.constant.arrayOfLength StandardMatrixEntry.length) sizes array
  else if stage.val < 7 then encoded scalar Empty.elim coefficient
  else if stage.val < 16 then encoded (EncodedDomain.binaryNaturals 0) sizes (⟨0, by positivity⟩ : Fin (2 ^ sizes 0))
  else encoded EncodedDomain.booleans sizes false

private theorem encoded_zero (sizes : Fin 3 → ℕ) :
    encoded (EncodedDomain.binaryNaturals 0) sizes (⟨0, by positivity⟩ : Fin (2 ^ sizes 0)) =
      buffer (Binary.word (List.replicate (sizes 0) false)) := by
  simpa only [Binary.value_replicate_false] using encoded_binaryNaturals (0 : Fin 3) sizes
    (List.replicate (sizes 0) false) (by simp)

/-- Each formatting command overwrites just its destination. The immutable
matrix and coefficient provide valid representatives even for empty domains
of bits or arbitrary specialization-dependent scalar encodings. -/
theorem initStage_runs (scalar : EncodedDomain.{0, 0} Empty) (sizes : Fin 3 → ℕ)
    (coefficient : scalar.Carrier Empty.elim)
    (array : (scalar.constant.arrayOfLength StandardMatrixEntry.length).Carrier sizes)
    (stage : Fin 19) (initial : Tapes Alphabet)
    (matrixEq : initial inputTape = encoded (scalar.constant.arrayOfLength StandardMatrixEntry.length) sizes array)
    (coefficientEq : initial (dataTape 3) = encoded scalar Empty.elim coefficient)
    (header : initial (sizeTape 0) = unary (sizes 0))
    (regions : ∀ name, Region ((domains scalar name).width sizes) 0 (initial name)) :
    ∃ ticks, ticks ≤ 2 * (scalar.constant.arrayOfLength StandardMatrixEntry.length).width sizes +
        2 * scalar.width Empty.elim + 2 * sizes 0 + 2 ∧
      Runs (fun name => (domains scalar name).width sizes) readOnly (initStage stage) ticks
        (initEntry stage) (fun _ => 0) initial (initExit stage) (fun _ => 0)
        (Function.update initial (initTarget stage) (initDefault scalar sizes coefficient array stage)) := by
  let width : TapeName → ℕ := fun name => (domains scalar name).width sizes
  by_cases matrixStage : stage.val < 3
  · have source : initSource stage = inputTape := ite_eq_left matrixStage
    have targetWidth : width (initTarget stage) = (scalar.constant.arrayOfLength StandardMatrixEntry.length).width sizes := by
      fin_cases stage <;> solve | rfl | norm_num at matrixStage
    have trace := StandardTapeCommands.copy_encoded_runs (scalar.constant.arrayOfLength StandardMatrixEntry.length)
      sizes array (initSource stage) (initTarget stage) (initSource_distinct stage) width readOnly
      (initTarget_writable stage) (by rw [source]; rfl) targetWidth initial (source ▸ matrixEq) (regions _)
    refine ⟨2 * (scalar.constant.arrayOfLength StandardMatrixEntry.length).width sizes + 2, by omega, ?_⟩
    have copyStage : stage.val < 7 := by omega
    fin_cases stage <;> solve | exact trace | norm_num at matrixStage
  · by_cases scalarStage : stage.val < 7
    · have source : initSource stage = dataTape 3 := ite_eq_right matrixStage
      have targetWidth : width (initTarget stage) = scalar.width Empty.elim := by
        fin_cases stage <;> solve | rfl | norm_num at matrixStage | norm_num at scalarStage
      have trace := StandardTapeCommands.copy_encoded_runs scalar Empty.elim coefficient
        (initSource stage) (initTarget stage) (initSource_distinct stage) width readOnly
        (initTarget_writable stage) (by rw [source]; rfl) targetWidth initial (source ▸ coefficientEq) (regions _)
      refine ⟨2 * scalar.width Empty.elim + 2, by omega, ?_⟩
      fin_cases stage <;> solve | exact trace | norm_num at matrixStage | norm_num at scalarStage
    · by_cases counterStage : stage.val < 16
      · have targetWidth : width (initTarget stage) = sizes 0 := by
          fin_cases stage <;> solve | rfl | norm_num at matrixStage | norm_num at scalarStage | norm_num at counterStage
        obtain ⟨old, oldLength, oldEq⟩ := (regions (initTarget stage)).exists_buffer
        have trace := StandardTapeCommands.clear_runs (sizeTape 0) (initTarget stage) (initCapacity_distinct stage)
          width readOnly (initTarget_writable stage) (List.replicate (sizes 0) true) old
          (by simp [width, domains, sizeTape, StandardMatrixRowStep.domains, StandardMatrixRowEntry.domains, EncodedDomain.unary])
          (by simpa only [List.length_replicate] using targetWidth)
          (by simpa only [List.length_replicate] using oldLength.trans targetWidth) initial header oldEq
        refine ⟨2 * sizes 0 + 2, by omega, ?_⟩
        simp only [List.length_replicate] at trace
        rw [← encoded_zero sizes] at trace
        fin_cases stage <;> solve | exact trace | norm_num at scalarStage | norm_num at counterStage
      · have targetWidth : width (initTarget stage) = 1 := by
          fin_cases stage <;> solve | rfl | norm_num at counterStage
        obtain ⟨old, oldLength, oldEq⟩ := (regions (initTarget stage)).exists_buffer
        change old.length = width (initTarget stage) at oldLength
        rw [targetWidth] at oldLength
        obtain ⟨oldBit, rfl⟩ := List.length_eq_one_iff.mp oldLength
        have trace := StandardTapeCommands.setBoolean_runs (initTarget stage) false width readOnly
          (initTarget_writable stage) targetWidth initial oldBit oldEq
        refine ⟨1, by omega, ?_⟩
        have booleanEq : buffer [Binary.data false] = encoded EncodedDomain.booleans sizes false :=
          (encoded_booleans sizes false).symm
        rw [booleanEq] at trace
        fin_cases stage <;> solve | exact trace | norm_num at counterStage

private theorem initDefault_valid (scalar : EncodedDomain.{0, 0} Empty) (sizes : Fin 3 → ℕ)
    (coefficient : scalar.Carrier Empty.elim)
    (array : (scalar.constant.arrayOfLength StandardMatrixEntry.length).Carrier sizes) (stage : Fin 19) :
    ∃ value : (domains scalar (initTarget stage)).Carrier sizes,
      initDefault scalar sizes coefficient array stage = encoded (domains scalar (initTarget stage)) sizes value := by
  fin_cases stage <;> first
    | exact ⟨array, rfl⟩
    | exact ⟨coefficient, rfl⟩
    | exact ⟨(⟨0, by positivity⟩ : Fin (2 ^ sizes 0)), rfl⟩
    | exact ⟨false, rfl⟩

/-- Initialization derives all nineteen writable words from immutable inputs.
Every temporary value is valid even if the subsequent traversal has no columns
to visit; there is no prefill or externally prepared scratch requirement. -/
theorem initialization_runs (scalar : EncodedDomain.{0, 0} Empty) (sizes : Fin 3 → ℕ)
    (coefficient : scalar.Carrier Empty.elim)
    (array : (scalar.constant.arrayOfLength StandardMatrixEntry.length).Carrier sizes)
    (initial : Tapes Alphabet)
    (matrixEq : initial inputTape = encoded (scalar.constant.arrayOfLength StandardMatrixEntry.length) sizes array)
    (coefficientEq : initial (dataTape 3) = encoded scalar Empty.elim coefficient)
    (header : initial (sizeTape 0) = unary (sizes 0))
    (regions : ∀ name, Region ((domains scalar name).width sizes) 0 (initial name)) :
    ∃ ticks final, ticks ≤ 19 * (2 * (scalar.constant.arrayOfLength StandardMatrixEntry.length).width sizes +
        2 * scalar.width Empty.elim + 2 * sizes 0 + 3) ∧
      Runs (fun name => (domains scalar name).width sizes) readOnly initialization ticks
        (Pipeline.position initEntry 0) (fun _ => 0) initial none (fun _ => 0) final ∧
      final (dataTape 4) = encoded (scalar.constant.arrayOfLength StandardMatrixEntry.length) sizes array ∧
      final (dataTape 5) = encoded (scalar.constant.arrayOfLength StandardMatrixEntry.length) sizes array ∧
      final (dataTape 2) = encoded (EncodedDomain.binaryNaturals 0) sizes (⟨0, by positivity⟩ : Fin (2 ^ sizes 0)) ∧
      (∀ name, readOnly name = false → ∃ value : (domains scalar name).Carrier sizes,
        final name = encoded (domains scalar name) sizes value) := by
  classical
  obtain ⟨ticks, final, cost, trace, finalValid⟩ := Pipeline.updates_runs
    (fun name => (domains scalar name).width sizes) readOnly initStage initEntry initExit
    initTarget initTarget_injective (initDefault scalar sizes coefficient array)
    (2 * (scalar.constant.arrayOfLength StandardMatrixEntry.length).width sizes +
      2 * scalar.width Empty.elim + 2 * sizes 0 + 2)
    initStage_halt initial regions
    (by
      intro stage tapes immutable currentRegions
      exact initStage_runs scalar sizes coefficient array stage tapes
        ((immutable inputTape rfl).trans matrixEq) ((immutable (dataTape 3) rfl).trans coefficientEq)
        ((immutable (sizeTape 0) rfl).trans header) currentRegions)
  refine ⟨ticks, final, cost, trace, finalValid 0, finalValid 1, finalValid 7, ?_⟩
  intro name writable
  obtain ⟨stage, rfl⟩ := writable_initTarget name writable
  obtain ⟨value, canonical⟩ := initDefault_valid scalar sizes coefficient array stage
  exact ⟨value, (finalValid stage).trans canonical⟩

end Polytime2.StandardMatrixRows
