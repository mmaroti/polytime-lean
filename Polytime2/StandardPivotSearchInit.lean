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

import Polytime2.StandardPivotSearchCalls

/-! # Initializing the fixed-width pivot-search workspace -/

namespace Polytime2.StandardPivotSearch

open MultiTape CallingConvention

def initTarget (stage : Fin 15) : TapeName := match stage.val with
  | 0 => elementTape | 1 => counterTape 1 | 2 => counterTape 0 | 3 => counterTape 2
  | 4 => counterTape 3 | 5 => counterTape 5 | 6 => counterTape 7 | 7 => rowLimitTape
  | 8 => differenceTape | 9 => nextTape | 10 => counterTape 4 | 11 => counterTape 8
  | 12 => foundTape | 13 => continueTape | _ => unitTape

theorem initTarget_injective : Function.Injective initTarget := by
  let ordinal : TapeName → ℕ := fun name => match name with
    | .inl (.inr true) => 0
    | .inl (.inl (.inr name)) => match name.val with
      | 1 => 1 | 0 => 2 | 2 => 3 | 3 => 4 | 5 => 5 | 7 => 6 | 4 => 10 | _ => 11
    | .inr name => match name.val with | 1 => 7 | 2 => 8 | 5 => 9 | 3 => 12 | 4 => 13 | _ => 14
    | _ => 0
  have inverse (stage : Fin 15) : ordinal (initTarget stage) = stage.val := by fin_cases stage <;> rfl
  intro first second equal
  exact Fin.ext ((inverse first).symm.trans ((congrArg ordinal equal).trans (inverse second)))

theorem initTarget_writable (stage : Fin 15) : readOnly (initTarget stage) = false := by
  fin_cases stage <;> rfl

theorem writable_initTarget (name : TapeName) (writable : readOnly name = false) : ∃ stage, initTarget stage = name := by
  fin_cases name <;> first
    | contradiction
    | exact ⟨0, rfl⟩ | exact ⟨1, rfl⟩ | exact ⟨2, rfl⟩ | exact ⟨3, rfl⟩ | exact ⟨4, rfl⟩
    | exact ⟨5, rfl⟩ | exact ⟨6, rfl⟩ | exact ⟨7, rfl⟩ | exact ⟨8, rfl⟩ | exact ⟨9, rfl⟩
    | exact ⟨10, rfl⟩ | exact ⟨11, rfl⟩ | exact ⟨12, rfl⟩ | exact ⟨13, rfl⟩ | exact ⟨14, rfl⟩

theorem initCapacity_distinct (stage : Fin 15) : sizeTape 0 ≠ initTarget stage := by
  fin_cases stage <;> simp [initTarget, sizeTape, counterTape, elementTape, rowLimitTape,
    differenceTape, nextTape, foundTape, continueTape, unitTape]

noncomputable def defaultBits (scalar : EncodedDomain.{0, 0} Empty) (defaultValue : scalar.Carrier Empty.elim) : List Bool :=
  List.ofFn (fun index : Fin (scalar.width Empty.elim) => (scalar.encode Empty.elim defaultValue).getLsbD index.val)

def InitStageState (width : ℕ) (stage : Fin 15) : Type :=
  if stage = 0 then Copy.State width else if stage = 1 then Fin 3 else
    if stage = 14 then Copy.State 0 else if stage.val < 10 then StandardBinaryScan.State Unit else Bool

instance initStageFinite (width : ℕ) (stage : Fin 15) : Fintype (InitStageState width stage) := by
  unfold InitStageState
  split_ifs <;> infer_instance

noncomputable def initStage (scalar : EncodedDomain.{0, 0} Empty) (defaultValue : scalar.Carrier Empty.elim)
    (stage : Fin 15) : Machine Alphabet (InitStageState (defaultBits scalar defaultValue).length stage) := by
  unfold InitStageState
  split_ifs with isDefault isCopy isUnit counterStage
  · exact StandardTapeCommands.setConstant (initTarget stage) (defaultBits scalar defaultValue)
  · subst stage
    exact StandardTapeCommands.copy startTape (counterTape 1) (by decide)
  · exact StandardTapeCommands.setConstant (initTarget stage) []
  · exact StandardTapeCommands.clear (sizeTape 0) (initTarget stage) (initCapacity_distinct stage)
  · exact StandardTapeCommands.setBoolean (initTarget stage) false

def initEntry (width : ℕ) (stage : Fin 15) : InitStageState width stage := by
  unfold InitStageState
  split_ifs
  · exact (false, Fin.last width)
  · exact 0
  · exact (false, 0)
  · exact .inl ()
  · exact false

def initExit (width : ℕ) (stage : Fin 15) : InitStageState width stage := by
  unfold InitStageState
  split_ifs
  · exact (true, 0)
  · exact 2
  · exact (true, 0)
  · exact .inr ((), true)
  · exact true

noncomputable def initialization (scalar : EncodedDomain.{0, 0} Empty) (defaultValue : scalar.Carrier Empty.elim) :
    Machine Alphabet (Pipeline.State (InitStageState (defaultBits scalar defaultValue).length)) :=
  Pipeline.machine (initStage scalar defaultValue) (initEntry (defaultBits scalar defaultValue).length)

theorem initStage_halt (scalar : EncodedDomain.{0, 0} Empty) (defaultValue : scalar.Carrier Empty.elim)
    (stage : Fin 15) (symbols : Symbols Alphabet) :
    initStage scalar defaultValue stage (initExit (defaultBits scalar defaultValue).length stage) symbols = none := by
  fin_cases stage <;> rfl

noncomputable def initDefault (scalar : EncodedDomain.{0, 0} Empty) (sizes : Fin 3 → ℕ)
    (defaultValue : scalar.Carrier Empty.elim) (start : Fin (2 ^ sizes 0)) (stage : Fin 15) : Turing.Tape Binary.Symbol :=
  if stage = 0 then encoded scalar Empty.elim defaultValue
  else if stage = 1 then encoded (EncodedDomain.binaryNaturals 0) sizes start
  else if stage = 14 then encoded StandardFinitePredicate.unitDomain Empty.elim (0 : Fin 1)
  else if stage.val < 10 then encoded (EncodedDomain.binaryNaturals 0) sizes (⟨0, by positivity⟩ : Fin (2 ^ sizes 0))
  else encoded EncodedDomain.booleans sizes false

private theorem encoded_zero (sizes : Fin 3 → ℕ) :
    encoded (EncodedDomain.binaryNaturals 0) sizes (⟨0, by positivity⟩ : Fin (2 ^ sizes 0)) =
      buffer (Binary.word (List.replicate (sizes 0) false)) := by
  simpa only [Binary.value_replicate_false] using encoded_binaryNaturals (0 : Fin 3) sizes
    (List.replicate (sizes 0) false) (by simp)

theorem initStage_runs (scalar : EncodedDomain.{0, 0} Empty) (sizes : Fin 3 → ℕ)
    (defaultValue : scalar.Carrier Empty.elim) (start : Fin (2 ^ sizes 0)) (stage : Fin 15) (initial : Tapes Alphabet)
    (startEq : initial startTape = encoded (EncodedDomain.binaryNaturals 0) sizes start)
    (header : initial (sizeTape 0) = unary (sizes 0))
    (regions : ∀ name, Region ((domains scalar name).width sizes) 0 (initial name)) :
    ∃ ticks, ticks ≤ 2 * scalar.width Empty.elim + 2 * sizes 0 + 2 ∧
      Runs (fun name => (domains scalar name).width sizes) readOnly (initStage scalar defaultValue stage) ticks
        (initEntry (defaultBits scalar defaultValue).length stage) (fun _ => 0) initial
        (initExit (defaultBits scalar defaultValue).length stage) (fun _ => 0)
        (Function.update initial (initTarget stage) (initDefault scalar sizes defaultValue start stage)) := by
  let width : TapeName → ℕ := fun name => (domains scalar name).width sizes
  by_cases isDefault : stage = 0
  · subst stage
    obtain ⟨old, length, oldEq⟩ := (regions elementTape).exists_buffer
    simp [domains, elementTape, StandardMatrixEntry.domains, EncodedDomain.constant,
      EncodedDomain.ofCodec] at length
    have trace := StandardTapeCommands.setConstant_runs elementTape (defaultBits scalar defaultValue) width readOnly rfl
      (by simp [width, domains, elementTape, StandardMatrixEntry.domains, EncodedDomain.constant, defaultBits])
      initial old (by simpa only [defaultBits, List.length_ofFn] using length) oldEq
    refine ⟨2 * (defaultBits scalar defaultValue).length + 1, ?_, trace⟩
    simp only [defaultBits, List.length_ofFn]
    omega
  · by_cases isCopy : stage = 1
    · subst stage
      have trace := StandardTapeCommands.copy_encoded_runs (EncodedDomain.binaryNaturals 0) sizes start
        startTape (counterTape 1) (by decide) width readOnly rfl rfl rfl initial startEq (regions _)
      refine ⟨2 * sizes 0 + 2, by omega, ?_⟩
      have exactWidth : (EncodedDomain.binaryNaturals (0 : Fin 3)).width sizes = sizes 0 := by
        simp [EncodedDomain.binaryNaturals, EncodedDomain.ofCodec]
      rw [exactWidth] at trace
      exact trace
    · by_cases isUnit : stage = 14
      · subst stage
        obtain ⟨old, length, oldEq⟩ := (regions unitTape).exists_buffer
        norm_num [domains, unitTape, StandardFinitePredicate.unitDomain, EncodedDomain.constant,
          EncodedDomain.fixed, EncodedDomain.ofCodec] at length
        have trace := StandardTapeCommands.setConstant_runs unitTape [] width readOnly rfl (by norm_num [width, domains, unitTape,
          StandardFinitePredicate.unitDomain, EncodedDomain.constant, EncodedDomain.fixed,
          EncodedDomain.ofCodec]) initial old (by simp [length]) oldEq
        refine ⟨1, by omega, ?_⟩
        have unitEncoding : encoded StandardFinitePredicate.unitDomain Empty.elim (0 : Fin 1) = buffer [] := by
          simp [StandardFinitePredicate.unitDomain, encoded, EncodedDomain.fixed, EncodedDomain.ofCodec,
            EncodedDomain.ArrayEncoding.bits, tape, buffer, Binary.word]
        change Runs width readOnly _ _ _ _ _ _ _
          (Function.update initial unitTape (encoded StandardFinitePredicate.unitDomain Empty.elim (0 : Fin 1)))
        rw [unitEncoding]
        exact trace
      · by_cases counterStage : stage.val < 10
        · have targetWidth : width (initTarget stage) = sizes 0 := by
            fin_cases stage <;> solve | simp [width, initTarget, domains, counterTape, rowLimitTape, nextTape, differenceTape,
                StandardMatrixEntry.domains, StandardMatrixAddress.domains, EncodedDomain.binaryNaturals,
                EncodedDomain.ofCodec] | norm_num at isDefault | norm_num at isCopy | norm_num at isUnit | norm_num at counterStage
          obtain ⟨old, length, oldEq⟩ := (regions (initTarget stage)).exists_buffer
          have trace := StandardTapeCommands.clear_runs (sizeTape 0) (initTarget stage) (initCapacity_distinct stage)
            width readOnly (initTarget_writable stage) (List.replicate (sizes 0) true) old
            (by simp [width, domains, sizeTape, StandardMatrixEntry.domains, StandardMatrixAddress.domains, EncodedDomain.unary])
            (by simpa only [List.length_replicate] using targetWidth)
            (by simpa only [List.length_replicate] using length.trans targetWidth) initial header oldEq
          simp only [List.length_replicate] at trace
          rw [← encoded_zero sizes] at trace
          refine ⟨2 * sizes 0 + 2, by omega, ?_⟩
          fin_cases stage <;> solve | exact trace | norm_num at isDefault | norm_num at isCopy | norm_num at isUnit | norm_num at counterStage
        · have targetWidth : width (initTarget stage) = 1 := by
            fin_cases stage <;> solve | norm_num [width, initTarget, domains, counterTape, foundTape, continueTape,
                StandardMatrixEntry.domains, StandardMatrixAddress.domains, EncodedDomain.booleans,
                EncodedDomain.fixed, EncodedDomain.ofCodec] | norm_num at counterStage | norm_num at isUnit
          obtain ⟨old, length, oldEq⟩ := (regions (initTarget stage)).exists_buffer
          change old.length = width (initTarget stage) at length
          rw [targetWidth] at length
          obtain ⟨oldBit, rfl⟩ := List.length_eq_one_iff.mp length
          have trace := StandardTapeCommands.setBoolean_runs (initTarget stage) false width readOnly
            (initTarget_writable stage) targetWidth initial oldBit oldEq
          have booleanEq : buffer [Binary.data false] = encoded EncodedDomain.booleans sizes false :=
            (encoded_booleans sizes false).symm
          rw [booleanEq] at trace
          refine ⟨1, by omega, ?_⟩
          fin_cases stage <;> solve | exact trace | norm_num at counterStage | norm_num at isUnit

private theorem initDefault_valid (scalar : EncodedDomain.{0, 0} Empty) (sizes : Fin 3 → ℕ)
    (defaultValue : scalar.Carrier Empty.elim) (start : Fin (2 ^ sizes 0)) (stage : Fin 15) :
    ∃ value : (domains scalar (initTarget stage)).Carrier sizes,
      initDefault scalar sizes defaultValue start stage = encoded (domains scalar (initTarget stage)) sizes value := by
  fin_cases stage <;> first
    | exact ⟨defaultValue, (encoded_constant scalar sizes _).symm⟩
    | exact ⟨start, rfl⟩
    | exact ⟨(0 : Fin 1), (encoded_constant StandardFinitePredicate.unitDomain sizes _).symm⟩
    | exact ⟨(⟨0, by positivity⟩ : Fin (2 ^ sizes 0)), rfl⟩ | exact ⟨false, rfl⟩

/-- All private words are valid before the first guard, including when there
are no rows to inspect. The matrix and unary sizes need no scratch formatting. -/
theorem initialization_runs (scalar : EncodedDomain.{0, 0} Empty) (sizes : Fin 3 → ℕ)
    (defaultValue : scalar.Carrier Empty.elim) (start : Fin (2 ^ sizes 0)) (initial : Tapes Alphabet)
    (startEq : initial startTape = encoded (EncodedDomain.binaryNaturals 0) sizes start)
    (header : initial (sizeTape 0) = unary (sizes 0))
    (regions : ∀ name, Region ((domains scalar name).width sizes) 0 (initial name)) :
    ∃ ticks final, ticks ≤ 15 * (2 * scalar.width Empty.elim + 2 * sizes 0 + 3) ∧
      Runs (fun name => (domains scalar name).width sizes) readOnly (initialization scalar defaultValue) ticks
        (Pipeline.position (initEntry (defaultBits scalar defaultValue).length) 0) (fun _ => 0) initial none (fun _ => 0) final ∧
      final (counterTape 1) = encoded (EncodedDomain.binaryNaturals 0) sizes start ∧
      final elementTape = encoded scalar Empty.elim defaultValue ∧
      final continueTape = encoded EncodedDomain.booleans sizes false ∧
      (∀ name, readOnly name = false → ∃ value : (domains scalar name).Carrier sizes,
        final name = encoded (domains scalar name) sizes value) := by
  obtain ⟨ticks, final, cost, trace, prepared⟩ := Pipeline.updates_runs
    (fun name => (domains scalar name).width sizes) readOnly (initStage scalar defaultValue)
    (initEntry (defaultBits scalar defaultValue).length) (initExit (defaultBits scalar defaultValue).length)
    initTarget initTarget_injective (initDefault scalar sizes defaultValue start)
    (2 * scalar.width Empty.elim + 2 * sizes 0 + 2) (initStage_halt scalar defaultValue) initial regions
    (by
      intro stage tapes immutable currentRegions
      exact initStage_runs scalar sizes defaultValue start stage tapes
        ((immutable startTape rfl).trans startEq) ((immutable (sizeTape 0) rfl).trans header) currentRegions)
  refine ⟨ticks, final, cost, trace, prepared 1, prepared 0, ?_, ?_⟩
  · have initializedContinue := prepared 13
    have targetIsContinue : initTarget (13 : Fin 15) = continueTape := rfl
    rw [targetIsContinue] at initializedContinue
    simpa [initDefault, continueTape] using initializedContinue
  intro name writable
  obtain ⟨stage, rfl⟩ := writable_initTarget name writable
  obtain ⟨value, canonical⟩ := initDefault_valid scalar sizes defaultValue start stage
  exact ⟨value, (prepared stage).trans canonical⟩

end Polytime2.StandardPivotSearch
