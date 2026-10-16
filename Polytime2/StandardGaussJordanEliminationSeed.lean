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

import Polytime2.StandardGaussJordanEliminationMath
import Polytime2.StandardGaussJordanColumnWorkspace

/-! # Seeding the outer elimination frame -/

namespace Polytime2.StandardGaussJordanElimination

open MultiTape CallingConvention StandardMatrixRows
open Binary (word)

variable {Scalar : Type} {cardinality : ℕ}

def seedTarget (stage : Fin 6) : TapeName := match stage.val with
  | 0 => workingTape | 1 => pivotTape | 2 => columnTape
  | 3 => nextColumnTape | 4 => differenceTape | _ => guardTape

theorem seedTarget_injective : Function.Injective seedTarget := by
  intro first second equal
  fin_cases first <;> fin_cases second <;> first | rfl | exact absurd equal (by decide)

def SeedStageState (stage : Fin 6) : Type :=
  if stage = 0 then Fin 3 else if stage = 5 then Bool else StandardBinaryScan.State Unit

instance seedStageFinite (stage : Fin 6) : Fintype (SeedStageState stage) := by
  unfold SeedStageState
  split_ifs <;> infer_instance

noncomputable def seedStage (stage : Fin 6) : Machine Alphabet (SeedStageState stage) := by
  unfold SeedStageState
  split_ifs with first last
  · exact StandardTapeCommands.copy inputTape (seedTarget stage) (by fin_cases stage <;> decide)
  · exact StandardTapeCommands.setBoolean (seedTarget stage) false
  · exact StandardTapeCommands.clear (sizeTape 0) (seedTarget stage) (by fin_cases stage <;> decide)

def seedEntry (stage : Fin 6) : SeedStageState stage := by
  unfold SeedStageState
  split_ifs
  · exact 0
  · exact false
  · exact .inl ()

def seedExit (stage : Fin 6) : SeedStageState stage := by
  unfold SeedStageState
  split_ifs
  · exact 2
  · exact true
  · exact .inr ((), true)

noncomputable def seed : Machine Alphabet (Pipeline.State SeedStageState) :=
  Pipeline.machine seedStage seedEntry

theorem seedStage_halt (stage : Fin 6) (symbols : Symbols Alphabet) :
    seedStage stage (seedExit stage) symbols = none := by fin_cases stage <;> rfl

noncomputable def seedDefault (enumeration : Scalar ≃ Fin cardinality) (sizes : Fin 3 → ℕ)
    (matrix : Matrix (Fin (sizes 1)) (Fin (sizes 2)) Scalar) (stage : Fin 6) :
    Turing.Tape Binary.Symbol :=
  if stage = 0 then encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes matrix
  else if stage = 5 then encoded EncodedDomain.booleans sizes false
  else encoded (EncodedDomain.binaryNaturals 0) sizes (⟨0, by positivity⟩ : Fin (2 ^ sizes 0))

theorem seedStage_runs (enumeration : Scalar ≃ Fin cardinality) (sizes : Fin 3 → ℕ)
    (matrix : Matrix (Fin (sizes 1)) (Fin (sizes 2)) Scalar) (stage : Fin 6)
    (initial : Tapes Alphabet)
    (inputEq : initial inputTape = encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes matrix)
    (header : initial (sizeTape 0) = unary (sizes 0))
    (regions : ∀ name, Region ((domains enumeration name).width sizes) 0 (initial name)) :
    ∃ ticks, ticks ≤ 2 * (matrixDomain (FieldRow.scalarDomain enumeration)).width sizes + 2 * sizes 0 + 2 ∧
      Runs (fun name => (domains enumeration name).width sizes) readOnly (seedStage stage) ticks
        (seedEntry stage) (fun _ => 0) initial (seedExit stage) (fun _ => 0)
        (Function.update initial (seedTarget stage) (seedDefault enumeration sizes matrix stage)) := by
  let width : TapeName → ℕ := fun name => (domains enumeration name).width sizes
  have writable : readOnly (seedTarget stage) = false := by fin_cases stage <;> decide
  by_cases first : stage = 0
  · subst stage
    have trace := StandardTapeCommands.copy_encoded_runs (matrixDomain (FieldRow.scalarDomain enumeration))
      sizes matrix inputTape workingTape (by decide) width readOnly (by decide) rfl rfl
      initial inputEq (regions workingTape)
    exact ⟨_, by omega, trace⟩
  · by_cases last : stage = 5
    · subst stage
      obtain ⟨old, length, oldEq⟩ := (regions guardTape).exists_buffer
      change old.length = (EncodedDomain.booleans (Parameter := Fin 3)).width sizes at length
      norm_num [EncodedDomain.booleans, EncodedDomain.fixed, EncodedDomain.ofCodec] at length
      obtain ⟨oldBit, rfl⟩ := List.length_eq_one_iff.mp length
      have trace := StandardTapeCommands.setBoolean_runs guardTape false width readOnly (by decide)
        (by
          change (EncodedDomain.booleans (Parameter := Fin 3)).width sizes = 1
          norm_num [EncodedDomain.booleans, EncodedDomain.fixed, EncodedDomain.ofCodec]) initial oldBit oldEq
      refine ⟨1, by omega, ?_⟩
      change Runs width readOnly (StandardTapeCommands.setBoolean guardTape false) 1
        false (fun _ => 0) initial true (fun _ => 0)
        (Function.update initial guardTape (encoded EncodedDomain.booleans sizes false))
      rw [encoded_booleans]
      exact trace
    · have targetWidth : width (seedTarget stage) = sizes 0 := by
        fin_cases stage <;> solve | contradiction | exact EncodedDomain.binaryNaturals_width 0 sizes
      obtain ⟨old, length, oldEq⟩ := (regions (seedTarget stage)).exists_buffer
      have trace := StandardTapeCommands.clear_runs (sizeTape 0) (seedTarget stage)
        (by fin_cases stage <;> decide) width readOnly writable
        (List.replicate (sizes 0) true) old
        (by
          simp only [List.length_replicate]
          change (EncodedDomain.unary.{0, 0} (0 : Fin 3)).width sizes = sizes 0
          simp [EncodedDomain.unary, EncodedDomain.ofCodec])
        (by simpa only [List.length_replicate] using targetWidth)
        (by simpa only [List.length_replicate] using length.trans targetWidth) initial header oldEq
      have zeroEncoding : encoded (EncodedDomain.binaryNaturals 0) sizes
          (⟨0, by positivity⟩ : Fin (2 ^ sizes 0)) = buffer (word (List.replicate (sizes 0) false)) := by
        simpa only [Binary.value_replicate_false] using encoded_binaryNaturals (0 : Fin 3) sizes
          (List.replicate (sizes 0) false) (by simp)
      simp only [List.length_replicate] at trace
      rw [← zeroEncoding] at trace
      refine ⟨2 * sizes 0 + 2, by omega, ?_⟩
      fin_cases stage <;> solve | exact trace | contradiction

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
  refine ⟨6 * (2 * matrixBound + 2 * MvPolynomial.X 0 + 3), ?_⟩
  intro sizes initial matrix inputEq header regions
  obtain ⟨ticks, final, cost, trace, outputs⟩ := Pipeline.updates_runs
    (fun name => (domains enumeration name).width sizes) readOnly seedStage seedEntry seedExit
    seedTarget seedTarget_injective (seedDefault enumeration sizes matrix)
    (2 * (matrixDomain (FieldRow.scalarDomain enumeration)).width sizes + 2 * sizes 0 + 2)
    seedStage_halt initial regions
    (by
      intro stage tapes immutable currentRegions
      exact seedStage_runs enumeration sizes matrix stage tapes
        ((immutable inputTape rfl).trans inputEq)
        ((immutable (sizeTape 0) (by decide)).trans header) currentRegions)
  refine ⟨ticks, final, ?_, trace, outputs⟩
  simp only [matrixBound, map_mul, map_add, map_ofNat, MvPolynomial.eval_X]
  omega

end Polytime2.StandardGaussJordanElimination
