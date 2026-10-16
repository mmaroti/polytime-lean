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

/-! # Initializing the column-clear caller from arbitrary writable contents -/

namespace Polytime2.StandardGaussJordanClear

open MultiTape CallingConvention
open Binary (word)

variable {Scalar : Type} [Field Scalar] {cardinality : ℕ}

noncomputable def zeroBits (enumeration : Scalar ≃ Fin cardinality) : List Bool :=
  let scalar := FieldRow.scalarDomain enumeration
  List.ofFn (fun index : Fin (scalar.width Empty.elim) =>
    (scalar.encode Empty.elim (0 : Scalar)).getLsbD index.val)

noncomputable def seedZero (enumeration : Scalar ≃ Fin cardinality) :
    Machine Alphabet (Copy.State (zeroBits enumeration).length) :=
  StandardTapeCommands.setConstant (dataTape 3) (zeroBits enumeration)

noncomputable def seedMatrix : Machine Alphabet (Fin 3) :=
  StandardTapeCommands.copy originalTape workingTape (by decide)

noncomputable def seed (enumeration : Scalar ≃ Fin cardinality) :
    Machine Alphabet (Sum (Copy.State (zeroBits enumeration).length) (Fin 3)) :=
  MultiTape.sequence (seedZero enumeration) seedMatrix 0

def seedEntry (width : ℕ) : Sum (Copy.State width) (Fin 3) :=
  .inl (false, Fin.last width)

def seedExit (width : ℕ) : Sum (Copy.State width) (Fin 3) := .inr 2

@[simp] theorem seedZero_halt (enumeration : Scalar ≃ Fin cardinality) (symbols : Symbols Alphabet) :
    seedZero enumeration (true, 0) symbols = none := by
  simp [seedZero, StandardTapeCommands.setConstant, MultiTape.wire,
    StandardConstant.machine, StandardConstant.machineSized]

@[simp] theorem seed_halt (enumeration : Scalar ≃ Fin cardinality) (symbols : Symbols Alphabet) :
    seed enumeration (seedExit (zeroBits enumeration).length) symbols = none := by
  simp [seed, seedExit, MultiTape.sequence, seedMatrix, StandardTapeCommands.copy,
    MultiTape.wire, StandardTerminatedCopy.machine]

/-- A specialization-fixed field zero overwrites arbitrary scalar contents;
no runtime tape supplies the constant or its width. -/
theorem seedZero_runs (enumeration : Scalar ≃ Fin cardinality) (sizes : Fin 3 → ℕ)
    (initial : Tapes Alphabet)
    (region : Region ((domains enumeration (dataTape 3)).width sizes) 0 (initial (dataTape 3))) :
    Runs (fun name => (domains enumeration name).width sizes) readOnly (seedZero enumeration)
      (2 * (zeroBits enumeration).length + 1)
      (false, Fin.last (zeroBits enumeration).length) (fun _ => 0) initial
      (true, 0) (fun _ => 0)
      (Function.update initial (dataTape 3)
        (encoded (FieldRow.scalarDomain enumeration) Empty.elim (0 : Scalar))) := by
  have targetWidth : (domains enumeration (dataTape 3)).width sizes = (zeroBits enumeration).length := by
    change (FieldRow.scalarDomain enumeration).constant.width sizes = (zeroBits enumeration).length
    simp [zeroBits, EncodedDomain.constant, EncodedDomain.ofCodec]
  obtain ⟨old, oldLength, oldEq⟩ := region.exists_buffer
  have trace := StandardTapeCommands.setConstant_runs (dataTape 3) (zeroBits enumeration)
    (fun name => (domains enumeration name).width sizes) readOnly rfl targetWidth initial old
    (oldLength.trans targetWidth) oldEq
  exact trace

/-- Initialize the scalar source used by the existing row initializer and
copy the immutable original matrix into private working storage. All other
tapes are preserved, and neither output needs a valid old encoding. -/
theorem seed_runs (enumeration : Scalar ≃ Fin cardinality) :
    ∃ bound : MvPolynomial (Fin 3) ℕ, ∀ (sizes : Fin 3 → ℕ) (initial : Tapes Alphabet)
      (matrix : ((FieldRow.scalarDomain enumeration).constant.arrayOfLength
        StandardMatrixEntry.length).Carrier sizes),
      initial originalTape = encoded (domains enumeration originalTape) sizes matrix →
      (∀ name, Region ((domains enumeration name).width sizes) 0 (initial name)) →
      ∃ ticks final, ticks ≤ MvPolynomial.eval sizes bound ∧
        Runs (fun name => (domains enumeration name).width sizes) readOnly (seed enumeration)
          ticks (seedEntry (zeroBits enumeration).length) (fun _ => 0) initial
          (seedExit (zeroBits enumeration).length) (fun _ => 0) final ∧
        final workingTape = encoded (domains enumeration workingTape) sizes matrix ∧
        final (dataTape 3) = encoded (FieldRow.scalarDomain enumeration) Empty.elim (0 : Scalar) ∧
        (∀ name, name ≠ workingTape → name ≠ dataTape 3 → final name = initial name) := by
  let matrixBound := ((FieldRow.scalarDomain enumeration).constant.arrayOfLength StandardMatrixEntry.length).widthPolynomial
  refine ⟨2 * matrixBound + MvPolynomial.C
    (2 * (FieldRow.scalarDomain enumeration).width Empty.elim + 4), ?_⟩
  intro sizes initial matrix matrixEq regions
  let zeroTape := encoded (FieldRow.scalarDomain enumeration) Empty.elim (0 : Scalar)
  let seeded := Function.update initial (dataTape 3) zeroTape
  have zeroTrace := seedZero_runs enumeration sizes initial (regions (dataTape 3))
  have matrixSource : seeded originalTape = encoded (domains enumeration originalTape) sizes matrix :=
    (Function.update_of_ne (by decide) _ _).trans matrixEq
  have copyTrace := StandardTapeCommands.copy_encoded_runs (domains enumeration originalTape)
    sizes matrix originalTape workingTape (by decide)
    (fun name => (domains enumeration name).width sizes) readOnly rfl rfl rfl seeded matrixSource
    (zeroTrace.region workingTape (regions workingTape))
  let final := Function.update seeded workingTape (encoded (domains enumeration workingTape) sizes matrix)
  have sameDomain : domains enumeration originalTape = domains enumeration workingTape := rfl
  have sameEncoding : encoded (domains enumeration originalTape) sizes matrix =
      encoded (domains enumeration workingTape) sizes matrix := rfl
  have complete := zeroTrace.sequence seedMatrix 0 (seedZero_halt enumeration) copyTrace
  refine ⟨(2 * (zeroBits enumeration).length + 1) +
    (2 * (domains enumeration originalTape).width sizes + 2) + 1, final, ?_, ?_,
    Function.update_self _ _ _, ?_, ?_⟩
  · have matrixWidth : (domains enumeration originalTape).width sizes = MvPolynomial.eval sizes matrixBound := rfl
    rw [matrixWidth]
    simp only [matrixBound, map_add, map_mul, map_ofNat, MvPolynomial.eval_C, zeroBits, List.length_ofFn]
    omega
  · simpa only [seed, seedEntry, seedExit, seedMatrix, final, sameEncoding, sameDomain] using complete
  · exact (Function.update_of_ne (by decide) _ _).trans (Function.update_self _ _ _)
  · intro name notMatrix notScalar
    exact (Function.update_of_ne notMatrix _ _).trans (Function.update_of_ne notScalar _ _)

def rowsWiring : StandardMatrixRows.TapeName ↪ TapeName :=
  ⟨(fun name => .inl (.inl (.inl (.inl name)))), by
    intro first second equal
    cases equal
    rfl⟩

@[simp] theorem rowsWiring_apply (name : StandardMatrixRows.TapeName) :
    rowsWiring name = .inl (.inl (.inl (.inl name))) := rfl

noncomputable def rowWorkspace : Machine Alphabet (Pipeline.State StandardMatrixRows.InitStageState) :=
  MultiTape.wire rowsWiring StandardMatrixRows.initialization

@[simp] theorem rowWorkspace_halt (symbols : Symbols Alphabet) : rowWorkspace none symbols = none := by
  simp [rowWorkspace, MultiTape.wire, StandardMatrixRows.initialization, Pipeline.machine]

/-- Reuse the existing nineteen-tape row initializer inside the column-clear
caller. Its matrix and scalar sources come from the seed phase; every old
writable word may still contain arbitrary symbols. -/
theorem rowWorkspace_runs (enumeration : Scalar ≃ Fin cardinality) (sizes : Fin 3 → ℕ)
    (matrix : ((FieldRow.scalarDomain enumeration).constant.arrayOfLength
      StandardMatrixEntry.length).Carrier sizes) (initial : Tapes Alphabet)
    (matrixEq : initial workingTape = encoded (domains enumeration workingTape) sizes matrix)
    (zeroEq : initial (dataTape 3) = encoded (FieldRow.scalarDomain enumeration) Empty.elim (0 : Scalar))
    (header : initial (sizeTape 0) = unary (sizes 0))
    (regions : ∀ name, Region ((domains enumeration name).width sizes) 0 (initial name)) :
    ∃ ticks final, ticks ≤ 19 *
      (2 * ((FieldRow.scalarDomain enumeration).constant.arrayOfLength StandardMatrixEntry.length).width sizes +
        2 * (FieldRow.scalarDomain enumeration).width Empty.elim + 2 * sizes 0 + 3) ∧
      Runs (fun name => (domains enumeration name).width sizes) readOnly rowWorkspace ticks
        (Pipeline.position StandardMatrixRows.initEntry 0) (fun _ => 0) initial none (fun _ => 0) final ∧
      final workingTape = encoded (domains enumeration workingTape) sizes matrix ∧
      final (dataTape 3) = encoded (FieldRow.scalarDomain enumeration) Empty.elim (0 : Scalar) ∧
      (∀ name, StandardMatrixRows.readOnly name = false →
        ∃ value : (domains enumeration (rowsWiring name)).Carrier sizes,
          final (rowsWiring name) = encoded (domains enumeration (rowsWiring name)) sizes value) ∧
      (∀ name, name ∉ Set.range rowsWiring → final name = initial name) := by
  obtain ⟨ticks, localFinal, cost, localTrace, workEq, resultEq, counterEq, canonical⟩ :=
    StandardMatrixRows.initialization_runs (FieldRow.scalarDomain enumeration) sizes (0 : Scalar)
      matrix (fun name => initial (rowsWiring name)) matrixEq zeroEq header
      (fun name => regions (rowsWiring name))
  have trace := localTrace.wire rowsWiring
    (fun name => (domains enumeration name).width sizes) readOnly (fun _ => rfl)
    (by intro name premise; fin_cases name <;> first | rfl | contradiction)
    initial (fun _ => 0)
  have start : install rowsWiring (fun name => initial (rowsWiring name)) initial = initial :=
    install_self rowsWiring initial
  have positions : install rowsWiring
      (fun _ : StandardMatrixRows.TapeName => (0 : ℤ))
      (fun _ : TapeName => (0 : ℤ)) = fun _ => 0 := install_self rowsWiring _
  rw [start, positions] at trace
  refine ⟨ticks, install rowsWiring localFinal initial, cost, trace, ?_, ?_, ?_, ?_⟩
  · exact (install_at rowsWiring localFinal initial StandardMatrixRows.inputTape).trans
      ((localTrace.readOnly_tape _ rfl).trans matrixEq)
  · exact (install_at rowsWiring localFinal initial (StandardMatrixRows.dataTape 3)).trans
      ((localTrace.readOnly_tape _ rfl).trans zeroEq)
  · intro name writable
    obtain ⟨value, encodedValue⟩ := canonical name writable
    exact ⟨value, (install_at rowsWiring localFinal initial name).trans encodedValue⟩
  · intro name outside
    exact install_outside rowsWiring localFinal initial name outside

def finishTarget (stage : Fin 5) : TapeName := match stage.val with
  | 0 => dataTape 1 | 1 => nextTape | 2 => differenceTape | 3 => guardTape | _ => limitTape

theorem finishTarget_injective : Function.Injective finishTarget := by
  intro first second equal
  fin_cases first <;> fin_cases second <;>
    simp_all [finishTarget, dataTape, nextTape, differenceTape, guardTape, limitTape,
      StandardGaussJordanClearInterval.dataTape, StandardGaussJordanClearStep.dataTape,
      StandardGaussJordanClearStep.nextTape,
      StandardGaussJordanClearInterval.differenceTape, StandardGaussJordanClearInterval.guardTape,
      StandardGaussJordanClearInterval.limitTape]

def finishReadOnly (name : TapeName) : Bool :=
  if name = dataTape 1 ∨ name = nextTape ∨ name = differenceTape ∨
      name = guardTape ∨ name = limitTape then false else true

def FinishStageState (stage : Fin 5) : Type :=
  if stage.val < 3 then StandardBinaryScan.State Unit else if stage = 3 then Bool else Fin 3

instance finishStageFinite (stage : Fin 5) : Fintype (FinishStageState stage) := by
  unfold FinishStageState
  split_ifs <;> infer_instance

noncomputable def finishStage (stage : Fin 5) : Machine Alphabet (FinishStageState stage) := by
  unfold FinishStageState
  split_ifs
  · exact StandardTapeCommands.clear (sizeTape 0) (finishTarget stage) (by
      fin_cases stage <;> decide)
  · exact StandardTapeCommands.setBoolean (finishTarget stage) false
  · exact StandardTapeCommands.copy (dataTape 0) (finishTarget stage) (by
      fin_cases stage <;> decide)

def finishEntry (stage : Fin 5) : FinishStageState stage := by
  unfold FinishStageState
  split_ifs
  · exact .inl ()
  · exact false
  · exact 0

def finishExit (stage : Fin 5) : FinishStageState stage := by
  unfold FinishStageState
  split_ifs
  · exact .inr ((), true)
  · exact true
  · exact 2

noncomputable def finishInitialization : Machine Alphabet (Pipeline.State FinishStageState) :=
  Pipeline.machine finishStage finishEntry

theorem finishStage_halt (stage : Fin 5) (symbols : Symbols Alphabet) :
    finishStage stage (finishExit stage) symbols = none := by
  fin_cases stage <;> rfl

noncomputable def finishDefault (sizes : Fin 3 → ℕ) (pivot : Fin (2 ^ sizes 0)) (stage : Fin 5) :
    Turing.Tape Binary.Symbol :=
  if stage.val < 3 then encoded (EncodedDomain.binaryNaturals 0) sizes
    (⟨0, by positivity⟩ : Fin (2 ^ sizes 0))
  else if stage = 3 then encoded EncodedDomain.booleans sizes false
  else encoded (EncodedDomain.binaryNaturals 0) sizes pivot

omit [Field Scalar] in
/-- Each finishing command overwrites a single private counter or guard,
using the immutable unary capacity or pivot as its source. -/
theorem finishStage_runs (enumeration : Scalar ≃ Fin cardinality) (sizes : Fin 3 → ℕ)
    (pivot : Fin (2 ^ sizes 0)) (stage : Fin 5) (initial : Tapes Alphabet)
    (pivotEq : initial (dataTape 0) = encoded (EncodedDomain.binaryNaturals 0) sizes pivot)
    (header : initial (sizeTape 0) = unary (sizes 0))
    (regions : ∀ name, Region ((domains enumeration name).width sizes) 0 (initial name)) :
    ∃ ticks, ticks ≤ 2 * sizes 0 + 2 ∧
      Runs (fun name => (domains enumeration name).width sizes) finishReadOnly
        (finishStage stage) ticks (finishEntry stage) (fun _ => 0) initial
        (finishExit stage) (fun _ => 0)
        (Function.update initial (finishTarget stage) (finishDefault sizes pivot stage)) := by
  let width : TapeName → ℕ := fun name => (domains enumeration name).width sizes
  have writable : finishReadOnly (finishTarget stage) = false := by fin_cases stage <;> decide
  by_cases counterStage : stage.val < 3
  · have targetWidth : width (finishTarget stage) = sizes 0 := by
      fin_cases stage <;> solve | norm_num at counterStage | exact EncodedDomain.binaryNaturals_width 0 sizes
    obtain ⟨old, oldLength, oldEq⟩ := (regions (finishTarget stage)).exists_buffer
    have trace := StandardTapeCommands.clear_runs (sizeTape 0) (finishTarget stage)
      (by fin_cases stage <;> decide) width finishReadOnly writable
      (List.replicate (sizes 0) true) old
      (by simp [width, domains, sizeTape, StandardGaussJordanClearInterval.domains,
        StandardGaussJordanClearInterval.sizeTape, StandardGaussJordanClearStep.domains,
        StandardGaussJordanClearStep.sizeTape, StandardGaussJordanClearTarget.domains,
        StandardGaussJordanClearTarget.sizeTape, StandardMatrixRows.domains,
        StandardMatrixRows.sizeTape, StandardMatrixRowStep.domains, StandardMatrixRowEntry.domains,
        EncodedDomain.unary])
      (by simpa only [List.length_replicate] using targetWidth)
      (by simpa only [List.length_replicate] using oldLength.trans targetWidth) initial header oldEq
    have zeroEncoding : encoded (EncodedDomain.binaryNaturals 0) sizes
        (⟨0, by positivity⟩ : Fin (2 ^ sizes 0)) =
        buffer (word (List.replicate (sizes 0) false)) := by
      simpa only [Binary.value_replicate_false] using
        encoded_binaryNaturals (0 : Fin 3) sizes (List.replicate (sizes 0) false) (by simp)
    simp only [List.length_replicate] at trace
    rw [← zeroEncoding] at trace
    refine ⟨2 * sizes 0 + 2, le_refl _, ?_⟩
    fin_cases stage <;> first | exact trace | norm_num at counterStage
  · by_cases booleanStage : stage = 3
    · subst stage
      obtain ⟨old, oldLength, oldEq⟩ := (regions guardTape).exists_buffer
      change old.length = (EncodedDomain.booleans (Parameter := Fin 3)).width sizes at oldLength
      norm_num [EncodedDomain.booleans, EncodedDomain.fixed, EncodedDomain.ofCodec] at oldLength
      obtain ⟨oldBit, rfl⟩ := List.length_eq_one_iff.mp oldLength
      have trace := StandardTapeCommands.setBoolean_runs guardTape false width finishReadOnly
        (by decide) (by
          change (EncodedDomain.booleans (Parameter := Fin 3)).width sizes = 1
          norm_num [EncodedDomain.booleans, EncodedDomain.fixed, EncodedDomain.ofCodec]) initial oldBit oldEq
      refine ⟨1, by omega, ?_⟩
      change Runs width finishReadOnly (StandardTapeCommands.setBoolean guardTape false)
        1 false (fun _ => 0) initial true (fun _ => 0)
        (Function.update initial guardTape (encoded EncodedDomain.booleans sizes false))
      rw [encoded_booleans]
      exact trace
    · have last : stage = 4 := by
        fin_cases stage <;> solve | rfl | norm_num at counterStage | contradiction
      subst stage
      have trace := StandardTapeCommands.copy_encoded_runs (EncodedDomain.binaryNaturals 0)
        sizes pivot (dataTape 0) limitTape (by decide) width finishReadOnly (by decide)
        rfl rfl initial pivotEq (regions limitTape)
      simp only [EncodedDomain.binaryNaturals_width] at trace
      exact ⟨2 * sizes 0 + 2, le_refl _, trace⟩

omit [Field Scalar] in
/-- Initialize every extra counter and guard, including for empty first or
second intervals. Every tape outside these five destinations is preserved. -/
theorem finishInitialization_runs (enumeration : Scalar ≃ Fin cardinality)
    (sizes : Fin 3 → ℕ) (pivot : Fin (2 ^ sizes 0)) (initial : Tapes Alphabet)
    (pivotEq : initial (dataTape 0) = encoded (EncodedDomain.binaryNaturals 0) sizes pivot)
    (header : initial (sizeTape 0) = unary (sizes 0))
    (regions : ∀ name, Region ((domains enumeration name).width sizes) 0 (initial name)) :
    ∃ ticks final, ticks ≤ 5 * (2 * sizes 0 + 3) ∧
      Runs (fun name => (domains enumeration name).width sizes) readOnly finishInitialization ticks
        (Pipeline.position finishEntry 0) (fun _ => 0) initial none (fun _ => 0) final ∧
      (∀ stage, final (finishTarget stage) = finishDefault sizes pivot stage) ∧
      (∀ name, finishReadOnly name = true → final name = initial name) := by
  obtain ⟨ticks, final, cost, trace, outputs⟩ := Pipeline.updates_runs
    (fun name => (domains enumeration name).width sizes) finishReadOnly
    finishStage finishEntry finishExit finishTarget finishTarget_injective
    (finishDefault sizes pivot) (2 * sizes 0 + 2) finishStage_halt initial regions
    (by
      intro stage tapes immutable currentRegions
      exact finishStage_runs enumeration sizes pivot stage tapes
        ((immutable (dataTape 0) (by decide)).trans pivotEq)
        ((immutable (sizeTape 0) (by decide)).trans header) currentRegions)
  refine ⟨ticks, final, cost, ?_, outputs, trace.readOnly_tape⟩
  exact trace.readOnly_mono (by
    intro name readonly
    unfold finishReadOnly
    split_ifs with targeted
    · rcases targeted with equal | equal | equal | equal | equal <;> subst name <;> contradiction
    · rfl)

end Polytime2.StandardGaussJordanClear

