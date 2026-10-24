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

import Polytime2.Matrices.IntegerHermiteStage
import Polytime2.Arrays.PrefixFlags
import Polytime2.Arrays.ZipWith

/-! # A certified Hermite stage on a runtime prefix

The input contains a fixed-length row array and an ordinary prefix length.
Only that prefix must be distinct and exclude the source and incoming rows.
The inactive suffix is unrestricted. The implementation prepares private
selection flags, eliminates once, and runs the fixed-workspace prefix fold.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain Realizable.Internal

variable {Parameter : Type} [Fintype Parameter]

private noncomputable def inputs (rows columns width length : MvPolynomial Parameter ℕ) : Fin 7 → EncodedDomain Parameter
  | 0 | 1 => boundedIndex rows
  | 2 => boundedIndex columns
  | 3 => integerMatrices rows columns width
  | 4 => integerMatrices rows rows width
  | 5 => (boundedIndex rows).arrayOfLength length
  | 6 => arrayPosition (length + 1)

private def allowed (rows columns width length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : ∀ name, (inputs rows columns width length name).Carrier sizes) :=
  arguments 0 ≠ arguments 1 ∧ 0 < (arguments 3).val (arguments 0) (arguments 2) ∧
    ((List.ofFn (arguments 5)).take (arguments 6).val).Nodup ∧
    arguments 0 ∉ (List.ofFn (arguments 5)).take (arguments 6).val ∧
    arguments 1 ∉ (List.ofFn (arguments 5)).take (arguments 6).val

/-- Normalize only the selected prefix, with no admissibility requirement on the inactive suffix. -/
noncomputable def integerHermiteRowStagePrefix (rows columns width length : MvPolynomial Parameter ℕ) :
    Computation Parameter (Fin 7) where
  inputDomains := inputs rows columns width length
  outputDomain := hermiteColumnState rows columns (hermiteStageWorkspace width)
  precondition := allowed rows columns width length
  compute sizes arguments :=
    let result := IntegerMatrix.hermiteRowStage (Row := Fin (MvPolynomial.eval sizes rows))
      (Column := Fin (MvPolynomial.eval sizes columns)) (arguments.val 0) (arguments.val 1) (arguments.val 2)
      ((List.ofFn (arguments.val 5)).take (arguments.val 6).val) (arguments.val 3).val (arguments.val 4).val
    have bound := IntegerMatrix.hermiteRowStage_bound (Row := Fin (MvPolynomial.eval sizes rows))
      (Column := Fin (MvPolynomial.eval sizes columns)) (MvPolynomial.eval sizes width)
      (MvPolynomial.eval sizes width) (MvPolynomial.eval sizes width) (arguments.val 0) (arguments.val 1)
      arguments.property.1 (arguments.val 2) ((List.ofFn (arguments.val 5)).take (arguments.val 6).val)
      arguments.property.2.2.1 arguments.property.2.2.2.1 (arguments.val 3).val (arguments.val 4).val
      arguments.property.2.1 (fun row => (arguments.val 3).property row (arguments.val 2))
      (arguments.val 3).property (arguments.val 4).property
    have capacity : MvPolynomial.eval sizes width + (3 * MvPolynomial.eval sizes width + 3) =
        MvPolynomial.eval sizes (hermiteStageWorkspace width) := by
      simp only [hermiteStageWorkspace, map_add, map_mul, map_ofNat, map_one]
      omega
    (⟨result.1, fun row column => (bound.1 row column).trans_le (pow_le_pow_right₀ (by decide) capacity.le)⟩,
      ⟨result.2, fun row column => (bound.2 row column).trans_le (pow_le_pow_right₀ (by decide) capacity.le)⟩)

private noncomputable def elimination (rows columns width length : MvPolynomial Parameter ℕ) :=
  ((integerHermiteRowStep rows columns width).withArguments (inputs rows columns width length)
    (Fin.castLEEmb (by decide : 5 ≤ 7)) (by intro name; fin_cases name <;> rfl)).withPrecondition
    (allowed rows columns width length) (fun _ _ valid => ⟨valid.1, valid.2.1⟩)

private theorem elimination_realizable (rows columns width length : MvPolynomial Parameter ℕ) :
    (elimination rows columns width length).Realizable :=
  ((integerHermiteRowStep_realizable rows columns width).withArguments (inputs rows columns width length)
    (Fin.castLEEmb (by decide : 5 ≤ 7)) (by intro name; fin_cases name <;> rfl)).withPrecondition
    (allowed rows columns width length) (fun _ _ valid => ⟨valid.1, valid.2.1⟩)

private noncomputable def selectedTokens (rows columns width length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerHermiteRowStagePrefix rows columns width length).Arguments sizes //
      (integerHermiteRowStagePrefix rows columns width length).precondition sizes arguments}) :
    ((booleans.prod (boundedIndex rows)).arrayOfLength length).Carrier sizes :=
  fun index => (decide (index.val < (arguments.val 6).val), arguments.val 5 index)

private theorem selectedTokens_realizable (rows columns width length : MvPolynomial Parameter ℕ) :
    (Computation.mk (inputs rows columns width length) ((booleans.prod (boundedIndex rows)).arrayOfLength length)
      (allowed rows columns width length) (selectedTokens rows columns width length)).Realizable := by
  let host := inputs rows columns width length
  let valid := allowed rows columns width length
  let operation (_sizes : Parameter → ℕ) (_context : ∀ name : Empty, (Empty.elim name : EncodedDomain Parameter).Carrier _sizes)
      (flag : booleans.Carrier _sizes) (row : (boundedIndex rows).Carrier _sizes) := (flag, row)
  let step := arrayZipWithStep (Context := Empty) Empty.elim booleans (boundedIndex rows) (booleans.prod (boundedIndex rows)) operation
  have stepReady : step.Realizable := (Realizable.argument step.inputDomains (.inr false) step.precondition).prodMk (Realizable.argument step.inputDomains (.inr true) step.precondition)
  have flags := ((arrayPrefixFlags_realizable length).withArguments host (MultiTape.oneTape 6) (by intros; rfl)).withPrecondition
    valid (by intros; trivial)
  have zipped := (arrayZipWith_realizable (Context := Empty) Empty.elim booleans (boundedIndex rows)
    (booleans.prod (boundedIndex rows)) length operation stepReady).onResults host valid
    (fun name sizes arguments => match name with
      | .inl impossible => impossible.elim
      | .inr false => (arrayPrefixFlags length).compute sizes ⟨(fun _ => arguments.val 6), trivial⟩
      | .inr true => arguments.val 5)
    (by intros; trivial) (by
      intro name
      rcases name with impossible | choice
      · exact impossible.elim
      · cases choice
        · exact flags
        · exact Realizable.argument host 5 valid)
  exact zipped.withSpecification valid (selectedTokens rows columns width length) (by intros; assumption) (by intros; rfl)

private noncomputable def controllerArguments (rows columns width length : MvPolynomial Parameter ℕ)
    (name : Fin 3 ⊕ Bool) (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerHermiteRowStagePrefix rows columns width length).Arguments sizes //
      (integerHermiteRowStagePrefix rows columns width length).precondition sizes arguments}) :
    ((hermiteStagePrefixController rows columns width length).inputDomains name).Carrier sizes :=
  match name with
  | .inl 0 => arguments.val 0
  | .inl 1 => arguments.val 1
  | .inl 2 => arguments.val 2
  | .inr false => (elimination rows columns width length).compute sizes arguments
  | .inr true => selectedTokens rows columns width length sizes arguments

private theorem countBound (rows columns width length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (integerHermiteRowStagePrefix rows columns width length).Arguments sizes) :
    (arguments 6).val ≤ MvPolynomial.eval sizes length := by
  have bounded := (arguments 6).isLt
  simp only [map_add, map_one] at bounded
  omega

private theorem controller_permitted (rows columns width length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerHermiteRowStagePrefix rows columns width length).Arguments sizes //
      (integerHermiteRowStagePrefix rows columns width length).precondition sizes arguments}) :
    (hermiteStagePrefixController rows columns width length).precondition sizes
      (fun name => controllerArguments rows columns width length name sizes arguments) := by
  refine ⟨(arguments.val 6).val, ?_, (arguments.val 3).val, (arguments.val 4).val, ?_⟩
  · exact ⟨countBound rows columns width length sizes arguments.val, (by intros; rfl), arguments.property.2.2.1,
      arguments.property.2.2.2.1, arguments.property.2.2.2.2⟩
  · exact ⟨arguments.property.1, arguments.property.2.1, (arguments.val 3).property, (arguments.val 4).property, rfl⟩

/-- All comparisons, token preparation, skipped states, and stage updates are certified by composition. -/
theorem integerHermiteRowStagePrefix_realizable (rows columns width length : MvPolynomial Parameter ℕ) :
    (integerHermiteRowStagePrefix rows columns width length).Realizable := by
  let computation := integerHermiteRowStagePrefix rows columns width length
  have complete := (hermiteStagePrefixController_realizable rows columns width length).onResults
    computation.inputDomains computation.precondition (controllerArguments rows columns width length)
    (controller_permitted rows columns width length) (by
      intro name
      rcases name with name | choice
      · fin_cases name
        · exact Realizable.argument computation.inputDomains 0 computation.precondition
        · exact Realizable.argument computation.inputDomains 1 computation.precondition
        · exact Realizable.argument computation.inputDomains 2 computation.precondition
      · cases choice
        · exact elimination_realizable rows columns width length
        · exact selectedTokens_realizable rows columns width length)
  apply complete.withSpecification computation.precondition computation.compute (by intros; assumption)
  intro sizes arguments valid
  have raw := hermiteStagePrefixController_correct rows columns width length sizes
    ⟨fun name => controllerArguments rows columns width length name sizes ⟨arguments, valid⟩,
      controller_permitted rows columns width length sizes ⟨arguments, valid⟩⟩ (arguments 6).val
    ⟨countBound rows columns width length sizes arguments, (by intros; rfl), valid.2.2.1, valid.2.2.2.1, valid.2.2.2.2⟩
    (arguments 3).val (arguments 4).val
    ⟨valid.1, valid.2.1, (arguments 3).property, (arguments 4).property, rfl⟩
  exact Prod.ext (Subtype.ext (congrArg Prod.fst raw)) (Subtype.ext (congrArg Prod.snd raw))

/-- The returned matrices equal the mathematical stage on precisely the selected prefix. -/
theorem integerHermiteRowStagePrefix_correct (rows columns width length : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerHermiteRowStagePrefix rows columns width length).Arguments sizes //
      (integerHermiteRowStagePrefix rows columns width length).precondition sizes arguments}) :
    let result := (integerHermiteRowStagePrefix rows columns width length).compute sizes arguments
    (result.1.val, result.2.val) = IntegerMatrix.hermiteRowStage
      (Row := Fin (MvPolynomial.eval sizes rows)) (Column := Fin (MvPolynomial.eval sizes columns))
      (arguments.val 0) (arguments.val 1) (arguments.val 2)
      ((List.ofFn (arguments.val 5)).take (arguments.val 6).val) (arguments.val 3).val (arguments.val 4).val := rfl

end Polytime2.Computation

