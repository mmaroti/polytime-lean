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


import Polytime2.TM0.Simulation
import Polytime2.Machine.Storage

/-! # Canonical initial track encoding of bounded source tapes

Align all source heads in a central row and take a fixed bounded number of
cells from each side. Polynomial source storage yields a polynomial row count.
This is the input encoding of the simulator, not a free runtime preparation
operation on a different external input format.
-/

namespace Polytime2.Tracks

open MultiTape

-- tapeLevel: source tape names; symbolLevel: their alphabets.
universe tapeLevel symbolLevel

variable {TapeName : Type tapeLevel} {Alphabet : TapeName → Type symbolLevel}
variable [∀ name, Inhabited (Alphabet name)]

/-- All initial heads are aligned; unused cells on either side are blank. -/
def initialRows (capacity : ℕ) (tapes : Tapes Alphabet) : List (Row Alphabet) :=
  (List.ofFn (fun index : Fin capacity =>
    ((fun name => (tapes name).left.nth index), fun _ => false))).reverse ++
  (MultiTape.read tapes, fun _ => true) ::
    List.ofFn (fun index : Fin capacity =>
      ((fun name => (tapes name).right.nth index), fun _ => false))

@[simp] theorem initialRows_length (capacity : ℕ) (tapes : Tapes Alphabet) :
    (initialRows capacity tapes).length = 2 * capacity + 1 := by
  simp [initialRows]
  omega

private theorem half_encoding {Symbol : Type symbolLevel} [Inhabited Symbol]
    (word : List Symbol) (capacity : ℕ) (bounded : word.length ≤ capacity) :
    Turing.ListBlank.mk (List.ofFn (fun index : Fin capacity => (Turing.ListBlank.mk word).nth index)) =
      Turing.ListBlank.mk word := by
  apply Turing.ListBlank.ext
  intro index
  simp only [Turing.ListBlank.nth_mk]
  by_cases within : index < capacity
  · simp [List.getI_eq_getElem?_getD, within]
  · rw [List.getI_eq_default _ (by simp; omega), List.getI_eq_default _ (by omega)]

/-- Every bounded source tape collection has this canonical track encoding;
source storage bounds therefore justify the simulator's input row bound. -/
theorem initialRows_represents (capacity : ℕ) (tapes : Tapes Alphabet)
    (bounded : ∀ name, Fits capacity (tapes name)) : Represents (initialRows capacity tapes) tapes := by
  intro name
  refine ⟨(List.ofFn (fun index : Fin capacity =>
      ((fun name => (tapes name).left.nth index), fun _ => false))).reverse,
    (MultiTape.read tapes, fun _ => true),
    List.ofFn (fun index : Fin capacity =>
      ((fun name => (tapes name).right.nth index), fun _ => false)), rfl, ?_, rfl, ?_, ?_⟩
  · intro entry member
    obtain ⟨index, rfl⟩ := List.mem_ofFn.mp (List.mem_reverse.mp member)
    rfl
  · intro entry member
    obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
    rfl
  · obtain ⟨left, right, presentation, size⟩ := bounded name
    have leftHalf : Turing.ListBlank.mk (List.ofFn (fun index : Fin capacity => (tapes name).left.nth index)) =
        (tapes name).left := by
      rw [presentation]
      simpa only [Turing.Tape.mk'_left] using half_encoding left capacity (by omega)
    have rightHalf : Turing.ListBlank.mk (List.ofFn (fun index : Fin capacity => (tapes name).right.nth index)) =
        (tapes name).right := by
      rw [presentation]
      simpa only [Turing.Tape.mk'_right, Turing.ListBlank.tail_mk] using
        half_encoding right.tail capacity (by simp only [List.length_tail]; omega)
    simp only [List.reverse_reverse, List.map_ofFn, Function.comp_def]
    rw [leftHalf, rightHalf]
    rfl

end Polytime2.Tracks

namespace Polytime2.Simulation

open MultiTape

-- tapeLevel: source tape names; symbolLevel: their alphabets.
-- stateLevel: source controller; parameterLevel: runtime size names.
universe tapeLevel symbolLevel stateLevel parameterLevel

variable {TapeName : Type tapeLevel} [DecidableEq TapeName] [Fintype TapeName]
variable {Alphabet : TapeName → Type symbolLevel} [∀ name, Inhabited (Alphabet name)]
variable [∀ name, Fintype (Alphabet name)] {State : Type stateLevel} [Fintype State]

/-- Polynomial source input storage supplies the canonical TM0 input encoding.
No separate representation or encoded-length hypothesis is required of callers. -/
theorem realizes_encoded {Parameter : Type parameterLevel} [Fintype Parameter]
    (names : List TapeName) (unique : names.Nodup) (complete : ∀ name, name ∈ names)
    {source : Machine Alphabet State} {sourceEntry sourceExit : State}
    {precondition : (Parameter → ℕ) → Tapes Alphabet → Prop}
    {postcondition : (Parameter → ℕ) → Tapes Alphabet → Tapes Alphabet → Prop}
    (certificate : MultiTape.Internal.Realizes source sourceEntry sourceExit precondition postcondition)
    (inputCapacity : MvPolynomial Parameter ℕ)
    (inputFits : ∀ assignment initial, precondition assignment initial →
      ∀ name, Fits (MvPolynomial.eval assignment inputCapacity) (initial name)) :
    ∃ timeBound rowBound : MvPolynomial Parameter ℕ,
      ∀ assignment initial, precondition assignment initial →
        ∃ ticks finalRows final, ticks ≤ MvPolynomial.eval assignment timeBound ∧
          finalRows.length ≤ MvPolynomial.eval assignment rowBound ∧
          postcondition assignment initial final ∧ Tracks.Represents finalRows final ∧
          (fun current => current.bind (Turing.TM0.step (SingleTape.compile (machine names source))))^[ticks]
            (some (SingleTape.configuration (entry names sourceEntry, Sweep.tape [Sweep.leftMarker]
              ((Tracks.initialRows (MvPolynomial.eval assignment inputCapacity) initial).map Sweep.row ++ [Sweep.rightMarker])))) =
            some (SingleTape.configuration (.inr (.inr ()), Sweep.tape [Sweep.leftMarker]
              (finalRows.map Sweep.row ++ [Sweep.rightMarker]))) ∧
          Turing.TM0.step (SingleTape.compile (machine names source))
            (SingleTape.configuration (.inr (.inr ()), Sweep.tape [Sweep.leftMarker]
              (finalRows.map Sweep.row ++ [Sweep.rightMarker]))) = none := by
  obtain ⟨timeBound, rowBound, runs⟩ := realizes names unique complete certificate (2 * inputCapacity + 1)
  refine ⟨timeBound, rowBound, ?_⟩
  intro assignment initial valid
  apply runs assignment initial valid _
    (Tracks.initialRows_represents _ _ (inputFits assignment initial valid))
  simp only [Tracks.initialRows_length, map_add, map_mul, map_ofNat, map_one]
  exact le_rfl

end Polytime2.Simulation
