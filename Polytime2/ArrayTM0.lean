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


import Polytime2.TM0Input
import Polytime2.Array

/-! # Polynomial TM0 realization of indexed array access

Instantiate the general simulator on the lookup/update machines. Their existing
mathematical contract supplies the exact resulting array and element; a shared
input storage estimate justifies the canonical single-tape input encoding.
-/

namespace Polytime2.Array

open MultiTape

-- parameterLevel: names of runtime sizes bounding the array and binary index.
universe parameterLevel

/-- All five argument and scratch tapes have polynomially bounded input storage. -/
theorem frame_fits (width : ℕ) (index element counter : List Bool) (flag : Bool)
    (blocks : List (List Bool)) (widths : ∀ block ∈ blocks, block.length = width)
    (elementLength : element.length = width) (counterLength : counter.length = index.length) :
    ∀ name, Fits (width * blocks.length + index.length + width + 3)
      (frame index [] blocks.flatten element counter flag name) := by
  intro name
  have flattened : blocks.flatten.length = width * blocks.length := by
    simpa [Nat.mul_comm] using blocks_length width blocks widths
  cases name with
  | index =>
    refine ⟨[3], Binary.word index ++ [0], rfl, ?_⟩
    simp [Binary.word]
    omega
  | array =>
    refine ⟨[3], Binary.word blocks.flatten ++ [0], rfl, ?_⟩
    simp only [Binary.word, List.length_append, List.length_cons, List.length_nil, List.length_map, flattened]
    omega
  | element =>
    refine ⟨[3], Binary.word element ++ [0], rfl, ?_⟩
    simp [Binary.word, elementLength]
    omega
  | counter =>
    refine ⟨[3], Binary.word counter ++ [0], rfl, ?_⟩
    simp [Binary.word, counterLength]
    omega
  | flag =>
    refine ⟨[], [Binary.data flag], rfl, ?_⟩
    simp

/-- Lookup and update have full polynomial TM0 certificates with their exact
mathematical output frames. The compiled machine is fixed before runtime sizes,
indices, and array contents; the tape catalogue comes from the finite signature. -/
theorem realizes_tm0 {Parameter : Type parameterLevel} [Fintype Parameter]
    (width : ℕ) (write : Bool) (arrayCapacity digitCapacity : MvPolynomial Parameter ℕ) :
    let names := (Finset.univ : Finset TapeName).toList
    let inputCapacity := MvPolynomial.C width * arrayCapacity + digitCapacity + MvPolynomial.C (width + 3)
    let program := TM0Input.machine (SingleTape.compile (Simulation.machine names (access width write)))
      (.inl (Simulation.entry names (.inl (.inl (.inl 0)))))
    ∃ timeBound rowBound : MvPolynomial Parameter ℕ,
      ∀ assignment index element counter flag (blocks : List (List Bool)),
        blocks.length ≤ MvPolynomial.eval assignment arrayCapacity →
        index.length ≤ MvPolynomial.eval assignment digitCapacity →
        (∀ block ∈ blocks, block.length = width) →
        ∀ valid : Binary.value index < blocks.length,
          element.length = width → counter.length = index.length →
          ∃ ticks finalRows, ticks ≤ MvPolynomial.eval assignment timeBound ∧
            finalRows.length ≤ MvPolynomial.eval assignment rowBound ∧
            Tracks.Represents finalRows (frame index []
              (if write then blocks.set (Binary.value index) element else blocks).flatten
              (if write then element else blocks[Binary.value index]) (List.replicate index.length false) false) ∧
            (fun current => current.bind (Turing.TM0.step program))^[ticks]
              (some (Turing.TM0.init (Sweep.leftMarker ::
                ((Tracks.initialRows (MvPolynomial.eval assignment inputCapacity)
                  (frame index [] blocks.flatten element counter flag)).map Sweep.row ++ [Sweep.rightMarker])))) =
              some (TM0Input.embed (SingleTape.configuration (.inr (.inr ()), Sweep.tape [Sweep.leftMarker]
                (finalRows.map Sweep.row ++ [Sweep.rightMarker])))) ∧
            Turing.TM0.step program
              (TM0Input.embed (SingleTape.configuration (.inr (.inr ()), Sweep.tape [Sweep.leftMarker]
                (finalRows.map Sweep.row ++ [Sweep.rightMarker])))) = none := by
  intro names inputCapacity program
  have inputFits : ∀ assignment initial,
      (∃ index element counter flag blocks,
        blocks.length ≤ MvPolynomial.eval assignment arrayCapacity ∧
        index.length ≤ MvPolynomial.eval assignment digitCapacity ∧
        Represents width index element counter flag blocks initial ∧ Binary.value index < blocks.length) →
      ∀ name, Fits (MvPolynomial.eval assignment inputCapacity) (initial name) := by
    intro assignment initial valid name
    obtain ⟨index, element, counter, flag, blocks, arrayBound, digitBound,
      ⟨widths, elementLength, counterLength, rfl⟩, _⟩ := valid
    apply (frame_fits width index element counter flag blocks widths elementLength counterLength name).mono
    have multiplied := Nat.mul_le_mul_left width arrayBound
    simp only [inputCapacity, map_add, map_mul, MvPolynomial.eval_C]
    omega
  obtain ⟨timeBound, rowBound, runs⟩ := Simulation.realizes_input names
    (Finset.nodup_toList _) (by intro name; simp [names]) (realizes width write arrayCapacity digitCapacity) inputCapacity inputFits
  refine ⟨timeBound, rowBound, ?_⟩
  intro assignment index element counter flag blocks arrayBound digitBound widths valid elementLength counterLength
  have represented : Represents width index element counter flag blocks
      (frame index [] blocks.flatten element counter flag) := ⟨widths, elementLength, counterLength, rfl⟩
  obtain ⟨ticks, finalRows, final, time, space, correct, output, trace, halted⟩ := runs assignment
    (frame index [] blocks.flatten element counter flag)
    ⟨index, element, counter, flag, blocks, arrayBound, digitBound, represented, valid⟩
  have finalValue := correct index element counter flag blocks represented valid
  subst final
  exact ⟨ticks, finalRows, time, space, output, trace, halted⟩

end Polytime2.Array
