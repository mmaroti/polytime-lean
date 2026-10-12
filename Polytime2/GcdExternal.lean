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

import Polytime2.Wiring
import Polytime2.GcdInput

/-! # Complete external binary gcd

A fixed finite machine reads a width and two padded binary operands with blank
working tapes. Preparation and gcd compose through mathematical contracts;
the output adapter includes TM0 simulation and erases the whole workspace.
-/

namespace Polytime2.GcdExternal

open MultiTape
open GcdInput (Input Alphabet inputWord workWiring)
open Binary (value)

noncomputable def arithmetic : Machine Alphabet GcdMachine.State := wire workWiring GcdMachine.machine
abbrev State := Sum GcdInput.State GcdMachine.State
noncomputable def machine : Machine Alphabet State := sequence GcdInput.machine arithmetic GcdMachine.entry

def entry : State := .inl GcdInput.entry
def exit : State := .inr GcdMachine.exit
abbrev hypothesis := GcdInput.hypothesis

def compute (input : Input) : ℕ := Nat.gcd (value input.1) (value input.2)

noncomputable def inputCapacity : MvPolynomial Unit ℕ := 3 * MvPolynomial.X () + 5
noncomputable def outputCapacity : MvPolynomial Unit ℕ := MvPolynomial.X () + 1

private theorem initial_eq (input : Input) :
    BinaryOutput.initial 4 (inputWord input) = GcdInput.preparedAt input 0 := by
  rw [BinaryOutput.initial_eq]
  funext name
  fin_cases name <;> rfl

/-- Mathematical preparation and gcd contracts compose without exposing their
controller sums, scratch layouts, or polynomial runtime witnesses. -/
theorem contract : Computes machine entry exit
    (fun _sizes : Unit → ℕ => fun input tapes => tapes = BinaryOutput.initial 4 (inputWord input))
    (BinaryOutput.representation 0 outputCapacity) hypothesis (fun _ => compute) := by
  have composed := GcdInput.contract.sequence (GcdMachine.contract.wire workWiring)
    (by intro sizes input valid; exact valid.2.2)
  apply composed.adapt
  · intro _ _ valid; exact valid
  · intro _ _ _ represented
    simpa only [initial_eq] using represented
  · intro sizes result tapes encoded
    change BinaryOutput.representation 0 outputCapacity sizes result tapes at encoded
    exact encoded

private theorem input_bound (sizes : Unit → ℕ) (input : Input) (valid : hypothesis sizes input) :
    (inputWord input).length ≤ MvPolynomial.eval sizes inputCapacity := by
  simp only [inputWord, GcdInput.sizeField, List.length_append, List.length_replicate,
    List.length_singleton, Binary.word, List.length_map, inputCapacity, map_add, map_mul,
    map_ofNat, MvPolynomial.eval_X]
  obtain ⟨firstWidth, secondWidth, _⟩ := valid
  omega

/-- Complete polynomial-time TM0 realization of binary gcd, including zero
operands. The input supplies no prepared workspace; the output contains only
binary result letters, with the physical head restored to their beginning. -/
theorem realizes_output_tm0 :
    let names := (Finset.univ : Finset (Fin 6)).toList
    let source := sequence (Simulation.machine names machine) (BinaryOutput.extract 4 0) 0
    let program := TM0Input.machine (SingleTape.compile source) (.inl (.inl (Simulation.entry names entry)))
    ∃ bound : MvPolynomial Unit ℕ,
      ∀ sizes input, hypothesis sizes input →
        ∃ ticks bits, ticks ≤ MvPolynomial.eval sizes bound ∧ value bits = compute input ∧
          bits.length ≤ sizes () + 1 ∧
          (fun current => current.bind (Turing.TM0.step program))^[ticks]
            (some (Turing.TM0.init (Sweep.leftMarker ::
              ((BinaryOutput.inputRows 4 (inputWord input)).map Sweep.row ++ [Sweep.rightMarker])))) =
            some (TM0Input.embed (SingleTape.configuration (.inr 7, Sweep.tape []
              (TrackOutput.word (BinaryOutput.outputLetter 4) bits)))) ∧
          Turing.TM0.step program (TM0Input.embed (SingleTape.configuration (.inr 7, Sweep.tape []
            (TrackOutput.word (BinaryOutput.outputLetter 4) bits)))) = none := by
  simpa only [outputCapacity, map_add, map_one, MvPolynomial.eval_X] using
    BinaryOutput.realizes_output_tm0 4 0 (fun _ => inputWord) hypothesis (fun _ => compute)
      inputCapacity outputCapacity input_bound contract

end Polytime2.GcdExternal
