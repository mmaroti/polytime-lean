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

import Polytime2.AddMultiplyInput
import Polytime2.BinaryOutput

/-! # External addition followed by multiplication

Only a width header and binary operands are supplied. All working tapes start
blank. The algorithm proof composes mathematical preparation and arithmetic
contracts; the external adapter supplies simulation and physical extraction.
-/

namespace Polytime2.AddMultiplyExternal

open MultiTape
open AddMultiplyInput (Input Alphabet inputWord workWiring)
open Binary (value)

noncomputable def arithmetic : Machine Alphabet (Sum BinaryAddition.State BinaryMultiplication.State) := wire workWiring AddMultiply.machine
abbrev State := Sum AddMultiplyInput.State (Sum BinaryAddition.State BinaryMultiplication.State)

noncomputable def machine : Machine Alphabet State := sequence AddMultiplyInput.machine arithmetic (.inl (.inl false))
def entry : State := Sum.inl AddMultiplyInput.entry
def exit : State := Sum.inr (.inr BinaryMultiplication.exit)

-- Size name false is the encoded addend width; true is the multiplier width.
def hypothesis (sizes : Bool → ℕ) (input : Input) : Prop :=
  input.2.1.length = input.1.length ∧ input.1.length = sizes false ∧ input.2.2.length = sizes true

def compute (input : Input) : ℕ := (value input.1 + value input.2.1) * value input.2.2

noncomputable def outputCapacity : MvPolynomial Bool ℕ := MvPolynomial.X false + 1 + MvPolynomial.X true
noncomputable def inputCapacity : MvPolynomial Bool ℕ := 3 * MvPolynomial.X false + 2 * MvPolynomial.X true + 3

private theorem initial_eq (input : Input) :
    BinaryOutput.initial 7 (inputWord input) = AddMultiplyInput.preparedAt input 0 := by
  rw [BinaryOutput.initial_eq]
  funext name
  fin_cases name <;> rfl

/-- Preparation followed by arithmetic, proved only through mathematical
contracts. Controller injections, tape updates, and runtime witnesses are hidden. -/
theorem contract : Computes machine entry exit
    (fun _sizes : Bool → ℕ => fun input tapes => tapes = BinaryOutput.initial 7 (inputWord input))
    (BinaryOutput.representation 2 outputCapacity) hypothesis (fun _ => compute) := by
  have composed := AddMultiplyInput.contract.sequence (AddMultiply.contract.wire workWiring)
    (by intro sizes input valid; exact valid)
  apply composed.adapt
  · intro sizes input valid; exact ⟨valid.1, valid.2.1.le, valid.2.2.le⟩
  · intro sizes input tapes represented
    simpa only [initial_eq] using represented
  · intro sizes result tapes encoded
    change ∃ bits, value bits = result ∧ bits.length ≤ sizes false + 1 + sizes true ∧
      tapes 2 = BinaryMultiplication.tape bits at encoded
    simpa only [AddMultiply.outputRepresentation, BinaryOutput.representation, outputCapacity,
      map_add, map_one, MvPolynomial.eval_X, workWiring, BinaryMultiplication.tape] using encoded

private theorem input_bound (sizes : Bool → ℕ) (input : Input) (valid : hypothesis sizes input) :
    (inputWord input).length ≤ MvPolynomial.eval sizes inputCapacity := by
  simp only [inputWord, AddMultiplyInput.sizeField, List.length_append, List.length_replicate,
    List.length_singleton, Binary.word, List.length_map, inputCapacity, map_add, map_mul,
    map_ofNat, MvPolynomial.eval_X]
  obtain ⟨sameLength, leftWidth, multiplierWidth⟩ := valid
  omega

/-- A finite TM0 machine computes `(a + b) * c` from width-encoded operands
and blank working tapes, leaving just binary output and a restored physical
head. Every preparation, computation, simulation, and extraction step is charged. -/
theorem realizes_output_tm0 :
    let names := (Finset.univ : Finset (Fin 10)).toList
    let source := sequence (Simulation.machine names machine) (BinaryOutput.extract 7 2) 0
    let program := TM0Input.machine (SingleTape.compile source) (.inl (.inl (Simulation.entry names entry)))
    ∃ bound : MvPolynomial Bool ℕ,
      ∀ sizes input, hypothesis sizes input →
        ∃ ticks bits, ticks ≤ MvPolynomial.eval sizes bound ∧ value bits = compute input ∧
          bits.length ≤ sizes false + 1 + sizes true ∧
          (fun current => current.bind (Turing.TM0.step program))^[ticks]
            (some (Turing.TM0.init (Sweep.leftMarker ::
              ((BinaryOutput.inputRows 7 (inputWord input)).map Sweep.row ++ [Sweep.rightMarker])))) =
            some (TM0Input.embed (SingleTape.configuration (.inr 7, Sweep.tape []
              (TrackOutput.word (BinaryOutput.outputLetter 7) bits)))) ∧
          Turing.TM0.step program (TM0Input.embed (SingleTape.configuration (.inr 7, Sweep.tape []
            (TrackOutput.word (BinaryOutput.outputLetter 7) bits)))) = none := by
  simpa only [outputCapacity, map_add, map_one, MvPolynomial.eval_X] using
    BinaryOutput.realizes_output_tm0 7 2 (fun _ => inputWord) hypothesis (fun _ => compute)
      inputCapacity outputCapacity input_bound contract

end Polytime2.AddMultiplyExternal
