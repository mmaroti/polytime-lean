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

import Polytime2.Contracts
import Polytime2.Simulation
import Polytime2.SparseInput
import Polytime2.TM0Input
import Polytime2.TrackOutput

/-! # External binary output for finite multi-tape computations

The adapter starts with one external input and blank working tapes. Simulation,
startup, output projection, and erasure are charged once by this theorem.
-/

namespace Polytime2.BinaryOutput

open MultiTape
open Binary (Symbol word value)

-- tapeLevel: tape roles; parameterLevel: size names; inputLevel: logical inputs;
-- stateLevel: the finite controller of the wrapped computation.
universe tapeLevel parameterLevel inputLevel stateLevel
variable {TapeName : Type tapeLevel} [Fintype TapeName] [DecidableEq TapeName]
variable {Parameter : Type parameterLevel} [Fintype Parameter]
variable {Input : (Parameter → ℕ) → Type inputLevel}
variable {Controller : Type stateLevel} [Fintype Controller]

abbrev Alphabet (TapeName : Type tapeLevel) := fun _ : TapeName => Symbol

def initial (inputName : TapeName) (letters : List Symbol) : Tapes (Alphabet TapeName) :=
  Tracks.inputTapes inputName 3 letters.headI letters.tail

omit [Fintype TapeName] in
/-- The header convention adds a single left marker, not prepared working storage. -/
theorem initial_eq (inputName : TapeName) (letters : List Symbol) :
    initial inputName letters = Function.update (fun _ => Binary.tape [] [] ()) inputName (Binary.tape [3] letters ()) := by
  have reconstruct : Turing.ListBlank.mk (letters.headI :: letters.tail) = Turing.ListBlank.mk letters := by
    cases letters with
    | nil => exact Turing.ListBlank.cons_head_tail (Turing.ListBlank.mk [])
    | cons => rfl
  unfold initial Tracks.inputTapes
  congr 1

def inputRows (inputName : TapeName) (letters : List Symbol) : List (Tracks.Row (Alphabet TapeName)) :=
  Tracks.inputRows inputName 3 letters.headI letters.tail

def representation (outputName : TapeName) (capacity : MvPolynomial Parameter ℕ)
    (assignment : Parameter → ℕ) (result : ℕ) (tapes : Tapes (Alphabet TapeName)) : Prop :=
  ∃ bits, value bits = result ∧ bits.length ≤ MvPolynomial.eval assignment capacity ∧
    tapes outputName = Binary.tape [3] (word bits ++ [0]) ()

/-- Physical output letters contain a bit only, with no working head markers. -/
def outputLetter (inputName : TapeName) (bit : Bool) : Tracks.Row (Alphabet TapeName) :=
  (Tracks.inputSymbols inputName (Binary.data bit), fun _ => false)

def extract (inputName outputName : TapeName) :
    Machine (fun _ : Unit => Sweep.Alphabet (Tracks.Row (Alphabet TapeName))) (Fin 8) :=
  TrackOutput.machine (fun row => row.2 outputName) (fun row => row.1 outputName) (outputLetter inputName)

omit [Fintype TapeName] in
private theorem extract_steps (inputName outputName : TapeName) (rows : List (Tracks.Row (Alphabet TapeName)))
    (bits : List Bool)
    (represented : Tracks.RepresentsAt outputName rows (Binary.tape [3] (word bits ++ [0]) ())) :
    ∃ ticks, ticks ≤ 2 * rows.length + 8 ∧ Steps (extract inputName outputName) ticks
      (0, Sweep.tape [Sweep.leftMarker] (rows.map Sweep.row ++ [Sweep.rightMarker]))
      (7, Sweep.tape [] (TrackOutput.word (outputLetter inputName) bits)) := by
  obtain ⟨before, current, after, split, unmarked, marked, _, tape⟩ := represented
  have encoded : Turing.ListBlank.mk ((current :: after).map (fun row => row.1 outputName)) =
      Turing.ListBlank.mk (word bits) := by
    have right := congrArg (fun tape : Turing.Tape Symbol => tape.right.cons tape.head) tape
    have reconstruct (payload : List Symbol) :
        Turing.ListBlank.mk (payload.headI :: payload.tail) = Turing.ListBlank.mk payload := by
      cases payload with
      | nil => exact Turing.ListBlank.cons_head_tail (Turing.ListBlank.mk [])
      | cons => rfl
    have payload := right.symm
    simp only [Binary.tape, Turing.Tape.mk', Turing.ListBlank.head_mk, Turing.ListBlank.tail_mk,
      Turing.ListBlank.cons_mk, reconstruct] at payload
    exact payload.trans (Binary.mk_append_blank _)
  subst rows
  exact TrackOutput.steps _ _ _ before current after bits unmarked marked encoded

/-- A computation with a mathematical binary-output contract has a complete
external TM0 realization. The bound includes preparation, simulation, startup,
and erasure of every working track. -/
theorem realizes_output_tm0 (inputName outputName : TapeName)
    (inputWord : ∀ assignment, Input assignment → List Symbol)
    (hypothesis : ∀ assignment, Input assignment → Prop)
    (compute : ∀ assignment, Input assignment → ℕ)
    {machine : Machine (Alphabet TapeName) Controller} {entry exit : Controller}
    (inputCapacity outputCapacity : MvPolynomial Parameter ℕ)
    (inputBound : ∀ assignment input, hypothesis assignment input →
      (inputWord assignment input).length ≤ MvPolynomial.eval assignment inputCapacity)
    (certificate : Computes machine entry exit
      (fun assignment input tapes => tapes = initial inputName (inputWord assignment input))
      (representation outputName outputCapacity) hypothesis compute) :
    let names := (Finset.univ : Finset TapeName).toList
    let source := sequence (Simulation.machine names machine) (extract inputName outputName) 0
    let program := TM0Input.machine (SingleTape.compile source) (.inl (.inl (Simulation.entry names entry)))
    ∃ bound : MvPolynomial Parameter ℕ,
      ∀ assignment input, hypothesis assignment input →
        ∃ ticks bits, ticks ≤ MvPolynomial.eval assignment bound ∧ value bits = compute assignment input ∧
          bits.length ≤ MvPolynomial.eval assignment outputCapacity ∧
          (fun current => current.bind (Turing.TM0.step program))^[ticks]
            (some (Turing.TM0.init (Sweep.leftMarker ::
              ((inputRows inputName (inputWord assignment input)).map Sweep.row ++ [Sweep.rightMarker])))) =
            some (TM0Input.embed (SingleTape.configuration (.inr 7, Sweep.tape []
              (TrackOutput.word (outputLetter inputName) bits)))) ∧
          Turing.TM0.step program (TM0Input.embed (SingleTape.configuration (.inr 7, Sweep.tape []
            (TrackOutput.word (outputLetter inputName) bits)))) = none := by
  intro names source program
  obtain ⟨halt, bound, runs⟩ := certificate
  have operational : Realizes machine entry exit
      (fun assignment tapes => ∃ input, hypothesis assignment input ∧ tapes = initial inputName (inputWord assignment input))
      (fun assignment before after => ∀ input, hypothesis assignment input →
        before = initial inputName (inputWord assignment input) → representation outputName outputCapacity assignment (compute assignment input) after) := by
    refine ⟨halt, bound, ?_⟩
    intro assignment before valid
    obtain ⟨input, good, encoded⟩ := valid
    obtain ⟨ticks, final, cost, trace, output⟩ := runs assignment input before good encoded
    refine ⟨ticks, final, cost, trace, ?_⟩
    intro other otherGood otherEncoded
    obtain ⟨otherTicks, otherFinal, _, otherTrace, otherOutput⟩ := runs assignment other before otherGood otherEncoded
    have equal := trace.final_eq otherTrace
      (by simp [step, halt]) (by simp [step, halt])
    have tapeEqual := congrArg Prod.snd equal
    change final = otherFinal at tapeEqual
    rw [tapeEqual]
    exact otherOutput
  obtain ⟨timeBound, rowBound, simulations⟩ := Simulation.realizes_steps names
    (Finset.nodup_toList _) (by intro name; simp [names]) operational (inputCapacity + 2)
  refine ⟨2 * (timeBound + 2 * rowBound + 9) + 1, ?_⟩
  intro assignment input good
  let letters := inputWord assignment input
  have rowBounded : (inputRows inputName letters).length ≤ MvPolynomial.eval assignment (inputCapacity + 2) := by
    have bounded := inputBound assignment input good
    simp only [inputRows, Tracks.inputRows_length, List.length_tail, map_add, map_ofNat]
    dsimp [letters]
    omega
  obtain ⟨ticks, finalRows, final, time, storage, correct, represented, trace⟩ := simulations assignment
    (initial inputName letters) ⟨input, good, rfl⟩ (inputRows inputName letters)
    (Tracks.inputRows_represents (Alphabet := Alphabet TapeName) inputName 3 letters.headI letters.tail) rowBounded
  obtain ⟨bits, computed, capacity, output⟩ := correct input good rfl
  have representedOutput := represented outputName
  rw [output] at representedOutput
  obtain ⟨extractTicks, extractCost, extracted⟩ := extract_steps inputName outputName finalRows bits representedOutput
  have complete := sequence_steps (Simulation.machine names machine) (extract inputName outputName) 0 trace
    (by intro symbols; rfl) extracted
  refine ⟨2 * (ticks + extractTicks + 1) + 1, bits, ?_, computed, capacity,
    TM0Input.initialized_steps _ _ _ (SingleTape.steps source complete), ?_⟩
  · simp only [map_add, map_mul, map_ofNat, map_one]
    omega
  · apply (TM0Input.step_embed _ _ _).trans
    rw [SingleTape.halt source _ (by rfl)]
    rfl

end Polytime2.BinaryOutput
