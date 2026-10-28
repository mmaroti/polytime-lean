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

import Polytime2.TM0.CallingConventionSimulation
import Polytime2.Machine.CallingConventionRegions
import Polytime2.TM0.TrackOutput

/-! # Standalone output extraction for standard-convention tapes -/

namespace Polytime2.CallingConvention

open MultiTape

-- tapeLevel: source tape roles; parameterLevel: unary size names;
-- carrierLevel: mathematical values represented on the selected source tape.
universe tapeLevel parameterLevel carrierLevel
variable {TapeName : Type tapeLevel} [DecidableEq TapeName]
variable {Parameter : Type parameterLevel} [Fintype Parameter]

/-- Physical binary output letters use one fixed track, with all head flags
erased. The choice of that track is fixed before runtime. -/
def outputLetter (name : TapeName) (bit : Bool) : Tracks.Row (Alphabet TapeName) :=
  ((fun other => if other = name then Binary.data bit else 0), fun _ => false)

def extractTo (name : TapeName) (outputRow : Bool → Tracks.Row (Alphabet TapeName)) :
    Machine (fun _ : Unit => Sweep.Alphabet (Tracks.Row (Alphabet TapeName))) (Fin 8) :=
  TrackOutput.machine (fun row => row.2 name) (fun row => row.1 name) outputRow

/-- Extract while formatting each bit with fixed finite controller memory. -/
def extractStatefulTo {Memory : Type} (name : TapeName)
    (outputRow : Memory → Bool → Memory × Tracks.Row (Alphabet TapeName)) :
    Machine (fun _ : Unit => Sweep.Alphabet (Tracks.Row (Alphabet TapeName))) (Fin 8 × Memory) :=
  TrackOutput.Stateful.machine (fun row => row.2 name) (fun row => row.1 name) outputRow

def extract (name : TapeName) := extractTo name (outputLetter name)

omit [DecidableEq TapeName] in
/-- A canonical fixed-width output needs no source boundary markers. Extraction
erases the simulator frame and restores the physical head, even at width zero. -/
theorem extractStatefulTo_runs {Memory : Type} (name : TapeName)
    (outputRow : Memory → Bool → Memory × Tracks.Row (Alphabet TapeName)) (memory : Memory)
    (domain : EncodedDomain.{parameterLevel, carrierLevel} Parameter)
    (sizes : Parameter → ℕ) (value : domain.Carrier sizes)
    (rows : List (Tracks.Row (Alphabet TapeName)))
    (represented : Tracks.RepresentsAt name rows (encoded domain sizes value)) :
    ∃ ticks, ticks ≤ 2 * rows.length + 8 ∧
      Steps (extractStatefulTo name outputRow) ticks
        ((0, memory), Sweep.tape [Sweep.leftMarker] (rows.map Sweep.row ++ [Sweep.rightMarker]))
        ((7, TrackOutput.Stateful.finalMemory outputRow memory
          (EncodedDomain.ArrayEncoding.bits (domain.encode sizes value))),
          Sweep.tape [] (TrackOutput.Stateful.word outputRow memory
          (List.ofFn (fun index : Fin (domain.width sizes) => (domain.encode sizes value).getLsbD index.val)))) := by
  obtain ⟨before, current, after, split, unmarked, marked, _, tapeEq⟩ := represented
  let bits := List.ofFn (fun index : Fin (domain.width sizes) =>
    (domain.encode sizes value).getLsbD index.val)
  have payload : Turing.ListBlank.mk ((current :: after).map (fun row => row.1 name)) =
      Turing.ListBlank.mk (Binary.word bits) := by
    have right := congrArg (fun source : Turing.Tape Binary.Symbol => source.right.cons source.head) tapeEq
    have reconstruct (contents : List Binary.Symbol) :
        Turing.ListBlank.mk (contents.headI :: contents.tail) = Turing.ListBlank.mk contents := by
      cases contents with
      | nil => exact Turing.ListBlank.cons_head_tail (Turing.ListBlank.mk [])
      | cons => rfl
    symm
    simpa only [encoded, EncodedDomain.ArrayEncoding.bits, tape, Turing.Tape.mk₁, Turing.Tape.mk₂, Turing.Tape.mk', Turing.ListBlank.head_mk,
      Turing.ListBlank.tail_mk, Turing.ListBlank.cons_mk, reconstruct, List.map_cons, bits] using right
  subst rows
  exact TrackOutput.Stateful.steps _ _ _ memory before current after bits unmarked marked payload

omit [DecidableEq TapeName] in
/-- Stateless output uses the same extraction proof with unit memory. -/
theorem extractTo_runs (name : TapeName) (outputRow : Bool → Tracks.Row (Alphabet TapeName))
    (domain : EncodedDomain.{parameterLevel, carrierLevel} Parameter)
    (sizes : Parameter → ℕ) (value : domain.Carrier sizes)
    (rows : List (Tracks.Row (Alphabet TapeName)))
    (represented : Tracks.RepresentsAt name rows (encoded domain sizes value)) :
    ∃ ticks, ticks ≤ 2 * rows.length + 8 ∧
      Steps (extractTo name outputRow) ticks
        (0, Sweep.tape [Sweep.leftMarker] (rows.map Sweep.row ++ [Sweep.rightMarker]))
        (7, Sweep.tape [] (TrackOutput.word outputRow
          (EncodedDomain.ArrayEncoding.bits (domain.encode sizes value)))) := by
  obtain ⟨ticks, bound, trace⟩ := extractStatefulTo_runs name
    (fun _ : Unit => fun bit => ((), outputRow bit)) () domain sizes value rows represented
  have projected := trace.rename Prod.fst (target := extractTo name outputRow)
    (by
      rintro ⟨phase, memory⟩ symbols ⟨next, nextMemory⟩ actions transition
      cases memory
      simp only [extractTo, TrackOutput.machine, extractStatefulTo] at *
      simp only [transition, Option.map_some])
  exact ⟨ticks, bound, by simpa only [TrackOutput.unit_word] using projected⟩

/-- The standard binary output convention specializes generic extraction. -/
theorem extract_runs (name : TapeName) (domain : EncodedDomain.{parameterLevel, carrierLevel} Parameter)
    (sizes : Parameter → ℕ) (value : domain.Carrier sizes)
    (rows : List (Tracks.Row (Alphabet TapeName)))
    (represented : Tracks.RepresentsAt name rows (encoded domain sizes value)) :
    ∃ ticks, ticks ≤ 2 * rows.length + 8 ∧
      Steps (extract name) ticks
        (0, Sweep.tape [Sweep.leftMarker] (rows.map Sweep.row ++ [Sweep.rightMarker]))
        (7, Sweep.tape [] (TrackOutput.word (outputLetter name)
          (List.ofFn (fun index : Fin (domain.width sizes) => (domain.encode sizes value).getLsbD index.val)))) :=
  extractTo_runs name (outputLetter name) domain sizes value rows represented

-- stateLevel: the finite controller of the routine being simulated.
-- outputNameLevel: names of declared mathematical outputs.
universe stateLevel outputNameLevel
variable {OutputName : Type outputNameLevel}
variable {State : Type stateLevel} [Fintype State] [Fintype TapeName]

/-- Realize a standard routine and extract one output as a standalone binary
word. Simulation, extraction, erasure, and startup all count toward the bound.
Only the mathematical inputs and declared outputs are representation witnesses.
-/
theorem Realizes.tm0_output
    {domains : TapeName → EncodedDomain.{parameterLevel, carrierLevel} Parameter}
    {readOnly : TapeName → Bool} {sizeTapes : Parameter ↪ TapeName}
    {outputTapes : OutputName ↪ TapeName}
    {source : Machine (Alphabet TapeName) State} {sourceEntry sourceExit : State}
    {hypothesis : ∀ assignment, Inputs domains readOnly assignment → Prop}
    {contract : ∀ assignment, Inputs domains readOnly assignment → Outputs domains outputTapes assignment → Prop}
    (certificate : Realizes domains readOnly sizeTapes outputTapes source sourceEntry sourceExit hypothesis contract)
    (resultName : OutputName) :
    let names := (Finset.univ : Finset TapeName).toList
    let combined := MultiTape.sequence (Simulation.machine names source) (extract (outputTapes resultName)) 0
    let program := TM0Input.machine (SingleTape.compile combined)
      (.inl (.inl (Simulation.entry names sourceEntry)))
    ∃ inputCapacity timeBound : MvPolynomial Parameter ℕ, ∀ assignment initial,
      (∃ input, hypothesis assignment input ∧ Entry domains readOnly assignment input initial ∧
        ∀ parameter, initial (sizeTapes parameter) = unary (assignment parameter)) →
      ∃ ticks input output final,
        ticks ≤ MvPolynomial.eval assignment timeBound ∧
        hypothesis assignment input ∧ Entry domains readOnly assignment input initial ∧
        contract assignment input output ∧ Exit domains outputTapes assignment output final ∧
        (∀ name, readOnly name = true → final name = initial name) ∧
        (fun current => current.bind (Turing.TM0.step program))^[ticks]
          (some (Turing.TM0.init (Sweep.leftMarker ::
            ((Tracks.initialRows (MvPolynomial.eval assignment inputCapacity) initial).map Sweep.row ++
              [Sweep.rightMarker])))) =
          some (TM0Input.embed (SingleTape.configuration (.inr 7, Sweep.tape []
            (TrackOutput.word (outputLetter (outputTapes resultName))
              (List.ofFn (fun index : Fin ((domains (outputTapes resultName)).width assignment) =>
                ((domains (outputTapes resultName)).encode assignment (output resultName)).getLsbD index.val)))))) ∧
        Turing.TM0.step program
          (TM0Input.embed (SingleTape.configuration (.inr 7, Sweep.tape []
            (TrackOutput.word (outputLetter (outputTapes resultName))
              (List.ofFn (fun index : Fin ((domains (outputTapes resultName)).width assignment) =>
                ((domains (outputTapes resultName)).encode assignment (output resultName)).getLsbD index.val)))))) = none := by
  classical
  intro names combined program
  let precondition := fun assignment initial => ∃ input,
    hypothesis assignment input ∧ Entry domains readOnly assignment input initial ∧
      ∀ parameter, initial (sizeTapes parameter) = unary (assignment parameter)
  let postcondition := fun assignment initial final => ∃ input output,
    hypothesis assignment input ∧ Entry domains readOnly assignment input initial ∧
      contract assignment input output ∧ Exit domains outputTapes assignment output final ∧
        ∀ name, readOnly name = true → final name = initial name
  have physical : MultiTape.Internal.Realizes source sourceEntry sourceExit precondition postcondition := by
    obtain ⟨sizeReadOnly, outputsWritable, halted, bound, execute⟩ := certificate
    refine ⟨halted, bound, ?_⟩
    intro assignment initial valid
    obtain ⟨input, validInput, represented, headers⟩ := valid
    obtain ⟨ticks, output, final, cost, trace, correct, returned⟩ :=
      execute assignment input initial validInput represented headers
    exact ⟨ticks, final, cost, trace.steps, input, output, validInput, represented,
      correct, returned, fun name immutable => trace.readOnly_tape name immutable⟩
  let widthBound := fun name => (domains name).widthPolynomial
  let inputCapacity := ∑ name, widthBound name
  have capacity (assignment : Parameter → ℕ) (name : TapeName) :
      (domains name).width assignment ≤ MvPolynomial.eval assignment inputCapacity := by
    simp only [inputCapacity, map_sum]
    exact Finset.single_le_sum (f := fun name => MvPolynomial.eval assignment (widthBound name))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ name)
  have inputFits (assignment : Parameter → ℕ) (initial : Tapes (Alphabet TapeName))
      (valid : precondition assignment initial) (name : TapeName) :
      Fits (MvPolynomial.eval assignment inputCapacity) (initial name) := by
    obtain ⟨input, validInput, represented, headers⟩ := valid
    obtain ⟨contents, length, tapeEq⟩ := (represented.region name).exists_buffer
    apply Fits.mono (small := (domains name).width assignment) ?_ (capacity assignment name)
    exact ⟨[], contents, tapeEq, by simp only [List.length_nil, zero_add, length, le_refl]⟩
  let rowCapacity := 2 * inputCapacity + 1
  obtain ⟨timeBound, rowBound, executeSimulation⟩ := Simulation.realizes_steps names
    (Finset.nodup_toList _) (by intro name; simp [names]) physical rowCapacity
  refine ⟨inputCapacity, 2 * (timeBound + 2 * rowBound + 9) + 1, ?_⟩
  intro assignment initial valid
  obtain ⟨simulationTicks, finalRows, final, simulationCost, storage, correct, represented, simulated⟩ :=
    executeSimulation assignment initial valid
      (Tracks.initialRows (MvPolynomial.eval assignment inputCapacity) initial)
      (Tracks.initialRows_represents _ _ (inputFits assignment initial valid))
      (by simp only [Tracks.initialRows_length, rowCapacity, map_add, map_mul, map_ofNat, map_one, le_refl])
  obtain ⟨input, output, validInput, inputEq, outputCorrect, returned, immutable⟩ := correct
  have outputRepresentation := represented (outputTapes resultName)
  rw [returned resultName] at outputRepresentation
  obtain ⟨extractTicks, extractCost, extracted⟩ :=
    extract_runs (outputTapes resultName) (domains (outputTapes resultName)) assignment (output resultName)
      finalRows outputRepresentation
  have complete := MultiTape.sequence_steps (Simulation.machine names source) (extract (outputTapes resultName)) 0
    simulated (by intro symbols; rfl) extracted
  refine ⟨2 * (simulationTicks + extractTicks + 1) + 1, input, output, final, ?_,
    validInput, inputEq, outputCorrect, returned, immutable,
    TM0Input.initialized_steps _ _ _ (SingleTape.steps combined complete), ?_⟩
  · simp only [map_add, map_mul, map_ofNat, map_one]
    omega
  · apply (TM0Input.step_embed _ _ _).trans
    rw [SingleTape.halt combined _ (by rfl)]
    rfl

end Polytime2.CallingConvention
