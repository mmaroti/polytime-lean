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

import Polytime2.CallingConvention
import Polytime2.TM0Input

/-! # TM0 realization of standard-convention routines

The simulator's track encoding is separate from the source routine's tapes.
Canonical inputs and arbitrary writable regions both have polynomial storage.
-/

namespace Polytime2.CallingConvention

open MultiTape

-- tapeLevel: tape roles; stateLevel: finite source controller states.
-- parameterLevel: unary size names; carrierLevel: mathematical tape values.
-- outputNameLevel: names of declared mathematical outputs.
universe tapeLevel stateLevel parameterLevel carrierLevel outputNameLevel
variable {TapeName : Type tapeLevel} [Fintype TapeName] [DecidableEq TapeName]
variable {State : Type stateLevel} [Fintype State]
variable {Parameter : Type parameterLevel} [Fintype Parameter]
variable {OutputName : Type outputNameLevel}

/-- A standard routine's mathematical contract, realized from `TM0.init` via
finite tracks. Representation witnesses tie the contract to the initial tape.
-/
def TM0Realizes
    (domains : TapeName → EncodedDomain.{parameterLevel, carrierLevel} Parameter)
    (readOnly : TapeName → Bool) (sizeTapes : Parameter ↪ TapeName)
    (outputTapes : OutputName ↪ TapeName)
    (source : Machine (Alphabet TapeName) State) (sourceEntry : State)
    (hypothesis : ∀ assignment, Inputs domains readOnly assignment → Prop)
    (contract : ∀ assignment, Inputs domains readOnly assignment →
      Outputs domains outputTapes assignment → Prop) : Prop :=
  let names := (Finset.univ : Finset TapeName).toList
  let program := TM0Input.machine (SingleTape.compile (Simulation.machine names source))
    (.inl (Simulation.entry names sourceEntry))
  ∃ inputCapacity timeBound rowBound : MvPolynomial Parameter ℕ,
    ∀ assignment initial,
      (∃ input, hypothesis assignment input ∧
        Entry domains readOnly assignment input initial ∧
        ∀ parameter, initial (sizeTapes parameter) = unary (assignment parameter)) →
      ∃ ticks finalRows final,
        ticks ≤ MvPolynomial.eval assignment timeBound ∧
        finalRows.length ≤ MvPolynomial.eval assignment rowBound ∧
        (∃ input output, hypothesis assignment input ∧
          Entry domains readOnly assignment input initial ∧
          contract assignment input output ∧
          Exit domains outputTapes assignment output final ∧
          ∀ name, readOnly name = true → final name = initial name) ∧
        Tracks.Represents finalRows final ∧
        (fun current => current.bind (Turing.TM0.step program))^[ticks]
          (some (Turing.TM0.init (Sweep.leftMarker ::
            ((Tracks.initialRows (MvPolynomial.eval assignment inputCapacity) initial).map
              Sweep.row ++ [Sweep.rightMarker])))) =
          some (TM0Input.embed (SingleTape.configuration (.inr (.inr ()),
            Sweep.tape [Sweep.leftMarker] (finalRows.map Sweep.row ++ [Sweep.rightMarker])))) ∧
        Turing.TM0.step program
          (TM0Input.embed (SingleTape.configuration (.inr (.inr ()),
            Sweep.tape [Sweep.leftMarker] (finalRows.map Sweep.row ++ [Sweep.rightMarker])))) = none

/-- Fixed-region execution transfers to the polynomial simulator without
source markers or an initialized scratch assumption.
-/
theorem Realizes.tm0
    {domains : TapeName → EncodedDomain.{parameterLevel, carrierLevel} Parameter}
    {readOnly : TapeName → Bool} {sizeTapes : Parameter ↪ TapeName}
    {outputTapes : OutputName ↪ TapeName}
    {source : Machine (Alphabet TapeName) State} {sourceEntry sourceExit : State}
    {hypothesis : ∀ assignment, Inputs domains readOnly assignment → Prop}
    {contract : ∀ assignment, Inputs domains readOnly assignment →
      Outputs domains outputTapes assignment → Prop}
    (certificate : Realizes domains readOnly sizeTapes outputTapes source sourceEntry sourceExit
      hypothesis contract) :
    TM0Realizes domains readOnly sizeTapes outputTapes source sourceEntry hypothesis contract := by
  classical
  let precondition := fun assignment initial => ∃ input,
    hypothesis assignment input ∧ Entry domains readOnly assignment input initial ∧
      ∀ parameter, initial (sizeTapes parameter) = unary (assignment parameter)
  let postcondition := fun assignment initial final => ∃ input output,
    hypothesis assignment input ∧ Entry domains readOnly assignment input initial ∧
      contract assignment input output ∧ Exit domains outputTapes assignment output final ∧
        ∀ name, readOnly name = true → final name = initial name
  have physical : MultiTape.Internal.Realizes source sourceEntry sourceExit precondition postcondition := by
    obtain ⟨sizeReadOnly, outputsWritable, halted, bound, run⟩ := certificate
    refine ⟨halted, bound, ?_⟩
    intro assignment initial valid
    obtain ⟨input, hypothesis, represented, sizes⟩ := valid
    obtain ⟨ticks, output, final, cost, trace, correct, returned⟩ :=
      run assignment input initial hypothesis represented sizes
    exact ⟨ticks, final, cost, trace.steps, input, output, hypothesis, represented,
      correct, returned, fun name immutable => trace.readOnly_tape name immutable⟩
  let bound := fun name => (domains name).widthPolynomial
  let inputCapacity := ∑ name, bound name
  have capacity (assignment : Parameter → ℕ) (name : TapeName) :
      (domains name).width assignment ≤ MvPolynomial.eval assignment inputCapacity := by
    simp only [inputCapacity, map_sum]
    exact Finset.single_le_sum (f := fun name => MvPolynomial.eval assignment (bound name))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ name)
  have inputFits : ∀ assignment initial, precondition assignment initial →
      ∀ name, Fits (MvPolynomial.eval assignment inputCapacity) (initial name) := by
    intro assignment initial valid name
    obtain ⟨input, hypothesis, represented, sizes⟩ := valid
    apply Fits.mono (large := MvPolynomial.eval assignment inputCapacity)
      (small := (domains name).width assignment) ?_ (capacity assignment name)
    cases immutable : readOnly name with
    | false =>
      obtain ⟨contents, length, equal⟩ := represented.2 name immutable
      refine ⟨[], contents, equal, ?_⟩
      simp only [List.length_nil, zero_add, length, le_refl]
    | true =>
      rw [represented.1 name immutable]
      refine ⟨[], Binary.word (List.ofFn (fun index : Fin ((domains name).width assignment) =>
        ((domains name).encode assignment (input ⟨name, immutable⟩)).getLsbD index.val)), rfl, ?_⟩
      simp [Binary.word]
  let names := (Finset.univ : Finset TapeName).toList
  obtain ⟨timeBound, rowBound, runs⟩ := Simulation.realizes_input names
    (Finset.nodup_toList _) (by intro name; simp [names]) physical inputCapacity inputFits
  exact ⟨inputCapacity, timeBound, rowBound, runs⟩

end Polytime2.CallingConvention
