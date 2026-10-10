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


import Polytime2.Act

/-! # A single-tape simulator for finite multi-tape machines

The controller reads marked track heads, applies the source transition table,
writes and moves the source heads, then repeats. Source states and command
vectors are finite runtime controller memory. Interval lengths and data remain
on tape; no runtime size changes the controller or the source tape catalogue.
-/

namespace Polytime2.Simulation

open MultiTape

-- tapeLevel: source tape names; symbolLevel: source alphabets.
-- stateLevel: source controller; parameterLevel: runtime size names.
universe tapeLevel symbolLevel stateLevel parameterLevel

variable {TapeName : Type tapeLevel} [DecidableEq TapeName]
variable {Alphabet : TapeName → Type symbolLevel} [∀ name, Inhabited (Alphabet name)]
variable {State : Type stateLevel}

abbrev Controller (Alphabet : TapeName → Type symbolLevel) (State : Type stateLevel) (names : List TapeName) :=
  Sum (State × Sweep.Controller (Symbols Alphabet))
    (Sum (State × Act.Packet Alphabet × Act.Controller Alphabet names) Unit)

instance controllerInhabited (names : List TapeName) : Inhabited (Controller Alphabet State names) :=
  ⟨.inr (.inr ())⟩

instance controllerFintype [Fintype TapeName] [∀ name, Fintype (Alphabet name)] [Fintype State]
    (names : List TapeName) : Fintype (Controller Alphabet State names) := inferInstanceAs
  (Fintype (Sum (State × Sweep.Controller (Symbols Alphabet))
    (Sum (State × Act.Packet Alphabet × Act.Controller Alphabet names) Unit)))

def entry (names : List TapeName) (state : State) : Controller Alphabet State names :=
  .inl (state, .inl (false, fun _ => default))

def machine (names : List TapeName) (source : Machine Alphabet State) :
    Machine (fun _ : Unit => Sweep.Alphabet (Tracks.Row Alphabet)) (Controller Alphabet State names)
  | .inl (state, readControl), symbols =>
    match Sweep.machine Tracks.collect readControl symbols with
    | some (next, actions) => some (.inl (state, next), actions)
    | none => match readControl with
      | .inr heads => match source state heads with
        | none => some (.inr (.inr ()), stationary symbols)
        | some (next, actions) =>
          some (.inr (.inl (next, Act.packet actions, Act.entry names (Act.packet actions))), stationary symbols)
      | _ => none
  | .inr (.inl (state, command, applyControl)), symbols =>
    match Act.machine names command applyControl symbols with
    | some (next, actions) => some (.inr (.inl (state, command, next)), actions)
    | none => some (entry names state, stationary symbols)
  | .inr (.inr ()), _ => none

@[simp] theorem halt (names : List TapeName) (source : Machine Alphabet State)
    (symbols : Symbols (fun _ : Unit => Sweep.Alphabet (Tracks.Row Alphabet))) :
    machine names source (.inr (.inr ())) symbols = none := rfl

/-- One source transition is implemented by a head scan, the full action pass,
and two stationary controller handovers. -/
theorem cycle (names : List TapeName) (unique : names.Nodup) (complete : ∀ name, name ∈ names)
    (source : Machine Alphabet State) (state nextState : State) (actions : Actions Alphabet)
    {rows : List (Tracks.Row Alphabet)} {tapes : Tapes Alphabet}
    (represented : Tracks.Represents rows tapes)
    (transition : source state (MultiTape.read tapes) = some (nextState, actions)) :
    ∃ finalRows ticks, finalRows.length ≤ rows.length + 2 * names.length ∧
      ticks ≤ 4 * rows.length + 9 + names.length * (4 * rows.length + 8 * names.length + 19) ∧
      Tracks.Represents finalRows (MultiTape.act actions tapes) ∧
      Steps (machine names source) ticks
        (entry names state, Sweep.tape [Sweep.leftMarker] (rows.map Sweep.row ++ [Sweep.rightMarker]))
        (entry names nextState, Sweep.tape [Sweep.leftMarker] (finalRows.map Sweep.row ++ [Sweep.rightMarker])) := by
  have collected := Tracks.collect_steps represented (fun _ => default) [] []
  have readTrace := collected.rename (fun control => .inl (state, control)) (target := machine names source)
    (by intro control symbols next writes instruction; simp [machine, instruction])
  have startApply : step (machine names source)
      (.inl (state, .inr (MultiTape.read tapes)),
        Sweep.tape [Sweep.leftMarker] (rows.map Sweep.row ++ [Sweep.rightMarker])) =
      some (.inr (.inl (nextState, Act.packet actions, Act.entry names (Act.packet actions))),
        Sweep.tape [Sweep.leftMarker] (rows.map Sweep.row ++ [Sweep.rightMarker])) := by
    simp [step, machine, Sweep.machine, transition]
  obtain ⟨finalRows, ticks, length, cost, correct, applied⟩ := Act.steps names unique complete (Act.packet actions) represented
  have applyTrace := applied.rename (fun control => .inr (.inl (nextState, Act.packet actions, control)))
    (target := machine names source)
    (by intro control symbols next writes instruction; simp [machine, instruction])
  have restart : step (machine names source)
      (.inr (.inl (nextState, Act.packet actions, Act.exit names)),
        Sweep.tape [Sweep.leftMarker] (finalRows.map Sweep.row ++ [Sweep.rightMarker])) =
      some (entry names nextState, Sweep.tape [Sweep.leftMarker] (finalRows.map Sweep.row ++ [Sweep.rightMarker])) := by
    simp [step, machine]
  refine ⟨finalRows, (2 * rows.length + 3) + (ticks + 1 + 1), length, by omega, ?_, ?_⟩
  · simpa only [Act.effect_packet] using correct
  · have combined := readTrace.trans (Steps.next startApply (applyTrace.trans (Steps.next restart (.zero _))))
    simpa [entry, Nat.add_assoc] using combined

/-- Source halting is detected by a final marked-head scan; the simulator then
halts unconditionally without changing the represented output tapes. -/
theorem terminal (names : List TapeName) (source : Machine Alphabet State) (state : State)
    {rows : List (Tracks.Row Alphabet)} {tapes : Tapes Alphabet}
    (represented : Tracks.Represents rows tapes) (stopped : source state (MultiTape.read tapes) = none) :
    Steps (machine names source) (2 * rows.length + 4)
      (entry names state, Sweep.tape [Sweep.leftMarker] (rows.map Sweep.row ++ [Sweep.rightMarker]))
      (.inr (.inr ()), Sweep.tape [Sweep.leftMarker] (rows.map Sweep.row ++ [Sweep.rightMarker])) := by
  have collected := Tracks.collect_steps represented (fun _ => default) [] []
  have readTrace := collected.rename (fun control => .inl (state, control)) (target := machine names source)
    (by intro control symbols next writes instruction; simp [machine, instruction])
  have stop : step (machine names source)
      (.inl (state, .inr (MultiTape.read tapes)), Sweep.tape [Sweep.leftMarker] (rows.map Sweep.row ++ [Sweep.rightMarker])) =
      some (.inr (.inr ()), Sweep.tape [Sweep.leftMarker] (rows.map Sweep.row ++ [Sweep.rightMarker])) := by
    simp [step, machine, Sweep.machine, stopped]
  simpa [entry, Nat.add_assoc] using readTrace.trans (Steps.next stop (.zero _))

/-- Cost envelope for one complete simulated transition. -/
def cycleCost (tapeCount rowCount : ℕ) : ℕ :=
  4 * rowCount + 9 + tapeCount * (4 * rowCount + 8 * tapeCount + 19)

private theorem cycleCost_mono (tapeCount : ℕ) {small large : ℕ} (bounded : small ≤ large) :
    cycleCost tapeCount small ≤ cycleCost tapeCount large := by
  have inner : 4 * small + 8 * tapeCount + 19 ≤ 4 * large + 8 * tapeCount + 19 := by omega
  have multiplied := Nat.mul_le_mul_left tapeCount inner
  unfold cycleCost
  omega

/-- Any counted source execution has a counted one-tape simulation. The largest
row interval grows at most linearly in the number of source transitions. -/
theorem steps (names : List TapeName) (unique : names.Nodup) (complete : ∀ name, name ∈ names)
    (source : Machine Alphabet State) {sourceTicks : ℕ}
    {initial final : Configuration Alphabet State} (trace : Steps source sourceTicks initial final)
    {rows : List (Tracks.Row Alphabet)} (represented : Tracks.Represents rows initial.2) :
    ∃ finalRows ticks, finalRows.length ≤ rows.length + 2 * names.length * sourceTicks ∧
      ticks ≤ sourceTicks * cycleCost names.length (rows.length + 2 * names.length * sourceTicks) ∧
      Tracks.Represents finalRows final.2 ∧
      Steps (machine names source) ticks
        (entry names initial.1, Sweep.tape [Sweep.leftMarker] (rows.map Sweep.row ++ [Sweep.rightMarker]))
        (entry names final.1, Sweep.tape [Sweep.leftMarker] (finalRows.map Sweep.row ++ [Sweep.rightMarker])) := by
  induction trace generalizing rows with
  | zero configuration => exact ⟨rows, 0, by simp, by simp, represented, .zero _⟩
  | @next count initial middle final transition rest hypothesis =>
    cases equation : source initial.1 (MultiTape.read initial.2) with
    | none => simp [step, equation] at transition
    | some command =>
      rcases command with ⟨nextState, actions⟩
      simp only [step, equation, Option.map_some, Option.some.injEq] at transition
      subst middle
      obtain ⟨middleRows, firstTicks, middleLength, firstCost, firstCorrect, firstTrace⟩ :=
        cycle names unique complete source initial.1 nextState actions represented equation
      obtain ⟨finalRows, secondTicks, finalLength, secondCost, correct, secondTrace⟩ := hypothesis firstCorrect
      have envelope : middleRows.length + 2 * names.length * count ≤
          rows.length + 2 * names.length * (count + 1) := by nlinarith
      have suffixBound := cycleCost_mono names.length envelope
      have suffixCost := secondCost.trans (Nat.mul_le_mul_left count suffixBound)
      have firstBound := cycleCost_mono names.length
        (show rows.length ≤ rows.length + 2 * names.length * (count + 1) by omega)
      have localCost : firstTicks ≤ cycleCost names.length rows.length := by
        simpa only [cycleCost] using firstCost
      have prefixCost := localCost.trans firstBound
      refine ⟨finalRows, firstTicks + secondTicks, by nlinarith, ?_, correct, firstTrace.trans secondTrace⟩
      nlinarith

/-- A multi-tape polynomial certificate transfers to a finite TM0 simulator.
Inputs and outputs use the marked-track encoding, with blank tape outside its
boundary markers. Both runtime and final row capacity have polynomial bounds. -/
theorem realizes {Parameter : Type parameterLevel} [Fintype Parameter]
    [Fintype TapeName] [∀ name, Fintype (Alphabet name)] [Fintype State]
    (names : List TapeName) (unique : names.Nodup) (complete : ∀ name, name ∈ names)
    {source : Machine Alphabet State} {sourceEntry sourceExit : State}
    {precondition : (Parameter → ℕ) → Tapes Alphabet → Prop}
    {postcondition : (Parameter → ℕ) → Tapes Alphabet → Tapes Alphabet → Prop}
    (certificate : Realizes source sourceEntry sourceExit precondition postcondition)
    (rowCapacity : MvPolynomial Parameter ℕ) :
    ∃ timeBound rowBound : MvPolynomial Parameter ℕ,
      ∀ assignment initial, precondition assignment initial →
        ∀ rows : List (Tracks.Row Alphabet), Tracks.Represents rows initial →
          rows.length ≤ MvPolynomial.eval assignment rowCapacity →
          ∃ ticks finalRows final, ticks ≤ MvPolynomial.eval assignment timeBound ∧
            finalRows.length ≤ MvPolynomial.eval assignment rowBound ∧
            postcondition assignment initial final ∧ Tracks.Represents finalRows final ∧
            (fun current => current.bind (Turing.TM0.step (SingleTape.compile (machine names source))))^[ticks]
              (some (SingleTape.configuration (entry names sourceEntry, Sweep.tape [Sweep.leftMarker]
                (rows.map Sweep.row ++ [Sweep.rightMarker])))) =
              some (SingleTape.configuration (.inr (.inr ()), Sweep.tape [Sweep.leftMarker]
                (finalRows.map Sweep.row ++ [Sweep.rightMarker]))) ∧
            Turing.TM0.step (SingleTape.compile (machine names source))
              (SingleTape.configuration (.inr (.inr ()), Sweep.tape [Sweep.leftMarker]
                (finalRows.map Sweep.row ++ [Sweep.rightMarker]))) = none := by
  obtain ⟨sourceHalt, sourceBound, runs⟩ := certificate
  let rowBound := rowCapacity + MvPolynomial.C (2 * names.length) * sourceBound
  let timeBound := 2 * (sourceBound + 1) *
    (4 * rowBound + 13 + MvPolynomial.C names.length * (4 * rowBound + MvPolynomial.C (8 * names.length + 19)))
  refine ⟨timeBound, rowBound, ?_⟩
  intro assignment initial valid rows represented bounded
  obtain ⟨sourceTicks, final, sourceCost, sourceTrace, correct⟩ := runs assignment initial valid
  obtain ⟨finalRows, ticks, length, cost, finalCorrect, simulation⟩ :=
    steps names unique complete source sourceTrace represented
  have growth : rows.length + 2 * names.length * sourceTicks ≤ MvPolynomial.eval assignment rowBound := by
    have multiplied := Nat.mul_le_mul_left (2 * names.length) sourceCost
    simp only [rowBound, map_add, map_mul, MvPolynomial.eval_C]
    omega
  have finalCapacity := length.trans growth
  let allowance := cycleCost names.length (MvPolynomial.eval assignment rowBound)
  have workCost : ticks ≤ MvPolynomial.eval assignment sourceBound * allowance := by
    exact cost.trans (Nat.mul_le_mul sourceCost (cycleCost_mono names.length growth))
  have stopCost : 2 * finalRows.length + 4 ≤ allowance + 4 := by
    dsimp [allowance, cycleCost]
    omega
  have totalCost : ticks + (2 * finalRows.length + 4) ≤
      (MvPolynomial.eval assignment sourceBound + 1) * (allowance + 4) := by
    have combined : ticks + (2 * finalRows.length + 4) ≤
        MvPolynomial.eval assignment sourceBound * allowance + (allowance + 4) := by omega
    nlinarith
  have stopped := terminal names source sourceExit finalCorrect (sourceHalt _)
  have trace := simulation.trans stopped
  refine ⟨2 * (ticks + (2 * finalRows.length + 4)), finalRows, final, ?_, finalCapacity,
    correct, finalCorrect, SingleTape.steps (machine names source) trace, ?_⟩
  · have doubled := Nat.mul_le_mul_left 2 totalCost
    convert doubled using 1
    simp only [timeBound, map_mul, map_add, map_ofNat, map_one, MvPolynomial.eval_C]
    dsimp [allowance, cycleCost]
    ring
  · exact SingleTape.halt (machine names source) _ (by rfl)

end Polytime2.Simulation
