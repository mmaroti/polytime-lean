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

import Polytime1.BlockLookupMachine

/-! # Fixed-table operations in an existing scalar slot

After reading the scalar into finite controller states, reverse emission reuses
its input cells as the output window. Both neighboring regions are preserved.
-/

namespace Polytime1.InPlaceTableMachine

open TupleMachine (Symbol word)
variable {width : ℕ}

/-- Reuse the existing reader and emitter, sending a completed read directly
into emission instead of reserving another scalar slot. -/
def machine (table : (Fin width → Bool) → (Fin width → Bool)) :
    Turing.TM0.Machine Symbol (FiniteTableMachine.State width width) := fun state symbol =>
  match state with
  | .read position bits =>
    if position.val < width then FiniteTableMachine.machine table state symbol
    else some (.emit (Fin.last width) (table bits), .write symbol)
  | _ => FiniteTableMachine.machine table state symbol

private theorem reads (table : (Fin width → Bool) → (Fin width → Bool))
    (bits : Fin width → Bool) (left tail : List Symbol) :
    Tape.Steps (machine table) width
      (Tape.configuration (.read 0 (fun _ => false)) left (word (List.ofFn bits) ++ tail))
      (Tape.configuration (.read (Fin.last width) bits) ((word (List.ofFn bits)).reverse ++ left) tail) := by
  have trace := FiniteTableMachine.reads table bits left tail
  apply (trace.rename_until id BlockLookupMachine.reading
    (by
      intro state symbol next action command allowed
      cases state with
      | read => trivial
      | halt => simp [FiniteTableMachine.machine] at command
      | rewind | emit =>
        simp only [FiniteTableMachine.machine] at command
        split at command <;>
          simp only [Option.some.injEq, Prod.mk.injEq] at command <;>
          obtain ⟨rfl, _⟩ := command <;> exact allowed.elim
      | write =>
        simp only [FiniteTableMachine.machine, Option.some.injEq, Prod.mk.injEq] at command
        obtain ⟨rfl, _⟩ := command
        exact allowed.elim)
    (targetMachine := machine table) ?_ trivial).2
  intro state symbol next action sourceAllowed nextAllowed command
  cases state with
  | read position stored =>
    by_cases valid : position.val < width
    · simp [machine, valid, command]
    · simp only [FiniteTableMachine.machine, valid, ↓reduceDIte,
        Option.some.injEq, Prod.mk.injEq] at command
      obtain ⟨equality, _⟩ := command
      rw [← equality] at nextAllowed
      exact nextAllowed.elim
  | rewind | emit | write | halt => exact sourceAllowed.elim

private def emitting : FiniteTableMachine.State width width → Prop
  | .emit _ _ | .write _ _ | .halt => True
  | _ => False

/-- Replace the scalar in place and restore its head, including width zero. -/
theorem realizes (table : (Fin width → Bool) → (Fin width → Bool))
    (bits : Fin width → Bool) (left tail : List Symbol) :
    Tape.Steps (machine table) (3 * width + 2)
      (Tape.configuration (.read 0 (fun _ => false)) left (word (List.ofFn bits) ++ tail))
      (Tape.configuration .halt left (word (List.ofFn (table bits)) ++ tail)) := by
  have read := reads table bits left tail
  have enter := Tape.stay (machine := machine table) (state := .read (Fin.last width) bits)
    (nextState := .emit (Fin.last width) (table bits)) ((word (List.ofFn bits)).reverse ++ left) tail
    (by intro symbol; simp [machine])
  have emit := FiniteTableMachine.emit_loop table (table bits) (word (List.ofFn bits)).reverse
    left tail (Fin.last width) (by simp)
  have emit' := emit.rename_from id emitting (targetMachine := machine table) (by
    intro state symbol next action allowed command
    cases state with
    | read | rewind => exact allowed.elim
    | emit remaining result =>
      by_cases positive : remaining.val > 0 <;>
        simp [FiniteTableMachine.machine, positive, Option.some.injEq, Prod.mk.injEq] at command <;>
        obtain ⟨rfl, _⟩ := command <;> trivial
    | write position result =>
      simp only [FiniteTableMachine.machine, Option.some.injEq, Prod.mk.injEq] at command
      obtain ⟨rfl, _⟩ := command
      trivial
    | halt => simp [FiniteTableMachine.machine] at command) (by
      intro state symbol next action allowed command
      cases state with
      | read | rewind => exact allowed.elim
      | emit | write | halt => exact command) trivial
  convert read.trans (Tape.Steps.next enter emit') using 1
  · simp only [Fin.val_last]
    omega
  · simp [Tape.configuration, List.take_of_length_le]

-- carrierLevel: the mathematical carrier of the fixed scalar codec.
universe carrierLevel
variable {Carrier : Type carrierLevel}

/-- Canonical fixed-domain operations overwrite their scalar slot, with a
constant bound independent of matrix dimensions and runtime values. -/
theorem realizes_operation (codec : BitCodec Carrier width) (operation : Carrier → Carrier)
    (value : Carrier) (left tail : List Symbol) :
    Tape.Steps (machine (FiniteTableMachine.encodedTable codec codec operation)) (3 * width + 2)
      (Tape.configuration (.read 0 (fun _ => false)) left
        (word (List.ofFn (BoolTuple.fromBits (codec.encode value))) ++ tail))
      (Tape.configuration .halt left
        (word (List.ofFn (BoolTuple.fromBits (codec.encode (operation value)))) ++ tail)) := by
  simpa only [FiniteTableMachine.encodedTable, BoolTuple.toBits_fromBits, codec.decode_encode] using
    realizes (FiniteTableMachine.encodedTable codec codec operation) (BoolTuple.fromBits (codec.encode value)) left tail

@[simp] theorem halt (table : (Fin width → Bool) → (Fin width → Bool)) (symbol : Symbol) :
    machine table .halt symbol = none := rfl

end Polytime1.InPlaceTableMachine
