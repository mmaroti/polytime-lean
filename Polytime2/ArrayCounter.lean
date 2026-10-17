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

import Polytime2.StandardBinaryDecrement
import Polytime2.StandardTapeCommands

/-! # Shared private counter operations for array navigation -/

namespace Polytime2.ArrayCounter

open MultiTape CallingConvention
open Binary (Symbol data word value)

abbrev Alphabet := CallingConvention.Alphabet (Fin 2)
abbrev State := Sum StandardBinaryDecrement.State (Fin 3)

def frame (bits : List Bool) (scratch : List Symbol) : Tapes Alphabet := fun name =>
  if name = 0 then buffer (word bits) else buffer scratch

def decrementWiring : Bool ↪ Fin 2 :=
  ⟨(fun name => if name then 1 else 0), by
    intro first second equal
    cases first <;> cases second <;> simp_all⟩

@[simp] theorem decrementWiring_apply (name : Bool) : decrementWiring name = (if name then 1 else 0) := rfl

noncomputable def decrement : Machine Alphabet StandardBinaryDecrement.State :=
  MultiTape.wire decrementWiring StandardBinaryDecrement.machine

noncomputable def copyBack : Machine Alphabet (Fin 3) := StandardTapeCommands.copy 1 0 (by decide)

noncomputable def machine : Machine Alphabet State :=
  MultiTape.sequence decrement copyBack 0

def entry : State := .inl StandardBinaryDecrement.entry
def exit : State := .inr 2

/-- Only private storage is overwritten; both fixed-width heads are restored. -/
theorem runs (bits : List Bool) (scratch : List Symbol) (sameLength : scratch.length = bits.length) :
    Runs (fun _ : Fin 2 => bits.length) (fun _ => false) machine (4 * bits.length + 6)
      entry (fun _ => 0) (frame bits scratch) exit (fun _ => 0)
      (frame (Binary.decrement bits) (word (Binary.decrement bits))) := by
  have first := (StandardBinaryDecrement.runs bits scratch sameLength).wire_of_eq
    decrementWiring (fun _ : Fin 2 => bits.length) (fun _ => false)
    (by intro name; rfl) (by intro name premise; cases premise)
    (frame bits scratch) (frame bits (word (Binary.decrement bits)))
    (by intro name; cases name <;> exact (buffer_padding _).symm)
    (by intro name; cases name <;> exact (buffer_padding _).symm)
    (by
      intro name outside
      fin_cases name
      · exact False.elim (outside ⟨false, rfl⟩)
      · exact False.elim (outside ⟨true, rfl⟩))
  have second := StandardTapeCommands.copy_runs (1 : Fin 2) 0 (by decide)
    (fun _ : Fin 2 => bits.length) (fun _ => false) rfl (Binary.decrement bits) (word bits)
    (Binary.decrement_length bits).symm (Binary.decrement_length bits).symm
    (by simp [word]) (frame bits (word (Binary.decrement bits))) rfl rfl
  have copied : Function.update (frame bits (word (Binary.decrement bits))) 0
      (buffer (word (Binary.decrement bits))) = frame (Binary.decrement bits) (word (Binary.decrement bits)) := by
    funext name
    fin_cases name <;> simp [frame]
  rw [copied] at second
  have complete := first.sequence copyBack 0
    (by intro symbols; simp [MultiTape.wire, StandardBinaryDecrement.machine, StandardBinaryDecrement.exit, MultiTape.withExit]) second
  simp only [Binary.decrement_length] at complete
  convert complete using 1 <;> first | rfl | omega

noncomputable def clear : Machine Alphabet (StandardBinaryScan.State Unit) :=
  MultiTape.wire decrementWiring (StandardBinaryScan.machine BinaryScan.clear)

theorem clear_runs (bits : List Bool) (scratch : List Symbol) (sameLength : scratch.length = bits.length) :
    Runs (fun _ : Fin 2 => bits.length) (fun _ => false) clear (2 * bits.length + 2)
      (.inl ()) (fun _ => 0) (frame bits scratch) (.inr ((), true)) (fun _ => 0)
      (frame bits (word (List.replicate bits.length false))) := by
  have trace := StandardBinaryScan.runs BinaryScan.clear () bits scratch sameLength
  simp only [StandardBinaryScan.run, BinaryScan.clear_run] at trace
  exact trace.wire_of_eq decrementWiring (fun _ : Fin 2 => bits.length) (fun _ => false)
    (by intro name; rfl) (by intro name premise; cases premise)
    (frame bits scratch) (frame bits (word (List.replicate bits.length false)))
    (by intro name; cases name <;> exact (buffer_padding _).symm)
    (by intro name; cases name <;> exact (buffer_padding _).symm)
    (by
      intro name outside
      fin_cases name
      · exact False.elim (outside ⟨false, rfl⟩)
      · exact False.elim (outside ⟨true, rfl⟩))


end Polytime2.ArrayCounter
