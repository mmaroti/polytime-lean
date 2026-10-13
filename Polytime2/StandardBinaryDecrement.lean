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

import Polytime2.StandardBinaryScan

/-! # Restoring fixed-width decrement into a separate output

Array traversal decrements private bounded counters. The input stays canonical
and unchanged; every output digit is overwritten, including from blank storage.
-/

namespace Polytime2.StandardBinaryDecrement

open MultiTape CallingConvention
open Binary (Symbol word value)

def update (borrow bit : Bool) : Bool × Bool := (borrow && !bit, bit != borrow)

private theorem idle_run (bits : List Bool) :
    BinaryScan.run update false bits = (false, bits) := by
  induction bits with
  | nil => rfl
  | cons bit bits hypothesis => cases bit <;> simp [BinaryScan.run, update, hypothesis]

/-- The finite borrow state implements the existing mathematical decrement. -/
theorem digits (bits : List Bool) : (BinaryScan.run update true bits).2 = Binary.decrement bits := by
  induction bits with
  | nil => rfl
  | cons bit bits hypothesis =>
    cases bit <;> simp [BinaryScan.run, update, Binary.decrement, hypothesis, idle_run]

abbrev State := Sum (StandardBinaryScan.State Bool) Unit

noncomputable def machine : Machine StandardBinaryScan.Alphabet State :=
  MultiTape.withExit (StandardBinaryScan.machine update)

def entry : State := .inl (.inl true)
def exit : State := .inr ()

/-- The private final borrow is hidden behind a single restoring exit. -/
theorem runs (bits : List Bool) (old : List Symbol) (sameLength : old.length = bits.length) :
    Runs (fun _ : Bool => bits.length) (fun name => !name) machine (2 * bits.length + 3)
      entry (fun _ => 0) (Copy.frame [0] (word bits ++ [0]) [0] (old ++ [0]))
      exit (fun _ => 0) (Copy.frame [0] (word bits ++ [0]) [0] (word (Binary.decrement bits) ++ [0])) := by
  have trace := (StandardBinaryScan.runs update true bits old sameLength).withExit
    (by intro symbols; simp [StandardBinaryScan.machine])
  rw [digits] at trace
  exact trace

-- parameterLevel: names of the runtime size parameters, including counter width.
universe parameterLevel
variable {Parameter : Type parameterLevel} [Fintype Parameter]

/-- Natural predecessor fits the same fixed binary capacity. -/
def compute (parameter : Parameter) (assignment : Parameter → ℕ)
    (number : Fin (2 ^ assignment parameter)) : Fin (2 ^ assignment parameter) :=
  ⟨number.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) number.isLt⟩

/-- Positive counters decrement by one on a distinct result tape. -/
theorem contract (parameter : Parameter) :
    CallingConvention.Realizes
      (StandardBinaryScan.domains (EncodedDomain.binaryNaturals parameter) (EncodedDomain.binaryNaturals parameter))
      StandardTerminatedCopy.readOnly StandardTerminatedCopy.sizeTapes
      (StandardBinaryScan.algorithm update) entry exit
      (fun assignment input => 0 < (input ⟨.inr false, rfl⟩ : Fin (2 ^ assignment parameter)).val)
      (fun assignment input output => output ⟨.inr true, rfl⟩ = compute parameter assignment (input ⟨.inr false, rfl⟩)) := by
  apply StandardBinaryScan.contract update true
    (EncodedDomain.binaryNaturals parameter) (EncodedDomain.binaryNaturals parameter)
    (by intro assignment; rfl) (fun _ number => 0 < number.val) (compute parameter)
  intro assignment number positive
  let bits := List.ofFn (fun index : Fin (assignment parameter) => (BitVec.ofFin number).getLsbD index.val)
  have bitsLength : bits.length = assignment parameter := List.length_ofFn
  have bitsValue : value bits = number.val := Binary.value_bits (BitVec.ofFin number)
  have decremented := Binary.decrement_value bits (by rw [bitsValue]; exact positive)
  have computed : (compute parameter assignment number).val = value (Binary.decrement bits) := by
    dsimp only [compute]
    omega
  change (BinaryScan.run update true bits).2 =
    List.ofFn (fun index : Fin (assignment parameter) =>
      (BitVec.ofFin (compute parameter assignment number)).getLsbD index.val)
  rw [digits, ← BitVec.ofNat_finVal, computed]
  exact (Binary.bits_value (Binary.decrement bits) ((Binary.decrement_length bits).trans bitsLength)).symm

end Polytime2.StandardBinaryDecrement
