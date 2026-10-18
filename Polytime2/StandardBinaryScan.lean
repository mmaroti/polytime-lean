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

import Polytime2.RestoringScan
import Polytime2.CallingConvention
import Polytime2.Copy
import Polytime2.StandardTerminatedCopy

/-! # Immutable-input finite-memory binary scans

The source fixes the width and remains unchanged. Every output bit is written
regardless of old contents; both heads return without boundary markers.
Clearing and binary shifts use the same scan with different finite memories.
-/

namespace Polytime2.StandardBinaryScan

open MultiTape CallingConvention
open Binary (Symbol word)
open Copy (frame)

-- memoryLevel: specialization-fixed finite transducer memory.
universe memoryLevel
variable {Memory : Type memoryLevel}

export RestoringScan (Alphabet State machine steps runs)
abbrev run := @BinaryScan.run

variable (update : Memory → Bool → Memory × Bool)

-- parameterLevel: size names; carrierLevel: mathematical input and output values.
universe parameterLevel carrierLevel
variable {Parameter : Type parameterLevel} [Fintype Parameter]

/-- The scan's mathematical domains can differ while their bit widths agree. -/
noncomputable def domains (inputDomain outputDomain : EncodedDomain.{parameterLevel, carrierLevel} Parameter) :
    Sum Parameter Bool → EncodedDomain.{parameterLevel, carrierLevel} Parameter
  | .inl parameter => EncodedDomain.unary parameter
  | .inr false => inputDomain
  | .inr true => outputDomain

/-- A common exit hides the transducer's private final controller memory. -/
noncomputable def algorithm :
    Machine (CallingConvention.Alphabet (Sum Parameter Bool)) (Sum (State Memory) Unit) :=
  MultiTape.wire StandardTerminatedCopy.dataTapes (MultiTape.withExit (machine update))

/-- A finite-memory scan realizes any mathematical map whose encodings follow
its digit rule. Hypotheses and correctness remain mathematical propositions. -/
theorem contract [Fintype Memory] (memory : Memory)
    (inputDomain outputDomain : EncodedDomain.{parameterLevel, carrierLevel} Parameter)
    (sameWidth : ∀ assignment, outputDomain.width assignment = inputDomain.width assignment)
    (hypothesis : ∀ assignment, inputDomain.Carrier assignment → Prop)
    (compute : ∀ assignment, inputDomain.Carrier assignment → outputDomain.Carrier assignment)
    (correct : ∀ assignment value, hypothesis assignment value →
      (run update memory (List.ofFn (fun index : Fin (inputDomain.width assignment) =>
        (inputDomain.encode assignment value).getLsbD index.val))).2 =
      List.ofFn (fun index : Fin (outputDomain.width assignment) =>
        (outputDomain.encode assignment (compute assignment value)).getLsbD index.val)) :
    CallingConvention.Realizes (domains inputDomain outputDomain) StandardTerminatedCopy.readOnly
      StandardTerminatedCopy.sizeTapes StandardTerminatedCopy.outputTapes (algorithm update) (.inl (.inl memory)) (.inr ())
      (fun assignment input => hypothesis assignment (input ⟨.inr false, rfl⟩))
      (fun assignment input output =>
        output () = compute assignment (input ⟨.inr false, rfl⟩)) := by
  let bound := inputDomain.widthPolynomial
  refine ⟨(by intro parameter; rfl), (by intro name; rfl),
    (by intro symbols; simp [algorithm, MultiTape.wire, MultiTape.withExit]), 2 * bound + 3, ?_⟩
  intro assignment input initial valid represented sizes
  let bits := List.ofFn (fun index : Fin (inputDomain.width assignment) =>
    (inputDomain.encode assignment (input ⟨.inr false, rfl⟩)).getLsbD index.val)
  have bitsLength : bits.length = inputDomain.width assignment := List.length_ofFn
  obtain ⟨old, oldLength, target⟩ := represented.2 (.inr true) rfl
  have oldFits : old.length = bits.length := by
    exact oldLength.trans ((sameWidth assignment).trans bitsLength.symm)
  have sourceEq : initial (.inr false) = buffer (word bits) := represented.1 (.inr false) rfl
  have targetEq : initial (.inr true) = buffer old := target
  let wiring := StandardTerminatedCopy.dataTapes (Parameter := Parameter)
  have start : install wiring (frame [0] (word bits ++ [0]) [0] (old ++ [0])) initial = initial := by
    funext name
    cases name with
    | inl parameter =>
      apply install_outside
      rintro ⟨name, equal⟩
      cases equal
    | inr name =>
      rw [show Sum.inr name = wiring name from rfl, install_at]
      cases name with
      | false =>
        change Turing.Tape.mk' _ _ = initial (.inr false)
        rw [buffer_padding]
        exact sourceEq.symm
      | true =>
        change Turing.Tape.mk' _ _ = initial (.inr true)
        rw [buffer_padding]
        exact targetEq.symm
  have localTrace := (runs update memory bits old oldFits).withExit
    (by intro symbols; simp [machine])
  have trace := localTrace.wire wiring
    (fun name => (domains inputDomain outputDomain name).width assignment)
    StandardTerminatedCopy.readOnly
    (by intro name; cases name with
        | false => exact bitsLength.symm
        | true => exact (sameWidth assignment).trans bitsLength.symm)
    (by intro name premise; exact premise) initial (fun _ => 0)
  have positions : install wiring (fun _ : Bool => (0 : ℤ))
      (fun _ : Sum Parameter Bool => (0 : ℤ)) = fun _ => 0 :=
    install_self wiring (fun _ : Sum Parameter Bool => (0 : ℤ))
  rw [start, positions] at trace
  let output : Outputs (domains inputDomain outputDomain) StandardTerminatedCopy.outputTapes assignment :=
    fun _ => compute assignment (input ⟨.inr false, rfl⟩)
  refine ⟨2 * bits.length + 2 + 1, output,
    install wiring (frame [0] (word bits ++ [0]) [0] (word (run update memory bits).2 ++ [0])) initial,
    ?_, trace, rfl, ?_⟩
  · simp only [EncodedDomain.width] at bitsLength
    simp only [bound, map_add, map_mul, map_ofNat]
    omega
  · intro name
    cases name
    change install wiring _ initial (wiring true) = encoded outputDomain assignment _
    rw [install_at]
    change Turing.Tape.mk' _ _ = encoded outputDomain assignment _
    rw [buffer_padding]
    change buffer (word (run update memory bits).2) = buffer (word _)
    rw [correct assignment _ valid]

end Polytime2.StandardBinaryScan
