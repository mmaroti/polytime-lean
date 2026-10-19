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

import Polytime2.Primitives.TapeCommands

/-! # Binary counter initialization from its unary capacity

The immutable size tape determines exactly which output cells are written.
Initialization is an ordinary computation and accepts blank output cells.
-/

namespace Polytime2.StandardCounterZero

open MultiTape CallingConvention
open Binary (Symbol word)

-- parameterLevel: immutable unary size names, including counter bit capacity.
universe parameterLevel
variable {Parameter : Type parameterLevel} [Fintype Parameter] [DecidableEq Parameter]

noncomputable def domains (capacity : Parameter) : Sum Parameter Unit → EncodedDomain Parameter
  | .inl parameter => EncodedDomain.unary parameter
  | .inr _ => EncodedDomain.binaryNaturals capacity

def readOnly : Sum Parameter Unit → Bool
  | .inl _ => true
  | .inr _ => false

def sizeTapes : Parameter ↪ Sum Parameter Unit :=
  ⟨Sum.inl, by intro first second equal; cases equal; rfl⟩

def outputTapes : Unit ↪ Sum Parameter Unit := oneTape (.inr ())

noncomputable def algorithm (capacity : Parameter) :
    Machine (CallingConvention.Alphabet (Sum Parameter Unit)) (StandardBinaryScan.State Unit) :=
  StandardTapeCommands.clear (.inl capacity) (.inr ()) (by simp)

/-- No prefill is required, and all unary size inputs remain unchanged. -/
theorem contract (capacity : Parameter) :
    CallingConvention.Realizes (domains capacity) readOnly sizeTapes outputTapes (algorithm capacity)
      (.inl ()) (.inr ((), true)) (fun _ _ => True)
      (fun _ _ output => (output ()).val = 0) := by
  refine ⟨(by intro parameter; rfl), (by intro name; rfl), (by
    intro symbols
    simp [algorithm, StandardTapeCommands.clear, MultiTape.wire, StandardBinaryScan.machine]),
    2 * MvPolynomial.X capacity + 2, ?_⟩
  intro assignment input initial valid represented sizes
  obtain ⟨old, oldLength, oldEq⟩ := represented.2 (.inr ()) rfl
  simp [domains, EncodedDomain.binaryNaturals, EncodedDomain.ofCodec] at oldLength
  have sourceEq : initial (.inl capacity) =
      buffer (word (List.replicate (assignment capacity) true)) := sizes capacity
  have trace := StandardTapeCommands.clear_runs (.inl capacity) (.inr ()) (by simp)
    (fun name => (domains capacity name).width assignment) readOnly rfl
    (List.replicate (assignment capacity) true) old (by simp [domains, EncodedDomain.unary])
    (by simp [domains, EncodedDomain.binaryNaturals]) (by simpa using oldLength)
    initial sourceEq oldEq
  have encodedZero : encoded (EncodedDomain.binaryNaturals capacity) assignment
      (⟨0, by positivity⟩ : Fin (2 ^ assignment capacity)) =
        buffer (word (List.replicate (assignment capacity) false)) := by
    have zero : Binary.value (List.replicate (assignment capacity) false) = 0 := by
      simp
    simpa only [zero] using encoded_binaryNaturals capacity assignment
      (List.replicate (assignment capacity) false) (by simp)
  let output : Outputs (domains capacity) outputTapes assignment := fun _ => ⟨0, by positivity⟩
  refine ⟨2 * assignment capacity + 2, output,
    Function.update initial (.inr ()) (buffer (word (List.replicate (assignment capacity) false))),
    ?_, ?_, rfl, ?_⟩
  · simp
  · simpa only [List.length_replicate, algorithm] using trace
  · intro name
    cases name
    change Function.update initial (.inr ())
      (buffer (word (List.replicate (assignment capacity) false))) (.inr ()) =
        encoded (EncodedDomain.binaryNaturals capacity) assignment ⟨0, _⟩
    rw [Function.update_self]
    exact encodedZero.symm

end Polytime2.StandardCounterZero
