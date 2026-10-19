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

import Polytime2.Primitives.RestoringScan
import Polytime2.Primitives.FixedCopy

/-! # Marker-free runtime-width copying

The source determines the extent of the copy. The destination may contain
blanks anywhere inside its reserved region. Both heads return to the first
cell, including when the source word is empty.
-/

namespace Polytime2.StandardTerminatedCopy

open MultiTape
open Binary (Symbol data word)
open Copy (frame)

def machine : Machine (fun _ : Bool => Symbol) (Fin 3) := fun state symbols =>
  match state.val with
  | 0 => if symbols false = 0 then
      some (1, fun name => (symbols name, some .left))
    else some (0, fun _ => (symbols false, some .right))
  | 1 => if symbols false = 0 then
      some (2, fun name => (symbols name, some .right))
    else some (1, fun name => (symbols name, some .left))
  | _ => none

private def copyDigit (_memory : Unit) (bit : Bool) : Unit × Bool := ((), bit)

private theorem copy_run (bits : List Bool) : BinaryScan.run copyDigit () bits = ((), bits) := by
  induction bits with
  | nil => rfl
  | cons bit bits hypothesis => simp [BinaryScan.run, copyDigit, hypothesis]

private def copyState : RestoringScan.State Unit → Fin 3
  | .inl _ => 0
  | .inr (_, false) => 1
  | .inr (_, true) => 2

private theorem copy_transition (state : RestoringScan.State Unit) (symbols : Symbols (fun _ : Bool => Symbol))
    (next : RestoringScan.State Unit) (actions : Actions (fun _ : Bool => Symbol))
    (instruction : RestoringScan.machine copyDigit state symbols = some (next, actions)) :
    machine (copyState state) symbols = some (copyState next, actions) := by
  have same : machine (copyState state) symbols =
      (RestoringScan.machine copyDigit state symbols).map
        (fun command => (copyState command.1, command.2)) := by
    have preserved (blank : symbols false ≠ 0) : data (symbols false == 2) = symbols false := by
      generalize equal : symbols false = symbol at *
      fin_cases symbol <;> simp_all [Binary.data]
    rcases state with memory | ⟨memory, finished⟩
    · cases memory
      by_cases blank : symbols false = 0
      · simp [RestoringScan.machine, machine, copyState, blank]
      · simp [RestoringScan.machine, machine, copyState, copyDigit, blank, preserved blank]
    · cases finished <;> by_cases blank : symbols false = 0 <;>
        simp [RestoringScan.machine, machine, copyState, blank]
  rw [same, instruction]
  rfl

/-- Copying specializes the shared scan without retaining controller memory. -/
theorem steps (bits : List Bool) (old : List Symbol)
    (sameLength : old.length = bits.length)
    (sourceLeft sourceRight targetLeft targetRight : List Symbol) :
    Steps machine (2 * bits.length + 2)
      (0, frame (0 :: sourceLeft) (word bits ++ 0 :: sourceRight)
        (0 :: targetLeft) (old ++ 0 :: targetRight))
      (2, frame (0 :: sourceLeft) (word bits ++ 0 :: sourceRight)
        (0 :: targetLeft) (word bits ++ 0 :: targetRight)) := by
  have trace := (RestoringScan.steps copyDigit () bits old sameLength
    sourceLeft sourceRight targetLeft targetRight).rename copyState copy_transition
  simpa only [copy_run, copyState] using trace

open CallingConvention

/-- Copying inherits safety and head restoration from the shared scanner. -/
theorem runs (bits : List Bool) (old : List Symbol) (sameLength : old.length = bits.length) :
    Runs (fun _ : Bool => bits.length) (fun name => !name) machine
      (2 * bits.length + 2) 0 (fun _ => 0)
      (frame [0] (word bits ++ [0]) [0] (old ++ [0]))
      2 (fun _ => 0) (frame [0] (word bits ++ [0]) [0] (word bits ++ [0])) := by
  have trace := (RestoringScan.runs copyDigit () bits old sameLength).rename copyState copy_transition
  simpa only [copy_run, copyState] using trace

-- parameterLevel: size names bounding the runtime number of copied bits.
universe parameterLevel

-- carrierLevel: mathematical elements copied by the routine.
universe carrierLevel

variable {Parameter : Type parameterLevel} [Fintype Parameter]

/-- Size arguments and the source are immutable; only the result is writable. -/
def readOnly : Sum Parameter Bool → Bool
  | .inl _ => true
  | .inr name => !name

/-- Every argument tape, including each unary size argument, has a domain. -/
noncomputable def domains (domain : EncodedDomain.{parameterLevel, carrierLevel} Parameter) :
    Sum Parameter Bool → EncodedDomain.{parameterLevel, carrierLevel} Parameter
  | .inl parameter => EncodedDomain.unary parameter
  | .inr _ => domain

def sizeTapes : Parameter ↪ Sum Parameter Bool :=
  ⟨Sum.inl, by intro first second equal; cases equal; rfl⟩

def dataTapes : Bool ↪ Sum Parameter Bool :=
  ⟨Sum.inr, by intro first second equal; cases equal; rfl⟩

/-- Only the result tape is a public output. -/
def outputTapes : Unit ↪ Sum Parameter Bool := oneTape (.inr true)

/-- The controller is independent of the runtime width. Size inputs are idle. -/
noncomputable def algorithm : Machine (CallingConvention.Alphabet (Sum Parameter Bool)) (Fin 3) :=
  MultiTape.wire dataTapes machine

/-- Copy any polynomial-width encoded domain, including its immutable unary
size inputs, with arbitrary initial output contents and restored heads. -/
theorem contract (domain : EncodedDomain.{parameterLevel, carrierLevel} Parameter) :
    CallingConvention.Realizes (domains domain) readOnly sizeTapes outputTapes algorithm 0 2
      (fun _ _ => True)
      (fun _ input output => output () = input ⟨.inr false, rfl⟩) := by
  let bound := domain.widthPolynomial
  refine ⟨(by intro parameter; rfl), (by intro name; rfl), (by intro symbols; simp [algorithm, MultiTape.wire, machine]),
    2 * bound + 2, ?_⟩
  intro assignment input initial valid represented sizes
  let bits := List.ofFn (fun index : Fin (domain.width assignment) =>
    (domain.encode assignment (input ⟨.inr false, rfl⟩)).getLsbD index.val)
  have bitsLength : bits.length = domain.width assignment := List.length_ofFn
  obtain ⟨old, oldLength, target⟩ := represented.2 (.inr true) rfl
  have source := represented.1 (.inr false) rfl
  have sourceEq : initial (.inr false) = buffer (word bits) := source
  have targetEq : initial (.inr true) = buffer old := target
  have start : install dataTapes (frame [0] (word bits ++ [0]) [0] (old ++ [0])) initial = initial := by
    funext name
    cases name with
    | inl parameter =>
      apply install_outside
      rintro ⟨name, equal⟩
      cases equal
    | inr name =>
      rw [show Sum.inr name = dataTapes name from rfl, install_at]
      cases name with
      | false =>
        change Turing.Tape.mk' _ _ = initial (.inr false)
        rw [buffer_padding]
        exact sourceEq.symm
      | true =>
        change Turing.Tape.mk' _ _ = initial (.inr true)
        rw [buffer_padding]
        exact targetEq.symm
  have trace := (runs bits old (oldLength.trans bitsLength.symm)).wire dataTapes
    (fun name => (domains domain name).width assignment) readOnly
    (by intro name; exact bitsLength.symm) (by intro name premise; exact premise) initial (fun _ => 0)
  have positions : install (dataTapes (Parameter := Parameter)) (fun _ : Bool => (0 : ℤ))
      (fun _ : Sum Parameter Bool => (0 : ℤ)) = fun _ => 0 := by
    exact install_self dataTapes (fun _ : Sum Parameter Bool => (0 : ℤ))
  rw [start, positions] at trace
  let output : Outputs (domains domain) outputTapes assignment := fun _ => input ⟨.inr false, rfl⟩
  refine ⟨2 * bits.length + 2, output,
    install dataTapes (frame [0] (word bits ++ [0]) [0] (word bits ++ [0])) initial,
    ?_, ?_, rfl, ?_⟩
  · simp only [EncodedDomain.width] at bitsLength
    simp only [bound, map_add, map_mul, map_ofNat]
    omega
  · exact trace
  · intro name
    cases name
    change install dataTapes _ initial (dataTapes true) = encoded domain assignment _
    rw [install_at]
    exact buffer_padding (word bits)

end Polytime2.StandardTerminatedCopy
