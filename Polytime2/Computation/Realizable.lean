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

import Polytime2.Computation
import Polytime2.CallingConventionRegions

/-! # Existential polynomial-time realizability

The `Internal` namespace is reserved for foundational realization proofs.
Application proofs must use the public mathematical composition rules.
-/

namespace Polytime2

open MultiTape CallingConvention

-- carrierLevel: mathematical values, independently of finite tape/controller names.
universe carrierLevel
variable {Parameter InputName : Type} [Fintype Parameter] [Fintype InputName]

namespace Computation.Realizable.Internal

/-- Size headers, arguments, one public result, and private scratch have distinct tapes. -/
abbrev TapeName (_computation : Computation.{carrierLevel} Parameter InputName)
    (ScratchName : Type) := Parameter ⊕ (InputName ⊕ (Unit ⊕ ScratchName))

noncomputable def domains (computation : Computation.{carrierLevel} Parameter InputName)
    {ScratchName : Type} (scratchDomains : ScratchName → EncodedDomain.{0, carrierLevel} Parameter) :
    Internal.TapeName computation ScratchName → EncodedDomain Parameter :=
  Sum.elim EncodedDomain.unary (Sum.elim computation.inputDomains
    (Sum.elim (fun _ => computation.outputDomain) scratchDomains))

def readOnly (computation : Computation.{carrierLevel} Parameter InputName)
    {ScratchName : Type} : Internal.TapeName computation ScratchName → Bool :=
  Sum.elim (fun _ => true) (Sum.elim (fun _ => true) (fun _ => false))

def sizeTapes (computation : Computation.{carrierLevel} Parameter InputName)
    (ScratchName : Type) : Parameter ↪ Internal.TapeName computation ScratchName :=
  ⟨Sum.inl, Sum.inl_injective⟩

abbrev inputTape (computation : Computation.{carrierLevel} Parameter InputName)
    {ScratchName : Type} (name : InputName) : Internal.TapeName computation ScratchName := .inr (.inl name)

abbrev outputTape (computation : Computation.{carrierLevel} Parameter InputName)
    {ScratchName : Type} : Internal.TapeName computation ScratchName := .inr (.inr (.inl ()))

/-- Select the sole public output; private writable tapes are excluded. -/
def outputTapes (computation : Computation.{carrierLevel} Parameter InputName)
    (ScratchName : Type) : Unit ↪ Internal.TapeName computation ScratchName :=
  ⟨fun _ => Internal.outputTape computation, by intro first second _; cases first; cases second; rfl⟩

abbrev scratchTape (computation : Computation.{carrierLevel} Parameter InputName)
    {ScratchName : Type} (name : ScratchName) : Internal.TapeName computation ScratchName := .inr (.inr (.inr name))

def arguments (computation : Computation.{carrierLevel} Parameter InputName)
    {ScratchName : Type} (scratchDomains : ScratchName → EncodedDomain.{0, carrierLevel} Parameter)
    (sizes : Parameter → ℕ)
    (input : Inputs (Internal.domains computation scratchDomains) (Internal.readOnly computation) sizes) :
    computation.Arguments sizes := fun name => input ⟨Internal.inputTape computation name, rfl⟩

/-- Only the public result is specified; scratch contents are not interpreted. -/
def resultCorrect (computation : Computation.{carrierLevel} Parameter InputName)
    {ScratchName : Type} (scratchDomains : ScratchName → EncodedDomain.{0, carrierLevel} Parameter)
    (sizes : Parameter → ℕ)
    (input : Inputs (Internal.domains computation scratchDomains) (Internal.readOnly computation) sizes)
    (output : Outputs (Internal.domains computation scratchDomains) (Internal.outputTapes computation ScratchName) sizes) : Prop :=
  ∃ valid : computation.precondition sizes (Internal.arguments computation scratchDomains sizes input),
    output () = computation.compute sizes
      ⟨Internal.arguments computation scratchDomains sizes input, valid⟩

variable {computation : Computation.{carrierLevel} Parameter InputName}

/-- Use the implementation certificate with ordinary named mathematical arguments.
Private scratch has no mathematical validity requirement on return. -/
theorem runs {ScratchName State : Type} [Fintype ScratchName] [Fintype State]
    (scratchDomains : ScratchName → EncodedDomain.{0, carrierLevel} Parameter)
    (machine : Machine (Alphabet (Internal.TapeName computation ScratchName)) State)
    (entry exit : State)
    (certificate : CallingConvention.Realizes (Internal.domains computation scratchDomains)
      (Internal.readOnly computation) (Internal.sizeTapes computation ScratchName) (Internal.outputTapes computation ScratchName) machine entry exit
      (fun sizes input => computation.precondition sizes (Internal.arguments computation scratchDomains sizes input))
      (Internal.resultCorrect computation scratchDomains)) :
    ∃ bound : MvPolynomial Parameter ℕ,
      ∀ (sizes : Parameter → ℕ) (arguments : computation.Arguments sizes)
        (valid : computation.precondition sizes arguments)
        (initial : Tapes (Alphabet (Internal.TapeName computation ScratchName))),
        (∀ parameter, initial (.inl parameter) = unary (sizes parameter)) →
        (∀ name, initial (Internal.inputTape computation name) =
          encoded (computation.inputDomains name) sizes (arguments name)) →
        (∀ name, Region ((Internal.domains computation scratchDomains name).width sizes) 0 (initial name)) →
        ∃ ticks final,
          ticks ≤ MvPolynomial.eval sizes bound ∧
          Runs (fun name => (Internal.domains computation scratchDomains name).width sizes)
            (Internal.readOnly computation) machine ticks entry (fun _ => 0) initial
            exit (fun _ => 0) final ∧
          final (Internal.outputTape computation) = encoded computation.outputDomain sizes
            (computation.compute sizes ⟨arguments, valid⟩) := by
  obtain ⟨sizeReadOnly, outputsWritable, halts, bound, execute⟩ := certificate
  refine ⟨bound, ?_⟩
  intro sizes arguments valid initial headers inputs regions
  let input : Inputs (Internal.domains computation scratchDomains) (Internal.readOnly computation) sizes :=
    fun name => match name with
      | ⟨.inl _, _⟩ => PUnit.unit
      | ⟨.inr (.inl argument), _⟩ => arguments argument
      | ⟨.inr (.inr _), impossible⟩ => False.elim (Bool.noConfusion impossible)
  have represented : Entry (Internal.domains computation scratchDomains)
      (Internal.readOnly computation) sizes input initial := by
    constructor
    · intro name readonly
      cases name with
      | inl parameter => exact (headers parameter).trans (encoded_unary parameter sizes).symm
      | inr name => cases name with
        | inl argument => exact inputs argument
        | inr name => contradiction
    · intro name writable
      exact (regions name).exists_buffer
  obtain ⟨ticks, output, final, cost, trace, correct, canonical⟩ :=
    execute sizes input initial valid represented headers
  obtain ⟨good, result⟩ := correct
  refine ⟨ticks, final, cost, trace, ?_⟩
  exact (canonical ()).trans (by rw [result]; rfl)

/-- Execute a hidden realization inside a larger tape collection. Only its
public result is interpreted; all other writable contents stay arbitrary. -/
theorem wiredRuns {ScratchName State TargetTape : Type}
    [Fintype ScratchName] [Fintype State]
    (scratchDomains : ScratchName → EncodedDomain.{0, carrierLevel} Parameter)
    (machine : Machine (Alphabet (Internal.TapeName computation ScratchName)) State)
    (entry exit : State)
    (certificate : CallingConvention.Realizes (Internal.domains computation scratchDomains)
      (Internal.readOnly computation) (Internal.sizeTapes computation ScratchName)
      (Internal.outputTapes computation ScratchName) machine entry exit
      (fun sizes input => computation.precondition sizes
        (Internal.arguments computation scratchDomains sizes input))
      (Internal.resultCorrect computation scratchDomains))
    (wiring : Internal.TapeName computation ScratchName ↪ TargetTape) :
    ∃ bound : MvPolynomial Parameter ℕ,
      ∀ (sizes : Parameter → ℕ) (arguments : computation.Arguments sizes)
        (valid : computation.precondition sizes arguments)
        (width : TargetTape → ℕ) (readOnly : TargetTape → Bool)
        (initial : Tapes (Alphabet TargetTape)),
        (∀ name, width (wiring name) = (Internal.domains computation scratchDomains name).width sizes) →
        (∀ name, readOnly (wiring name) = true → Internal.readOnly computation name = true) →
        (∀ parameter, initial (wiring (.inl parameter)) = unary (sizes parameter)) →
        (∀ name, initial (wiring (Internal.inputTape computation name)) =
          encoded (computation.inputDomains name) sizes (arguments name)) →
        (∀ name, Region (width (wiring name)) 0 (initial (wiring name))) →
        ∃ ticks final, ticks ≤ MvPolynomial.eval sizes bound ∧
          Runs width readOnly (MultiTape.wire wiring machine) ticks entry (fun _ => 0)
            initial exit (fun _ => 0) final ∧
          final (wiring (Internal.outputTape computation)) = encoded computation.outputDomain sizes
            (computation.compute sizes ⟨arguments, valid⟩) ∧
          (∀ name, name ∉ Set.range wiring → final name = initial name) ∧
          (∀ name, Internal.readOnly computation name = true →
            final (wiring name) = initial (wiring name)) := by
  obtain ⟨bound, execute⟩ := runs scratchDomains machine entry exit certificate
  refine ⟨bound, ?_⟩
  intro sizes arguments valid width readOnly initial widths readonly headers inputs regions
  obtain ⟨ticks, localFinal, cost, trace, correct⟩ := execute sizes arguments valid
    (fun name => initial (wiring name)) headers inputs
    (by intro name; rw [← widths]; exact regions name)
  obtain ⟨final, lifted, located, outside, immutable⟩ :=
    trace.wire_restoring wiring width readOnly widths readonly initial (fun _ => rfl)
  exact ⟨ticks, final, cost, lifted, (located _).trans correct, outside, immutable⟩

end Computation.Realizable.Internal

open Computation.Realizable

/-- Existence of a finite machine realizing the mathematical specification.

MANDATORY ABSTRACTION BOUNDARY: APPLICATION PROOFS MUST NOT UNFOLD, DESTRUCT,
OR EXTRACT WITNESSES FROM `Computation.Realizable`. NEVER depend on a reused
computation's machine, scratch tapes, controller states, execution traces, or
polynomial witnesses. Reuse computations ONLY through the standard certified
composition, restriction, and other mathematical construction rules. If a rule
is missing, implement a reusable library rule; DO NOT bypass this boundary.

Witness unpacking is permitted EXCLUSIVELY in foundational realization proofs
and the library implementation of those rules. `Realizable.Internal` is NOT a
supported application API. This is a mandatory library convention, not a claim
that Lean prevents unfolding the proposition.
-/
def Computation.Realizable (computation : Computation.{carrierLevel} Parameter InputName) : Prop :=
  ∃ ScratchName : Type, ∃ finiteScratch : Fintype ScratchName,
    ∃ scratchDomains : ScratchName → EncodedDomain.{0, carrierLevel} Parameter,
      ∃ State : Type, ∃ finiteStates : Fintype State,
        ∃ machine : Machine (Alphabet (Internal.TapeName computation ScratchName)) State,
          ∃ entry exit : State,
            let _scratchFiniteInstance : Fintype ScratchName := finiteScratch
            let _stateFiniteInstance : Fintype State := finiteStates
            CallingConvention.Realizes (Internal.domains computation scratchDomains)
              (Internal.readOnly computation) (Internal.sizeTapes computation ScratchName)
              (Internal.outputTapes computation ScratchName) machine entry exit
              (fun sizes input => computation.precondition sizes
                (Internal.arguments computation scratchDomains sizes input))
              (Internal.resultCorrect computation scratchDomains)

/-- Strengthen a precondition without inspecting the reused realization. -/
theorem Computation.Realizable.withPrecondition
    {computation : Computation.{carrierLevel} Parameter InputName}
    (realizable : computation.Realizable)
    (precondition : ∀ sizes, computation.Arguments sizes → Prop)
    (implies : ∀ sizes arguments, precondition sizes arguments →
      computation.precondition sizes arguments) :
    (computation.withPrecondition precondition implies).Realizable := by
  obtain ⟨ScratchName, finiteScratch, scratchDomains, State, finiteStates,
    machine, entry, exit, certificate⟩ := realizable
  let scratchFiniteInstance : Fintype ScratchName := finiteScratch
  let stateFiniteInstance : Fintype State := finiteStates
  refine ⟨ScratchName, finiteScratch, scratchDomains, State, finiteStates,
    machine, entry, exit, ?_⟩
  obtain ⟨sizeReadOnly, outputsWritable, halts, bound, execute⟩ := certificate
  refine ⟨sizeReadOnly, outputsWritable, halts, bound, ?_⟩
  intro sizes input initial valid represented headers
  obtain ⟨ticks, output, final, cost, trace, correct, canonical⟩ :=
    execute sizes input initial (implies sizes _ valid) represented headers
  obtain ⟨good, result⟩ := correct
  exact ⟨ticks, output, final, cost, trace, ⟨valid, result⟩, canonical⟩

/-- Replace a mathematical specification after proving agreement on its inputs. -/
theorem Computation.Realizable.withSpecification
    {computation : Computation.{carrierLevel} Parameter InputName}
    (realizable : computation.Realizable)
    (precondition : ∀ sizes, computation.Arguments sizes → Prop)
    (compute : ∀ sizes, {arguments : computation.Arguments sizes // precondition sizes arguments} →
      computation.outputDomain.Carrier sizes)
    (compatible : ∀ sizes arguments, precondition sizes arguments →
      computation.precondition sizes arguments)
    (correct : ∀ sizes arguments valid,
      computation.compute sizes ⟨arguments, compatible sizes arguments valid⟩ =
        compute sizes ⟨arguments, valid⟩) :
    (Computation.mk computation.inputDomains computation.outputDomain precondition compute).Realizable := by
  have restricted := realizable.withPrecondition precondition compatible
  have equal : computation.withPrecondition precondition compatible =
      Computation.mk computation.inputDomains computation.outputDomain precondition compute := by
    change Computation.mk _ _ _ _ = Computation.mk _ _ _ _
    congr 1
    funext sizes arguments
    exact correct sizes arguments.val arguments.property
  rwa [equal] at restricted

end Polytime2
