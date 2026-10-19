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

import Polytime2.Computation.Realizable
import Polytime2.Encoding.BoundedUnary
import Polytime2.Primitives.UnaryHeader

/-! # Compiling certified unary size producers to private raw headers

The producer uses proper bounded unary data. Its finite implementation is
followed by the restoring header adapter. Only polynomial capacities and
runtime witnesses are chosen privately by this reusable compiler rule.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation.Realizable.Internal

open MultiTape CallingConvention

variable {Parameter InputName : Type} [Fintype Parameter] [Fintype InputName]

/-- Public arguments retain their exact widths; private writable tapes reserve
one larger capacity, independently of the producer's runtime value. -/
noncomputable def privateWidths (computation : Computation Parameter InputName) (Scratch : Type)
    (sizes : Parameter → ℕ) (capacity : ℕ) : TapeName computation Scratch → ℕ
  | .inl parameter => sizes parameter
  | .inr (.inl name) => (computation.inputDomains name).width sizes
  | .inr (.inr _) => capacity

/-- A certified bounded unary computation prepares a raw private size tape,
including its own scratch, from blank writable storage of any larger capacity. -/
theorem preparesUnary (computation : Computation Parameter InputName)
    (capacityPolynomial : MvPolynomial Parameter ℕ)
    (outputDomain : computation.outputDomain = EncodedDomain.boundedUnary capacityPolynomial)
    (realizable : computation.Realizable) :
    ∃ (Scratch : Type) (_finiteScratch : Fintype Scratch)
      (State : Type) (_finiteState : Fintype State)
      (machine : Machine (Alphabet (TapeName computation Scratch)) State)
      (entry exit : State) (capacityBound runtimeBound : MvPolynomial Parameter ℕ),
      (∀ symbols, machine exit symbols = none) ∧
      ∀ (sizes : Parameter → ℕ) (arguments : computation.Arguments sizes)
        (valid : computation.precondition sizes arguments) (capacity : ℕ)
        (_fits : MvPolynomial.eval sizes capacityBound ≤ capacity)
        (initial : Tapes (Alphabet (TapeName computation Scratch))),
        (∀ parameter, initial (.inl parameter) = unary (sizes parameter)) →
        (∀ name, initial (inputTape computation name) = encoded (computation.inputDomains name) sizes (arguments name)) →
        (∀ name, readOnly computation name = false → initial name = buffer []) →
        (∀ name, Region (privateWidths computation Scratch sizes capacity name) 0 (initial name)) →
        ∃ ticks final, ticks ≤ MvPolynomial.eval sizes runtimeBound ∧
          Runs (privateWidths computation Scratch sizes capacity) (readOnly computation) machine ticks
            entry (fun _ => 0) initial exit (fun _ => 0) final ∧
          final (outputTape computation) = unary
            ((cast (congrArg (fun domain : EncodedDomain Parameter => domain.Carrier sizes) outputDomain)
              (computation.compute sizes ⟨arguments, valid⟩)).val) := by
  classical
  rcases computation with ⟨inputDomains, resultDomain, precondition, compute⟩
  cases outputDomain
  let computation : Computation Parameter InputName :=
    ⟨inputDomains, EncodedDomain.boundedUnary capacityPolynomial, precondition, compute⟩
  change computation.Realizable at realizable
  obtain ⟨SourceScratch, sourceScratchFinite, sourceScratchDomains, SourceState, sourceStateFinite,
    source, sourceEntry, sourceExit, sourceCertificate⟩ := realizable
  let _sourceScratchFinite := sourceScratchFinite
  let _sourceStateFinite := sourceStateFinite
  let Scratch := SourceScratch ⊕ Unit
  let temporary : TapeName computation Scratch := scratchTape computation (.inr ())
  let sourceWiring : TapeName computation SourceScratch ↪ TapeName computation Scratch :=
    ⟨(fun role => match role with
      | .inl parameter => .inl parameter
      | .inr (.inl argument) => inputTape computation argument
      | .inr (.inr (.inl _)) => temporary
      | .inr (.inr (.inr name)) => scratchTape computation (.inl name)), by
      intro first second equal
      rcases first with parameter | argument | result | name <;>
        rcases second with parameter' | argument' | result' | name'
      all_goals first
        | (cases result; cases result'; rfl)
        | (dsimp only [temporary, inputTape, scratchTape] at equal; cases equal <;> rfl)⟩
  let headerWiring : Bool ↪ TapeName computation Scratch :=
    ⟨(fun choice => if choice then outputTape computation else temporary), by
      intro first second equal
      cases first <;> cases second <;> simp_all [temporary, outputTape, scratchTape]⟩
  let prepare : Machine (Alphabet (TapeName computation Scratch)) SourceState := MultiTape.wire sourceWiring source
  let normalize : Machine (Alphabet (TapeName computation Scratch)) (SymbolScan.State Unit) :=
    MultiTape.wire headerWiring UnaryHeader.machine
  let algorithm := MultiTape.sequence prepare normalize (.inl ())
  obtain ⟨sourceBound, execute⟩ := Internal.runs sourceScratchDomains source sourceEntry sourceExit sourceCertificate
  let storageBound := capacityPolynomial + ∑ name, (sourceScratchDomains name).widthPolynomial
  refine ⟨Scratch, inferInstance, _, inferInstance, algorithm, .inl sourceEntry, .inr (.inr ((), true)),
    storageBound, sourceBound + 2 * capacityPolynomial + 3, ?_, ?_⟩
  · intro symbols
    simp [algorithm, MultiTape.sequence, normalize, MultiTape.wire, UnaryHeader.machine, SymbolScan.machine]
  intro sizes arguments valid capacity fits initial headers inputs blank regions
  let width := privateWidths computation Scratch sizes capacity
  let readonly : TapeName computation Scratch → Bool := readOnly computation
  have total : MvPolynomial.eval sizes capacityPolynomial + ∑ name, (sourceScratchDomains name).width sizes ≤ capacity := by
    simpa only [storageBound, map_add, map_sum] using fits
  have capacityFits : MvPolynomial.eval sizes capacityPolynomial ≤ capacity := by omega
  have scratchFits (name : SourceScratch) : (sourceScratchDomains name).width sizes ≤ capacity :=
    (Finset.single_le_sum (fun other _ => Nat.zero_le ((sourceScratchDomains other).width sizes))
      (Finset.mem_univ name)).trans (by omega)
  have widths : ∀ role, (domains computation sourceScratchDomains role).width sizes ≤ width (sourceWiring role) := by
    rintro (parameter | argument | result | name)
    · simp [width, privateWidths, sourceWiring, domains, EncodedDomain.unary, EncodedDomain.ofCodec]
    · exact le_rfl
    · exact capacityFits
    · exact scratchFits name
  obtain ⟨sourceTicks, sourceFinal, sourceCost, sourceTrace, correct⟩ := execute sizes arguments valid
    (fun role => initial (sourceWiring role)) headers inputs (by
      rintro (parameter | argument | result | name)
      · simpa [width, privateWidths, sourceWiring, domains, EncodedDomain.unary, EncodedDomain.ofCodec]
          using regions (.inl parameter)
      · exact regions (inputTape computation argument)
      · change Region _ 0 (initial temporary)
        rw [blank temporary rfl]
        exact CallingConvention.blank_region _
      · change Region _ 0 (initial (scratchTape computation (.inl name)))
        rw [blank (scratchTape computation (.inl name)) rfl]
        exact CallingConvention.blank_region _)
  have enlarged := sourceTrace.regions (fun role => width (sourceWiring role)) (fun _ => 0) (by
    intro role writable
    constructor
    · omega
    · simp only [zero_add]
      exact_mod_cast widths role)
  simp only [add_zero] at enlarged
  obtain ⟨middle, sourceLifted, located, outside, preserved⟩ := enlarged.wire_restoring sourceWiring width readonly
    (fun _ => rfl) (by rintro (parameter | argument | result | name) premise <;> first | rfl | contradiction)
    initial (fun _ => rfl)
  have properHeader : middle temporary = buffer (Binary.word
      (BoundedUnary.bits (MvPolynomial.eval sizes capacityPolynomial) (compute sizes ⟨arguments, valid⟩).val)) := by
    have result := (located (outputTape computation)).trans correct
    change middle temporary = encoded (EncodedDomain.boundedUnary capacityPolynomial) sizes
      (compute sizes ⟨arguments, valid⟩) at result
    simpa only [encoded, EncodedDomain.boundedUnary, BoundedUnary.encode_bits, tape, buffer] using result
  have outputBlank : middle (outputTape computation) = buffer [] := by
    refine (outside (outputTape computation) ?_).trans (blank (outputTape computation) rfl)
    rintro ⟨role, equal⟩
    rcases role with parameter | argument | result | name
    all_goals dsimp only [sourceWiring, temporary, outputTape, inputTape, scratchTape] at equal
    all_goals cases equal
  have normalized := UnaryHeader.runs_at headerWiring width readonly rfl
    (MvPolynomial.eval sizes capacityPolynomial) (compute sizes ⟨arguments, valid⟩) capacityFits middle properHeader (by
      change Region _ 0 (middle (outputTape computation))
      rw [outputBlank]
      exact CallingConvention.blank_region _)
  have combined := sourceLifted.sequence normalize (.inl ())
    (by intro symbols; simp [MultiTape.wire, sourceCertificate.2.2.1]) normalized
  refine ⟨sourceTicks + (2 * MvPolynomial.eval sizes capacityPolynomial + 2) + 1, _, ?_, combined, ?_⟩
  · simp only [map_add, map_mul, map_ofNat]
    omega
  · exact Function.update_self _ _ _

end Polytime2.Computation.Realizable.Internal
