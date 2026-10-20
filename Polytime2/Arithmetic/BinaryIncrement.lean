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

import Polytime2.Arithmetic.BinaryScan
import Polytime2.Machine.CallingConventionRegions

/-! # Fixed-capacity binary counter increment

The source counter is immutable and the separate result is fully overwritten.
Overflow is modular; callers needing ordinary addition prove capacity bounds.
-/

namespace Polytime2.StandardBinaryIncrement

open CallingConvention

-- parameterLevel: immutable unary size names, including the counter capacity.
universe parameterLevel
variable {Parameter : Type parameterLevel} [Fintype Parameter]

def next (capacity : Parameter) (assignment : Parameter → ℕ)
    (value : Fin (2 ^ assignment capacity)) : Fin (2 ^ assignment capacity) :=
  ⟨(value.val + 1) % 2 ^ assignment capacity, Nat.mod_lt _ (by positivity)⟩

/-- The counter width is a unary size parameter, so it never grows in a loop. -/
theorem contract (capacity : Parameter) :
    let domain := EncodedDomain.binaryNaturals capacity
    CallingConvention.Realizes (StandardBinaryScan.domains domain domain)
      StandardTerminatedCopy.readOnly StandardTerminatedCopy.sizeTapes StandardTerminatedCopy.outputTapes
      (StandardBinaryScan.algorithm BinaryScan.increment)
      (.inl (.inl true)) (.inr ()) (fun _ _ => True)
      (fun assignment input output => output () =
        next capacity assignment (input ⟨.inr false, rfl⟩)) := by
  apply StandardBinaryScan.contract BinaryScan.increment true
    (EncodedDomain.binaryNaturals capacity) (EncodedDomain.binaryNaturals capacity)
    (by intro assignment; rfl) (fun _ _ => True) (next capacity)
  intro assignment value valid
  let bits := List.ofFn (fun index : Fin (assignment capacity) => (BitVec.ofFin value).getLsbD index.val)
  simp only [EncodedDomain.binaryNaturals, EncodedDomain.ofCodec]
  change (BinaryScan.run _ _ (EncodedDomain.ArrayEncoding.bits _)).2 =
    EncodedDomain.ArrayEncoding.bits _
  rw [EncodedDomain.ArrayEncoding.bits_cast, EncodedDomain.ArrayEncoding.bits_cast]
  change (BinaryScan.run BinaryScan.increment true bits).2 =
    List.ofFn (fun index : Fin (assignment capacity) =>
      (BitVec.ofFin (next capacity assignment value)).getLsbD index.val)
  have length : (BinaryScan.run BinaryScan.increment true bits).2.length = assignment capacity := by
    simp [bits]
  have resultValue : Binary.value (BinaryScan.run BinaryScan.increment true bits).2 =
      (next capacity assignment value).val := by
    rw [BinaryScan.increment_value]
    simp only [bits, Binary.value_bits, List.length_ofFn, next]
    rfl
  have encoded := Binary.bits_value (BinaryScan.run BinaryScan.increment true bits).2 length
  rw [resultValue] at encoded
  simpa only [← BitVec.ofNat_finVal] using encoded.symm

/-- Increment in any caller workspace. The only writable local tape is the
separate result, so every other caller tape is preserved. -/
theorem wired_runs {TapeName : Type} [Fintype TapeName] (capacity : Parameter)
    (width : (Parameter → ℕ) → TapeName → ℕ) (readOnly : TapeName → Bool)
    (wiring : Parameter ⊕ Bool ↪ TapeName)
    (widths : ∀ sizes name, width sizes (wiring name) =
      (StandardBinaryScan.domains (EncodedDomain.binaryNaturals capacity)
        (EncodedDomain.binaryNaturals capacity) name).width sizes)
    (immutable : ∀ name, readOnly (wiring name) = true → StandardTerminatedCopy.readOnly name = true) :
    ∃ bound : MvPolynomial Parameter ℕ, ∀ (sizes : Parameter → ℕ)
      (initial : MultiTape.Tapes (Alphabet TapeName)) (value : Fin (2 ^ sizes capacity)),
      initial (wiring (.inr false)) = encoded (EncodedDomain.binaryNaturals capacity) sizes value →
      (∀ parameter, initial (wiring (.inl parameter)) = unary (sizes parameter)) →
      Region (sizes capacity) 0 (initial (wiring (.inr true))) →
      ∃ ticks final, ticks ≤ MvPolynomial.eval sizes bound ∧
        Runs (width sizes) readOnly (MultiTape.wire wiring (StandardBinaryScan.algorithm BinaryScan.increment)) ticks
          (.inl (.inl true)) (fun _ => 0) initial (.inr ()) (fun _ => 0) final ∧
        final (wiring (.inr true)) = encoded (EncodedDomain.binaryNaturals capacity) sizes (next capacity sizes value) ∧
        (∀ name, name ≠ wiring (.inr true) → final name = initial name) := by
  obtain ⟨bound, execute⟩ := (contract capacity).wired_runs wiring
  refine ⟨bound, ?_⟩
  intro sizes initial value valueEq headers region
  let input : Inputs (StandardBinaryScan.domains (EncodedDomain.binaryNaturals capacity)
      (EncodedDomain.binaryNaturals capacity)) StandardTerminatedCopy.readOnly sizes := fun name => by
    rcases name with ⟨name, readonly⟩
    cases name with
    | inl parameter => exact PUnit.unit
    | inr output => cases output with
      | false => exact value
      | true => contradiction
  obtain ⟨ticks, output, final, cost, trace, correct, canonical, outside, unchanged⟩ :=
    execute sizes input (width sizes) readOnly initial (widths sizes) immutable trivial
      (by
        intro name readonly
        cases name with
        | inl parameter =>
          change initial (wiring (.inl parameter)) = encoded (EncodedDomain.unary parameter) sizes PUnit.unit
          rw [encoded_unary]
          exact headers parameter
        | inr output => cases output with
          | false => exact valueEq
          | true => contradiction)
      (by
        intro name writable
        cases name with
        | inl parameter => contradiction
        | inr output => cases output with
          | false => contradiction
          | true =>
            rw [widths]
            change Region ((EncodedDomain.binaryNaturals capacity).width sizes) 0 _
            simpa only [EncodedDomain.binaryNaturals_width] using region)
      headers
  refine ⟨ticks, final, cost, trace, ?_, ?_⟩
  · have result := canonical ()
    change output () = next capacity sizes value at correct
    rw [correct] at result
    exact result
  · intro name different
    apply preserved_of_wiring wiring StandardTerminatedCopy.readOnly initial final outside unchanged
    intro localName equal
    cases localName with
    | inl parameter => rfl
    | inr output => cases output with
      | false => rfl
      | true => exact False.elim (different equal.symm)

end Polytime2.StandardBinaryIncrement
