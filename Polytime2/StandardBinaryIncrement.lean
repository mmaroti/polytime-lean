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

end Polytime2.StandardBinaryIncrement
