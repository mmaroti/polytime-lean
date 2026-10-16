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
import Polytime2.BinaryEncoding
import Mathlib.Data.Fintype.EquivFin

/-! # Encoded domains at scalar machine boundaries

Specializations can supply arbitrary finite tagged carriers. Size-dependent
binary natural domains need no domain-expression syntax or width evaluator.
-/

namespace Polytime2.Examples.EncodedDomains

-- parameterLevel: size names for a specialized domain.
universe parameterLevel
variable {Parameter : Type parameterLevel} [Fintype Parameter]

/-- The polynomial bounds digit capacity rather than numeric magnitude.
Even zero digits encode exactly one natural number. -/
noncomputable abbrev binaryNaturals : EncodedDomain Unit := EncodedDomain.binaryNaturals ()

example : binaryNaturals.width (fun _ => 7) = 7 := by
  simp [binaryNaturals, EncodedDomain.binaryNaturals, EncodedDomain.ofCodec]

example : binaryNaturals.decode (fun _ => 0) 0 = some (0 : Fin 1) := by
  simp [binaryNaturals, EncodedDomain.binaryNaturals, EncodedDomain.ofCodec, BitVec.cast]

example : EncodedDomain.ArrayEncoding.bits (binaryNaturals.encode (fun _ => 3) (5 : Fin 8)) =
    EncodedDomain.ArrayEncoding.bits (5#3) := by
  simp only [binaryNaturals, EncodedDomain.binaryNaturals, EncodedDomain.ofCodec,
    EncodedDomain.ArrayEncoding.bits_cast]
  rfl

-- Empty and singleton carriers share zero-bit width but have different decoders.
example : (EncodedDomain.fixed (Parameter := Unit) (Equiv.refl (Fin 0))).decode
    (fun _ => 0) 0 = none := by
  simp [EncodedDomain.fixed, EncodedDomain.ofCodec, BitVec.cast]

example : (EncodedDomain.fixed (Parameter := Unit) (Equiv.refl (Fin 1))).decode
    (fun _ => 0) 0 =
      some (0 : Fin 1) := by
  simp [EncodedDomain.fixed, EncodedDomain.ofCodec, BitVec.cast]

-- Unused binary labels are rejected rather than assigned an arbitrary element.
example : (EncodedDomain.fixed (Parameter := Unit) (Equiv.refl (Fin 3))).decode
    (fun _ => 0) ((3#2).cast (by
      simp only [EncodedDomain.fixed, EncodedDomain.ofCodec, MvPolynomial.eval_C]
      decide)) = none := by
  simp [EncodedDomain.fixed, EncodedDomain.ofCodec, BitVec.cast]

example : (EncodedDomain.fixed (Parameter := Unit) (Equiv.refl (Fin 3))).decode
    (fun _ => 0) ((2#2).cast (by
      simp only [EncodedDomain.fixed, EncodedDomain.ofCodec, MvPolynomial.eval_C]
      decide)) =
      some (2 : Fin 3) := by
  simp [EncodedDomain.fixed, EncodedDomain.ofCodec, BitVec.cast]

/-- A family of finite carriers is specialization data. The tagged union's
chosen enumeration is fixed independently of the number of coordinates. -/
noncomputable def taggedDomain {SortName : Type} [Fintype SortName]
    (Carrier : SortName → Type) [∀ sort, Fintype (Carrier sort)] : EncodedDomain Parameter :=
  EncodedDomain.fixed (Fintype.equivFin (Σ sort, Carrier sort))

example {SortName : Type} [Fintype SortName] (Carrier : SortName → Type)
    [∀ sort, Fintype (Carrier sort)] (assignment : Parameter → ℕ)
    (value : Σ sort, Carrier sort) :
    (taggedDomain (Parameter := Parameter) Carrier).decode assignment
      ((taggedDomain (Parameter := Parameter) Carrier).encode assignment value) =
        some value := by
  exact (taggedDomain (Parameter := Parameter) Carrier).decode_encode assignment value

end Polytime2.Examples.EncodedDomains
