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
abbrev binaryNaturals : EncodedDomain Unit := EncodedDomain.binaryNaturals ()

#guard binaryNaturals.width (fun _ => 7) = 7
example : binaryNaturals.decode (fun _ => 0) 0#0 = some (0 : Fin 1) := rfl
example : binaryNaturals.encode (fun _ => 3) (5 : Fin 8) = 5#3 := rfl

/-- Clearing a runtime-width counter preserves its input and writes zero to
an arbitrary output region, with a separate immutable unary size argument. -/
example : CallingConvention.Realizes (StandardBinaryScan.domains binaryNaturals binaryNaturals)
    StandardTerminatedCopy.readOnly StandardTerminatedCopy.sizeTapes
    (StandardBinaryScan.algorithm BinaryScan.clear) (.inl (.inl ())) (.inr ())
    (fun _ _ => True) (fun assignment _ output =>
      output ⟨.inr true, rfl⟩ = (⟨0, by positivity⟩ : Fin (2 ^ assignment ()))) := by
  apply StandardBinaryScan.contract BinaryScan.clear () binaryNaturals binaryNaturals
    (fun _ => rfl) (fun _ _ => True)
    (fun assignment _ => (⟨0, by positivity⟩ : Fin (2 ^ assignment ())))
  intro assignment value valid
  simp [binaryNaturals, EncodedDomain.binaryNaturals, BinaryScan.clear_run]

-- Empty and singleton carriers share zero-bit width but have different decoders.
#guard (EncodedDomain.fixed (Parameter := Unit) (Equiv.refl (Fin 0))).decode
  (fun _ => 0) 0#0 = none
example : (EncodedDomain.fixed (Parameter := Unit) (Equiv.refl (Fin 1))).decode
    (fun _ => 0) 0#0 = some (0 : Fin 1) := rfl

-- Unused binary labels are rejected rather than assigned an arbitrary element.
#guard (EncodedDomain.fixed (Parameter := Unit) (Equiv.refl (Fin 3))).decode
  (fun _ => 0) 3#2 = none
example : (EncodedDomain.fixed (Parameter := Unit) (Equiv.refl (Fin 3))).decode
    (fun _ => 0) 2#2 = some (2 : Fin 3) := rfl

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
