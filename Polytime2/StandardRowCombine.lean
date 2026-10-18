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

import Polytime2.FiniteTable

/-! # Finite row-entry operations as a family-table specialization

Three immutable scalar arguments produce two separate scalar results. The
controller, codecs, and preservation proof come from the generic finite table.
-/

namespace Polytime2.StandardRowCombine

open MultiTape CallingConvention

abbrev Alphabet := CallingConvention.Alphabet (Fin 3 ⊕ Fin 2)
abbrev State (width : ℕ) := FiniteTable.State (fun _ : Fin 3 => width) (fun _ : Fin 2 => width)

def entry {width : ℕ} : State width := FiniteTable.entry _ _
def exit {width : ℕ} : State width := none
abbrev readOnly : Fin 3 ⊕ Fin 2 → Bool := FiniteTable.readOnly
abbrev sizeTapes : Empty ↪ (Fin 3 ⊕ Fin 2) := FiniteTable.sizeTapes
abbrev outputTapes : Fin 2 ↪ (Fin 3 ⊕ Fin 2) := FiniteTable.outputTapes

-- carrierLevel: scalar carriers fixed by the specialization.
universe carrierLevel

abbrev domains (domain : EncodedDomain.{0, carrierLevel} Empty) :=
  FiniteTable.domains (fun _ : Fin 3 => domain) (fun _ : Fin 2 => domain)

noncomputable def algorithm (domain : EncodedDomain.{0, carrierLevel} Empty)
    (operation : ∀ sizes, domain.Carrier sizes → domain.Carrier sizes → domain.Carrier sizes →
      domain.Carrier sizes × domain.Carrier sizes) : Machine Alphabet (State (domain.width Empty.elim)) :=
  FiniteTable.algorithm (fun _ : Fin 3 => domain) (fun _ : Fin 2 => domain)
    (fun sizes values name => if name = 0 then (operation sizes (values 0) (values 1) (values 2)).1
      else (operation sizes (values 0) (values 1) (values 2)).2)

/-- Both results are overwritten from arbitrary old contents, including at width zero. -/
theorem contract (domain : EncodedDomain.{0, carrierLevel} Empty)
    (operation : ∀ sizes, domain.Carrier sizes → domain.Carrier sizes → domain.Carrier sizes →
      domain.Carrier sizes × domain.Carrier sizes) :
    CallingConvention.Realizes (domains domain) readOnly sizeTapes outputTapes (algorithm domain operation) entry exit
      (fun _ _ => True)
      (fun sizes input output => (output 0, output 1) =
        operation sizes (input ⟨.inl 0, rfl⟩) (input ⟨.inl 1, rfl⟩) (input ⟨.inl 2, rfl⟩)) := by
  apply (FiniteTable.contract (fun _ : Fin 3 => domain) (fun _ : Fin 2 => domain) _).postcondition
  intro sizes input output correct
  exact Prod.ext (congrFun correct 0) (congrFun correct 1)

end Polytime2.StandardRowCombine
