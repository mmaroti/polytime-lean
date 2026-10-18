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

/-! # A unary finite predicate with one argument and one result tape -/

namespace Polytime2.StandardFinitePredicate

open MultiTape CallingConvention

abbrev Alphabet := CallingConvention.Alphabet (Fin 1 ⊕ Fin 1)
noncomputable abbrev State (width : ℕ) :=
  FiniteTable.State (fun _ : Fin 1 => width) (fun _ : Fin 1 => EncodedDomain.booleans.width Empty.elim)
abbrev readOnly : Fin 1 ⊕ Fin 1 → Bool := FiniteTable.readOnly
abbrev sizeTapes : Empty ↪ (Fin 1 ⊕ Fin 1) := FiniteTable.sizeTapes
abbrev outputTapes : Fin 1 ↪ (Fin 1 ⊕ Fin 1) := FiniteTable.outputTapes

noncomputable def entry {width : ℕ} : State width := FiniteTable.entry _ _
noncomputable def exit {width : ℕ} : State width := none

noncomputable abbrev domains (domain : EncodedDomain.{0, 0} Empty) :=
  FiniteTable.domains (fun _ : Fin 1 => domain) (fun _ : Fin 1 => EncodedDomain.booleans)

noncomputable def machine (domain : EncodedDomain.{0, 0} Empty)
    (predicate : ∀ sizes, domain.Carrier sizes → Bool) : Machine Alphabet (State (domain.width Empty.elim)) :=
  FiniteTable.algorithm (fun _ : Fin 1 => domain) (fun _ : Fin 1 => EncodedDomain.booleans)
    (fun sizes values _ => predicate sizes (values 0))

/-- The predicate needs no dummy argument or private singleton tape. -/
theorem contract (domain : EncodedDomain.{0, 0} Empty)
    (predicate : ∀ sizes, domain.Carrier sizes → Bool) :
    CallingConvention.Realizes (domains domain) readOnly sizeTapes outputTapes (machine domain predicate) entry exit
      (fun _ _ => True)
      (fun sizes input output => output 0 = predicate sizes (input ⟨.inl 0, rfl⟩)) := by
  apply (FiniteTable.contract (fun _ : Fin 1 => domain) (fun _ : Fin 1 => EncodedDomain.booleans) _).postcondition
  intro sizes input output correct
  exact congrFun correct 0

end Polytime2.StandardFinitePredicate
