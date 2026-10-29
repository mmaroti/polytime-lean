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

import Polytime2.Computation.Layout
import Polytime2.Computation.Constant
import Polytime2.Computation.Reindex
import Polytime2.Primitives.FiniteTable

/-! # Specialization-fixed finite operations on mathematical arguments -/

namespace Polytime2.Computation

open MultiTape CallingConvention Realizable

-- carrierLevel: mathematical carriers of the fixed domains.
universe carrierLevel
variable {Argument : Type} [Fintype Argument]

/-- Arbitrarily many separate fixed encoded arguments compute one result. -/
def finiteOperation (inputs : Argument → EncodedDomain.{0, carrierLevel} Empty)
    (output : EncodedDomain.{0, carrierLevel} Empty)
    (operation : ((name : Argument) → (inputs name).Carrier Empty.elim) → output.Carrier Empty.elim) :
    Computation Empty Argument where
  inputDomains := inputs
  outputDomain := output
  precondition _ _ := True
  compute sizes arguments := by
    cases Subsingleton.elim sizes Empty.elim
    exact operation arguments.val

namespace Realizable.Internal

private noncomputable def finitePlacement : PublicTape Empty Argument ↪ (Fin (Fintype.card Argument) ⊕ Fin 1) :=
  ⟨(fun role => match role with
    | .inl empty => nomatch empty
    | .inr (.inl name) => .inl (Fintype.equivFin Argument name)
    | .inr (.inr _) => .inr 0), by
    intro first second equal
    rcases first with empty | first | first
    · cases empty
    · rcases second with empty | second | second
      · cases empty
      · exact congrArg (fun name => Sum.inr (Sum.inl name))
          ((Fintype.equivFin Argument).injective (Sum.inl.inj equal))
      · cases equal
    · rcases second with empty | second | second
      · cases empty
      · cases equal
      · cases first; cases second; rfl⟩

end Realizable.Internal

open Realizable.Internal in
/-- Every specialization-fixed family operation uses the same finite table. -/
theorem finiteOperation_realizable (inputs : Argument → EncodedDomain.{0, carrierLevel} Empty)
    (output : EncodedDomain.{0, carrierLevel} Empty)
    (operation : ((name : Argument) → (inputs name).Carrier Empty.elim) → output.Carrier Empty.elim) :
    (finiteOperation inputs output operation).Realizable := by
  classical
  let sourceInputs := fun name => inputs ((Fintype.equivFin Argument).symm name)
  let sourceOutputs := fun _ : Fin 1 => output
  let sourceOperation := fun sizes (values : ∀ name, (sourceInputs name).Carrier sizes) (_ : Fin 1) =>
    (finiteOperation inputs output operation).compute sizes
      ⟨(fun name => by simpa [sourceInputs, finiteOperation] using values (Fintype.equivFin Argument name)), trivial⟩
  refine ofNamedLayout (finiteOperation inputs output operation)
    (FiniteTable.domains sourceInputs sourceOutputs) FiniteTable.readOnly
    FiniteTable.sizeTapes FiniteTable.outputTapes
    (FiniteTable.algorithm sourceInputs sourceOutputs sourceOperation) (FiniteTable.entry _ _) none _ _
    (FiniteTable.contract sourceInputs sourceOutputs sourceOperation) finitePlacement
    (by
      intro role
      rcases role with empty | name | result
      · cases empty
      · change inputs name = inputs ((Fintype.equivFin Argument).symm (Fintype.equivFin Argument name))
        rw [Equiv.symm_apply_apply]
      · cases result; rfl)
    (by intro role; rcases role with empty | name | result; cases empty; rfl; rfl)
    (by
      intro name outside
      cases name with
      | inl name => exact False.elim (outside ⟨.inr (.inl ((Fintype.equivFin Argument).symm name)), by
          change Sum.inl (Fintype.equivFin Argument ((Fintype.equivFin Argument).symm name)) = Sum.inl name
          rw [Equiv.apply_symm_apply]⟩)
      | inr name => rfl)
    (by intro empty; cases empty) 0 rfl (by intro sizes input valid; trivial) ?_
  intro sizes input valid result correct
  have selected := congrFun correct 0
  exact congrArg (encoded output sizes) selected

/-- False and true name the two arguments, whose carrier types may differ. -/
def finiteTable (firstDomain secondDomain outputDomain : EncodedDomain.{0, carrierLevel} Empty)
    (operation : firstDomain.Carrier Empty.elim → secondDomain.Carrier Empty.elim →
      outputDomain.Carrier Empty.elim) : Computation Empty Bool :=
  finiteOperation (fun | false => firstDomain | true => secondDomain) outputDomain
    (fun values => operation (values false) (values true))

theorem finiteTable_realizable
    (firstDomain secondDomain outputDomain : EncodedDomain.{0, carrierLevel} Empty)
    (operation : firstDomain.Carrier Empty.elim → secondDomain.Carrier Empty.elim →
      outputDomain.Carrier Empty.elim) : (finiteTable firstDomain secondDomain outputDomain operation).Realizable :=
  finiteOperation_realizable _ _ _

/-- A specialization-fixed predicate with an ordinary Boolean result at any
runtime size assignment. The caller supplies only its mathematical function. -/
noncomputable def finitePredicate {Parameter : Type} [Fintype Parameter]
    (domain : EncodedDomain.{0, 0} Empty) (predicate : domain.Carrier Empty.elim → Bool) :
    Computation Parameter Unit :=
  unaryMap domain.constant EncodedDomain.booleans (fun _ _ => True) (fun _ value => predicate value.val)

set_option backward.isDefEq.respectTransparency false in
theorem finitePredicate_realizable {Parameter : Type} [Fintype Parameter]
    (domain : EncodedDomain.{0, 0} Empty) (predicate : domain.Carrier Empty.elim → Bool) :
    (finitePredicate (Parameter := Parameter) domain predicate).Realizable := by
  have raw := (finiteOperation_realizable (fun _ : Unit => domain) EncodedDomain.booleans
    (fun values => predicate (values ()))).withConstantSizes (Parameter := Parameter)
  exact raw.reinterpretOutput EncodedDomain.booleans (fun _ value => value)
    (by intros; simp [withConstantSizes, finiteOperation, EncodedDomain.booleans, EncodedDomain.width])
    (by intros; simp [withConstantSizes, finiteOperation, EncodedDomain.constant_encode_bits,
      EncodedDomain.booleans, EncodedDomain.fixed_encode_bits])

/-- Three separate arguments from one fixed domain compute one mathematical result. -/
def finiteTernary (domain : EncodedDomain.{0, carrierLevel} Empty)
    (operation : domain.Carrier Empty.elim → domain.Carrier Empty.elim →
      domain.Carrier Empty.elim → domain.Carrier Empty.elim) : Computation Empty (Fin 3) :=
  finiteOperation (fun _ => domain) domain (fun values => operation (values 0) (values 1) (values 2))

theorem finiteTernary_realizable (domain : EncodedDomain.{0, carrierLevel} Empty)
    (operation : domain.Carrier Empty.elim → domain.Carrier Empty.elim →
      domain.Carrier Empty.elim → domain.Carrier Empty.elim) :
    (finiteTernary domain operation).Realizable := finiteOperation_realizable _ _ _

end Polytime2.Computation
