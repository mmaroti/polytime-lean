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
import Polytime2.StandardConstant
import Polytime2.StandardCounterZero

/-! # Nullary computations for constants and counter initialization -/

namespace Polytime2.Computation

open MultiTape CallingConvention Realizable

-- carrierLevel: specialization-fixed mathematical constant values.
universe carrierLevel

/-- A specialization-fixed constant has no mathematical or runtime size inputs. -/
def constant (domain : EncodedDomain.{0, carrierLevel} Empty)
    (value : ∀ sizes, domain.Carrier sizes) : Computation Empty Empty where
  inputDomains := Empty.elim
  outputDomain := domain
  precondition _ _ := True
  compute sizes _ := value sizes

/-- Counter initialization reads its unary capacity and needs no value input. -/
noncomputable def counterZero {Parameter : Type} [Fintype Parameter] (capacity : Parameter) : Computation Parameter Empty where
  inputDomains := Empty.elim
  outputDomain := EncodedDomain.binaryNaturals capacity
  precondition _ _ := True
  compute sizes _ := (0 : Fin (2 ^ sizes capacity))

namespace Realizable.Internal

private def zeroPlacement (Parameter : Type) : PublicTape Parameter Empty ↪ Parameter ⊕ Unit :=
  (Function.Embedding.refl Parameter).sumMap (Equiv.emptySum Empty Unit).toEmbedding

private def constantPlacement : PublicTape Empty Empty ↪ Unit :=
  ⟨(fun _ => ()), by intro first second equal; fin_cases first; fin_cases second; rfl⟩

end Realizable.Internal

open Realizable.Internal in
/-- Encoded constant bits are compiled into finite control. Their encoding need
not be an executable routine, since specialization fixes it before runtime. -/
theorem constant_realizable (domain : EncodedDomain.{0, carrierLevel} Empty)
    (value : ∀ sizes, domain.Carrier sizes) : (constant domain value).Realizable := by
  let bits := List.ofFn (fun index : Fin (domain.width Empty.elim) =>
    (domain.encode Empty.elim (value Empty.elim)).getLsbD index.val)
  refine ofNamedLayout (constant domain value) (fun _ : Unit => domain) (fun _ => false)
    StandardConstant.sizeTapes (Function.Embedding.refl Unit)
    (StandardConstant.machine bits) (false, Fin.last bits.length) (true, 0) _ _
    (StandardConstant.contract domain value) constantPlacement
    (by intro role; fin_cases role; rfl) (by intro role; fin_cases role; rfl)
    (by intro name outside; rfl) (by intro empty; cases empty) () rfl
    (by intro sizes input valid; trivial) ?_
  intro sizes input valid output correct
  exact congrArg (encoded domain sizes) correct

open Realizable.Internal in
theorem counterZero_realizable {Parameter : Type} [Fintype Parameter] (capacity : Parameter) :
    (counterZero capacity).Realizable := by
  classical
  refine ofNamedLayout (counterZero capacity) (StandardCounterZero.domains capacity)
    StandardCounterZero.readOnly StandardCounterZero.sizeTapes StandardCounterZero.outputTapes
    (StandardCounterZero.algorithm capacity) (.inl ()) (.inr ((), true)) _ _
    (StandardCounterZero.contract capacity) (zeroPlacement Parameter)
    (by rintro (parameter | empty | result) <;> first | rfl | cases empty)
    (by rintro (parameter | empty | result) <;> first | rfl | cases empty)
    (by intro name outside; cases name with
      | inl parameter => exact False.elim (outside ⟨.inl parameter, rfl⟩)
      | inr result => rfl)
    (by intro parameter; rfl) () rfl (by intro sizes input valid; trivial) ?_
  intro sizes input valid output correct
  apply congrArg (encoded (EncodedDomain.binaryNaturals capacity) sizes)
  apply Fin.ext
  exact correct

end Polytime2.Computation
