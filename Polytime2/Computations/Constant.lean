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

private def noArgumentsLayout (Parameter : Type) :
    Parameter ⊕ Unit ≃ Parameter ⊕ (Empty ⊕ (Unit ⊕ Empty)) :=
  Equiv.sumCongr (Equiv.refl Parameter)
    (((Equiv.emptySum Empty (Unit ⊕ Empty)).trans (Equiv.sumEmpty Unit Empty)).symm)

end Realizable.Internal

open Realizable.Internal in
/-- Encoded constant bits are compiled into finite control. Their encoding need
not be an executable routine, since specialization fixes it before runtime. -/
theorem constant_realizable (domain : EncodedDomain.{0, carrierLevel} Empty)
    (value : ∀ sizes, domain.Carrier sizes) : (constant domain value).Realizable := by
  let computation := constant domain value
  let scratchDomains : Empty → EncodedDomain.{0, carrierLevel} Empty := Empty.elim
  let layout : Unit ≃ TapeName computation Empty :=
    (Equiv.emptySum Empty Unit).symm.trans (noArgumentsLayout Empty)
  let bits := List.ofFn (fun index : Fin (domain.width Empty.elim) =>
    (domain.encode Empty.elim (value Empty.elim)).getLsbD index.val)
  let values : ∀ name sizes, (domains computation scratchDomains (layout name)).Carrier sizes ≃
      domain.Carrier sizes := fun _ _ => Equiv.refl _
  refine ofLayout computation scratchDomains (fun _ : Unit => domain) (fun _ => false)
    StandardConstant.sizeTapes (Function.Embedding.refl Unit)
    (StandardConstant.machine bits) (false, Fin.last bits.length) (true, 0) _ _
    (StandardConstant.contract domain value) layout.toEmbedding values
    (by intro name sizes; rfl) (by intro name sizes element; rfl)
    (by intro name; rfl) (by intro parameter; cases parameter) () rfl
    (by intro sizes input valid; trivial) ?_
  intro sizes input valid output correct
  exact congrArg (encoded domain sizes) correct

open Realizable.Internal in
theorem counterZero_realizable {Parameter : Type} [Fintype Parameter] (capacity : Parameter) :
    (counterZero capacity).Realizable := by
  classical
  let computation := counterZero capacity
  let scratchDomains : Empty → EncodedDomain Parameter := Empty.elim
  let layout : Parameter ⊕ Unit ≃ TapeName computation Empty := noArgumentsLayout Parameter
  let values : ∀ name sizes, (domains computation scratchDomains (layout name)).Carrier sizes ≃
      (StandardCounterZero.domains capacity name).Carrier sizes := by
    intro name sizes
    cases name <;> exact Equiv.refl _
  refine ofLayout computation scratchDomains (StandardCounterZero.domains capacity)
    StandardCounterZero.readOnly StandardCounterZero.sizeTapes StandardCounterZero.outputTapes
    (StandardCounterZero.algorithm capacity) (.inl ()) (.inr ((), true)) _ _
    (StandardCounterZero.contract capacity) layout.toEmbedding values
    (by intro name sizes; cases name <;> rfl)
    (by intro name sizes element; cases name <;> rfl)
    (by intro name; cases name <;> rfl) (by intro parameter; rfl) () rfl
    (by intro sizes input valid; trivial) ?_
  intro sizes input valid output correct
  apply congrArg (encoded (EncodedDomain.binaryNaturals capacity) sizes)
  apply Fin.ext
  exact correct

end Polytime2.Computation
