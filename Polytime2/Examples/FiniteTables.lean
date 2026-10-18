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

import Polytime2.Computations.FiniteTable

/-! # Finite tables through mathematical specifications -/

namespace Polytime2.Examples.FiniteTables

open Polytime2.Computation

private noncomputable def threeElements : EncodedDomain Empty := EncodedDomain.fixed (Equiv.refl (Fin 3))

noncomputable def addition : Polytime2.Computation Empty Bool :=
  finiteTable threeElements threeElements threeElements
    (fun _ (first : Fin 3) (second : Fin 3) => first + second)

example : addition.Realizable := finiteTable_realizable threeElements threeElements threeElements _
example : (addition.compute Empty.elim
    ⟨(fun | false => (1 : Fin 3) | true => (2 : Fin 3)), True.intro⟩ : Fin 3) = (0 : Fin 3) := rfl

-- Singleton domains have zero-bit arguments and results.
example : (finiteTable (EncodedDomain.fixed (Equiv.refl (Fin 1)))
    (EncodedDomain.fixed (Equiv.refl (Fin 1))) (EncodedDomain.fixed (Equiv.refl (Fin 1)))
    (fun _ first _ => first)).Realizable := finiteTable_realizable _ _ _ _

/-- Four arguments include different widths and a zero-bit singleton. -/
private noncomputable def mixedInputs : Fin 4 → EncodedDomain Empty
  | 0 => threeElements
  | 1 => EncodedDomain.booleans
  | 2 => threeElements
  | 3 => EncodedDomain.fixed (Equiv.refl (Fin 1))

private noncomputable def mixedOutputs : Fin 2 → EncodedDomain Empty
  | 0 => EncodedDomain.booleans
  | 1 => threeElements

private noncomputable def mixedOperation (sizes : Empty → ℕ)
    (values : ∀ name, (mixedInputs name).Carrier sizes) : ∀ name, (mixedOutputs name).Carrier sizes
  | 0 => values 1
  | 1 => (show Fin 3 from values 0) + (show Fin 3 from values 2)

example : CallingConvention.Realizes (FiniteTable.domains mixedInputs mixedOutputs)
    FiniteTable.readOnly FiniteTable.sizeTapes FiniteTable.outputTapes
    (FiniteTable.algorithm mixedInputs mixedOutputs mixedOperation) (FiniteTable.entry _ _) none
    (fun _ _ => True)
    (fun sizes input output => output = mixedOperation sizes (fun name => input ⟨.inl name, rfl⟩)) :=
  FiniteTable.contract mixedInputs mixedOutputs mixedOperation

-- A nullary operation has no input tapes and writes its result directly.
example : (finiteOperation (fun name : Empty => nomatch name) EncodedDomain.booleans
    (fun _ _ => true)).Realizable := finiteOperation_realizable _ _ _

end Polytime2.Examples.FiniteTables
