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

import Polytime2.Computation.Specification
import Polytime2.Arithmetic.CounterOperations

/-! # Certifying a mathematical answer behind a stable boundary

The copy machine certifies the identity specification. Clients use the explicit
mathematical equation; ordinary conversion does not inspect the implementation.
-/

namespace Polytime2.Examples.Specification

open Polytime2.Computation

variable {Parameter : Type} [Fintype Parameter]

noncomputable def identity (domain : EncodedDomain Parameter) :
    Computation Parameter Unit :=
  specification (fun _ => domain) domain (fun _ _ => True)
    (fun _ arguments => arguments.val ())

theorem identity_realizable (domain : EncodedDomain Parameter) :
    (identity domain).Realizable := by
  apply (copy_realizable domain).specification
  intro sizes arguments valid
  rfl

example (domain : EncodedDomain Parameter) (sizes : Parameter → ℕ)
    (value : domain.Carrier sizes) :
    (identity domain).compute sizes ⟨fun _ => value, trivial⟩ = value := by
  fail_if_success rfl
  exact specification_compute _ _ _ _ _ _

end Polytime2.Examples.Specification
