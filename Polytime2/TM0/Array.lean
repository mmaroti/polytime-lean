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

import Polytime2.Arrays.Operations
import Polytime2.TM0.Computation

/-! # Polynomial TM0 realization of array access

Delimited public inputs contain only the unary sizes and encoded arguments.
Element widths and all private storage are prepared internally.
-/

namespace Polytime2.Array

variable {Parameter : Type} [Fintype Parameter]

/-- Lookup with polynomial element width transfers to the public TM0 format. -/
theorem lookup_realizes_tm0 (element : EncodedDomain Parameter)
    (indexCapacity : Parameter) (length : MvPolynomial Parameter ℕ) :
    (Computation.arrayLookup element indexCapacity length).TM0Realizable :=
  (Computation.arrayLookup_realizable element indexCapacity length).tm0

/-- Update preserves its arguments and exports only the separate result array. -/
theorem update_realizes_tm0 (element : EncodedDomain Parameter)
    (indexCapacity : Parameter) (length : MvPolynomial Parameter ℕ) :
    (Computation.arrayUpdate element indexCapacity length).TM0Realizable :=
  (Computation.arrayUpdate_realizable element indexCapacity length).tm0

end Polytime2.Array
