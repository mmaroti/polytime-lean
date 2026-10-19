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

import Polytime2.TM0.Computation
import Polytime2.Primitives.ConstantOperations
import Polytime2.Arithmetic.CounterOperations
import Polytime2.Arithmetic.GcdOperations
import Polytime2.GaussJordan.Operations

/-! # Complete single-tape exports through the public mathematical interface

Examples cover no inputs or sizes, runtime-width data including width zero,
multiple arguments, and rectangular elimination with two public dimensions.
No example inspects a realization's controller, scratch, or runtime witness.
-/

namespace Polytime2.Examples.TM0

open Polytime2.Computation

-- Separators preserve empty blocks, and binary zero is ordinary input data.
#guard DelimitedInput.serialize id [[], [false, true], []] =
  [.inr 1, .inr 0, .inr 0, .inl false, .inl true, .inr 0, .inr 0, .inr 2]

/-- A constant computation needs neither a size block nor an argument block. -/
example : (constant (EncodedDomain.fixed (Equiv.refl (Fin 1))) (fun _ => (0 : Fin 1))).TM0Realizable :=
  (constant_realizable (EncodedDomain.fixed (Equiv.refl (Fin 1))) (fun _ => (0 : Fin 1))).tm0

/-- A zero-capacity argument and result are both empty binary words. -/
example : (copy (EncodedDomain.binaryNaturals ())).TM0Realizable :=
  (copy_realizable (EncodedDomain.binaryNaturals ())).tm0

/-- Both gcd operands are supplied as separate delimited argument blocks. -/
example : gcd.TM0Realizable := gcd_realizable.tm0

/-- The external theorem needs only the fixed field and its two dimensions. -/
example {Scalar : Type} [Field Scalar] [DecidableEq Scalar] {cardinality : ℕ}
    (enumeration : Scalar ≃ Fin cardinality) : (gaussJordan enumeration).TM0Realizable :=
  (gaussJordan_realizable enumeration).tm0

end Polytime2.Examples.TM0
