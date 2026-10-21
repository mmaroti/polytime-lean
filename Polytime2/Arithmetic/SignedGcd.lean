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

import Polytime2.Arithmetic.SignedArithmetic
import Polytime2.Arithmetic.NaturalArithmetic

/-! # Nonnegative gcd of signed integers at the operands' magnitude width

Every operand pair is admissible, including `(0,0)`. The existing unsigned gcd
runs on the ordinary magnitudes. Its nonnegative result is returned as a
canonical signed integer, with no additional public size or capacity premise.
-/

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

noncomputable def integerGcd (width : MvPolynomial Parameter ℕ) : Computation Parameter Bool where
  inputDomains _ := binaryIntegers width
  outputDomain := binaryIntegers width
  precondition _ _ := True
  compute sizes arguments :=
    let answer := gcdValue (MvPolynomial.eval sizes width)
      ⟨(arguments.val false).val.natAbs, (arguments.val false).property⟩
      ⟨(arguments.val true).val.natAbs, (arguments.val true).property⟩
    ⟨(answer.val : ℤ), by simpa using answer.isLt⟩

theorem integerGcd_correct (width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (integerGcd width).Arguments sizes) :
    let answer := (integerGcd width).compute sizes ⟨arguments, trivial⟩
    0 ≤ answer.val ∧ answer.val = (Int.gcd (arguments false).val (arguments true).val : ℤ) := by
  exact ⟨Int.natCast_nonneg _, rfl⟩

theorem integerGcd_realizable (width : MvPolynomial Parameter ℕ) :
    (integerGcd width).Realizable := by
  let inputs := (integerGcd width).inputDomains
  have magnitude := (Realizable.Internal.naturalGcd_realizable width).onResults inputs (fun _ _ => True)
    (fun name _ arguments => ⟨(arguments.val name).val.natAbs, (arguments.val name).property⟩)
    (by intros; trivial) (by
      intro name
      exact (integerMagnitude_realizable width).withArguments inputs (MultiTape.oneTape name) (fun _ => rfl))
  have constructed := magnitude.followedBy (Realizable.Internal.integerOfMagnitude_realizable width) rfl
    (by intros; trivial)
  exact constructed.withSpecification (fun _ _ => True) (integerGcd width).compute
    (by intros; trivial) (by intros; rfl)

end Polytime2.Computation
