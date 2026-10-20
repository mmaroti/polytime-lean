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

import Polytime2.Arrays.PackingInvariant
import Polytime2.Computation.Substitution

/-! # Polynomial-time packing into private raw capacity blocks

This intermediate interface retains zero padding as raw bits. The final public
interface will expose the exact mathematical array at its computed count.
-/

namespace Polytime2.Computation

variable {Parameter : Type} [Fintype Parameter]

/-- Internal raw-capacity result, independent of the traversal's counters. -/
noncomputable def arrayPackRawSized (element : EncodedDomain Parameter) (capacity : Parameter)
    (length : MvPolynomial Parameter ℕ) : Computation Parameter Bool where
  inputDomains choice := if choice then element.arrayOfLength length
    else EncodedDomain.booleans.arrayOfLength length
  outputDomain := (EncodedDomain.bitVectors element.widthPolynomial).arrayOfLength length
  precondition sizes _ := MvPolynomial.eval sizes length < 2 ^ sizes capacity
  compute sizes arguments := ArrayPacking.rawPack (element.encode sizes) (arguments.val false) (arguments.val true)

theorem arrayPackRawSized_realizable (element : EncodedDomain Parameter) (capacity : Parameter)
    (length : MvPolynomial Parameter ℕ) : (arrayPackRawSized element capacity length).Realizable := by
  let counter := EncodedDomain.binaryNaturals capacity
  let array := (EncodedDomain.bitVectors element.widthPolynomial).arrayOfLength length
  have tail := (packingInitialized_realizable element capacity length).followedBy
    (pairProjection_realizable counter (counter.prod array) true) rfl (by intros; trivial)
  have result := tail.followedBy (pairProjection_realizable counter array true) rfl (by intros; trivial)
  exact result.withSpecification (arrayPackRawSized element capacity length).precondition
    (arrayPackRawSized element capacity length).compute (by intros; assumption) (by
      intro sizes arguments valid
      exact (packingInitialized_correct element capacity length sizes arguments valid).2.2)

end Polytime2.Computation
