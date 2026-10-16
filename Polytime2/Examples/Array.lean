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

import Polytime2.Computation.Composition
import Polytime2.Computations.Array

/-! # Array access through public mathematical certificates

The original immutable array remains available after lookup and update.
A compound computation reads one entry and writes it at another coordinate.
-/

namespace Polytime2.Examples.Array

open Polytime2.Computation

noncomputable section MathematicalExamples

private def element : EncodedDomain Bool := EncodedDomain.fixed (Equiv.refl (Fin 3))
private def length : MvPolynomial Bool ℕ := MvPolynomial.X true
private def originalDomains : Fin 3 → EncodedDomain Bool
  | 0 | 1 => EncodedDomain.binaryNaturals false
  | 2 => element.arrayOfLength length

private def sourceSelection : Bool ↪ Fin 3 :=
  ⟨(fun | false => 0 | true => 2), by intro first second equal; cases first <;> cases second <;> simp_all⟩

private def readSource : Polytime2.Computation Bool (Fin 3) :=
  ((arrayLookup element false length).withArguments originalDomains sourceSelection
    (by intro name; cases name <;> rfl)).withPrecondition
    (fun sizes arguments => (arguments 0).val < MvPolynomial.eval sizes length ∧
      (arguments 1).val < MvPolynomial.eval sizes length)
    (by intro sizes arguments valid; exact valid.1)

private def continuationDomains : Fin 3 ⊕ Unit → EncodedDomain Bool :=
  Sum.elim originalDomains (fun _ => element)

private def updateSelection : Fin 3 ↪ Fin 3 ⊕ Unit :=
  ⟨(fun | 0 => .inl 1 | 1 => .inl 2 | 2 => .inr ()), by
    intro first second equal
    fin_cases first <;> fin_cases second <;> first | rfl | cases equal⟩

private def writeTarget : Polytime2.Computation Bool (Fin 3 ⊕ Unit) :=
  (arrayUpdate element false length).withArguments continuationDomains updateSelection
    (by intro name; fin_cases name <;> rfl)

/-- Arguments are the source index, target index, and immutable array. -/
def indexedCopy : Polytime2.Computation Bool (Fin 3) :=
  readSource.letThen writeTarget (fun _ => rfl) rfl
    (by intro sizes arguments valid; exact valid.2)

/-- Lookup and update compose without exposing either machine or scratch. -/
theorem indexedCopy_realizable : indexedCopy.Realizable := by
  apply Computation.Realizable.letThen
  · exact ((arrayLookup_realizable element false length 2 (fun _ => by norm_num [element, EncodedDomain.booleans, EncodedDomain.fixed, EncodedDomain.ofCodec])).withArguments
      originalDomains sourceSelection _).withPrecondition _ _
  · exact (arrayUpdate_realizable element false length 2 (fun _ => by norm_num [element, EncodedDomain.booleans, EncodedDomain.fixed, EncodedDomain.ofCodec])).withArguments
      continuationDomains updateSelection _

/-- Equal source and target indices are allowed; lookup finishes before update. -/
theorem indexedCopy_correct (sizes : Bool → ℕ) (arguments : indexedCopy.Arguments sizes)
    (valid : indexedCopy.precondition sizes arguments) :
    indexedCopy.compute sizes ⟨arguments, valid⟩ =
      Function.update (arguments 2) ⟨(arguments 1).val, valid.2⟩
        (arguments 2 ⟨(arguments 0).val, valid.1⟩) := rfl

example : (arrayLookup element false length).Realizable :=
  arrayLookup_realizable element false length 2 (fun _ => by norm_num [element, EncodedDomain.booleans, EncodedDomain.fixed, EncodedDomain.ofCodec])
example : (arrayUpdate element false length).Realizable :=
  arrayUpdate_realizable element false length 2 (fun _ => by norm_num [element, EncodedDomain.booleans, EncodedDomain.fixed, EncodedDomain.ofCodec])

-- Singleton elements occupy zero bits, but lookup and update remain realizable.
example : (arrayLookup (EncodedDomain.fixed (Equiv.refl (Fin 1))) false length).Realizable :=
  arrayLookup_realizable _ _ _ 0 (fun _ => by norm_num [element, EncodedDomain.booleans, EncodedDomain.fixed, EncodedDomain.ofCodec])
example : (arrayUpdate (EncodedDomain.fixed (Equiv.refl (Fin 1))) false length).Realizable :=
  arrayUpdate_realizable _ _ _ 0 (fun _ => by norm_num [element, EncodedDomain.booleans, EncodedDomain.fixed, EncodedDomain.ofCodec])

end MathematicalExamples
end Polytime2.Examples.Array
