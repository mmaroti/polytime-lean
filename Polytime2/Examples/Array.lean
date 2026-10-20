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

import Polytime2.Computation.Conditional
import Polytime2.Arrays.Operations

/-! # Array access through public mathematical certificates

The original immutable array remains available after lookup and update.
A compound computation reads one entry and writes it at another coordinate.
-/

namespace Polytime2.Examples.Array

open Polytime2.Computation

noncomputable section MathematicalExamples

private def element : EncodedDomain Bool := EncodedDomain.fixed (Equiv.refl (Fin 3))
private def length : MvPolynomial Bool ℕ := MvPolynomial.X true

/-- Two valid coordinates and an immutable array suffice; no capacity or
separate index-range precondition is exposed. -/
private def originalDomains : Fin 3 → EncodedDomain Bool
  | 0 | 1 => EncodedDomain.boundedIndex length
  | 2 => element.arrayOfLength length

def indexedCopy : Polytime2.Computation Bool (Fin 3) where
  inputDomains := originalDomains
  outputDomain := element.arrayOfLength length
  precondition _ _ := True
  compute _ arguments := Function.update (arguments.val 2) (arguments.val 1)
    (arguments.val 2 (arguments.val 0))

theorem indexedCopy_realizable : indexedCopy.Realizable := by
  have read := (arrayLookup_realizable element length).onResults originalDomains (fun _ _ => True)
    (fun choice _ arguments => match choice with | false => arguments.val 0 | true => arguments.val 2)
    (by intros; trivial) (by
      intro choice
      cases choice
      · exact Realizable.argument originalDomains 0 (fun _ _ => True)
      · exact Realizable.argument originalDomains 2 (fun _ _ => True))
  exact (arrayUpdate_realizable element length).onResults originalDomains (fun _ _ => True)
    (fun name _ arguments => match name with
      | 0 => arguments.val 1 | 1 => arguments.val 2 | 2 => arguments.val 2 (arguments.val 0))
    (by intros; trivial) (by
      intro name
      fin_cases name
      · exact Realizable.argument originalDomains 1 (fun _ _ => True)
      · exact Realizable.argument originalDomains 2 (fun _ _ => True)
      · exact read)

/-- Equal source and target coordinates are allowed. -/
theorem indexedCopy_correct (sizes : Bool → ℕ) (arguments : indexedCopy.Arguments sizes) :
    indexedCopy.compute sizes ⟨arguments, trivial⟩ =
      Function.update (arguments 2) (arguments 1) (arguments 2 (arguments 0)) := rfl

example : (arrayLookup element length).Realizable := arrayLookup_realizable _ _
example : (arrayUpdate element length).Realizable := arrayUpdate_realizable _ _

/-- The element width can itself depend on sizes, including nested rows. -/
example {Parameter : Type} [Fintype Parameter] (scalar : EncodedDomain Parameter)
    (rows columns : MvPolynomial Parameter ℕ) :
    (arrayLookup (scalar.arrayOfLength columns) rows).Realizable := arrayLookup_realizable _ _

example {Parameter : Type} [Fintype Parameter] (scalar : EncodedDomain Parameter)
    (rows columns : MvPolynomial Parameter ℕ) :
    (arrayUpdate (scalar.arrayOfLength columns) rows).Realizable := arrayUpdate_realizable _ _

example : (arrayLookup (EncodedDomain.binaryNaturals false) length).Realizable := arrayLookup_realizable _ _
example : (arrayUpdate (element.arrayOfLength 0) length).Realizable := arrayUpdate_realizable _ _

/-- Empty arrays have no coordinate, while singleton and zero-width elements
remain valid targets of the generic algorithms. -/
example (sizes : Bool → ℕ) : IsEmpty ((EncodedDomain.boundedIndex (Parameter := Bool) 0).Carrier sizes) := by
  change IsEmpty (Fin 0)
  infer_instance

example : (arrayLookup element 0).Realizable := arrayLookup_realizable _ _
example : (arrayUpdate (EncodedDomain.fixed (Parameter := Bool) (Equiv.refl (Fin 1))) length).Realizable :=
  arrayUpdate_realizable _ _

/-- Coordinates reject representable binary values outside the mathematical bound. -/
example (sizes : Bool → ℕ) (bits : BitVec (MvPolynomial.eval sizes length))
    (outside : MvPolynomial.eval sizes length ≤ bits.toNat) :
    (EncodedDomain.boundedIndex length).decode sizes bits = none := by
  simp [EncodedDomain.boundedIndex, Nat.not_lt.mpr outside]

end MathematicalExamples
end Polytime2.Examples.Array
