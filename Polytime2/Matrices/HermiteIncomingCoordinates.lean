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

import Polytime2.Arrays.PositionWiden
import Polytime2.Arrays.Operations
import Polytime2.Arrays.Queue
import Polytime2.Computation.RecordArguments
import Polytime2.Computation.Conditional

/-! # Certified coordinate preparation for incoming Hermite stages

The input gives selected rows, old pivot columns, and an old-pivot position.
Return the selected source row, last incoming row, pivot column, and ordinary
prefix length. General numeric-index lookup reads both arrays directly from
the existing position codec; the prefix length reuses zero extension.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation.Realizable.Internal

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

/-- Prepare the four mathematical coordinates needed by one incoming pivot stage. -/
noncomputable def hermiteIncomingCoordinates (rows columns pivots : MvPolynomial Parameter ℕ) :
    Computation Parameter (Fin 3) where
  inputDomains | 0 => (boundedIndex rows).arrayOfLength (pivots + 1)
               | 1 => (boundedIndex columns).arrayOfLength pivots
               | 2 => arrayPosition pivots
  outputDomain := (boundedIndex rows).prod ((boundedIndex rows).prod
    ((boundedIndex columns).prod (arrayPosition (pivots + 1 + 1))))
  precondition _ _ := True
  compute sizes arguments :=
    (arguments.val 0 ⟨(arguments.val 2).val, by
      simp only [map_add, map_one]
      exact Nat.lt_succ_of_lt (arguments.val 2).isLt⟩,
      (successorValues pivots sizes (arguments.val 0) (Fin.last (MvPolynomial.eval sizes pivots)),
        (arguments.val 1 (arguments.val 2), ⟨(arguments.val 2).val, by
          simp only [map_add, map_one]
          have bounded : (arguments.val 2).val < MvPolynomial.eval sizes pivots :=
            (arguments.val 2).isLt
          omega⟩)))

/-- All lookups, last-row access, and prefix-count widening use existing certified components. -/
theorem hermiteIncomingCoordinates_realizable (rows columns pivots : MvPolynomial Parameter ℕ) :
    (hermiteIncomingCoordinates rows columns pivots).Realizable := by
  let computation := hermiteIncomingCoordinates rows columns pivots
  have numeric : ∀ sizes (index : (arrayPosition pivots).Carrier sizes),
      Binary.value (ArrayEncoding.bits ((arrayPosition pivots).encode sizes index)) = index.val := by
    intro sizes index
    exact (Binary.value_bits _).trans (by simp [arrayPosition, boundedIndexOfWidth])
  have source := (arrayLookupWithIndex_realizable (boundedIndex rows) (arrayPosition pivots)
    (fun _ index => index.val) numeric (pivots + 1)).onResults computation.inputDomains computation.precondition
    (fun choice _ arguments => match choice with | false => arguments.val 2 | true => arguments.val 0)
    (by
      intro sizes arguments
      change (arguments.val 2).val < MvPolynomial.eval sizes (pivots + 1)
      simp only [map_add, map_one]
      exact Nat.lt_succ_of_lt (arguments.val 2).isLt) (by
      intro choice
      cases choice
      · exact Realizable.argument computation.inputDomains 2 computation.precondition
      · exact Realizable.argument computation.inputDomains 0 computation.precondition)
  have incoming := (arrayLast_realizable (boundedIndex rows) pivots).withArguments computation.inputDomains
    (MultiTape.oneTape 0) (by intros; rfl)
  have column := (arrayLookupWithIndex_realizable (boundedIndex columns) (arrayPosition pivots)
    (fun _ index => index.val) numeric pivots).onResults computation.inputDomains computation.precondition
    (fun choice _ arguments => match choice with | false => arguments.val 2 | true => arguments.val 1)
    (by intro sizes arguments; exact (arguments.val 2).isLt) (by
      intro choice
      cases choice
      · exact Realizable.argument computation.inputDomains 2 computation.precondition
      · exact Realizable.argument computation.inputDomains 1 computation.precondition)
  have count := (arrayPositionWiden_realizable pivots 2).withArguments computation.inputDomains
    (MultiTape.oneTape 2) (by intros; rfl)
  have countAligned := count.withEncodedOutput (arrayPosition (pivots + 1 + 1))
    (fun sizes arguments => ⟨(arguments.val 2).val, by
      have bounded : (arguments.val 2).val < MvPolynomial.eval sizes pivots := (arguments.val 2).isLt
      simp only [map_add, map_one]
      omega⟩)
    (by
      intro sizes
      change MvPolynomial.eval sizes (pivots + 1 + 1 + 1) =
        MvPolynomial.eval sizes (pivots + 2 + 1)
      simp only [map_add, map_one, map_ofNat]
      omega)
    (by
      intro sizes arguments
      simp [CallingConvention.encoded, arrayPositionWiden, encodingMap, unaryMap, arrayPosition, boundedIndexOfWidth,
        Computation.withArguments, map_add, map_one, map_ofNat, Nat.add_assoc]
      congr 2 <;> try simp [map_add, map_one, map_ofNat, Nat.add_assoc]
      congr 1 <;> simp [map_add, map_one, map_ofNat, Nat.add_assoc])
  have lastPair := Realizable.pairOutputs computation.inputDomains _ _ computation.precondition _ _ column countAligned
  have remaining := Realizable.pairOutputs computation.inputDomains _ _ computation.precondition _ _ incoming lastPair
  have prepared := Realizable.pairOutputs computation.inputDomains _ _ computation.precondition _ _ source remaining
  exact prepared.withSpecification computation.precondition computation.compute (by intros; assumption) (by intros; rfl)

/-- The prepared prefix length is exactly the selected pivot's ordinary numeric position. -/
theorem hermiteIncomingCoordinates_count (rows columns pivots : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (hermiteIncomingCoordinates rows columns pivots).Arguments sizes //
      (hermiteIncomingCoordinates rows columns pivots).precondition sizes arguments}) :
    ((hermiteIncomingCoordinates rows columns pivots).compute sizes arguments).2.2.2.val = (arguments.val 2).val := rfl

end Polytime2.Computation.Realizable.Internal
