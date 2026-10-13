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

import Polytime2.StandardMatrixRowEntry

/-! # Scalar combination inside the shared matrix-row workspace -/

namespace Polytime2.Examples.MatrixRowEntry

open Polytime2.StandardMatrixRowEntry CallingConvention

-- Private outputs begin blank; writable call entry follows
-- from their fixed regions. The controller adds 1 + 1 * 1 over two elements.
example :
    let scalar : EncodedDomain.{0, 0} Empty := EncodedDomain.booleans
    let sizes := ![3, 2, 3]
    let initial : MultiTape.Tapes Alphabet := fun name => buffer
      (List.replicate ((domains scalar name).width sizes)
        (if name = .inr 3 ∨ name = .inr 7 ∨ name = .inr 8 then 2 else 0))
    ∃ ticks final, Runs (fun name => (domains scalar name).width sizes) readOnly
      (combine false scalar (fun _ (coefficient source target : Bool) => (source, target != (coefficient && source))))
      ticks StandardRowCombine.entry (fun _ => 0) initial StandardRowCombine.exit (fun _ => 0) final ∧
      final (.inr 9) = tape [true] ∧ final (.inr 10) = tape [false] := by
  intro scalar sizes initial
  obtain ⟨bound, execute⟩ := combine_runs false scalar
    (fun _ (coefficient source target : Bool) => (source, target != (coefficient && source)))
  have coefficientEq : initial (.inr 3) = encoded scalar Empty.elim true := by
    change buffer [2] = encoded EncodedDomain.booleans Empty.elim true
    exact (encoded_booleans Empty.elim true).symm
  have sourceEq : initial (.inr 7) = encoded scalar Empty.elim true := by
    change buffer [2] = encoded EncodedDomain.booleans Empty.elim true
    exact (encoded_booleans Empty.elim true).symm
  have targetEq : initial (.inr 8) = encoded scalar Empty.elim true := by
    change buffer [2] = encoded EncodedDomain.booleans Empty.elim true
    exact (encoded_booleans Empty.elim true).symm
  obtain ⟨ticks, final, cost, trace, first, second, outside, immutable⟩ := execute sizes initial true true true
    coefficientEq sourceEq targetEq (by
      intro name
      simpa only [List.length_replicate] using buffer_region
        (List.replicate ((domains scalar name).width sizes)
          (if name = .inr 3 ∨ name = .inr 7 ∨ name = .inr 8 then 2 else 0)))
  change final (.inr 9) = encoded EncodedDomain.booleans Empty.elim true at first
  change final (.inr 10) = encoded EncodedDomain.booleans Empty.elim false at second
  refine ⟨ticks, final, trace, ?_, ?_⟩
  · simpa only [encoded_booleans, tape, buffer, Binary.word, List.map_cons, List.map_nil] using first
  · simpa only [encoded_booleans, tape, buffer, Binary.word, List.map_cons, List.map_nil] using second

end Polytime2.Examples.MatrixRowEntry
