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

import Polytime2.Matrices.Map
import Polytime2.Encoding.IntegerMatrices
import Polytime2.Arithmetic.SignedWidth

/-! # Narrowing ordinary integer matrices after a proved bound

The input is a rectangular integer matrix at a source magnitude width. The
mathematical precondition says every entry fits the target width. The result is
exactly the same matrix at that width. Refine the whole-matrix guarantee, move
it to individual entries without changing bits, and map the certified scalar
narrowing. No runtime checks, modular reduction, or new matrix machine are used.
-/

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

/-- Preserve the matrix while discarding magnitude bits proved to be zero. -/
noncomputable def integerMatrixNarrow (rows columns sourceWidth targetWidth : MvPolynomial Parameter ℕ) :
    Computation Parameter Unit where
  inputDomains _ := integerMatrices rows columns sourceWidth
  outputDomain := integerMatrices rows columns targetWidth
  precondition sizes arguments := ∀ row column, ((arguments ()).val row column).natAbs < 2 ^ MvPolynomial.eval sizes targetWidth
  compute _ arguments := ⟨(arguments.val ()).val, arguments.property⟩

theorem integerMatrixNarrow_realizable (rows columns sourceWidth targetWidth : MvPolynomial Parameter ℕ)
    (widths : ∀ sizes, MvPolynomial.eval sizes targetWidth ≤ MvPolynomial.eval sizes sourceWidth) :
    (integerMatrixNarrow rows columns sourceWidth targetWidth).Realizable := by
  classical
  let computation := integerMatrixNarrow rows columns sourceWidth targetWidth
  let source := binaryIntegers sourceWidth
  let target := binaryIntegers targetWidth
  let fits sizes (value : source.Carrier sizes) := value.val.natAbs < 2 ^ MvPolynomial.eval sizes targetWidth
  let restricted := source.restrict fits
  let operation sizes (value : restricted.Carrier sizes) : target.Carrier sizes :=
    ⟨value.val.val, value.property⟩
  have scalar := (Realizable.Internal.integerNarrowAtWidths_realizable sourceWidth targetWidth widths).reinterpretInputs
    (fun _ : Unit => restricted) (fun _ _ value => value.val) (by intros; rfl) (by intros; rfl)
    (fun _ _ => True) (by intro sizes arguments _valid; exact (arguments ()).property)
  have step : (unaryMap restricted target (fun _ _ => True) (fun sizes value => operation sizes value.val)).Realizable :=
    scalar.withSpecification (fun _ _ => True) _ (by intros; trivial) (by intros; rfl)
  have mapped := matrixMap_realizable restricted target rows columns operation step
  have collected := mapped.reindexOutput computation.outputDomain.Carrier
    (fun sizes => IntegerMatrix.entryBoundEquiv (2 ^ MvPolynomial.eval sizes targetWidth))
  let fitsMatrix sizes (value : (integerMatrices rows columns sourceWidth).Carrier sizes) :=
    ∀ row column, (value.val row column).natAbs < 2 ^ MvPolynomial.eval sizes targetWidth
  let copied := (copy (integerMatrices rows columns sourceWidth)).withPrecondition computation.precondition
    (by intros; trivial)
  have copiedReady : copied.Realizable := (copy_realizable _).withPrecondition computation.precondition (by intros; trivial)
  let prepared := copied.refineOutput fitsMatrix (by intro sizes arguments; exact arguments.property)
  have preparedReady : prepared.Realizable := copiedReady.refineOutput fitsMatrix (by intro sizes arguments; exact arguments.property)
  have consumed := collected.reinterpretInputs (fun _ : Unit => prepared.outputDomain)
    (fun _ _ value row column => ⟨⟨value.val.val row column, value.val.property row column⟩, value.property row column⟩)
    (by intros; rfl) (by
      intro name sizes value
      change ArrayEncoding.bits ((matrix source rows columns).encode sizes
        (IntegerMatrix.entryBoundEquiv (2 ^ MvPolynomial.eval sizes sourceWidth) value.val)) = _
      apply matrix_encode_bits_congr source restricted rows columns sizes
      intro row column
      rfl)
    (fun _ _ => True) (by intros; trivial)
  have complete := preparedReady.followedBy consumed rfl (by intros; trivial)
  apply complete.withSpecification computation.precondition computation.compute (by intros; assumption)
  intro sizes arguments valid
  apply Subtype.ext
  funext row column
  rfl

end Polytime2.Computation
