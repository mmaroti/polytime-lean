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

import Polytime2.Primitives.BitOperations
import Polytime2.Encoding.Records
import Mathlib.Data.List.OfFn

/-! # Concatenating arrays without changing their element words

Input two mathematical arrays over the same encoded element domain. Return
their concatenation at the sum of their lengths. The product's consecutive
words are already the output array's canonical encoding, including empty
arrays. This constructor supports rectangular augmented matrices row by row.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

/-- Concatenate two arrays, retaining their order and exact element encodings. -/
noncomputable def arrayAppend (element : EncodedDomain.{0, 0} Parameter)
    (firstLength secondLength : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  encodingMap ((element.arrayOfLength firstLength).prod (element.arrayOfLength secondLength))
    (element.arrayOfLength (firstLength + secondLength)) (fun sizes value index =>
      Fin.append value.1 value.2 (Fin.cast (map_add (MvPolynomial.eval sizes) firstLength secondLength) index))

/-- Concatenation retains the complete mathematical element order. -/
theorem arrayAppend_list (element : EncodedDomain.{0, 0} Parameter)
    (firstLength secondLength : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (arrayAppend element firstLength secondLength).Arguments sizes // True}) :
    List.ofFn ((arrayAppend element firstLength secondLength).compute sizes arguments) =
      List.ofFn (arguments.val ()).1 ++ List.ofFn (arguments.val ()).2 := by
  change List.ofFn (fun index => Fin.append (arguments.val ()).1 (arguments.val ()).2
    (index.cast (map_add (MvPolynomial.eval sizes) firstLength secondLength))) = _
  rw [List.ofFn_congr (map_add (MvPolynomial.eval sizes) firstLength secondLength)]
  simp only [Fin.cast_cast, Fin.cast_refl, id_eq]
  exact List.ofFn_fin_append _ _

/-- Concatenation reuses the existing consecutive product and array words. -/
theorem arrayAppend_realizable (element : EncodedDomain.{0, 0} Parameter)
    (firstLength secondLength : MvPolynomial Parameter ℕ) :
    (arrayAppend element firstLength secondLength).Realizable := by
  apply encodingMap_realizable
  · intro sizes
    simp [EncodedDomain.width, EncodedDomain.arrayOfLength, add_mul]
  · intro sizes value
    simp only [bits_prod_encode, arrayOfLength_encode_bits]
    rw [ArrayEncoding.bits_encode_cast]
    simp only [ArrayEncoding.bits_encode]
    have mapped : (fun index => ArrayEncoding.bits (element.encode sizes (Fin.append value.1 value.2 index))) =
        Fin.append (fun index => ArrayEncoding.bits (element.encode sizes (value.1 index)))
          (fun index => ArrayEncoding.bits (element.encode sizes (value.2 index))) := by
      funext index
      cases index using Fin.addCases <;> simp
    rw [mapped, List.ofFn_fin_append, List.flatten_append]

end Polytime2.Computation
