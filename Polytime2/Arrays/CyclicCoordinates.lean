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

import Polytime2.Arithmetic.CyclicCoordinate
import Polytime2.Arrays.ZipWith

/-! # Vectors of actual cyclic and free coordinates

Combine a natural modulus vector and an independently bounded signed integer
vector. Return the actual bounded ZMod coordinate at every position, retaining
each modulus. Zero moduli preserve free integer coordinates rather than
collapsing them to zero. All capacities are derived from the input widths.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

private noncomputable def native (length modulusWidth valueWidth : MvPolynomial Parameter ℕ) :=
  arrayZipWith (Empty.elim : Empty → EncodedDomain Parameter)
    (binaryNaturalsOfWidth modulusWidth) (binaryIntegers valueWidth)
    (boundedCyclic modulusWidth (modulusWidth + valueWidth)) length
    (fun sizes _ modulus value => (integerCyclicCoordinate modulusWidth valueWidth).compute sizes
      ⟨(fun choice => match choice with | false => modulus | true => value), trivial⟩)

private theorem native_realizable (length modulusWidth valueWidth : MvPolynomial Parameter ℕ) :
    (native length modulusWidth valueWidth).Realizable := by
  exact (integerCyclicCoordinate_realizable modulusWidth valueWidth).zipWith length

/-- Transport a vector to its actual cyclic/free coordinates, with all moduli retained. -/
private noncomputable def implementation (length modulusWidth valueWidth : MvPolynomial Parameter ℕ) :
    Computation Parameter Bool :=
  (native length modulusWidth valueWidth).onResults
    (fun choice => (if choice then binaryIntegers valueWidth else binaryNaturalsOfWidth modulusWidth).arrayOfLength length)
    (fun _ _ => True)
    (fun name _ arguments => match name with | .inl impossible => nomatch impossible | .inr choice => arguments.val choice)
    (by intros; trivial)

/-- Certified scalar transport lifts pointwise through the shared array traversal. -/
private theorem implementation_realizable (length modulusWidth valueWidth : MvPolynomial Parameter ℕ) :
    (implementation length modulusWidth valueWidth).Realizable := by
  apply (native_realizable length modulusWidth valueWidth).onResults _ _ _ (by intros; trivial)
  intro name
  rcases name with impossible | choice
  · exact impossible.elim
  · exact Realizable.argument _ choice _

/-- The scalar mathematical quotient map applied at each position. Traversal
and argument preparation are hidden behind the specification boundary. -/
noncomputable def integerCyclicCoordinates (length modulusWidth valueWidth : MvPolynomial Parameter ℕ) :
    Computation Parameter Bool :=
  specification
    (fun choice => (if choice then binaryIntegers valueWidth else binaryNaturalsOfWidth modulusWidth).arrayOfLength length)
    ((boundedCyclic modulusWidth (modulusWidth + valueWidth)).arrayOfLength length)
    (fun _ _ => True)
    (fun sizes arguments index => (integerCyclicCoordinate modulusWidth valueWidth).compute sizes
      ⟨(fun choice => match choice with
        | false => arguments.val false index | true => arguments.val true index), trivial⟩)

theorem integerCyclicCoordinates_realizable (length modulusWidth valueWidth : MvPolynomial Parameter ℕ) :
    (integerCyclicCoordinates length modulusWidth valueWidth).Realizable := by
  apply (implementation_realizable length modulusWidth valueWidth).specification
  intros
  rfl

/-- Explicitly evaluate the pointwise mathematical composition. -/
theorem integerCyclicCoordinates_compute (length modulusWidth valueWidth : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ) (arguments : (integerCyclicCoordinates length modulusWidth valueWidth).Arguments sizes)
    (index : Fin (MvPolynomial.eval sizes length)) :
    (integerCyclicCoordinates length modulusWidth valueWidth).compute sizes ⟨arguments, trivial⟩ index =
      (integerCyclicCoordinate modulusWidth valueWidth).compute sizes
        ⟨(fun choice => match choice with
          | false => arguments false index | true => arguments true index), trivial⟩ := by
  simp only [integerCyclicCoordinates, specification_compute]

/-- Every output retains exactly its corresponding input modulus. -/
theorem integerCyclicCoordinates_modulus (length modulusWidth valueWidth : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ) (arguments : (integerCyclicCoordinates length modulusWidth valueWidth).Arguments sizes)
    (index : Fin (MvPolynomial.eval sizes length)) :
    ((integerCyclicCoordinates length modulusWidth valueWidth).compute sizes ⟨arguments, trivial⟩ index).1 =
      arguments false index := by
  rw [integerCyclicCoordinates_compute]
  exact integerCyclicCoordinate_modulus modulusWidth valueWidth sizes
    (fun choice => match choice with | false => arguments false index | true => arguments true index)

/-- Every coordinate is the input integer's ordinary image in the reported ZMod domain. -/
theorem integerCyclicCoordinates_correct (length modulusWidth valueWidth : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ) (arguments : (integerCyclicCoordinates length modulusWidth valueWidth).Arguments sizes)
    (index : Fin (MvPolynomial.eval sizes length)) :
    let result := (integerCyclicCoordinates length modulusWidth valueWidth).compute sizes ⟨arguments, trivial⟩ index
    result.2.val = ((arguments true index).val : ZMod result.1.val) := by
  dsimp only
  rw [integerCyclicCoordinates_compute]
  exact integerCyclicCoordinate_correct modulusWidth valueWidth sizes
    (fun choice => match choice with | false => arguments false index | true => arguments true index)

/-- The whole quotient vector vanishes exactly when every modulus divides its integer coordinate. -/
theorem integerCyclicCoordinates_zero_iff (length modulusWidth valueWidth : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ) (arguments : (integerCyclicCoordinates length modulusWidth valueWidth).Arguments sizes) :
    (∀ index, ((integerCyclicCoordinates length modulusWidth valueWidth).compute sizes ⟨arguments, trivial⟩ index).2.val = 0) ↔
      ∀ index, ((arguments false index).val : ℤ) ∣ (arguments true index).val := by
  apply forall_congr'
  intro index
  rw [integerCyclicCoordinates_correct]
  rw [integerCyclicCoordinates_modulus]
  exact ZMod.intCast_zmod_eq_zero_iff_dvd _ _

end Polytime2.Computation
