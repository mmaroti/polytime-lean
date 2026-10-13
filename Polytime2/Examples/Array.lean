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

import Polytime2.StandardArrayLookupContract
import Polytime2.IndexedCopy
import Polytime2.CallingConventionSimulation
import Polytime2.StandardArrayLookupSizedContract
import Polytime2.StandardMatrixLookup
import Polytime2.StandardMatrixUpdate
import Polytime2.StandardArrayUpdate

/-! # Standard array access boundary cases

These checks exercise the complete lookup controller with immutable original
arguments, blank outputs, arbitrary old scratch contents, and zero-bit elements.
-/

namespace Polytime2.Examples.Array

open Binary (word data)
open CallingConvention (buffer Runs)

-- Lookup the middle of three two-bit elements using a binary index of one.
example : ∃ ticks, ticks ≤ 58 ∧
    Runs (StandardArrayLookup.widths 2 2 6) StandardArrayLookup.readOnly (StandardArrayLookup.machine 2)
      ticks (StandardArrayLookup.entry 2) (fun _ => 0)
      (StandardArrayLookup.initialFrame [true, false]
        [false, true, true, false, true, true] [0, 2] [2, 0] [0, 0] 2)
      (StandardArrayLookup.exit 2) (fun _ => 0)
      (StandardArrayLookup.frame [true, false] (buffer (word [false, true, true, false, true, true]))
        (word [true, false]) [false, false] (word [false, false]) (data false)) :=
  StandardArrayLookup.runs 2 [true, false] [false, true] [true, false] [true, true]
    rfl rfl [0, 2] [2, 0] [0, 0] rfl rfl rfl 2

-- Zero-bit elements still allow a nonzero index and return every head to zero.
example : ∃ ticks, ticks ≤ 50 ∧
    Runs (StandardArrayLookup.widths 0 2 0) StandardArrayLookup.readOnly (StandardArrayLookup.machine 0)
      ticks (StandardArrayLookup.entry 0) (fun _ => 0)
      (StandardArrayLookup.initialFrame [true, false] [] [] [0, 2] [2, 0] 2)
      (StandardArrayLookup.exit 0) (fun _ => 0)
      (StandardArrayLookup.frame [true, false] (buffer []) [] [false, false]
        (word [false, false]) (data false)) :=
  StandardArrayLookup.runs 0 [true, false] [] [] [] rfl rfl [] [0, 2] [2, 0] rfl rfl rfl 2

-- Index zero needs no seek iteration, but cleanup still overwrites its scratch.
example : ∃ ticks, ticks ≤ 23 ∧
    Runs (StandardArrayLookup.widths 1 1 1) StandardArrayLookup.readOnly (StandardArrayLookup.machine 1)
      ticks (StandardArrayLookup.entry 1) (fun _ => 0)
      (StandardArrayLookup.initialFrame [false] [true] [0] [2] [2] 2)
      (StandardArrayLookup.exit 1) (fun _ => 0)
      (StandardArrayLookup.frame [false] (buffer (word [true])) (word [true]) [false]
        (word [false]) (data false)) :=
  StandardArrayLookup.runs 1 [false] [] [true] [] rfl rfl [0] [2] [2] rfl rfl rfl 2

example : Fintype (StandardArrayLookup.State 2) := inferInstance

/-- The public contract works for an opaque finite carrier with unused labels. -/
abbrev threeElements : EncodedDomain Bool := EncodedDomain.fixed (Equiv.refl (Fin 3))

abbrev twoElements : EncodedDomain Bool := EncodedDomain.fixed (Equiv.refl (Fin 2))

example : CallingConvention.Realizes (StandardArrayLookup.domains threeElements)
    StandardArrayLookup.argumentReadOnly StandardArrayLookup.sizeTapes
    (StandardArrayLookup.algorithm 2) (StandardArrayLookup.entry 2) (StandardArrayLookup.exit 2)
    (fun assignment input => (input ⟨.inr 0, rfl⟩).val < assignment true)
    (fun assignment input output => ∃ within : (input ⟨.inr 0, rfl⟩).val < assignment true,
      output ⟨.inr 2, rfl⟩ = input ⟨.inr 1, rfl⟩ ⟨(input ⟨.inr 0, rfl⟩).val, within⟩) :=
  StandardArrayLookup.contract threeElements 2 (by intro assignment; change Nat.clog 2 3 = 2; decide)

/-- Rectangular matrices use row-major array storage under the same typed
calling convention as scalar-array lookup. -/
example : CallingConvention.Realizes
    (StandardMatrixLookup.domains twoElements false (MvPolynomial.X false)
      (MvPolynomial.X true))
    StandardMatrixLookup.readOnly StandardMatrixLookup.sizeTapes
    (StandardMatrixLookup.algorithm 1) (StandardArrayLookup.entry 1)
    (StandardArrayLookup.exit 1)
    (fun assignment input => (input ⟨.inr 0, rfl⟩).val <
      MvPolynomial.eval assignment (MvPolynomial.X false * MvPolynomial.X true))
    (fun assignment input output => ∃ within : (input ⟨.inr 0, rfl⟩).val <
      MvPolynomial.eval assignment (MvPolynomial.X false * MvPolynomial.X true),
      output ⟨.inr 2, rfl⟩ =
        EncodedDomain.MatrixEncoding.flattenPolynomial (MvPolynomial.X false)
          (MvPolynomial.X true) assignment (input ⟨.inr 1, rfl⟩)
          ⟨(input ⟨.inr 0, rfl⟩).val, within⟩) := by
  exact StandardMatrixLookup.contract twoElements 1 false (MvPolynomial.X false)
    (MvPolynomial.X true)
    (by intro assignment; change Nat.clog 2 2 = 1; decide)

/-- Matrix update writes a distinct result tape, whose row-major view differs
from the source at exactly the selected flat index. -/
example : CallingConvention.Realizes
    (StandardMatrixUpdate.domains twoElements false (MvPolynomial.X false)
      (MvPolynomial.X true))
    StandardMatrixUpdate.readOnly StandardMatrixUpdate.sizeTapes
    (StandardMatrixUpdate.algorithm 1) (StandardArrayUpdate.entry 1)
    (StandardArrayUpdate.exit 1)
    (fun assignment input => (input ⟨.inr 0, rfl⟩).val <
      MvPolynomial.eval assignment (MvPolynomial.X false * MvPolynomial.X true))
    (fun assignment input output => ∃ within : (input ⟨.inr 0, rfl⟩).val <
      MvPolynomial.eval assignment (MvPolynomial.X false * MvPolynomial.X true),
      EncodedDomain.MatrixEncoding.flattenPolynomial (MvPolynomial.X false)
          (MvPolynomial.X true) assignment (output ⟨.inr 3, rfl⟩) =
        Function.update
          (EncodedDomain.MatrixEncoding.flattenPolynomial (MvPolynomial.X false)
            (MvPolynomial.X true) assignment (input ⟨.inr 1, rfl⟩))
          ⟨(input ⟨.inr 0, rfl⟩).val, within⟩ (input ⟨.inr 2, rfl⟩)) := by
  exact StandardMatrixUpdate.contract twoElements 1 false (MvPolynomial.X false)
    (MvPolynomial.X true)
    (by intro assignment; change Nat.clog 2 2 = 1; decide)

example : CallingConvention.Realizes (StandardArrayUpdate.domains threeElements)
    StandardArrayUpdate.argumentReadOnly StandardArrayUpdate.sizeTapes
    (StandardArrayUpdate.algorithm 2) (StandardArrayUpdate.entry 2)
    (StandardArrayUpdate.exit 2)
    (fun assignment input => (input ⟨.inr 0, rfl⟩).val <
      MvPolynomial.eval assignment (MvPolynomial.X true))
    (fun assignment input output => ∃ within : (input ⟨.inr 0, rfl⟩).val <
        MvPolynomial.eval assignment (MvPolynomial.X true),
      output ⟨.inr 3, rfl⟩ = Function.update (input ⟨.inr 1, rfl⟩)
        ⟨(input ⟨.inr 0, rfl⟩).val, within⟩ (input ⟨.inr 2, rfl⟩)) :=
  StandardArrayUpdate.contract threeElements 2
    (by intro assignment; change Nat.clog 2 3 = 2; decide)

/-- The complete interface also specializes to zero-bit elements. -/
abbrev singletonElements : EncodedDomain Bool := EncodedDomain.fixed (Equiv.refl (Fin 1))

example : CallingConvention.Realizes (StandardArrayLookup.domains singletonElements)
    StandardArrayLookup.argumentReadOnly StandardArrayLookup.sizeTapes
    (StandardArrayLookup.algorithm 0) (StandardArrayLookup.entry 0) (StandardArrayLookup.exit 0)
    (fun assignment input => (input ⟨.inr 0, rfl⟩).val < assignment true)
    (fun assignment input output => ∃ within : (input ⟨.inr 0, rfl⟩).val < assignment true,
      output ⟨.inr 2, rfl⟩ = input ⟨.inr 1, rfl⟩ ⟨(input ⟨.inr 0, rfl⟩).val, within⟩) :=
  StandardArrayLookup.contract singletonElements 0 (by intro assignment; change Nat.clog 2 1 = 0; decide)

/-- A row-major matrix of fixed field elements has a polynomial bit width. -/
abbrev binaryField : EncodedDomain Bool := EncodedDomain.fixed (Equiv.refl (Fin 2))

abbrev matrixField : EncodedDomain (Fin 3) :=
  EncodedDomain.fixed (Equiv.refl (Fin 2))

noncomputable def matrixBits : MvPolynomial Bool ℕ :=
  MvPolynomial.X false * MvPolynomial.X true

noncomputable def matrixDomain : EncodedDomain Bool :=
  EncodedDomain.matrix binaryField (MvPolynomial.X false) (MvPolynomial.X true)

example (assignment : Bool → ℕ) :
    matrixDomain.Carrier assignment =
      (Fin (assignment false) → Fin (assignment true) → Fin 2) := by
  simp [matrixDomain, EncodedDomain.matrix, EncodedDomain.reindex,
    binaryField, EncodedDomain.fixed]

example (assignment : Bool → ℕ) :
    matrixDomain.width assignment = assignment false * assignment true := by
  have fieldWidth : Nat.clog 2 2 = 1 := by norm_num
  simp [matrixDomain, EncodedDomain.matrix, EncodedDomain.reindex,
    EncodedDomain.arrayOfLength, binaryField, EncodedDomain.fixed,
    MvPolynomial.eval_mul, fieldWidth]

example (assignment : Bool → ℕ)
    (values : matrixDomain.Carrier assignment) :
    matrixDomain.decode assignment (matrixDomain.encode assignment values) =
      some values := by
  exact matrixDomain.decode_encode assignment values

example (assignment : Bool → ℕ)
    (values : Fin (MvPolynomial.eval assignment matrixBits) → Fin 2) :
    (EncodedDomain.arrayOfLength binaryField matrixBits).decode assignment
      ((EncodedDomain.arrayOfLength binaryField matrixBits).encode assignment values) =
        some values :=
  (EncodedDomain.arrayOfLength binaryField matrixBits).decode_encode assignment values

example (assignment : Bool → ℕ) :
    (EncodedDomain.arrayOfLength binaryField matrixBits).width assignment =
      assignment false * assignment true := by
  have fieldWidth : binaryField.width assignment = 1 := by
    norm_num [binaryField, EncodedDomain.fixed]
  simp [EncodedDomain.arrayOfLength, matrixBits, MvPolynomial.eval_mul, fieldWidth]

/-- Three independent unary sizes specialize lookup to a row-major matrix. -/
example :
    CallingConvention.Realizes
      (StandardArrayLookupSized.domainsSized matrixField 0
        (MvPolynomial.X 1 * MvPolynomial.X 2))
      StandardArrayLookupSized.argumentReadOnly StandardArrayLookupSized.sizeTapes
      (StandardArrayLookupSized.algorithmSized 1)
      (StandardArrayLookup.entry 1) (StandardArrayLookup.exit 1)
      (fun sizes input => (input ⟨.inr 0, rfl⟩ : Fin (2 ^ sizes 0)).val <
        MvPolynomial.eval sizes (MvPolynomial.X 1 * MvPolynomial.X 2))
      (fun sizes input output =>
        ∃ within : (input ⟨.inr 0, rfl⟩).val <
            MvPolynomial.eval sizes (MvPolynomial.X 1 * MvPolynomial.X 2),
          output ⟨.inr 2, rfl⟩ =
            input ⟨.inr 1, rfl⟩ ⟨(input ⟨.inr 0, rfl⟩).val, within⟩) := by
  apply StandardArrayLookupSized.contractSized matrixField 1 0
    (MvPolynomial.X 1 * MvPolynomial.X 2)
  intro sizes
  norm_num [matrixField, EncodedDomain.fixed]

/-- The same three sizes certify row-major matrix entry replacement. -/
example :
    CallingConvention.Realizes
      (StandardArrayUpdate.domainsSized matrixField 0
        (MvPolynomial.X 1 * MvPolynomial.X 2))
      StandardArrayUpdate.argumentReadOnlySized StandardArrayUpdate.sizeTapesSized
      (StandardArrayUpdate.algorithmSized 1)
      (StandardArrayUpdate.entry 1) (StandardArrayUpdate.exit 1)
      (fun sizes input => (input ⟨.inr 0, rfl⟩ : Fin (2 ^ sizes 0)).val <
        MvPolynomial.eval sizes (MvPolynomial.X 1 * MvPolynomial.X 2))
      (fun sizes input output =>
        ∃ within : (input ⟨.inr 0, rfl⟩).val <
            MvPolynomial.eval sizes (MvPolynomial.X 1 * MvPolynomial.X 2),
          output ⟨.inr 3, rfl⟩ =
            Function.update (input ⟨.inr 1, rfl⟩)
              ⟨(input ⟨.inr 0, rfl⟩).val, within⟩ (input ⟨.inr 2, rfl⟩)) := by
  apply StandardArrayUpdate.contractSized matrixField 1 0
    (MvPolynomial.X 1 * MvPolynomial.X 2)
  intro sizes
  norm_num [matrixField, EncodedDomain.fixed]

/-- The machine contract also accepts a row-major matrix shape. -/
example (element : EncodedDomain Bool) (elementWidth : ℕ)
    (fixedWidth : ∀ assignment, element.width assignment = elementWidth) :
    CallingConvention.Realizes
      (StandardArrayLookupSized.domainsSized element
        false (MvPolynomial.X false * MvPolynomial.X true))
      StandardArrayLookupSized.argumentReadOnly StandardArrayLookupSized.sizeTapes
      (StandardArrayLookupSized.algorithmSized elementWidth)
      (StandardArrayLookup.entry elementWidth)
      (StandardArrayLookup.exit elementWidth)
      (fun assignment input => (input ⟨.inr 0, rfl⟩).val <
        MvPolynomial.eval assignment (MvPolynomial.X false * MvPolynomial.X true))
      (fun assignment input output =>
        ∃ within : (input ⟨.inr 0, rfl⟩).val <
            MvPolynomial.eval assignment (MvPolynomial.X false * MvPolynomial.X true),
          output ⟨.inr 2, rfl⟩ =
            input ⟨.inr 1, rfl⟩ ⟨(input ⟨.inr 0, rfl⟩).val, within⟩) :=
  StandardArrayLookupSized.contractSized element elementWidth
    false (MvPolynomial.X false * MvPolynomial.X true) fixedWidth

-- Invalid element labels remain invalid inside the array encoding.
#guard (threeElements.array true).decode (fun _ => 2) 15#4 = none

-- A zero-bit element domain still supports arrays of arbitrary assigned length.
example (assignment : Bool → ℕ) (values : Fin (assignment true) → Fin 1) :
    ((EncodedDomain.fixed (Parameter := Bool) (Equiv.refl (Fin 1))).array true).decode
      assignment 0#0 = some values := by
  have encodedZero :
      ((EncodedDomain.fixed (Parameter := Bool) (Equiv.refl (Fin 1))).array true).encode
        assignment values = 0#0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro index bounded
    change index < assignment true * Nat.clog 2 1 at bounded
    norm_num at bounded
  rw [← encodedZero]
  exact ((EncodedDomain.fixed (Parameter := Bool) (Equiv.refl (Fin 1))).array true).decode_encode
    assignment values

/-- A zero-bit element still permits indexed copy over a rectangular array.
Three independent unary sizes specify index capacity, rows, and columns;
source and target may coincide. The composed contract transfers to TM0. -/
example (element : EncodedDomain (Fin 3))
    (zeroWidth : ∀ assignment, element.width assignment = 0) :
    CallingConvention.TM0Realizes
      (IndexedCopy.domains element 0 (MvPolynomial.X 1 * MvPolynomial.X 2))
      IndexedCopy.argumentReadOnly IndexedCopy.sizeTapes
      (IndexedCopy.algorithm 0) (IndexedCopy.entry 0)
      (fun assignment input =>
        (input ⟨.inr 0, rfl⟩).val <
            MvPolynomial.eval assignment (MvPolynomial.X 1 * MvPolynomial.X 2) ∧
          (input ⟨.inr 1, rfl⟩).val <
            MvPolynomial.eval assignment (MvPolynomial.X 1 * MvPolynomial.X 2))
      (fun assignment input output =>
        ∃ sourceBound : (input ⟨.inr 0, rfl⟩).val <
            MvPolynomial.eval assignment (MvPolynomial.X 1 * MvPolynomial.X 2),
          ∃ targetBound : (input ⟨.inr 1, rfl⟩).val <
              MvPolynomial.eval assignment (MvPolynomial.X 1 * MvPolynomial.X 2),
            output ⟨.inr 3, rfl⟩ = Function.update (input ⟨.inr 2, rfl⟩)
              ⟨(input ⟨.inr 1, rfl⟩).val, targetBound⟩
              (input ⟨.inr 2, rfl⟩ ⟨(input ⟨.inr 0, rfl⟩).val, sourceBound⟩)) :=
  (IndexedCopy.contract element 0 0 (MvPolynomial.X 1 * MvPolynomial.X 2) zeroWidth).tm0

end Polytime2.Examples.Array
