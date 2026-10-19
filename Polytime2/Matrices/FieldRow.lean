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

import Polytime2.Arrays.MapContract
import Polytime2.Matrices.RowCombine
import Mathlib.Algebra.Field.Defs

/-! # Binary-encoded finite-field row operations

The field presentation is fixed by the specialization. Coefficients and source
rows are immutable; results occupy separate tapes with arbitrary initial data.
For binary row operations, each array entry is a pair of source and target
values. Its fixed presentation hides the scalar-pair bit layout.
-/

namespace Polytime2.FieldRow

open CallingConvention

-- parameterLevel: unary size names; Scalar: the fixed field carrier.
universe parameterLevel
variable {Parameter : Type parameterLevel} [Fintype Parameter]
variable {Scalar : Type} [Field Scalar] {cardinality : ℕ}

noncomputable def scalarDomain (enumeration : Scalar ≃ Fin cardinality) : EncodedDomain Empty :=
  EncodedDomain.fixed enumeration

noncomputable def pairDomain (enumeration : Scalar ≃ Fin cardinality) : EncodedDomain Empty :=
  EncodedDomain.fixed ((enumeration.prodCongr enumeration).trans finProdFinEquiv)

def scale (coefficient value : Scalar) : Scalar := coefficient * value
def normalize (coefficient value : Scalar) : Scalar := coefficient⁻¹ * value

def add (coefficient : Scalar) (values : Scalar × Scalar) : Scalar × Scalar :=
  (values.1, values.2 + coefficient * values.1)

def swap (_coefficient : Scalar) (values : Scalar × Scalar) : Scalar × Scalar :=
  (values.2, values.1)

omit [Field Scalar] in
/-- Corresponding entries can also be combined on separate argument tapes,
without first packing them into an array of scalar pairs. -/
theorem combine_contract (enumeration : Scalar ≃ Fin cardinality)
    (operation : Scalar → Scalar → Scalar → Scalar × Scalar) :
    CallingConvention.Realizes (StandardRowCombine.domains (scalarDomain enumeration))
      StandardRowCombine.readOnly StandardRowCombine.sizeTapes StandardRowCombine.outputTapes
      (StandardRowCombine.algorithm (scalarDomain enumeration) (fun _ => operation))
      StandardRowCombine.entry StandardRowCombine.exit (fun _ _ => True)
      (fun _ input output => (output 0, output 1) =
        operation (input ⟨.inl 0, rfl⟩) (input ⟨.inl 1, rfl⟩) (input ⟨.inl 2, rfl⟩)) :=
  StandardRowCombine.contract (scalarDomain enumeration) (fun _ => operation)

/-- Multiplication by any coefficient, including zero, maps the whole row. -/
theorem scale_contract (enumeration : Scalar ≃ Fin cardinality)
    (length : MvPolynomial Parameter ℕ) :
    let domain := scalarDomain enumeration
    CallingConvention.Realizes (StandardArrayMap.domains domain domain length)
      StandardArrayMap.argumentReadOnly StandardArrayMap.sizeTapes StandardArrayMap.outputTapes
      (StandardArrayMap.algorithm domain domain (fun _ => scale (Scalar := Scalar)))
      StandardArrayMap.entry StandardArrayMap.exit (fun _ _ => True)
      (fun _ input output => output () =
        fun index => scale (Scalar := Scalar) (input ⟨.inr 0, rfl⟩) (input ⟨.inr 1, rfl⟩ index)) :=
  StandardArrayMap.contract (scalarDomain enumeration) (scalarDomain enumeration) length (fun _ => scale (Scalar := Scalar))

/-- Pivot inversion is part of the fixed field table, with no runtime arithmetic
oracle. A nonzero-pivot assumption belongs to the caller's correctness proof. -/
theorem normalize_contract (enumeration : Scalar ≃ Fin cardinality)
    (length : MvPolynomial Parameter ℕ) :
    let domain := scalarDomain enumeration
    CallingConvention.Realizes (StandardArrayMap.domains domain domain length)
      StandardArrayMap.argumentReadOnly StandardArrayMap.sizeTapes StandardArrayMap.outputTapes
      (StandardArrayMap.algorithm domain domain (fun _ => normalize (Scalar := Scalar)))
      StandardArrayMap.entry StandardArrayMap.exit (fun _ _ => True)
      (fun _ input output => output () =
        fun index => normalize (Scalar := Scalar) (input ⟨.inr 0, rfl⟩) (input ⟨.inr 1, rfl⟩ index)) :=
  StandardArrayMap.contract (scalarDomain enumeration) (scalarDomain enumeration) length (fun _ => normalize (Scalar := Scalar))

/-- The source component is retained, and the target receives its scaled sum. -/
theorem add_contract (enumeration : Scalar ≃ Fin cardinality)
    (length : MvPolynomial Parameter ℕ) :
    CallingConvention.Realizes
      (StandardArrayMap.domains (scalarDomain enumeration) (pairDomain enumeration) length)
      StandardArrayMap.argumentReadOnly StandardArrayMap.sizeTapes StandardArrayMap.outputTapes
      (StandardArrayMap.algorithm (scalarDomain enumeration) (pairDomain enumeration) (fun _ => add (Scalar := Scalar)))
      StandardArrayMap.entry StandardArrayMap.exit (fun _ _ => True)
      (fun _ input output => output () =
        fun index => add (Scalar := Scalar) (input ⟨.inr 0, rfl⟩) (input ⟨.inr 1, rfl⟩ index)) :=
  StandardArrayMap.contract (scalarDomain enumeration) (pairDomain enumeration) length (fun _ => add (Scalar := Scalar))

omit [Field Scalar] in
/-- Swapping also covers identical mathematical rows. Both result components
are written to the separate output array; every input remains unchanged. -/
theorem swap_contract (enumeration : Scalar ≃ Fin cardinality)
    (length : MvPolynomial Parameter ℕ) :
    CallingConvention.Realizes
      (StandardArrayMap.domains (scalarDomain enumeration) (pairDomain enumeration) length)
      StandardArrayMap.argumentReadOnly StandardArrayMap.sizeTapes StandardArrayMap.outputTapes
      (StandardArrayMap.algorithm (scalarDomain enumeration) (pairDomain enumeration) (fun _ => swap (Scalar := Scalar)))
      StandardArrayMap.entry StandardArrayMap.exit (fun _ _ => True)
      (fun _ input output => output () =
        fun index => swap (Scalar := Scalar) (input ⟨.inr 0, rfl⟩) (input ⟨.inr 1, rfl⟩ index)) :=
  StandardArrayMap.contract (scalarDomain enumeration) (pairDomain enumeration) length (fun _ => swap (Scalar := Scalar))

end Polytime2.FieldRow
