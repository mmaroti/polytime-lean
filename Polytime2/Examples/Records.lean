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

import Polytime2.Computation.Sums
import Polytime2.Encoding.BoundedUnary
import Polytime2.Arithmetic.CounterOperations
import Polytime2.TM0.Computation

/-! # Heterogeneous runtime-width records and variants

The fields include a runtime-width word and an array of such words. All public
operations have certified polynomial time and generic standalone TM0 exports.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Examples.Records

open _root_.Polytime2.EncodedDomain _root_.Polytime2.Computation

noncomputable def fields : Fin 3 → EncodedDomain Bool :=
  ![bitVectors (MvPolynomial.X false), booleans,
    (bitVectors (MvPolynomial.X false)).arrayOfLength (MvPolynomial.X true)]

example : (record 3 fields).widthPolynomial =
    MvPolynomial.X false + 1 + MvPolynomial.X true * MvPolynomial.X false := by
  simp [fields, Fin.sum_univ_succ, arrayOfLength, booleans, fixed, ofCodec]
  ring

example : (recordConstructor 3 fields).Realizable := recordConstructor_realizable _ _
example : (recordProjection 3 fields 2).Realizable := recordProjection_realizable _ _ _
example : (recordConstructor 3 fields).TM0Realizable := (recordConstructor_realizable _ _).tm0

private def sizes : Bool → ℕ := fun name => if name then 2 else 3

private noncomputable def values : (index : Fin 3) → (fields index).Carrier sizes := by
  refine Fin.cons ?_ (Fin.cons ?_ (Fin.cons ?_ (fun index => Fin.elim0 index)))
  · change BitVec (MvPolynomial.eval sizes (MvPolynomial.X false))
    exact (5#3).cast (by simp [sizes])
  · exact true
  · change Fin (MvPolynomial.eval sizes (MvPolynomial.X true)) →
      BitVec (MvPolynomial.eval sizes (MvPolynomial.X false))
    exact fun index => (if index.val = 0 then 1#3 else 4#3).cast (by simp [sizes])

example : (recordProjection 3 fields 2).compute sizes ⟨(fun _ => values), trivial⟩ = values 2 := rfl

/-- Fields are adjacent bits; even the nested array introduces no delimiters. -/
example : ArrayEncoding.bits ((record 3 fields).encode sizes values) =
    ArrayEncoding.bits ((fields 0).encode sizes (values 0)) ++
      ArrayEncoding.bits ((fields 1).encode sizes (values 1)) ++
      ArrayEncoding.bits ((fields 2).encode sizes (values 2)) := by
  rw [bits_record_encode]
  simp [List.ofFn_succ, List.append_assoc]

noncomputable def alternatives : Fin 2 → EncodedDomain Bool :=
  ![bitVectors (MvPolynomial.X false),
    (bitVectors (MvPolynomial.X false)).arrayOfLength (MvPolynomial.X true)]

example : (variant 2 alternatives).widthPolynomial =
    1 + MvPolynomial.X false + MvPolynomial.X true * MvPolynomial.X false := by
  simp [alternatives, Fin.sum_univ_succ, arrayOfLength]
  ring

example : (variantInjection 2 alternatives 0).Realizable := variantInjection_realizable _ _ _
example : (variantInjection 2 alternatives 1).Realizable := variantInjection_realizable _ _ _
example : (variantProjection 2 alternatives 1).Realizable := variantProjection_realizable _ _ _
example : (variantTag 2 alternatives).Realizable := variantTag_realizable _ _
example : (variantIs 2 alternatives 1).Realizable := variantIs_realizable _ _ _
example : (variantInjection 2 alternatives 1).TM0Realizable := (variantInjection_realizable _ _ _).tm0

/-- Case analysis followed by reinjection is the identity on a variant. -/
example : (variantCases 2 alternatives (variant 2 alternatives) (fun _ _ _ => True)
    (fun index _ value => Sigma.mk index value.val)).Realizable :=
  variantCases_realizable _ _ _ _ _ (fun index => variantInjection_realizable _ _ index)

private noncomputable def firstValue : (variant 2 alternatives).Carrier sizes := by
  refine ⟨(0 : Fin 2), ?_⟩
  change BitVec (MvPolynomial.eval sizes (MvPolynomial.X false))
  exact (5#3).cast (by simp [sizes])

example : ArrayEncoding.bits ((variant 2 alternatives).encode sizes firstValue) =
    [false, true, false, true, false, false, false, false, false, false] := by
  rw [bits_variant_encode]
  simp [firstValue, VariantEncoding.fields, alternatives, sizes, List.ofFn_succ,
    ArrayEncoding.bits, fixed, ofCodec, arrayOfLength, bitVectors, -BitVec.cast_ofNat]

example : (variantProjection 2 alternatives 0).compute sizes
    ⟨(fun _ => firstValue), rfl⟩ = firstValue.2 := rfl

/-- Nonzero inactive data must be rejected, even with a valid tag and payload. -/
example (slots : (index : Fin 2) → BitVec ((alternatives index).width sizes))
    (nonzero : slots 1 ≠ 0) :
    (variant 2 alternatives).decode sizes ((VariantEncoding.storage 2 alternatives).encode sizes ((0 : Fin 2), slots)) = none :=
  variant_rejects_inactive _ _ _ 0 1 slots (by decide) nonzero

private def selectedPrecondition :
    ∀ index sizes, (alternatives index).Carrier sizes → Prop :=
  Fin.cases (fun _ _ => True) (fun _ _ _ => False)

private def selectedBranch : ∀ index sizes,
    {value // selectedPrecondition index sizes value} → (alternatives 0).Carrier sizes :=
  Fin.cases (fun _ value => value.val) (fun _ _ value => False.elim value.property)

/-- An impossible unselected branch needs no executable algorithm. -/
example : (variantCases 2 alternatives (alternatives 0) selectedPrecondition selectedBranch).Realizable := by
  apply variantCases_realizable
  intro index
  fin_cases index
  · exact copy_realizable (alternatives 0)
  · apply Realizable.ofFalsePrecondition
    intro sizes arguments valid
    exact valid

/-- An inactive alternative may even have an empty mathematical carrier. -/
example : (variantInjection 2
    ![fixed (Parameter := Bool) (Equiv.refl (Fin 0)), fixed (Equiv.refl (Fin 1))] 1).Realizable :=
  variantInjection_realizable _ _ _

example : (variantInjection 1 (fun _ => fixed (Parameter := Bool) (Equiv.refl (Fin 1))) 0).Realizable :=
  variantInjection_realizable _ _ _

/-- Empty records and empty variants require no dummy fields. -/
example : (recordConstructor (Parameter := Bool) 0 Fin.elim0).Realizable := recordConstructor_realizable _ _
example : (variantCases (Parameter := Bool) 0 Fin.elim0 booleans
    (fun index => Fin.elim0 index) (fun index => Fin.elim0 index)).Realizable :=
  variantCases_realizable _ _ _ _ _ (fun index => Fin.elim0 index)

/-- Two singleton alternatives still have distinct tags and zero-width payloads. -/
example : (variant 2 (fun _ => fixed (Parameter := Bool) (Equiv.refl (Fin 1)))).width sizes = 1 := by
  norm_num [width, Fin.sum_univ_succ, fixed, ofCodec]

/-- Sums expose ordinary alternatives, including runtime-width payloads. -/
example : (sumInl (fields 0) (fields 2)).Realizable := sumInl_realizable _ _
example : (sumInr (fields 0) (fields 2)).TM0Realizable := (sumInr_realizable _ _).tm0

example : (sumCases (booleans (Parameter := Bool)) booleans booleans
    (fun _ _ => True) (fun _ _ => False)
    (fun _ value => value.val) (fun _ value => False.elim value.property)).Realizable := by
  apply sumCases_realizable
  · exact copy_realizable _
  · apply Realizable.ofFalsePrecondition
    intro sizes arguments impossible
    exact impossible

/-- Rejection coordinates cannot decode the search sentinel, even at size zero. -/
example (length : MvPolynomial Bool ℕ) (assignment : Bool → ℕ) :
    (unaryIndex length).decode assignment
      (BoundedUnary.encode (MvPolynomial.eval assignment length)
        (Fin.last (MvPolynomial.eval assignment length))) = none := by
  simp [unaryIndex, BoundedUnary.decode_encode]

end Polytime2.Examples.Records
