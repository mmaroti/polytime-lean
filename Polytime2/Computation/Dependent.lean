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

import Polytime2.Encoding.Dependent
import Polytime2.Computation.Records
import Polytime2.Primitives.BitOperations

/-! # Certified access to bounded dependent call frames

These operations expose the stored index and zero-padded payload through the
ordinary mathematical interface. Runtime-dependent payload interpretation
remains in the dependent pair, not in a new representation structure.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

variable {Parameter NewParameter Name : Type}
variable [Fintype Parameter] [Fintype NewParameter] [Fintype Name]

/-- Project a named field through the existing finite record implementation. -/
noncomputable def namedRecordProjection (fields : Name → EncodedDomain Parameter) (name : Name) :
    Computation Parameter Unit :=
  unaryMap (EncodedDomain.namedRecord fields) (fields name) (fun _ _ => True)
    (fun _ values => values.val name)

/-- Names affect only the specialization's field order. -/
theorem namedRecordProjection_realizable (fields : Name → EncodedDomain Parameter) (name : Name) :
    (namedRecordProjection fields name).Realizable := by
  let enumeration := Fintype.equivFin Name
  obtain ⟨position, rfl⟩ := enumeration.symm.surjective name
  apply Realizable.Internal.fieldProjection _ _
    (EncodedDomain.recordOffset (Fintype.card Name)
      (fun index => fields (enumeration.symm index)) position)
  intro sizes values
  let sourceValues := (Equiv.piCongrLeft (fun name => (fields name).Carrier sizes)
    enumeration.symm).symm values.val
  obtain ⟨before, after, split, length⟩ :=
    EncodedDomain.split_record_encode (Fintype.card Name)
      (fun index => fields (enumeration.symm index)) sizes sourceValues position
  refine ⟨before, after, ?_, length⟩
  change EncodedDomain.ArrayEncoding.bits
    ((EncodedDomain.record (Fintype.card Name)
      (fun index => fields (enumeration.symm index))).encode sizes sourceValues) = _
  simpa only [sourceValues, Equiv.piCongrLeft_symm_apply] using split

section BoundedPairs

variable (index : EncodedDomain Parameter)
variable (assignment : ∀ sizes, index.Carrier sizes → NewParameter → ℕ)
variable (payload : EncodedDomain NewParameter) (capacity : MvPolynomial Parameter ℕ)
variable (fits : ∀ sizes value, payload.width (assignment sizes value) ≤ MvPolynomial.eval sizes capacity)

/-- The canonical storage view is an ordinary pair of index and padded bits. -/
noncomputable def boundedSigmaStorage : Computation Parameter Unit :=
  encodingMap (EncodedDomain.boundedSigma index assignment payload capacity fits)
    (index.prod (EncodedDomain.bitVectors capacity))
    (fun sizes value => (value.1,
      (payload.encode (assignment sizes value.1) value.2).setWidth (MvPolynomial.eval sizes capacity)))

theorem boundedSigmaStorage_realizable :
    (boundedSigmaStorage index assignment payload capacity fits).Realizable :=
  encodingMap_realizable _ _ _ (fun _ => rfl) (fun _ _ => rfl)

/-- Read the size record without interpreting or inspecting the payload. -/
noncomputable def boundedSigmaIndex : Computation Parameter Unit :=
  (boundedSigmaStorage index assignment payload capacity fits).followedBy
    (pairProjection index (EncodedDomain.bitVectors capacity) false) rfl (by intros; trivial)

theorem boundedSigmaIndex_realizable :
    (boundedSigmaIndex index assignment payload capacity fits).Realizable :=
  (boundedSigmaStorage_realizable index assignment payload capacity fits).followedBy
    (pairProjection_realizable _ _ false) rfl (by intros; trivial)

/-- Read the padded payload as a fixed-capacity binary word. -/
noncomputable def boundedSigmaPayload : Computation Parameter Unit :=
  (boundedSigmaStorage index assignment payload capacity fits).followedBy
    (pairProjection index (EncodedDomain.bitVectors capacity) true) rfl (by intros; trivial)

theorem boundedSigmaPayload_realizable :
    (boundedSigmaPayload index assignment payload capacity fits).Realizable :=
  (boundedSigmaStorage_realizable index assignment payload capacity fits).followedBy
    (pairProjection_realizable _ _ true) rfl (by intros; trivial)

end BoundedPairs

end Polytime2.Computation
