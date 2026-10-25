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

import Polytime2.Arrays.PackingCall
import Polytime2.TM0.Computation

/-! # Stable packing with exact arrays, shared indices, and computed-size calls -/

namespace Polytime2.Examples.Packing

open _root_.Polytime2.Computation EncodedDomain ArrayPacking

variable {Parameter : Type} [Fintype Parameter]

example (element : EncodedDomain Parameter) (length : MvPolynomial Parameter ℕ) :
    (arrayPack element length).TM0Realizable := (arrayPack_realizable element length).tm0

/-- Both the number of blocks and their widths depend on runtime sizes. -/
example : (arrayPack (bitVectors (MvPolynomial.X () : MvPolynomial Unit ℕ))
    ((MvPolynomial.X ()) ^ 2)).TM0Realizable := (arrayPack_realizable _ _).tm0

/-- A coordinate can hold related fields and a nested runtime-sized array.
Packing uses one selection and count for all fields. -/
example : (arrayPack
    ((bitVectors (MvPolynomial.X (0 : Fin 2))).prod
      ((bitVectors (MvPolynomial.X 1)).arrayOfLength (MvPolynomial.X 0 + MvPolynomial.X 1)))
    (MvPolynomial.X 0)).TM0Realizable := (arrayPack_realizable _ _).tm0

/-- Empty element domains need no padding element when the source is empty. -/
example : (arrayPack ((EncodedDomain.fixed (Parameter := Empty) (Equiv.refl (Fin 0))).constant :
    EncodedDomain Unit) 0).TM0Realizable := (arrayPack_realizable _ _).tm0

/-- Zero-width elements still retain their logical multiplicity and indices. -/
example : (arrayPack (bitVectors (0 : MvPolynomial Unit ℕ)) (MvPolynomial.X ())).TM0Realizable :=
  (arrayPack_realizable _ _).tm0

example (element : EncodedDomain Parameter) (length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (values : (element.arrayOfLength length).Carrier sizes) :
    ((arrayPack element length).compute sizes
      ⟨(fun | false => fun _ => false | true => values), trivial⟩).1.val = 0 := by
  rw [arrayPack_compute]
  exact count_all_false

example (element : EncodedDomain Parameter) (length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (values : (element.arrayOfLength length).Carrier sizes) :
    ((arrayPack element length).compute sizes
      ⟨(fun | false => fun _ => true | true => values), trivial⟩).1.val = MvPolynomial.eval sizes length := by
  rw [arrayPack_compute]
  exact count_all_true

example : count ![true, false, true, false] = 2 := by decide

example : (rank ![true, false, true, false] ⟨(2 : Fin 4), by decide⟩).val = 1 := by
  rw [← prefix_count_rank]
  decide

example : pack ![true, false, true, false] ![7, 10, 3, 13]
    (rank ![true, false, true, false] ⟨(2 : Fin 4), by decide⟩) = 3 :=
  pack_rank _ _ _

/-- Paired source data and dependency indices use exactly the same dense map. -/
example {length : ℕ} (flags : Fin length → Bool) (values : Fin length → ℕ)
    (dependencies : Fin length → Fin length) :
    pack flags (fun index => (values index, dependencies index)) =
      fun position => (pack flags values position, pack flags dependencies position) :=
  pack_pair flags values dependencies

/-- Selected dependency references are translated to the same dense indices
before or after packing their containing coordinate records. -/
example {length : ℕ} (flags : Fin length → Bool)
    (dependencies : Fin length → {index : Fin length // flags index = true}) :
    pack flags (fun index => rank flags (dependencies index)) =
      fun position => rank flags (dependencies (selection flags position).val) :=
  pack_map flags dependencies (rank flags)

example (element : EncodedDomain Parameter) (length : MvPolynomial Parameter ℕ) :
    (arrayPackWithPositions element length).TM0Realizable :=
  (arrayPackWithPositions_realizable element length).tm0

/-- A stored packed result can be consumed without the original mask or array
and without repeating the packing algorithm. -/
noncomputable def copyPackedValue (element : EncodedDomain Parameter) (length : MvPolynomial Parameter ℕ) :
    Computation Parameter Unit :=
  (boundedArrayCallFrame element length).followedBy
    ((copy (packingPayload element)).atComputedSizes (packingCallBounds length)) rfl (by intros; trivial)

theorem copyPackedValue_realizable (element : EncodedDomain Parameter) (length : MvPolynomial Parameter ℕ) :
    (copyPackedValue element length).Realizable :=
  (boundedArrayCallFrame_realizable element length).followedBy
    ((copy_realizable (packingPayload element)).atComputedSizes (packingCallBounds length))
    rfl (by intros; trivial)

example (element : EncodedDomain Parameter) (length : MvPolynomial Parameter ℕ) :
    (copyPackedValue element length).TM0Realizable := (copyPackedValue_realizable element length).tm0

example (element : EncodedDomain Parameter) (length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (copyPackedValue element length).Arguments sizes) :
    ((copyPackedValue element length).compute sizes ⟨arguments, trivial⟩).2 = (arguments ()).2 := rfl

example (element : EncodedDomain Parameter) (length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (value : (boundedArray element length).Carrier sizes) :
    (boundedArray element length).decode sizes ((boundedArray element length).encode sizes value) = some value :=
  (boundedArray element length).decode_encode sizes value

/-- Invoke an ordinary exact-array consumer at the retained count. Preparation
and execution both use public certificates; no machine witnesses are exposed. -/
noncomputable def packedCopy (element : EncodedDomain Parameter) (length : MvPolynomial Parameter ℕ) :
    Computation Parameter Bool :=
  (preparePackingCall element length).followedBy
    ((copy (packingPayload element)).atComputedSizes (packingCallBounds length)) rfl (by intros; trivial)

theorem packedCopy_realizable (element : EncodedDomain Parameter) (length : MvPolynomial Parameter ℕ) :
    (packedCopy element length).Realizable :=
  (preparePackingCall_realizable element length).followedBy
    ((copy_realizable (packingPayload element)).atComputedSizes (packingCallBounds length))
    rfl (by intros; trivial)

example (element : EncodedDomain Parameter) (length : MvPolynomial Parameter ℕ) :
    (packedCopy element length).TM0Realizable := (packedCopy_realizable element length).tm0

example (element : EncodedDomain Parameter) (length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (packedCopy element length).Arguments sizes) :
    ((packedCopy element length).compute sizes ⟨arguments, trivial⟩).2 =
      pack (arguments false) (arguments true) := rfl

example (element : EncodedDomain Parameter) (length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (packedCopy element length).Arguments sizes) :
    (((packedCopy element length).compute sizes ⟨arguments, trivial⟩).1 (.inr ())).val =
      count (arguments false) := rfl

end Polytime2.Examples.Packing
