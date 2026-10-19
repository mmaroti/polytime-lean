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

import Polytime2.Computation.Records
import Polytime2.Primitives.BitOperations

/-! # Runtime-width array tails and appending an element

Both operations reuse record projection and construction. They supply the queue
update used to collect results of a certified array traversal.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

namespace ArrayQueue

/-- Remove one block and append the next computed block. -/
def push {Element : Type} {length : ℕ} (queue : Fin (length + 1) → Element)
    (value : Element) : Fin (length + 1) → Element := Fin.snoc (Fin.tail queue) value

theorem ofFn_push {Element : Type} {length : ℕ} (queue : Fin (length + 1) → Element)
    (value : Element) : List.ofFn (push queue value) = (List.ofFn queue).tail ++ [value] := by
  rw [List.ofFn_succ']
  simp only [push, Fin.snoc_castSucc, Fin.snoc_last, List.concat_eq_append]
  conv_rhs => rw [List.ofFn_succ]
  rfl

/-- After a bounded traversal, the queue consists of unused seed blocks followed
by the computed results, independently of the seed contents. -/
theorem collect {Input Element : Type} {length : ℕ} (operation : Input → Element)
    (entries : List Input) (queue : Fin (length + 1) → Element)
    (bounded : entries.length ≤ length) :
    List.ofFn (entries.foldl (fun current value => push current (operation value)) queue) =
      (List.ofFn queue).drop entries.length ++ entries.map operation := by
  induction entries generalizing queue with
  | nil => simp
  | cons first rest hypothesis =>
    have restBound : rest.length ≤ length := by
      simp only [List.length_cons] at bounded
      omega
    rw [List.foldl_cons, hypothesis _ restBound, ofFn_push,
      List.drop_append_of_le_length (by simpa using restBound)]
    simp [List.append_assoc]

/-- A full traversal leaves precisely the computed results after its spare block. -/
theorem collect_tail {Input Element : Type} {length : ℕ} (operation : Input → Element)
    (entries : List Input) (queue : Fin (length + 1) → Element)
    (count : entries.length = length) :
    List.ofFn (Fin.tail (entries.foldl (fun current value => push current (operation value)) queue)) =
      entries.map operation := by
  have collected := congrArg List.tail (collect operation entries queue count.le)
  have nonempty : (List.ofFn queue).drop entries.length ≠ [] := by
    simp [List.drop_eq_nil_iff, count]
  rw [List.tail_append_of_ne_nil nonempty, List.tail_drop,
    List.drop_eq_nil_of_le (by simp [count])] at collected
  change List.ofFn (fun index =>
    entries.foldl (fun current value => push current (operation value)) queue index.succ) = _
  simpa only [List.ofFn_succ, List.tail_cons, List.nil_append] using collected

end ArrayQueue

variable {Parameter : Type} [Fintype Parameter]

/-- Normalize a polynomial successor length at the mathematical boundary. -/
noncomputable def successorValues {Element : Type} (length : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ) (values : Fin (MvPolynomial.eval sizes (length + 1)) → Element) :
    Fin (MvPolynomial.eval sizes length + 1) → Element :=
  fun index => values (Fin.cast (by simp) index)

/-- Drop the first element of a nonempty array. The remaining length may be zero. -/
noncomputable def arrayTail (element : EncodedDomain Parameter)
    (length : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  unaryMap (element.arrayOfLength (length + 1)) (element.arrayOfLength length)
    (fun _ _ => True) (fun sizes values => Fin.tail (successorValues length sizes values.val))

theorem arrayTail_realizable (element : EncodedDomain Parameter)
    (length : MvPolynomial Parameter ℕ) : (arrayTail element length).Realizable := by
  let source := element.arrayOfLength (length + 1)
  let target := element.prod (element.arrayOfLength length)
  have split : (encodingMap source target (fun sizes values => ((successorValues length sizes values) 0,
      Fin.tail (successorValues length sizes values)))).Realizable := by
    apply encodingMap_realizable
    · intro sizes
      simp [source, target, EncodedDomain.arrayOfLength,
        EncodedDomain.ofCodec, Nat.add_mul, Nat.add_comm]
    · intro sizes values
      simp only [source, target,
        EncodedDomain.arrayOfLength_encode_bits]
      simp only [EncodedDomain.ArrayEncoding.bits_encode]
      rw [List.ofFn_congr (show MvPolynomial.eval sizes (length + 1) =
        MvPolynomial.eval sizes length + 1 by simp)]
      simp [List.ofFn_succ, successorValues, Fin.tail, EncodedDomain.ArrayEncoding.bits_append,
        EncodedDomain.arrayOfLength_encode_bits, EncodedDomain.ArrayEncoding.bits_encode]
  have projected := split.followedBy (pairProjection_realizable element (element.arrayOfLength length) true)
    (by rfl) (by intros; trivial)
  exact projected.withSpecification (arrayTail element length).precondition (arrayTail element length).compute
    (by intros; trivial) (by intros; rfl)

/-- Split off the last element of a nonempty runtime-width array. -/
noncomputable def arrayUnsnoc (element : EncodedDomain Parameter)
    (length : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  encodingMap (element.arrayOfLength (length + 1)) ((element.arrayOfLength length).prod element)
    (fun sizes values =>
      ((fun index => successorValues length sizes values index.castSucc),
        successorValues length sizes values (Fin.last (MvPolynomial.eval sizes length))))

theorem arrayUnsnoc_realizable (element : EncodedDomain Parameter)
    (length : MvPolynomial Parameter ℕ) : (arrayUnsnoc element length).Realizable := by
  apply encodingMap_realizable
  · intro sizes
    simp [EncodedDomain.arrayOfLength, EncodedDomain.ofCodec, Nat.add_mul, Nat.add_comm]
  · intro sizes values
    simp only [EncodedDomain.arrayOfLength_encode_bits, EncodedDomain.ArrayEncoding.bits_encode]
    rw [List.ofFn_congr (show MvPolynomial.eval sizes (length + 1) =
      MvPolynomial.eval sizes length + 1 by simp), List.ofFn_succ']
    simp [successorValues, List.concat_eq_append, EncodedDomain.ArrayEncoding.bits_append,
      EncodedDomain.arrayOfLength_encode_bits, EncodedDomain.ArrayEncoding.bits_encode]

/-- Read the last accumulator stored by a prefix traversal. -/
noncomputable def arrayLast (element : EncodedDomain Parameter)
    (length : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  (arrayUnsnoc element length).followedBy (pairProjection (element.arrayOfLength length) element true)
    rfl (by intros; trivial)

theorem arrayLast_realizable (element : EncodedDomain Parameter)
    (length : MvPolynomial Parameter ℕ) : (arrayLast element length).Realizable :=
  (arrayUnsnoc_realizable element length).followedBy
    (pairProjection_realizable (element.arrayOfLength length) element true) rfl (by intros; trivial)

/-- Drop the final accumulator to retain the strict prefix values. -/
noncomputable def arrayInit (element : EncodedDomain Parameter)
    (length : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  (arrayUnsnoc element length).followedBy (pairProjection (element.arrayOfLength length) element false)
    rfl (by intros; trivial)

theorem arrayInit_realizable (element : EncodedDomain Parameter)
    (length : MvPolynomial Parameter ℕ) : (arrayInit element length).Realizable :=
  (arrayUnsnoc_realizable element length).followedBy
    (pairProjection_realizable (element.arrayOfLength length) element false) rfl (by intros; trivial)

/-- Append at the mathematical boundary while normalizing polynomial evaluation. -/
noncomputable def snocValues {Element : Type} (length : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ) (values : Fin (MvPolynomial.eval sizes length) → Element)
    (value : Element) : Fin (MvPolynomial.eval sizes (length + 1)) → Element :=
  fun index => Fin.snoc (α := fun _ => Element) values value (Fin.cast (by simp) index)

/-- Appending blocks and constructing the corresponding record have equal bits. -/
theorem arraySnoc_encoding (element : EncodedDomain Parameter)
    (length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (values : (element.arrayOfLength length).Carrier sizes) (value : element.Carrier sizes) :
    CallingConvention.encoded (element.arrayOfLength (length + 1)) sizes
      (snocValues length sizes values value) =
      CallingConvention.encoded ((element.arrayOfLength length).prod element) sizes (values, value) := by
  apply congrArg (fun bits => CallingConvention.buffer (Binary.word bits))
  simp only [EncodedDomain.arrayOfLength_encode_bits, EncodedDomain.ArrayEncoding.bits_encode]
  rw [List.ofFn_congr (show MvPolynomial.eval sizes (length + 1) =
    MvPolynomial.eval sizes length + 1 by simp)]
  rw [List.ofFn_succ']
  simp [snocValues, List.concat_eq_append, EncodedDomain.ArrayEncoding.bits_append,
    EncodedDomain.arrayOfLength_encode_bits, EncodedDomain.ArrayEncoding.bits_encode]

end Polytime2.Computation
