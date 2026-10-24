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

import Polytime2.Arrays.Queue
import Polytime2.Arrays.FoldContract
import Polytime2.Computation.Arguments
import Polytime2.Computation.Composition

/-! # Array transformations through certified computations

Results are collected by a fold over raw encoded blocks. All bit patterns are
valid in its private queue, so initialization does not require a default value
of the mathematical output domain.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

variable {Parameter Context : Type} [Fintype Parameter] [Fintype Context]

/-- A total element computation receives immutable context and one element. -/
noncomputable def arrayTransformStep (context : Context → EncodedDomain.{0, 0} Parameter)
    (source target : EncodedDomain.{0, 0} Parameter)
    (operation : ∀ sizes, (∀ name, (context name).Carrier sizes) → source.Carrier sizes → target.Carrier sizes) :
    Computation Parameter (Context ⊕ Unit) where
  inputDomains := Sum.elim context (fun _ => source)
  outputDomain := target
  precondition _ _ := True
  compute sizes values := operation sizes (fun name => values.val (.inl name)) (values.val (.inr ()))

/-- Transform every element, allowing different runtime-dependent domain widths. -/
noncomputable def arrayTransform (context : Context → EncodedDomain.{0, 0} Parameter)
    (source target : EncodedDomain.{0, 0} Parameter) (length : MvPolynomial Parameter ℕ)
    (operation : ∀ sizes, (∀ name, (context name).Carrier sizes) → source.Carrier sizes → target.Carrier sizes) :
    Computation Parameter (Context ⊕ Unit) where
  inputDomains := Sum.elim context (fun _ => source.arrayOfLength length)
  outputDomain := target.arrayOfLength length
  precondition _ _ := True
  compute sizes values := fun index => operation sizes (fun name => values.val (.inl name)) (values.val (.inr ()) index)

namespace ArrayTransform

/-- One queue update retains raw blocks and appends the new canonical encoding. -/
noncomputable def update (target : EncodedDomain.{0, 0} Parameter) (length : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (queue : ((EncodedDomain.bitVectors target.widthPolynomial).arrayOfLength (length + 1)).Carrier sizes)
    (value : target.Carrier sizes) :=
  snocValues length sizes (Fin.tail (successorValues length sizes queue)) (target.encode sizes value)

/-- The spare queue block makes the collected answer independent of its seed. -/
theorem collected (target : EncodedDomain.{0, 0} Parameter) (length : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ) {Input : Type}
    (operation : Input → target.Carrier sizes)
    (array : Fin (MvPolynomial.eval sizes length) → Input)
    (seed : ((EncodedDomain.bitVectors target.widthPolynomial).arrayOfLength (length + 1)).Carrier sizes) :
    Fin.tail (successorValues length sizes (ArrayFold.prefixValue
      (fun queue value => update target length sizes queue (operation value)) array seed
      (MvPolynomial.eval sizes length))) = fun index => target.encode sizes (operation (array index)) := by
  let normalize := successorValues (Element := BitVec (target.width sizes)) length sizes
  let encode := fun value => target.encode sizes (operation value)
  have commutes := List.foldl_hom normalize
    (g₁ := fun queue value => update target length sizes queue (operation value))
    (g₂ := fun queue value => ArrayQueue.push queue (encode value))
    (l := List.ofFn array) (init := seed) (by
      intro queue value
      funext index
      simp [normalize, update, snocValues, successorValues, ArrayQueue.push, encode])
  apply List.ofFn_injective
  unfold ArrayFold.prefixValue
  rw [List.take_of_length_le (by simp)]
  change List.ofFn (Fin.tail (normalize _)) = _
  rw [← commutes]
  simpa [encode, Function.comp_def] using ArrayQueue.collect_tail encode (List.ofFn array) (normalize seed) (by simp)

/-- The collector is built entirely from public composition and record rules. -/
theorem update_realizable
    (context : Context → EncodedDomain.{0, 0} Parameter) (source target : EncodedDomain.{0, 0} Parameter)
    (length : MvPolynomial Parameter ℕ)
    (operation : ∀ sizes, (∀ name, (context name).Carrier sizes) → source.Carrier sizes → target.Carrier sizes)
    (step : (arrayTransformStep context source target operation).Realizable) :
    (arrayFoldStep context source ((EncodedDomain.bitVectors target.widthPolynomial).arrayOfLength (length + 1))
      (fun _ _ _ _ => True) (fun sizes values queue value => update target length sizes queue (operation sizes values value))).Realizable := by
  let raw := EncodedDomain.bitVectors target.widthPolynomial
  let queue := raw.arrayOfLength (length + 1)
  let inputs : Context ⊕ Bool → EncodedDomain.{0, 0} Parameter := Sum.elim context (fun choice => if choice then source else queue)
  let selection : Context ⊕ Unit ↪ Context ⊕ Bool :=
    ⟨Sum.map id (fun _ => true), by
      rintro (first | first) (second | second) equal <;> simp_all⟩
  have computed := step.withArguments inputs selection (by rintro (name | name); rfl; cases name; rfl)
  have encoded := computed.followedBy (encode_realizable target) (by rfl) (by intros; trivial)
  have tail := (arrayTail_realizable raw length).withArguments inputs
    ⟨(fun _ => .inr false), by intro first second _; cases first; cases second; rfl⟩
    (by intro name; cases name; rfl)
  exact (tail.prodMk (left := raw.arrayOfLength length) (right := raw) encoded).reinterpretOutput queue
    (fun sizes parts => snocValues length sizes parts.1 parts.2)
    (by intro sizes; simp [queue, raw, EncodedDomain.arrayOfLength, EncodedDomain.ofCodec, Nat.add_mul])
    (fun sizes parts => arraySnoc_encode_bits raw length sizes _ _)

end ArrayTransform

/-- A certified total element computation lifts to runtime arrays. The collector
uses existing folds and record operations, without exposing machine witnesses. -/
theorem arrayTransform_realizable
    (context : Context → EncodedDomain.{0, 0} Parameter) (source target : EncodedDomain.{0, 0} Parameter)
    (length : MvPolynomial Parameter ℕ)
    (operation : ∀ sizes, (∀ name, (context name).Carrier sizes) → source.Carrier sizes → target.Carrier sizes)
    (step : (arrayTransformStep context source target operation).Realizable) :
    (arrayTransform context source target length operation).Realizable := by
  let computation := arrayTransform context source target length operation
  let raw := EncodedDomain.bitVectors target.widthPolynomial
  let queue := raw.arrayOfLength (length + 1)
  have allocated := zeroBitArray_realizable target.widthPolynomial (length + 1)
  have seed := allocated.withArguments computation.inputDomains
    ⟨Empty.elim, by intro impossible; exact impossible.elim⟩ (by intro impossible; exact impossible.elim)
  let domains : (Context ⊕ Unit) ⊕ Unit → EncodedDomain.{0, 0} Parameter :=
    Sum.elim computation.inputDomains (fun _ => queue)
  let selection : Context ⊕ Bool ↪ (Context ⊕ Unit) ⊕ Unit :=
    ⟨(fun name => match name with
      | .inl name => .inl (.inl name)
      | .inr false => .inr ()
      | .inr true => .inl (.inr ())), by
      rintro (name | first) (name' | second) equal
      all_goals try cases first
      all_goals try cases second
      all_goals simp_all⟩
  have fold := (arrayFold_total_realizable context source queue length
    (fun sizes values queue value => ArrayTransform.update target length sizes queue (operation sizes values value))
    (ArrayTransform.update_realizable context source target length operation step)).withArguments
      domains selection (by rintro (name | choice); rfl; cases choice <;> rfl)
  have collected := seed.letThen fold (fun _ => rfl) rfl (by intros; trivial)
  have tail := collected.followedBy (arrayTail_realizable raw length) (by rfl) (by intros; trivial)
  have result := tail.withEncodedOutput computation.outputDomain
    (fun sizes arguments => computation.compute sizes ⟨arguments.val, trivial⟩)
    (by intro sizes; rfl) (by
      intro sizes arguments
      change CallingConvention.encoded (target.arrayOfLength length) sizes
        (fun index => operation sizes (fun name => arguments.val (.inl name)) (arguments.val (.inr ()) index)) =
        CallingConvention.encoded (raw.arrayOfLength length) sizes
          (Fin.tail (successorValues length sizes (ArrayFold.prefixValue
            (fun queue value => ArrayTransform.update target length sizes queue
              (operation sizes (fun name => arguments.val (.inl name)) value))
            (arguments.val (.inr ())) (fun _ => 0) (MvPolynomial.eval sizes length))))
      rw [ArrayTransform.collected]
      apply congrArg (fun bits => CallingConvention.buffer (Binary.word bits))
      simp [raw, EncodedDomain.arrayOfLength_encode_bits, EncodedDomain.ArrayEncoding.bits_encode])
  exact result

/-- Lift a total unary computation to an array without an immutable context. -/
noncomputable def mapArray (source target : EncodedDomain.{0, 0} Parameter)
    (length : MvPolynomial Parameter ℕ)
    (operation : ∀ sizes, source.Carrier sizes → target.Carrier sizes) : Computation Parameter Unit where
  inputDomains _ := source.arrayOfLength length
  outputDomain := target.arrayOfLength length
  precondition _ _ := True
  compute sizes arguments := fun index => operation sizes (arguments.val () index)

theorem mapArray_realizable (source target : EncodedDomain.{0, 0} Parameter)
    (length : MvPolynomial Parameter ℕ)
    (operation : ∀ sizes, source.Carrier sizes → target.Carrier sizes)
    (step : (unaryMap source target (fun _ _ => True) (fun sizes value => operation sizes value.val)).Realizable) :
    (mapArray source target length operation).Realizable := by
  have selected := step.withArguments
    (arrayTransformStep Empty.elim source target (fun sizes _ value => operation sizes value)).inputDomains
    ⟨Sum.inr, Sum.inr_injective⟩ (by intro name; cases name; rfl)
  have mapped := arrayTransform_realizable Empty.elim source target length (fun sizes _ value => operation sizes value) selected
  exact mapped.withArguments (mapArray source target length operation).inputDomains
    ⟨Sum.elim Empty.elim id, by
      rintro (impossible | first) (impossible' | second) equal
      all_goals first | exact impossible.elim | exact impossible'.elim | exact congrArg Sum.inr equal⟩
    (by rintro (impossible | name); exact impossible.elim; cases name; rfl)

end Polytime2.Computation
