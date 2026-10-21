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

import Polytime2.Computation.Fields
import Polytime2.Primitives.Join
import Polytime2.Computation.Reindex
import Polytime2.Computation.Composition

/-! # Mathematical record operations with hidden tape implementations -/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

universe carrierLevel
variable {Parameter : Type} [Fintype Parameter]

/-- Projection takes one record tape and returns its selected coordinate. -/
noncomputable def recordProjection (count : ℕ)
    (fields : Fin count → EncodedDomain.{0, carrierLevel} Parameter) (index : Fin count) :
    Computation Parameter Unit :=
  unaryMap (EncodedDomain.record count fields) (fields index) (fun _ _ => True)
    (fun _ value => value.val index)

theorem recordProjection_realizable (count : ℕ)
    (fields : Fin count → EncodedDomain.{0, carrierLevel} Parameter) (index : Fin count) :
    (recordProjection count fields index).Realizable :=
  Realizable.Internal.fieldProjection _ _ (EncodedDomain.recordOffset count fields index)
    _ _ (fun sizes value => EncodedDomain.split_record_encode count fields sizes value.val index)

/-- Construct a record from one immutable input tape per coordinate. -/
noncomputable def recordConstructor (count : ℕ)
    (fields : Fin count → EncodedDomain.{0, carrierLevel} Parameter) : Computation Parameter (Fin count) where
  inputDomains := fields
  outputDomain := EncodedDomain.record count fields
  precondition _ _ := True
  compute _ values := values.val

open MultiTape CallingConvention Realizable.Internal in
/-- Construction accepts arbitrary output contents, including for empty records. -/
theorem recordConstructor_realizable (count : ℕ)
    (fields : Fin count → EncodedDomain.{0, carrierLevel} Parameter) :
    (recordConstructor count fields).Realizable := by
  classical
  let computation := recordConstructor count fields
  let domains : Parameter ⊕ Join.TapeName count → EncodedDomain.{0, carrierLevel} Parameter :=
    Sum.elim EncodedDomain.unary (Sum.elim fields (fun _ => EncodedDomain.record count fields))
  let readOnly : Parameter ⊕ Join.TapeName count → Bool := Sum.elim (fun _ => true) Join.readOnly
  let sizes : Parameter ↪ Parameter ⊕ Join.TapeName count := ⟨Sum.inl, Sum.inl_injective⟩
  let data : Join.TapeName count ↪ Parameter ⊕ Join.TapeName count := ⟨Sum.inr, Sum.inr_injective⟩
  let outputs : Unit ↪ Parameter ⊕ Join.TapeName count := oneTape (.inr (.inr ()))
  let algorithm := wire (Alphabet := Alphabet (Parameter ⊕ Join.TapeName count)) data Join.machine
  have certificate : CallingConvention.Realizes domains readOnly sizes outputs algorithm Join.entry Join.exit
      (fun _ _ => True)
      (fun assignment input output => output () = fun index => input ⟨.inr (.inl index), rfl⟩) := by
    refine ⟨(by intro parameter; rfl), (by intro name; rfl),
      (by intro symbols; simp [algorithm, wire, Join.halt]),
      count * (2 * computation.outputDomain.widthPolynomial + 6) +
        computation.outputDomain.widthPolynomial + 4, ?_⟩
    intro assignment input initial valid represented headers
    let values := fun index => input ⟨.inr (.inl index), rfl⟩
    let words := fun index => EncodedDomain.ArrayEncoding.bits ((fields index).encode assignment (values index))
    have joined := EncodedDomain.bits_record_encode count fields assignment values
    have totalLength : (List.ofFn words).flatten.length = computation.outputDomain.width assignment := by
      rw [← joined]
      exact List.length_ofFn
    obtain ⟨old, oldLength, oldEq⟩ := represented.2 (.inr (.inr ())) rfl
    obtain ⟨ticks, cost, localTrace⟩ := Join.runs words old (oldLength.trans totalLength.symm)
    let result : Tapes (Alphabet (Join.TapeName count)) :=
      Sum.elim (fun index => encoded (fields index) assignment (values index))
        (fun _ => encoded computation.outputDomain assignment values)
    have localWidths : ∀ name, (domains (data name)).width assignment = Join.widths words name := by
      intro name
      cases name with
      | inl index => exact (List.length_ofFn).symm
      | inr name => exact totalLength.symm
    have trace := localTrace.wire_at_of_eq data (fun name => (domains name).width assignment) readOnly
      localWidths (by intro name premise; exact premise)
      (fun _ => 0) (fun _ => 0) initial (install data result initial)
      (by intro name; rfl) (by intro name; rfl) (by intros; rfl)
      (by
        intro name
        cases name with
        | inl index => exact represented.1 (.inr (.inl index)) rfl
        | inr name => cases name; exact oldEq)
      (by
        intro name
        rw [install_at]
        cases name with
        | inl index => rfl
        | inr name => cases name; exact congrArg (fun bits => buffer (Binary.word bits)) joined)
      (by intro name outside; exact install_outside _ _ _ _ outside)
    refine ⟨ticks, (fun _ => values), _, ?_, trace, rfl, ?_⟩
    · simpa only [map_add, map_mul, map_ofNat, map_natCast, Nat.cast_id,
        ← totalLength] using cost
    · intro name; cases name; exact install_at data _ initial (.inr ())
  refine ofNamedLayout computation domains readOnly sizes outputs algorithm Join.entry Join.exit _ _
    certificate (Function.Embedding.refl _)
    (by rintro (parameter | argument | result); all_goals rfl)
    (by rintro (parameter | argument | result); all_goals rfl)
    (by intro name outside; exact False.elim (outside ⟨name, rfl⟩))
    (by intro parameter; rfl) () rfl (by intros; trivial) ?_
  intro assignment input valid output correct
  exact congrArg (encoded computation.outputDomain assignment) correct

/-- Project either coordinate of the ordinary pair carrier. -/
noncomputable def pairProjection (left right : EncodedDomain.{0, carrierLevel} Parameter)
    (second : Bool) : Computation Parameter Unit :=
  if second then unaryMap (left.prod right) right (fun _ _ => True) (fun _ value => value.val.2)
  else unaryMap (left.prod right) left (fun _ _ => True) (fun _ value => value.val.1)

theorem pairProjection_realizable (left right : EncodedDomain.{0, carrierLevel} Parameter)
    (second : Bool) : (pairProjection left right second).Realizable := by
  cases second with
  | false =>
    change (unaryMap (left.prod right) left (fun _ _ => True) (fun _ value => value.val.1)).Realizable
    apply Realizable.Internal.fieldProjection _ _ 0
    intro sizes value
    exact ⟨[], EncodedDomain.ArrayEncoding.bits (right.encode sizes value.val.2),
      by simp [EncodedDomain.ArrayEncoding.bits_append], by simp⟩
  | true =>
    change (unaryMap (left.prod right) right (fun _ _ => True) (fun _ value => value.val.2)).Realizable
    apply Realizable.Internal.fieldProjection _ _ left.widthPolynomial
    intro sizes value
    exact ⟨EncodedDomain.ArrayEncoding.bits (left.encode sizes value.val.1), [],
      by simp [EncodedDomain.ArrayEncoding.bits_append], by simp⟩

/-- Binary construction retains the ordinary pair carrier. -/
noncomputable def pairConstructor
    (left right : EncodedDomain.{0, carrierLevel} Parameter) : Computation Parameter (Fin 2) where
  inputDomains := ![left, right]
  outputDomain := left.prod right
  precondition _ _ := True
  compute _ values := (values.val 0, values.val 1)

theorem pairConstructor_realizable
    (left right : EncodedDomain.{0, carrierLevel} Parameter) :
    (pairConstructor left right).Realizable := by
  refine (recordConstructor_realizable 2 ![left, right]).reinterpretOutput (left.prod right)
    (fun _ values => (values 0, values 1)) ?_ ?_
  · intro sizes
    simp [recordConstructor, EncodedDomain.width, Fin.sum_univ_succ]
  · intro sizes values
    change EncodedDomain.ArrayEncoding.bits ((left.prod right).encode sizes (values 0, values 1)) =
      EncodedDomain.ArrayEncoding.bits ((EncodedDomain.record 2 ![left, right]).encode sizes values)
    exact (EncodedDomain.bits_prod_encode left right sizes _).trans (by
      simpa [List.ofFn_succ] using
        (EncodedDomain.bits_record_encode 2 ![left, right] sizes values).symm)

/-- Collect two certified results from the same immutable arguments. -/
theorem Realizable.pairOutputs {InputName : Type} [Fintype InputName]
    (inputDomains : InputName → EncodedDomain.{0, carrierLevel} Parameter)
    (left right : EncodedDomain.{0, carrierLevel} Parameter)
    (precondition : ∀ sizes, ((name : InputName) → (inputDomains name).Carrier sizes) → Prop)
    (first : ∀ sizes, {arguments // precondition sizes arguments} → left.Carrier sizes)
    (second : ∀ sizes, {arguments // precondition sizes arguments} → right.Carrier sizes)
    (firstRealizable : (Computation.mk inputDomains left precondition first).Realizable)
    (secondRealizable : (Computation.mk inputDomains right precondition second).Realizable) :
    (Computation.mk inputDomains (left.prod right) precondition
      (fun sizes arguments => (first sizes arguments, second sizes arguments))).Realizable := by
  classical
  let firstComputation := Computation.mk inputDomains left precondition first
  let secondComputation := Computation.mk inputDomains right precondition second
  let context := Sum.elim inputDomains (fun _ : Unit => left)
  let contextSecond := secondComputation.withArguments context
    ⟨Sum.inl, Sum.inl_injective⟩ (fun _ => rfl)
  let finalContext := Sum.elim context (fun _ : Unit => right)
  let selection : Fin 2 ↪ (InputName ⊕ Unit) ⊕ Unit :=
    ⟨(fun name => if name = 0 then .inl (.inr ()) else .inr ()), by
      intro a b equal; fin_cases a <;> fin_cases b <;> simp_all⟩
  have selected : ∀ name, finalContext (selection name) = (pairConstructor left right).inputDomains name := by
    intro name; fin_cases name <;> rfl
  let finish := (pairConstructor left right).withArguments finalContext selection selected
  have finishRealizable := (pairConstructor_realizable left right).withArguments finalContext selection selected
  have secondContextRealizable := secondRealizable.withArguments context
    ⟨Sum.inl, Sum.inl_injective⟩ (fun _ => rfl)
  have continuation := secondContextRealizable.letThen finishRealizable
    (fun _ => rfl) rfl (by intros; trivial)
  have complete := firstRealizable.letThen continuation (fun _ => rfl) rfl (by intros; assumption)
  exact complete

/-- Assemble any finite family of results, sharing the same immutable inputs. -/
theorem Realizable.recordOutputs {InputName : Type} [Fintype InputName]
    (inputDomains : InputName → EncodedDomain.{0, carrierLevel} Parameter)
    (count : ℕ) (fields : Fin count → EncodedDomain.{0, carrierLevel} Parameter)
    (precondition : ∀ sizes, ((name : InputName) → (inputDomains name).Carrier sizes) → Prop)
    (results : ∀ index sizes, {arguments // precondition sizes arguments} → (fields index).Carrier sizes)
    (realizable : ∀ index, (Computation.mk inputDomains (fields index) precondition (results index)).Realizable) :
    (Computation.mk inputDomains (EncodedDomain.record count fields) precondition
      (fun sizes arguments index => results index sizes arguments)).Realizable := by
  classical
  induction count with
  | zero =>
    have empty := (recordConstructor_realizable 0 fields).withArguments inputDomains
      ⟨Fin.elim0, by intro index; exact Fin.elim0 index⟩ (fun index => Fin.elim0 index)
    exact empty.withSpecification precondition (fun sizes arguments index => results index sizes arguments)
      (by intros; trivial) (by intros; funext index; exact Fin.elim0 index)
  | succ count hypothesis =>
    have tail := hypothesis (Fin.tail fields) (fun index => results index.succ) (fun index => realizable index.succ)
    have pair := Realizable.pairOutputs inputDomains (fields 0) (EncodedDomain.record count (Fin.tail fields))
      precondition (results 0) (fun sizes arguments index => results index.succ sizes arguments) (realizable 0) tail
    have combined := pair.reinterpretOutput (EncodedDomain.record (count + 1) fields)
      (fun _ values => Fin.cons values.1 values.2) (fun _ => rfl) (by intros; rfl)
    exact combined.withSpecification precondition _ (by intros; assumption) (by
      intro sizes arguments valid
      funext index
      exact Fin.cases rfl (fun _ => rfl) index)

end Polytime2.Computation
