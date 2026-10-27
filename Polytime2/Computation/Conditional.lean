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

import Polytime2.Computation.RecordArguments
import Polytime2.Computation.Branch
import Polytime2.Arithmetic.CounterOperations

/-! # Conditional results on a shared mathematical context -/

namespace Polytime2.Computation.Realizable

variable {Parameter InputName : Type} [Fintype Parameter] [Fintype InputName]

/-- Certify one mathematical computation by a runtime case split. Only the
selected branch needs its guard hypothesis; the common precondition is retained. -/
theorem ofCases {computation : Computation Parameter InputName}
    (condition : ∀ sizes, computation.Arguments sizes → Bool)
    (guardReady : (Computation.mk computation.inputDomains EncodedDomain.booleans computation.precondition
      (fun sizes arguments => condition sizes arguments.val)).Realizable)
    (whenTrue : (computation.withPrecondition
      (fun sizes arguments => computation.precondition sizes arguments ∧ condition sizes arguments = true)
      (fun _ _ valid => valid.1)).Realizable)
    (whenFalse : (computation.withPrecondition
      (fun sizes arguments => computation.precondition sizes arguments ∧ condition sizes arguments = false)
      (fun _ _ valid => valid.1)).Realizable) : computation.Realizable := by
  let first := computation.withPrecondition
    (fun sizes arguments => computation.precondition sizes arguments ∧ condition sizes arguments = true)
    (fun _ _ valid => valid.1)
  let second := computation.withPrecondition
    (fun sizes arguments => computation.precondition sizes arguments ∧ condition sizes arguments = false)
    (fun _ _ valid => valid.1)
  let choice := first.choose second (fun _ => rfl) rfl
  let values (name : InputName ⊕ Unit) sizes
      (arguments : {arguments : computation.Arguments sizes // computation.precondition sizes arguments}) :
      (choice.inputDomains name).Carrier sizes := match name with
    | .inl original => arguments.val original
    | .inr () => condition sizes arguments.val
  have valid sizes arguments : choice.precondition sizes (fun name => values name sizes arguments) := by
    cases selected : condition sizes arguments.val <;>
      simpa [choice, first, second, Computation.choose, Computation.withPrecondition, values, selected]
        using And.intro arguments.property selected
  have complete := (whenTrue.choose whenFalse (fun _ => rfl) rfl).onResults computation.inputDomains
    computation.precondition values valid (by
      intro name
      cases name with
      | inl original => exact argument computation.inputDomains original computation.precondition
      | inr singleton => cases singleton; exact guardReady)
  apply complete.withSpecification computation.precondition computation.compute (by intros; assumption)
  intro sizes arguments accepted
  dsimp only [Computation.onResults, Computation.choose, Computation.withPrecondition, values]
  split <;> rfl

/-- A certified Boolean selects between two certified results on the same
context. The enclosing precondition permits either branch. -/
theorem conditional (inputs : InputName → EncodedDomain Parameter) (output : EncodedDomain Parameter)
    (allowed : ∀ sizes, (∀ name, (inputs name).Carrier sizes) → Prop)
    (condition : ∀ sizes, {arguments // allowed sizes arguments} → Bool)
    (first second : ∀ sizes, {arguments // allowed sizes arguments} → output.Carrier sizes)
    (conditionReady : (Computation.mk inputs EncodedDomain.booleans allowed condition).Realizable)
    (firstReady : (Computation.mk inputs output allowed first).Realizable)
    (secondReady : (Computation.mk inputs output allowed second).Realizable) :
    (Computation.mk inputs output allowed
      (fun sizes arguments => if condition sizes arguments then first sizes arguments else second sizes arguments)).Realizable := by
  let choice := (Computation.mk inputs output allowed first).choose
    (Computation.mk inputs output allowed second) (fun _ => rfl) rfl
  let values (name : InputName ⊕ Unit) sizes
      (arguments : {arguments : ∀ name, (inputs name).Carrier sizes // allowed sizes arguments}) :
      (choice.inputDomains name).Carrier sizes :=
    match name with
    | .inl name => arguments.val name
    | .inr _ => condition sizes arguments
  have valid sizes arguments : choice.precondition sizes (fun name => values name sizes arguments) := by
    cases selected : condition sizes arguments <;>
      simpa [choice, Computation.choose, values, selected] using arguments.property
  have producers name : (Computation.mk inputs (choice.inputDomains name) allowed (values name)).Realizable := by
    cases name with
    | inl name => exact argument inputs name allowed
    | inr name => cases name; exact conditionReady
  have complete := (firstReady.choose secondReady (fun _ => rfl) rfl).onResults inputs allowed values valid producers
  apply complete.withSpecification allowed _ (by intros; assumption)
  intro sizes arguments good
  change (choice.compute sizes ⟨(fun name => values name sizes ⟨arguments, good⟩), valid sizes ⟨arguments, good⟩⟩) = _
  cases selected : condition sizes ⟨arguments, good⟩ with
  | false =>
    calc
      _ = second sizes ⟨arguments, good⟩ := by simp [choice, Computation.choose, values, selected]
      _ = _ := (ite_eq_right (fun positive => Bool.noConfusion (selected.symm.trans positive))).symm
  | true =>
    calc
      _ = first sizes ⟨arguments, good⟩ := by simp [choice, Computation.choose, values, selected]
      _ = _ := (ite_eq_left selected).symm

end Polytime2.Computation.Realizable

namespace Polytime2.Computation

variable {Parameter InputName : Type} [Fintype Parameter] [Fintype InputName]

/-- Run a partial consumer behind a guard, returning a supplied result on
rejection. In particular, an optional consumer may return none directly,
without introducing another optional layer. Both branches need certificates. -/
noncomputable def guarded (consumer : Computation Parameter InputName)
    (fallback : ∀ sizes, consumer.outputDomain.Carrier sizes)
    (allowed : ∀ sizes, consumer.Arguments sizes → Prop)
    (guard : ∀ sizes, consumer.Arguments sizes → Bool)
    (permits : ∀ sizes arguments, allowed sizes arguments → guard sizes arguments = true →
      consumer.precondition sizes arguments) : Computation Parameter InputName where
  inputDomains := consumer.inputDomains
  outputDomain := consumer.outputDomain
  precondition := allowed
  compute sizes arguments := if selected : guard sizes arguments.val = true then
    consumer.compute sizes ⟨arguments.val, permits sizes arguments.val arguments.property selected⟩
    else fallback sizes

theorem Realizable.guarded {consumer : Computation Parameter InputName} (ready : consumer.Realizable)
    (fallback : ∀ sizes, consumer.outputDomain.Carrier sizes)
    (fallbackReady : (Computation.mk (Empty.elim : Empty → EncodedDomain Parameter)
      consumer.outputDomain (fun _ _ => True) (fun sizes _ => fallback sizes)).Realizable)
    (allowed : ∀ sizes, consumer.Arguments sizes → Prop)
    (guard : ∀ sizes, consumer.Arguments sizes → Bool)
    (permits : ∀ sizes arguments, allowed sizes arguments → guard sizes arguments = true →
      consumer.precondition sizes arguments)
    (guardReady : (Computation.mk consumer.inputDomains EncodedDomain.booleans allowed
      (fun sizes arguments => guard sizes arguments.val)).Realizable) :
    (consumer.guarded fallback allowed guard permits).Realizable := by
  apply Realizable.ofCases (computation := consumer.guarded fallback allowed guard permits) guard guardReady
  · let selected sizes arguments := allowed sizes arguments ∧ guard sizes arguments = true
    have active := ready.withPrecondition selected (by
      intro sizes arguments valid
      exact permits sizes arguments valid.1 valid.2)
    apply active.withSpecification selected _ (by intros; assumption)
    intro sizes arguments valid
    change consumer.compute sizes _ = if h : guard sizes arguments = true then _ else _
    rw [dite_eq_left valid.2]
  · let rejected sizes arguments := allowed sizes arguments ∧ guard sizes arguments = false
    have absent := fallbackReady.onResults consumer.inputDomains rejected
      (fun empty => empty.elim) (by intros; trivial) (fun empty => empty.elim)
    apply absent.withSpecification rejected _ (by intros; assumption)
    intro sizes arguments valid
    change fallback sizes = if h : guard sizes arguments = true then _ else _
    rw [dite_eq_right (by rw [valid.2]; decide)]

end Polytime2.Computation
