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

/-! # Recording all accumulator prefixes using the existing fold compiler -/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

namespace ArrayQueue

/-- A bounded scan retains unused seed blocks followed by the new prefix states. -/
theorem scan_collect {Source State : Type} {length : ℕ} (update : State → Source → State)
    (entries : List Source) (queue : Fin (length + 1) → State) (bounded : entries.length ≤ length) :
    List.ofFn (entries.foldl (fun current value => push current (update (current (Fin.last length)) value)) queue) =
      (List.ofFn queue).drop entries.length ++ (entries.scanl update (queue (Fin.last length))).tail := by
  induction entries generalizing queue with
  | nil => simp
  | cons first rest hypothesis =>
    have restBound : rest.length ≤ length := by simp only [List.length_cons] at bounded; omega
    rw [List.foldl_cons, hypothesis _ restBound, ofFn_push,
      List.drop_append_of_le_length (by simpa using restBound)]
    simp only [push, Fin.snoc_last, List.length_cons, List.scanl_cons, List.tail_cons,
      List.drop_tail, List.append_assoc]
    congr 1
    cases rest <;> simp [List.scanl_cons]

/-- After a full traversal the surviving seed and all computed prefixes remain. -/
theorem scan_full {Source State : Type} {length : ℕ} (update : State → Source → State)
    (entries : List Source) (queue : Fin (length + 1) → State) (count : entries.length = length) :
    List.ofFn (entries.foldl (fun current value => push current (update (current (Fin.last length)) value)) queue) =
      entries.scanl update (queue (Fin.last length)) := by
  rw [scan_collect update entries queue count.le, count]
  have remaining : (List.ofFn queue).drop length = [queue (Fin.last length)] := by
    rw [List.ofFn_succ']
    simp
  rw [remaining]
  cases entries <;> simp [List.scanl_cons]

end ArrayQueue

variable {Parameter : Type} [Fintype Parameter]

/-- One total scan update takes the old state and one source element. -/
noncomputable def scanElementStep (source state : EncodedDomain.{0, 0} Parameter)
    (update : ∀ sizes, state.Carrier sizes → source.Carrier sizes → state.Carrier sizes) :
    Computation Parameter Bool where
  inputDomains choice := if choice then source else state
  outputDomain := state
  precondition _ _ := True
  compute sizes arguments := update sizes (arguments.val false) (arguments.val true)

/-- The last queue value is the live state; append its successor and drop the oldest. -/
noncomputable def scanQueueUpdate (source state : EncodedDomain.{0, 0} Parameter)
    (length : MvPolynomial Parameter ℕ)
    (update : ∀ sizes, state.Carrier sizes → source.Carrier sizes → state.Carrier sizes)
    (sizes : Parameter → ℕ) (queue : (state.arrayOfLength (length + 1)).Carrier sizes)
    (value : source.Carrier sizes) : (state.arrayOfLength (length + 1)).Carrier sizes :=
  snocValues length sizes (Fin.tail (successorValues length sizes queue))
    (update sizes (successorValues length sizes queue (Fin.last (MvPolynomial.eval sizes length))) value)

noncomputable def scanQueueStep (source state : EncodedDomain.{0, 0} Parameter)
    (length : MvPolynomial Parameter ℕ)
    (update : ∀ sizes, state.Carrier sizes → source.Carrier sizes → state.Carrier sizes) :
    Computation Parameter Bool where
  inputDomains choice := if choice then source else state.arrayOfLength (length + 1)
  outputDomain := state.arrayOfLength (length + 1)
  precondition _ _ := True
  compute sizes arguments := scanQueueUpdate source state length update sizes (arguments.val false) (arguments.val true)

/-- Record projection and construction implement a scan step without a new controller. -/
theorem scanQueueStep_realizable (source state : EncodedDomain.{0, 0} Parameter)
    (length : MvPolynomial Parameter ℕ)
    (update : ∀ sizes, state.Carrier sizes → source.Carrier sizes → state.Carrier sizes)
    (step : (scanElementStep source state update).Realizable) :
    (scanQueueStep source state length update).Realizable := by
  let computation := scanQueueStep source state length update
  have latest := (arrayLast_realizable state length).withArguments computation.inputDomains
    ⟨(fun _ => false), by intro first second _; cases first; cases second; rfl⟩
    (by intro name; cases name; rfl)
  let domains : Bool ⊕ Unit → EncodedDomain Parameter := Sum.elim computation.inputDomains (fun _ => state)
  have continuation := step.withArguments domains
    ⟨(fun choice => if choice then (Sum.inl true : Bool ⊕ Unit) else .inr ()), by
      intro first second equal; cases first <;> cases second <;> simp_all⟩
    (by intro choice; cases choice <;> rfl)
  have computed := latest.letThen continuation (fun _ => rfl) rfl (by intros; trivial)
  have tail := (arrayTail_realizable state length).withArguments computation.inputDomains
    ⟨(fun _ => false), by intro first second _; cases first; cases second; rfl⟩
    (by intro name; cases name; rfl)
  have pair := Realizable.pairOutputs computation.inputDomains (state.arrayOfLength length) state
    (fun _ _ => True)
    (fun sizes arguments => Fin.tail (successorValues length sizes (arguments.val false)))
    (fun sizes arguments => update sizes
      (successorValues length sizes (arguments.val false) (Fin.last (MvPolynomial.eval sizes length)))
      (arguments.val true)) tail computed
  exact pair.reinterpretOutput computation.outputDomain
    (fun sizes parts => snocValues length sizes parts.1 parts.2)
    (by intro sizes; simp [computation, scanQueueStep, EncodedDomain.arrayOfLength, EncodedDomain.ofCodec, Nat.add_mul])
    (fun sizes parts => arraySnoc_encode_bits state length sizes _ _)

/-- A seed queue and input array produce every prefix state. Only its last seed
value survives; in particular arbitrary earlier seed values are permitted. -/
noncomputable def arrayScan (source state : EncodedDomain.{0, 0} Parameter)
    (length : MvPolynomial Parameter ℕ)
    (update : ∀ sizes, state.Carrier sizes → source.Carrier sizes → state.Carrier sizes) :
    Computation Parameter Bool :=
  (arrayFold Empty.elim source (state.arrayOfLength (length + 1)) length (fun _ _ _ _ => True)
    (fun sizes _ queue value => scanQueueUpdate source state length update sizes queue value)).withArguments
    (fun choice => if choice then source.arrayOfLength length else state.arrayOfLength (length + 1))
    ⟨Sum.elim Empty.elim id, by
      rintro (impossible | first) (impossible' | second) equal
      all_goals first | exact impossible.elim | exact impossible'.elim | exact congrArg Sum.inr equal⟩
    (by rintro (impossible | choice); exact impossible.elim; cases choice <;> rfl)

theorem arrayScan_realizable (source state : EncodedDomain.{0, 0} Parameter)
    (length : MvPolynomial Parameter ℕ)
    (update : ∀ sizes, state.Carrier sizes → source.Carrier sizes → state.Carrier sizes)
    (step : (scanElementStep source state update).Realizable) :
    (arrayScan source state length update).Realizable := by
  have selected := (scanQueueStep_realizable source state length update step).withArguments
    (arrayFoldStep Empty.elim source (state.arrayOfLength (length + 1)) (fun _ _ _ _ => True)
      (fun sizes _ queue value => scanQueueUpdate source state length update sizes queue value)).inputDomains
    ⟨Sum.inr, Sum.inr_injective⟩ (by intro choice; cases choice <;> rfl)
  have folded := arrayFold_total_realizable Empty.elim source (state.arrayOfLength (length + 1)) length
    (fun sizes _ queue value => scanQueueUpdate source state length update sizes queue value) selected
  exact folded.withArguments _ _ _

/-- The certified output records all mathematical prefix states in order. -/
theorem arrayScan_correct (source state : EncodedDomain.{0, 0} Parameter)
    (length : MvPolynomial Parameter ℕ)
    (update : ∀ sizes, state.Carrier sizes → source.Carrier sizes → state.Carrier sizes)
    (sizes : Parameter → ℕ) (initial : (state.arrayOfLength (length + 1)).Carrier sizes)
    (array : (source.arrayOfLength length).Carrier sizes) :
    List.ofFn (successorValues length sizes
      ((arrayScan source state length update).compute sizes ⟨(fun | false => initial | true => array), trivial⟩)) =
      (List.ofFn array).scanl (update sizes)
        (successorValues length sizes initial (Fin.last (MvPolynomial.eval sizes length))) := by
  let normalize := successorValues (Element := state.Carrier sizes) length sizes
  have commutes := List.foldl_hom normalize
    (g₁ := scanQueueUpdate source state length update sizes)
    (g₂ := fun queue value => ArrayQueue.push queue (update sizes (queue (Fin.last (MvPolynomial.eval sizes length))) value))
    (l := List.ofFn array) (init := initial) (by
      intro queue value
      funext index
      simp [normalize, scanQueueUpdate, snocValues, successorValues, ArrayQueue.push])
  change List.ofFn (normalize (ArrayFold.prefixValue _ array initial _)) = _
  unfold ArrayFold.prefixValue
  rw [List.take_of_length_le (by simp), ← commutes]
  exact ArrayQueue.scan_full (update sizes) (List.ofFn array) (normalize initial) (by simp)

end Polytime2.Computation
