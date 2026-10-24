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

import Polytime2.Arrays.Fold
import Polytime2.Computation.Layout

/-! # Polynomial realizability of bounded array folds -/

set_option backward.isDefEq.respectTransparency false

attribute [local simp] Function.Embedding.coeFn_mk

namespace Polytime2.Computation

open MultiTape CallingConvention
open Binary (Symbol word)
open Realizable.Internal

variable {Parameter Context : Type} [Fintype Parameter] [Fintype Context]

set_option maxHeartbeats 1500000 in
/-- Array-fold applications provide mathematical invariants and a certified
update. The library allocates temporary values, traverses the array, and
accounts for all copies, cursor movements, and polynomial runtime costs. -/
theorem arrayFold_realizable
    (context : Context → EncodedDomain Parameter) (element accumulator : EncodedDomain Parameter)
    (length : MvPolynomial Parameter ℕ)
    (admissible : ∀ sizes, (∀ name, (context name).Carrier sizes) →
      (element.arrayOfLength length).Carrier sizes → accumulator.Carrier sizes → Prop)
    (update : ∀ sizes, (∀ name, (context name).Carrier sizes) → accumulator.Carrier sizes → element.Carrier sizes → accumulator.Carrier sizes)
    (allowed : ∀ sizes, (∀ name, (context name).Carrier sizes) → accumulator.Carrier sizes → element.Carrier sizes → Prop)
    (stepRealizable : (arrayFoldStep context element accumulator allowed update).Realizable)
    (invariant : ∀ sizes, (∀ name, (context name).Carrier sizes) →
      (element.arrayOfLength length).Carrier sizes → accumulator.Carrier sizes → ℕ → accumulator.Carrier sizes → Prop)
    (starts : ∀ sizes values array initial, admissible sizes values array initial → invariant sizes values array initial 0 initial)
    (permits : ∀ sizes values array initial, admissible sizes values array initial →
      ∀ index : Fin (MvPolynomial.eval sizes length), ∀ value,
        invariant sizes values array initial index.val value → allowed sizes values value (array index))
    (preserves : ∀ sizes values array initial, admissible sizes values array initial →
      ∀ index : Fin (MvPolynomial.eval sizes length), ∀ value,
        invariant sizes values array initial index.val value →
          invariant sizes values array initial (index.val + 1) (update sizes values value (array index))) :
    (arrayFold context element accumulator length admissible update).Realizable := by
  classical
  let computation := arrayFold context element accumulator length admissible update
  apply Realizable.withComputedWidth computation element.widthPolynomial
  apply Realizable.withComputedWidth (computation.withUnaryWidth element.widthPolynomial) length
  let extended := (computation.withUnaryWidth element.widthPolynomial).withUnaryWidth length
  let step := arrayFoldStep context element accumulator allowed update
  obtain ⟨Scratch, finiteScratch, scratch, State, finiteState, source, sourceEntry, sourceExit, sourceCertificate⟩ := stepRealizable
  let scratchFiniteInstance : Fintype Scratch := finiteScratch
  let stateFiniteInstance : Fintype State := finiteState
  let slots : Fin 7 ↪ (Parameter ⊕ (Context ⊕ (Fin 7 ⊕ Scratch))) := ⟨(fun name => .inr (.inr (.inl name))), by intro first second equal; exact Sum.inl.inj (Sum.inr.inj (Sum.inr.inj equal))⟩
  have slots_apply (name : Fin 7) : slots name = (Sum.inr (Sum.inr (Sum.inl name)) : (Parameter ⊕ (Context ⊕ (Fin 7 ⊕ Scratch)))) := rfl
  let domains : (Parameter ⊕ (Context ⊕ (Fin 7 ⊕ Scratch))) → EncodedDomain Parameter := Sum.elim EncodedDomain.unary
    (Sum.elim context (Sum.elim ![accumulator, element.arrayOfLength length, accumulator, element, accumulator,
      EncodedDomain.unaryOfLength element.widthPolynomial, EncodedDomain.unaryOfLength length] scratch))
  let readonly : (Parameter ⊕ (Context ⊕ (Fin 7 ⊕ Scratch))) → Bool := Sum.elim (fun _ => true)
    (Sum.elim (fun _ => true) (Sum.elim ![true, true, false, false, false, true, true] (fun _ => false)))
  let sizeTapes : Parameter ↪ (Parameter ⊕ (Context ⊕ (Fin 7 ⊕ Scratch))) := ⟨Sum.inl, Sum.inl_injective⟩
  let outputs : Unit ↪ (Parameter ⊕ (Context ⊕ (Fin 7 ⊕ Scratch))) := oneTape (slots 2)
  let sourceWiring : Realizable.Internal.TapeName step Scratch ↪ (Parameter ⊕ (Context ⊕ (Fin 7 ⊕ Scratch))) :=
    ⟨(fun name => match name with
      | .inl parameter => .inl parameter
      | .inr (.inl (.inl name)) => .inr (.inl name)
      | .inr (.inl (.inr name)) => if name then slots 3 else slots 2
      | .inr (.inr (.inl _)) => slots 4
      | .inr (.inr (.inr name)) => .inr (.inr (.inr name))), by
      intro first second equal
      rcases first with parameter | (name | choice) | result | name <;>
        rcases second with parameter' | (name' | choice') | result' | name'
      all_goals try cases choice
      all_goals try cases choice'
      all_goals simp_all [Sum.inl.injEq, Sum.inr.injEq,
        Sum.inl_ne_inr, Sum.inr_ne_inl, Fin.ext_iff]⟩
  let readWiring : Fin 3 ↪ (Parameter ⊕ (Context ⊕ (Fin 7 ⊕ Scratch))) :=
    ⟨(fun name => slots (![5, 1, 3] name)), by
      intro first second equal
      have equal := slots.injective equal
      fin_cases first <;> fin_cases second <;> simp_all⟩
  let moveWiring : Bool ↪ (Parameter ⊕ (Context ⊕ (Fin 7 ⊕ Scratch))) :=
    ⟨(fun name => if name then slots 1 else slots 5), by
      intro first second equal; cases first <;> cases second <;> simp_all [Fin.ext_iff, Sum.inl.injEq, Sum.inr.injEq]⟩
  let extract := wire (Alphabet := Alphabet (Parameter ⊕ (Context ⊕ (Fin 7 ⊕ Scratch)))) readWiring UnaryCopy.machine
  let advance := wire (Alphabet := Alphabet (Parameter ⊕ (Context ⊕ (Fin 7 ⊕ Scratch)))) moveWiring UnaryMove.machine
  let increment := wire (Alphabet := Alphabet (Parameter ⊕ (Context ⊕ (Fin 7 ⊕ Scratch)))) (oneTape (slots 6)) (Move.machine 1 .right)
  let call := wire (Alphabet := Alphabet (Parameter ⊕ (Context ⊕ (Fin 7 ⊕ Scratch)))) sourceWiring source
  let prepareAcc := StandardTapeCommands.copy (slots 0) (slots 2) (by simp [slots_apply, Fin.ext_iff, Sum.inl.injEq, Sum.inr.injEq])
  let commit := StandardTapeCommands.copy (slots 4) (slots 2) (by simp [slots_apply, Fin.ext_iff, Sum.inl.injEq, Sum.inr.injEq])
  let body := MultiTape.sequence extract
    (MultiTape.sequence call (MultiTape.sequence commit (MultiTape.sequence advance increment 1) (.inl (.inl false))) (.inl 0)) (.inl sourceEntry)
  let bodyExit : Fin 4 ⊕ (State ⊕ (Fin 3 ⊕ ((Bool ⊕ (Fin 2 ⊕ Fin 3)) ⊕ Fin 2))) :=
    .inr (.inr (.inr (.inr 0)))
  let guard : Machine (Alphabet (Parameter ⊕ (Context ⊕ (Fin 7 ⊕ Scratch)))) Unit := fun _ _ => none
  let condition := fun symbols : Symbols (Alphabet (Parameter ⊕ (Context ⊕ (Fin 7 ⊕ Scratch)))) => decide (symbols (slots 6) ≠ 0)
  let loop := MultiTape.withExit (MultiTape.whileMachine guard body () (.inl 0) condition)
  let restoreArray := wire (Alphabet := Alphabet (Parameter ⊕ (Context ⊕ (Fin 7 ⊕ Scratch)))) (oneTape (slots 1)) StandardHead.BlankReturn.fromEnd
  let restoreLength := wire (Alphabet := Alphabet (Parameter ⊕ (Context ⊕ (Fin 7 ⊕ Scratch)))) (oneTape (slots 6)) StandardHead.BlankReturn.fromEnd
  let restoration := MultiTape.sequence restoreArray restoreLength (.inl 1)
  let algorithm := MultiTape.sequence prepareAcc (MultiTape.sequence loop restoration (.inl (.inl 1))) (.inl (.inl (.inl ())))
  obtain ⟨stepBound, executeStep⟩ := Realizable.Internal.wiredRuns scratch source sourceEntry sourceExit sourceCertificate sourceWiring
  have bodyHalt : ∀ symbols, body bodyExit symbols = none := by
    intro symbols
    simp [body, bodyExit, MultiTape.sequence, increment, wire, Move.machine]
  have certificate : CallingConvention.Realizes domains readonly sizeTapes outputs algorithm (.inl 0)
      (.inr (.inr (.inr (.inr 2))))
      (fun sizes input => admissible sizes (fun name => input ⟨.inr (.inl name), rfl⟩)
        (input ⟨slots 1, rfl⟩) (input ⟨slots 0, rfl⟩))
      (fun sizes input output => output () = ArrayFold.prefixValue
        (update sizes (fun name => input ⟨.inr (.inl name), rfl⟩))
        (input ⟨slots 1, rfl⟩) (input ⟨slots 0, rfl⟩) (MvPolynomial.eval sizes length)) := by
    refine ⟨(by intro parameter; rfl), (by intro name; rfl), ?_,
      2 * accumulator.widthPolynomial + 2 + (length + 1) *
        (stepBound + 5 * element.widthPolynomial + 2 * accumulator.widthPolynomial + 20) +
        length * element.widthPolynomial + length + 15, ?_⟩
    · intro symbols
      simp [algorithm, MultiTape.sequence, restoration, restoreLength, wire,
        StandardHead.BlankReturn.fromEnd, StandardHead.BlankReturn.machine]
    · intro sizes input initial valid represented headers
      let width := fun name => (domains name).width sizes
      let values := fun name => input ⟨.inr (.inl name), rfl⟩
      let array : (element.arrayOfLength length).Carrier sizes := input ⟨slots 1, rfl⟩
      let seed : accumulator.Carrier sizes := input ⟨slots 0, rfl⟩
      let count := MvPolynomial.eval sizes length
      let elementWidth := element.width sizes
      let arrayBits := EncodedDomain.ArrayEncoding.bits ((element.arrayOfLength length).encode sizes array)
      let state := ArrayFold.prefixValue (update sizes values) array seed
      let position : ℕ → (Parameter ⊕ (Context ⊕ (Fin 7 ⊕ Scratch))) → ℤ := fun index name =>
        if name = slots 1 then (index * elementWidth : ℕ) else if name = slots 6 then index else 0
      let representation := fun index (tapes : Tapes (Alphabet (Parameter ⊕ (Context ⊕ (Fin 7 ⊕ Scratch))))) =>
        (∀ name, Region (width name) (position index name) (tapes name)) ∧
        (∀ parameter, tapes (.inl parameter) = unary (sizes parameter)) ∧
        (∀ name, tapes (.inr (.inl name)) = encoded (context name) sizes (values name)) ∧
        tapes (slots 5) = unary elementWidth ∧
        tapes (slots 6) = Realizable.Internal.ArrayFold.cursor (List.replicate count true) index ∧
        tapes (slots 1) = Realizable.Internal.ArrayFold.cursor arrayBits (index * elementWidth) ∧
        tapes (slots 2) = encoded accumulator sizes (state index)
      have stateInvariant : ∀ index, index ≤ count → invariant sizes values array seed index (state index) :=
        fun index bounded => ArrayFold.prefix_invariant _ _ _ _ (starts sizes values array seed valid)
          (fun index value good => preserves sizes values array seed valid index value good) index bounded
      have positionZero : position 0 = fun _ => 0 := by funext name; simp [position]
      have writablePosition : ∀ index name, readonly name = false → position index name = 0 := by
        intro index name writable
        by_cases arrayName : name = slots 1
        · subst name; contradiction
        · by_cases lengthName : name = slots 6
          · subst name; contradiction
          · simp [position, arrayName, lengthName]
      have sourceWidths : ∀ name, width (sourceWiring name) = (Realizable.Internal.domains step scratch name).width sizes := by
        intro name
        rcases name with parameter | (name | choice) | result | name
        all_goals first | rfl | (cases choice <;> rfl)
      have sourcePositions : ∀ index name, position index (sourceWiring name) = 0 := by
        intro index name
        rcases name with parameter | (name | choice) | result | name
        all_goals try cases choice
        all_goals simp [position, sourceWiring, slots_apply]
      have inputPreserved {First : Type} {machine : Machine (Alphabet (Parameter ⊕ (Context ⊕ (Fin 7 ⊕ Scratch)))) First}
          {ticks first last tapes final} (index next : ℕ)
          (trace : Runs width readonly machine ticks first (position index) tapes last (position next) final)
          (good : representation index tapes) :
          (∀ parameter, final (.inl parameter) = unary (sizes parameter)) ∧
          (∀ name, final (.inr (.inl name)) = encoded (context name) sizes (values name)) ∧
          final (slots 5) = unary elementWidth ∧
          final (slots 6) = Realizable.Internal.ArrayFold.cursor (List.replicate count true) next ∧
          final (slots 1) = Realizable.Internal.ArrayFold.cursor arrayBits (next * elementWidth) := by
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · intro parameter
          apply trace.readOnly_tape_match (.inl parameter) rfl _
          intro cell
          rw [good.2.1 parameter]
          simp [position, slots_apply]
        · intro name
          apply trace.readOnly_tape_match (.inr (.inl name)) rfl _
          intro cell
          rw [good.2.2.1 name]
          simp [position, slots_apply]
        · apply trace.readOnly_tape_match (slots 5) rfl _
          intro cell
          rw [good.2.2.2.1]
          simp [position, slots_apply]
        · apply trace.readOnly_tape_match (slots 6) rfl _
          intro cell
          rw [good.2.2.2.2.1]
          simp [position, slots_apply, Realizable.Internal.ArrayFold.cursor_nth]
        · apply trace.readOnly_tape_match (slots 1) rfl _
          intro cell
          rw [good.2.2.2.2.2.1]
          simp [position, slots_apply, Realizable.Internal.ArrayFold.cursor_nth]
      have widthEq : initial (slots 5) = unary elementWidth := by
        have encoded := represented.1 (slots 5) rfl
        change initial (slots 5) = CallingConvention.encoded (EncodedDomain.unaryOfLength element.widthPolynomial) sizes _ at encoded
        cases input ⟨slots 5, rfl⟩
        exact encoded.trans (EncodedDomain.encoded_unaryOfLength element.widthPolynomial sizes)
      have lengthEq : initial (slots 6) = unary count := by
        have encoded := represented.1 (slots 6) rfl
        change initial (slots 6) = CallingConvention.encoded (EncodedDomain.unaryOfLength length) sizes _ at encoded
        cases input ⟨slots 6, rfl⟩
        exact encoded.trans (EncodedDomain.encoded_unaryOfLength length sizes)
      let seedBits := EncodedDomain.ArrayEncoding.bits (accumulator.encode sizes seed)
      obtain ⟨old, oldLength, oldEq⟩ := represented.2 (slots 2) rfl
      have initialized := StandardTapeCommands.copy_runs (slots 0) (slots 2) (by simp [slots_apply, Fin.ext_iff, Sum.inl.injEq, Sum.inr.injEq]) width readonly rfl
        seedBits old (List.length_ofFn.symm) (List.length_ofFn.symm) (oldLength.trans List.length_ofFn.symm) initial (represented.1 (slots 0) rfl) oldEq
      let prepared := Function.update initial (slots 2) (encoded accumulator sizes seed)
      have preparedValid : representation 0 prepared := by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro name
          simpa only [positionZero, prepared, encoded, CallingConvention.tape, buffer, seedBits] using initialized.region name (represented.region name)
        · intro parameter
          exact (initialized.readOnly_tape (.inl parameter) rfl).trans (headers parameter)
        · intro name
          exact (initialized.readOnly_tape (.inr (.inl name)) rfl).trans (represented.1 (.inr (.inl name)) rfl)
        · exact (initialized.readOnly_tape (slots 5) rfl).trans widthEq
        · exact (initialized.readOnly_tape (slots 6) rfl).trans lengthEq
        · rw [Nat.zero_mul, Realizable.Internal.ArrayFold.cursor_zero]
          change prepared (slots 1) = encoded (element.arrayOfLength length) sizes array
          rw [show prepared (slots 1) = initial (slots 1) by simp [prepared, slots_apply]]
          exact represented.1 (slots 1) rfl
        · change prepared (slots 2) = _
          simp [prepared, state]
      have advanced : ∀ index, 0 ≤ index → index < count → ∀ tapes,
          representation index tapes → ∃ ticks final,
            ticks ≤ MvPolynomial.eval sizes stepBound + 5 * elementWidth + 2 * accumulator.width sizes + 18 ∧
            Runs width readonly body ticks (.inl 0) (position index) tapes bodyExit (position (index + 1)) final ∧
            representation (index + 1) final := by
        intro index lower active tapes good
        let coordinate : Fin count := ⟨index, active⟩
        let value := array coordinate
        let payload := EncodedDomain.ArrayEncoding.bits (element.encode sizes value)
        have payloadLength : payload.length = elementWidth := List.length_ofFn
        obtain ⟨before, after, split, beforeLength⟩ :=
          EncodedDomain.ArrayEncoding.split_encode (element.encode sizes) count array coordinate
        have arraySplit : arrayBits = before ++ payload ++ after := by
          change EncodedDomain.ArrayEncoding.bits ((element.arrayOfLength length).encode sizes array) = _
          rw [EncodedDomain.arrayOfLength_encode_bits]
          exact split
        have sourceAt : tapes (slots 1) = Binary.tape (word before.reverse ++ [0]) (word payload ++ (word after ++ [0])) () := by
          rw [good.2.2.2.2.2.1, arraySplit, ← beforeLength]
          simpa [word, List.append_assoc] using Realizable.Internal.ArrayFold.cursor_split before (payload ++ after)
        obtain ⟨oldElement, oldElementLength, oldElementEq⟩ :=
          (good.1 (slots 3)).exists_buffer
        have scalarLength : oldElement.length = payload.length := oldElementLength.trans payloadLength.symm
        have localRead := UnaryCopy.runs (word payload) oldElement (by simpa [word] using scalarLength)
          (word before.reverse ++ [0]) (word after ++ [0]) [] []
          (fun name => width (readWiring name)) (fun name => position index (readWiring name))
          (by simp [position, readWiring, slots_apply, payloadLength, width, domains, word, elementWidth])
        let extracted := Function.update tapes (slots 3) (encoded element sizes value)
        have readTrace : Runs width readonly extract (3 * elementWidth + 3) 0 (position index) tapes
            3 (position index) extracted := by
          simpa only [word, List.length_map, payloadLength] using
            localRead.wire_at_of_eq readWiring width readonly (by intro name; rfl)
              (by intro name premise; fin_cases name <;> first | rfl | exact premise)
              (position index) (position index) tapes extracted
              (by intro name; rfl) (by intro name; rfl) (by intros; rfl)
              (by intro name; fin_cases name <;>
                simp [readWiring, UnaryCopy.frame, good.2.2.2.1, sourceAt, oldElementEq,
                  unary, CallingConvention.tape, buffer, Binary.tape, Turing.Tape.mk₁, Turing.Tape.mk₂, word,
                  payloadLength] <;> exact (buffer_padding _).symm)
              (by intro name; fin_cases name <;>
                simp [extracted, readWiring, slots_apply, UnaryCopy.frame, good.2.2.2.1, sourceAt, encoded,
                  unary, CallingConvention.tape, buffer, Binary.tape, Turing.Tape.mk₁, Turing.Tape.mk₂, word,
                  payload, payloadLength] <;> exact (buffer_padding _).symm)
              (by intro name outside; exact Function.update_of_ne (by
                intro equal; subst name; exact outside ⟨2, rfl⟩) _ _)
        let arguments : step.Arguments sizes := fun name => match name with
          | .inl name => values name
          | .inr false => state index
          | .inr true => value
        have stepAllowed : step.precondition sizes arguments :=
          permits sizes values array seed valid coordinate (state index) (stateInvariant index (by omega))
        obtain ⟨stepTicks, called, stepCost, calledTrace, nextEq, _, _⟩ := executeStep sizes arguments stepAllowed
          width readonly extracted sourceWidths
          (by intro name premise; rcases name with parameter | (name | choice) | result | name <;>
            first | rfl | exact premise)
          (by intro parameter; exact (readTrace.readOnly_tape (.inl parameter) rfl).trans (good.2.1 parameter))
          (by intro name; cases name with
            | inl name => exact (readTrace.readOnly_tape (.inr (.inl name)) rfl).trans (good.2.2.1 name)
            | inr choice => cases choice with
              | false => simpa [extracted, sourceWiring, Realizable.Internal.inputTape, step, arrayFoldStep, arrayFoldPartialStep, arguments, slots_apply] using good.2.2.2.2.2.2
              | true => exact Function.update_self _ _ _)
          (by intro name; simpa only [sourcePositions] using readTrace.region (sourceWiring name) (good.1 (sourceWiring name)))
        have calledTrace := calledTrace.regions width (position index) (by
          intro name writable; simp only [writablePosition index name writable]; simp)
        simp only [zero_add] at calledTrace
        let nextValue := update sizes values (state index) value
        let nextBits := EncodedDomain.ArrayEncoding.bits (accumulator.encode sizes nextValue)
        have calledRegion : Region (accumulator.width sizes) 0 (called (slots 2)) := by
          simpa [position, slots_apply, width, domains] using
            calledTrace.region (slots 2) (readTrace.region (slots 2) (good.1 (slots 2)))
        obtain ⟨oldAccumulator, oldAccumulatorLength, oldAccumulatorEq⟩ := calledRegion.exists_buffer
        have committed := StandardTapeCommands.copy_runs (slots 4) (slots 2) (by simp [slots_apply, Fin.ext_iff, Sum.inl.injEq, Sum.inr.injEq]) width readonly rfl
          nextBits oldAccumulator (List.length_ofFn.symm) (List.length_ofFn.symm) (oldAccumulatorLength.trans List.length_ofFn.symm)
          called nextEq oldAccumulatorEq
        have committed := committed.regions width (position index) (by
          intro name writable; simp only [writablePosition index name writable]; simp)
        simp only [zero_add] at committed
        let stored := Function.update called (slots 2) (encoded accumulator sizes nextValue)
        have prefixTrace := readTrace.sequence call sourceEntry (by intro symbols; simp [extract, wire, UnaryCopy.halt]) calledTrace
        have prefixTrace := prefixTrace.sequence commit 0 (by intro symbols; simp [MultiTape.sequence, call, wire, sourceCertificate.2.2.1]) committed
        have frozen := inputPreserved index index prefixTrace good
        let moved := Function.update stored (slots 1) (Realizable.Internal.ArrayFold.cursor arrayBits ((index + 1) * elementWidth))
        let afterPosition : (Parameter ⊕ (Context ⊕ (Fin 7 ⊕ Scratch))) → ℤ := fun name => if name = slots 6 then index else
          if name = slots 1 then ((index + 1) * elementWidth : ℕ) else 0
        have localMove := UnaryMove.runs elementWidth (stored (slots 1))
          (fun name => width (moveWiring name)) (fun name => readonly (moveWiring name))
          (fun name => position index (moveWiring name))
        have movedTrace : Runs width readonly advance (2 * elementWidth + 5) (.inl false)
            (position index) stored (.inr (.inr 2)) afterPosition moved := by
          exact localMove.wire_at_of_eq moveWiring width readonly (by intro name; rfl) (by intro name premise; exact premise)
            (position index) afterPosition stored moved
            (by intro name; cases name <;> rfl)
            (by intro name; cases name <;> simp [position, afterPosition, moveWiring, slots_apply, Nat.add_mul, Nat.cast_add, Nat.cast_mul])
            (by intro name outside; by_cases equal : name = slots 1
                · exact False.elim (outside ⟨true, equal.symm⟩)
                · simp [afterPosition, position, equal])
            (by intro name; cases name <;> simpa [moveWiring, stored, nextBits, encoded, CallingConvention.tape, buffer, slots_apply] using frozen.2.2.1)
            (by intro name; cases name <;> simp [moved, moveWiring, slots_apply, show stored (slots 5) = unary elementWidth from frozen.2.2.1, show stored (slots 1) = Realizable.Internal.ArrayFold.cursor arrayBits (index * elementWidth) from frozen.2.2.2.2,
                Realizable.Internal.ArrayFold.cursor_advance, Nat.add_mul])
            (by intro name outside; exact Function.update_of_ne (by intro equal; subst name; exact outside ⟨true, rfl⟩) _ _)
        let final := Function.update moved (slots 6) (Realizable.Internal.ArrayFold.cursor (List.replicate count true) (index + 1))
        have localCount := StandardHead.move_runs 1 .right (fun _ : Unit => width (slots 6)) (fun _ => true)
          (fun _ => (index : ℤ)) (fun _ : Unit => moved (slots 6))
        have countTrace : Runs width readonly increment 1 1 afterPosition moved 0 (position (index + 1)) final := by
          have last_eq : Fin.last 1 = (1 : Fin 2) := by decide
          simpa only [Nat.cast_one, one_mul, displacement, increment, last_eq] using
            localCount.wire_at_of_eq (oneTape (slots 6)) width readonly (by intro name; rfl) (by intro name premise; rfl)
              afterPosition (position (index + 1)) moved final
              (by intro name; cases name; simp [afterPosition, slots_apply])
              (by intro name; cases name; simp [position, slots_apply, displacement])
              (by intro name outside; by_cases equal : name = slots 6
                  · exact False.elim (outside ⟨(), equal.symm⟩)
                  · simp [afterPosition, position, equal])
              (by intro name; cases name; rfl)
              (by intro name; cases name; simp [final, moved, slots_apply, show stored (slots 6) = Realizable.Internal.ArrayFold.cursor (List.replicate count true) index from frozen.2.2.2.1,
                Realizable.Internal.ArrayFold.cursor_advance, Function.iterate_one])
              (by intro name outside; exact Function.update_of_ne (by intro equal; subst name; exact outside ⟨(), rfl⟩) _ _)
        have tail := movedTrace.sequence increment 1 (by intro symbols; simp [advance, wire, UnaryMove.halt]) countTrace
        have tail := committed.sequence (MultiTape.sequence advance increment 1) (.inl (.inl false))
          (by intro symbols; simp [StandardTapeCommands.copy, wire, StandardTerminatedCopy.machine]) tail
        have tail := calledTrace.sequence (MultiTape.sequence commit (MultiTape.sequence advance increment 1) (.inl (.inl false))) (.inl 0)
          (by intro symbols; simp [wire, sourceCertificate.2.2.1]) tail
        have complete := readTrace.sequence (MultiTape.sequence call (MultiTape.sequence commit (MultiTape.sequence advance increment 1) (.inl (.inl false))) (.inl 0)) (.inl sourceEntry) (by intro symbols; simp [extract, wire, UnaryCopy.halt]) tail
        have immutable := inputPreserved index (index + 1) complete good
        refine ⟨_, final, ?_, complete, ?_⟩
        · have nextBitsLength : nextBits.length = accumulator.width sizes := List.length_ofFn
          simp only [nextBitsLength]
          omega
        · refine ⟨(fun name => complete.region name (good.1 name)), immutable.1, immutable.2.1,
            immutable.2.2.1, immutable.2.2.2.1, immutable.2.2.2.2, ?_⟩
          have nextState : state (index + 1) = nextValue := ArrayFold.prefix_succ _ _ _ coordinate
          simp [final, moved, stored, slots_apply, nextState]
      obtain ⟨loopTicks, loopFinal, loopCost, loopTrace, loopValid⟩ := Runs.whileRange_at width readonly
        guard body () () (.inl 0) bodyExit condition representation representation position
        0 count 0 (MvPolynomial.eval sizes stepBound + 5 * elementWidth + 2 * accumulator.width sizes + 18)
        (by omega) (by intro symbols; rfl) bodyHalt
        (by intro index lower upper tapes good; exact ⟨0, tapes, le_rfl, Runs.zero _ _ _, good⟩)
        advanced
        (by
          intro index lower upper tapes good
          simp only [condition, MultiTape.read, good.2.2.2.2.1]
          simp only [ne_eq, Realizable.Internal.ArrayFold.cursor_blank, List.length_replicate, not_le])
        prepared preparedValid
      have arrayLength : arrayBits.length = count * elementWidth := by
        simp [arrayBits, count, elementWidth]
      let afterArray : (Parameter ⊕ (Context ⊕ (Fin 7 ⊕ Scratch))) → ℤ := fun name => if name = slots 6 then count else 0
      let arrayRestored := Function.update loopFinal (slots 1) (encoded (element.arrayOfLength length) sizes array)
      have localArrayRestore := StandardHead.BlankReturn.fromEnd_runs arrayBits
      have arrayTrace : Runs width readonly restoreArray (arrayBits.length + 3) (.inl 1)
          (position count) loopFinal (.inr 2) afterArray arrayRestored := by
        exact localArrayRestore.wire_at_of_eq (oneTape (slots 1)) width readonly
          (by intro name; cases name; change (element.arrayOfLength length).width sizes = arrayBits.length; exact List.length_ofFn.symm)
          (by intro name premise; rfl)
          (position count) afterArray loopFinal arrayRestored
          (by intro name; cases name; simp [position, slots_apply, arrayLength])
          (by intro name; cases name; simp [afterArray, slots_apply])
          (by intro name outside; by_cases equal : name = slots 1
              · exact False.elim (outside ⟨(), equal.symm⟩)
              · simp [position, afterArray, equal])
          (by
            intro name; cases name
            change loopFinal (slots 1) = _
            rw [loopValid.2.2.2.2.2.1, ← arrayLength, Realizable.Internal.ArrayFold.cursor_end])
          (by intro name; cases name; exact Function.update_self _ _ _)
          (by intro name outside; exact Function.update_of_ne (by intro equal; subst name; exact outside ⟨(), rfl⟩) _ _)
      let final := Function.update arrayRestored (slots 6) (unary count)
      have localLengthRestore := StandardHead.BlankReturn.fromEnd_runs (List.replicate count true)
      have lengthTrace : Runs width readonly restoreLength (count + 3) (.inl 1)
          afterArray arrayRestored (.inr 2) (fun _ => 0) final := by
        simpa only [List.length_replicate] using
          localLengthRestore.wire_at_of_eq (oneTape (slots 6)) width readonly
            (by intro name; cases name; change (EncodedDomain.unaryOfLength length).width sizes = _; simp [EncodedDomain.unaryOfLength, count])
            (by intro name premise; rfl) afterArray (fun _ => 0) arrayRestored final
            (by intro name; cases name; simp [afterArray]) (by intros; rfl)
            (by intro name outside; by_cases equal : name = slots 6
                · exact False.elim (outside ⟨(), equal.symm⟩)
                · simp [afterArray, equal])
            (by
              intro name; cases name
              change arrayRestored (slots 6) = _
              dsimp only [arrayRestored]
              rw [Function.update_of_ne (by simp [slots_apply] : slots 6 ≠ slots 1)]
              rw [loopValid.2.2.2.2.1]
              simpa only [List.length_replicate] using Realizable.Internal.ArrayFold.cursor_end (List.replicate count true))
            (by intro name; cases name; exact Function.update_self _ _ _)
            (by intro name outside; exact Function.update_of_ne (by intro equal; subst name; exact outside ⟨(), rfl⟩) _ _)
      have restored := arrayTrace.sequence restoreLength (.inl 1)
        (by intro symbols; simp [restoreArray, wire, MultiTape.sequence, StandardHead.BlankReturn.fromEnd, StandardHead.BlankReturn.machine]) lengthTrace
      have tail := loopTrace.sequence restoration (.inl (.inl 1)) (by intro symbols; rfl) restored
      rw [positionZero] at tail
      have complete := initialized.sequence (MultiTape.sequence loop restoration (.inl (.inl 1))) (.inl (.inl (.inl ())))
        (by intro symbols; simp [StandardTapeCommands.copy, wire, StandardTerminatedCopy.machine]) tail
      refine ⟨_, (fun _ => state count), final, ?_, complete, rfl, ?_⟩
      · have seedBitsLength : seedBits.length = accumulator.width sizes := List.length_ofFn
        simp only [Nat.sub_zero, Nat.zero_add, Nat.add_assoc] at loopCost
        simp only [map_add, map_mul, map_ofNat, map_one]
        change _ ≤ 2 * accumulator.width sizes + 2 + (count + 1) *
          (MvPolynomial.eval sizes stepBound + 5 * elementWidth + 2 * accumulator.width sizes + 20) +
          count * elementWidth + count + 15
        simp only [arrayLength, seedBitsLength]
        ring_nf at loopCost ⊢
        omega
      · intro name; cases name
        change final (slots 2) = encoded accumulator sizes (state count)
        simpa [final, arrayRestored, slots_apply] using loopValid.2.2.2.2.2.2
  let placement : PublicTape Parameter (((Context ⊕ Bool) ⊕ Unit) ⊕ Unit) ↪ (Parameter ⊕ (Context ⊕ (Fin 7 ⊕ Scratch))) :=
    (Function.Embedding.refl Parameter).sumMap
      ⟨(fun role => match role with
        | .inl (.inl (.inl (.inl name))) => .inl name
        | .inl (.inl (.inl (.inr choice))) => .inr (.inl (if choice then 1 else 0))
        | .inl (.inl (.inr _)) => .inr (.inl 5)
        | .inl (.inr _) => .inr (.inl 6)
        | .inr _ => .inr (.inl 2)), by
        intro first second equal
        rcases first with (((name | choice) | widthName) | lengthName) | result <;>
          rcases second with (((name' | choice') | widthName') | lengthName') | result'
        all_goals try cases choice
        all_goals try cases choice'
        all_goals simp [Sum.inl.injEq, Sum.inr.injEq,
          Sum.inl_ne_inr, Sum.inr_ne_inl, Fin.ext_iff] at equal ⊢
        all_goals assumption⟩
  refine ofNamedLayout extended domains readonly sizeTapes outputs algorithm (.inl 0)
    (.inr (.inr (.inr (.inr 2)))) _ _ certificate placement
    (by rintro (parameter | (((name | choice) | widthName) | lengthName) | result) <;> first | rfl | (cases choice <;> rfl))
    (by rintro (parameter | (((name | choice) | widthName) | lengthName) | result) <;> first | rfl | (cases choice <;> rfl))
    (by
      intro name outside
      rcases name with parameter | name | name | name
      · exact False.elim (outside ⟨.inl parameter, rfl⟩)
      · exact False.elim (outside ⟨.inr (.inl (.inl (.inl (.inl name)))), rfl⟩)
      · fin_cases name
        · exact False.elim (outside ⟨.inr (.inl (.inl (.inl (.inr false)))), rfl⟩)
        · exact False.elim (outside ⟨.inr (.inl (.inl (.inl (.inr true)))), rfl⟩)
        · exact False.elim (outside ⟨.inr (.inr ()), rfl⟩)
        · rfl
        · rfl
        · exact False.elim (outside ⟨.inr (.inl (.inl (.inr ()))), rfl⟩)
        · exact False.elim (outside ⟨.inr (.inl (.inr ())), rfl⟩)
      · rfl)
    (by intro parameter; rfl) () rfl (by intro sizes input valid; exact valid) ?_
  intro sizes input valid output correct
  exact congrArg (encoded accumulator sizes) correct

/-- Total updates need no application invariant or precondition proof. -/
theorem arrayFold_total_realizable
    (context : Context → EncodedDomain Parameter) (element accumulator : EncodedDomain Parameter)
    (length : MvPolynomial Parameter ℕ)
    (update : ∀ sizes, (∀ name, (context name).Carrier sizes) →
      accumulator.Carrier sizes → element.Carrier sizes → accumulator.Carrier sizes)
    (stepRealizable : (arrayFoldStep context element accumulator (fun _ _ _ _ => True) update).Realizable) :
    (arrayFold context element accumulator length (fun _ _ _ _ => True) update).Realizable :=
  arrayFold_realizable context element accumulator length _ update _ stepRealizable
    (fun _ _ _ _ _ _ => True) (by intros; trivial) (by intros; trivial) (by intros; trivial)

end Polytime2.Computation
