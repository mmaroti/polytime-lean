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

import Polytime1.RetainedLookupMachine
import Polytime1.BlockWriteMachine

/-! # Runtime address conversion followed by an indexed scalar write -/

namespace Polytime1.RetainedWriteMachine

open TupleMachine

namespace PrepareWrite

abbrev State (width : ℕ) := Fin (width + 1) × Fin 3

/-- Restore the writer's counter separator and move back across the replacement
slot. Only the fixed scalar width is held in finite controller states. -/
def machine (width : ℕ) : Turing.TM0.Machine Symbol (State width) := fun (remaining, phase) symbol =>
  match phase.val with
  | 0 => some ((remaining, 1), .move .left)
  | 1 => some ((remaining, 2), .write (data false))
  | _ => if remaining.val > 0 then
      some ((⟨remaining.val - 1, by omega⟩, 2), .move .left) else none

private theorem rewind {width : ℕ} (symbols left right : List Symbol) (remaining : Fin (width + 1))
    (position : remaining.val = symbols.length) :
    Tape.Steps (machine width) symbols.length
      (Tape.configuration (remaining, 2) (symbols ++ left) right)
      (Tape.configuration (0, 2) left (symbols.reverse ++ right)) := by
  induction symbols generalizing remaining right with
  | nil =>
    have equality : remaining = 0 := Fin.ext position
    subst remaining
    exact .zero _
  | cons symbol symbols hypothesis =>
    have positive : remaining.val > 0 := by simp at position; omega
    let next : Fin (width + 1) := ⟨remaining.val - 1, by omega⟩
    have step := Tape.move_left_list (machine := machine width) (state := (remaining, 2)) (nextState := (next, 2))
      (symbols ++ left) right symbol (by intro current; simp [machine, positive, next])
    have rest := hypothesis (symbol :: right) next (by dsimp [next]; simp at position; omega)
    simpa [List.reverse_cons, List.append_assoc] using Tape.Steps.next step rest

/-- Reposition the head from the binary counter to the runtime replacement. -/
theorem realizes {width : ℕ} (bits : Fin width → Bool) (left right : List Symbol) :
    Tape.Steps (machine width) (width + 2)
      (Tape.configuration (Fin.last width, 0) (3 :: ((word (List.ofFn bits)).reverse ++ left)) right)
      (Tape.configuration (0, 2) left (word (List.ofFn bits) ++ data false :: right)) := by
  have back := Tape.move_left_list (machine := machine width) (state := (Fin.last width, 0)) (nextState := (Fin.last width, 1))
    ((word (List.ofFn bits)).reverse ++ left) right 3 (by intro current; rfl)
  have separator := Tape.write (machine := machine width) (state := (Fin.last width, 1)) (nextState := (Fin.last width, 2))
    ((word (List.ofFn bits)).reverse ++ left) right 3 (data false) (by rfl)
  have rewound := rewind (word (List.ofFn bits)).reverse left (data false :: right) (Fin.last width) (by simp)
  simpa only [List.length_reverse, word_length, List.length_ofFn, List.reverse_reverse] using
    Tape.Steps.next back (Tape.Steps.next separator rewound)

@[simp] theorem halt {width : ℕ} (symbol : Symbol) : machine width (0, 2) symbol = none := rfl

end PrepareWrite

abbrev State (width : ℕ) := Sum RetainedAddressMachine.State
  (Sum (PrepareWrite.State width) (BlockWriteMachine.State width))

variable {width : ℕ}

def machine : Turing.TM0.Machine Symbol (State width) :=
  Tape.sequence RetainedAddressMachine.machine
    (Tape.sequence (PrepareWrite.machine width) (BlockWriteMachine.machine (width := width))
      (.inl (.read 0 (fun _ => false)))) (.inl (Fin.last width, 0))

/-- Compute the padded address from unary scratch, read the replacement from
its runtime slot, and update exactly that array field. Retained fields survive. -/
theorem realizes (replacement original : Fin width → Bool) (before after : List Bool)
    (retained left right : List Symbol)
    (retainedValid : ∀ symbol ∈ retained, symbol ≠ 3 ∧ symbol ≠ 6)
    (positive : 0 < width) :
    let length := before.length + width + after.length
    ∃ ticks, ticks ≤ 768 * (length + retained.length + 1) ^ 2 ∧
      Tape.Steps (machine (width := width)) ticks
        (Tape.configuration (.inl (.inl 3))
          (3 :: ((word (List.ofFn replacement)).reverse ++ retained.reverse ++ 6 ::
            (UnaryMachine.units before.length ++ 7 :: left)))
          (word (Binary.digits length 0) ++ 4 :: (word (before ++ List.ofFn original ++ after) ++ right)))
        (Tape.configuration (.inr (.inr (.inr (.inr (.inr (.inr (.inr .halt)))))))
          (retained.reverse ++ 6 :: (List.replicate before.length 0 ++ 7 :: left))
          (word (List.ofFn replacement) ++ 3 :: (List.replicate length (data true) ++
            4 :: (word before ++ word (List.ofFn replacement) ++ word after ++ right)))) := by
  dsimp only
  let length := before.length + width + after.length
  let gap := retained ++ word (List.ofFn replacement)
  let tail := 4 :: (word (before ++ List.ofFn original ++ after) ++ right)
  let caller := retained.reverse ++ 6 :: (List.replicate before.length 0 ++ 7 :: left)
  have indexFits : before.length < 2 ^ length :=
    (by dsimp [length]; omega : before.length < length).trans Nat.lt_two_pow_self
  have gapValid : ∀ symbol ∈ gap, symbol ≠ 3 ∧ symbol ≠ 6 := by
    intro symbol member
    simp only [gap, List.mem_append] at member
    rcases member with member | member
    · exact retainedValid symbol member
    · obtain ⟨bit, _, equality⟩ := List.mem_map.mp member
      subst symbol; cases bit <;> decide
  obtain ⟨addressTicks, addressBound, converted⟩ := RetainedAddressMachine.loop before.length 0 length 0
    gap left tail gapValid (by simpa using indexFits)
  have converted' : Tape.Steps RetainedAddressMachine.machine addressTicks
      (Tape.configuration (.inl 3)
        (3 :: ((word (List.ofFn replacement)).reverse ++ retained.reverse ++ 6 :: (UnaryMachine.units before.length ++ 7 :: left)))
        (word (Binary.digits length 0) ++ tail))
      (Tape.configuration (.inr 4) (3 :: ((word (List.ofFn replacement)).reverse ++ caller))
        (word (Binary.digits length before.length) ++ tail)) := by
    simpa [gap, caller, List.reverse_append, List.append_assoc] using converted
  have prepared := PrepareWrite.realizes replacement caller (word (Binary.digits length before.length) ++ tail)
  have indexValue : Binary.value (Binary.digits length before.length) = before.length := by
    simp [Nat.mod_eq_of_lt indexFits]
  obtain ⟨writeTicks, writeBound, written⟩ := BlockWriteMachine.store replacement original
    (Binary.digits length before.length) before after caller right positive indexValue
  have written' : Tape.Steps (BlockWriteMachine.machine (width := width)) writeTicks
      (Tape.configuration (.inl (.read 0 (fun _ => false))) caller
        (word (List.ofFn replacement) ++ data false :: (word (Binary.digits length before.length) ++ tail)))
      (Tape.configuration (.inr (.inr (.inr (.inr (.inr .halt))))) caller
        (word (List.ofFn replacement) ++ 3 :: (List.replicate length (data true) ++
          4 :: (word before ++ word (List.ofFn replacement) ++ word after ++ right)))) := by
    simpa [tail, List.append_assoc] using written
  have writeTrace := Tape.sequence_steps (.inl (.read 0 (fun _ => false)) : BlockWriteMachine.State width)
    prepared (by intro symbol; exact PrepareWrite.halt symbol) written'
  have result := Tape.sequence_steps
    (.inl (Fin.last width, 0) : Sum (PrepareWrite.State width) (BlockWriteMachine.State width)) converted'
    (by intro symbol; exact RetainedAddressMachine.halt symbol) writeTrace
  refine ⟨addressTicks + (width + 2 + (writeTicks + 1) + 1), ?_, ?_⟩
  · let capacity := length + retained.length + 1
    have addressCost : addressTicks ≤ 25 * capacity ^ 2 := by
      calc
        addressTicks ≤ (before.length + 1) * (3 * length + 2 * (before.length + gap.length) + 20) := by simpa using addressBound
        _ ≤ capacity * (5 * capacity + 20) := Nat.mul_le_mul
          (by dsimp [capacity, length]; omega)
          (by simp only [gap, List.length_append, word_length, List.length_ofFn]; dsimp [capacity, length]; omega)
        _ ≤ 25 * capacity ^ 2 := by dsimp [capacity]; ring_nf; nlinarith
    have frameWidth : length + before.length + width + after.length + 2 = 2 * (length + 1) := by dsimp [length]; omega
    simp only [Binary.digits_length] at writeBound
    rw [frameWidth] at writeBound
    have cost : 128 * (2 * (length + 1)) ^ 2 = 512 * (length + 1) ^ 2 := by ring
    rw [cost] at writeBound
    have writeCost : writeTicks ≤ 512 * capacity ^ 2 := writeBound.trans (Nat.mul_le_mul_left 512
      (Nat.pow_le_pow_left (by dsimp [capacity]; omega : length + 1 ≤ capacity) 2))
    have widthBound : width ≤ capacity := by dsimp [capacity, length]; omega
    dsimp [capacity] at addressCost writeCost widthBound
    ring_nf at addressCost writeCost ⊢
    nlinarith
  · simpa [machine, caller, tail, Tape.configuration] using result

@[simp] theorem halt (symbol : Symbol) :
    machine (width := width) (.inr (.inr (.inr (.inr (.inr (.inr (.inr .halt))))))) symbol = none := by
  simp [machine, Tape.sequence]

/-- Initialize a fresh or consumed binary window before address conversion and
the indexed write. The replacement and retained fields remain runtime tape data. -/
theorem realizes_from_uniform (replacement original : Fin width → Bool) (before after : List Bool)
    (inputSymbol : Symbol) (retained left right : List Symbol)
    (inputValid : inputSymbol ≠ 4)
    (retainedValid : ∀ symbol ∈ retained, symbol ≠ 3 ∧ symbol ≠ 6)
    (positive : 0 < width) :
    let length := before.length + width + after.length
    ∃ ticks, ticks ≤ 896 * (length + retained.length + 1) ^ 2 ∧
      Tape.Steps (Tape.sequence AddressMachine.ZeroWindow.machine (machine (width := width)) (.inl (.inl 3))) ticks
        (Tape.configuration (.inl 0)
          (3 :: ((word (List.ofFn replacement)).reverse ++ retained.reverse ++ 6 ::
            (UnaryMachine.units before.length ++ 7 :: left)))
          (List.replicate length inputSymbol ++ 4 :: (word (before ++ List.ofFn original ++ after) ++ right)))
        (Tape.configuration (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr .halt))))))))
          (retained.reverse ++ 6 :: (List.replicate before.length 0 ++ 7 :: left))
          (word (List.ofFn replacement) ++ 3 :: (List.replicate length (data true) ++
            4 :: (word before ++ word (List.ofFn replacement) ++ word after ++ right)))) := by
  dsimp only
  let length := before.length + width + after.length
  have initialized := AddressMachine.ZeroWindow.realizes_from_uniform length inputSymbol
    ((word (List.ofFn replacement)).reverse ++ retained.reverse ++ 6 :: (UnaryMachine.units before.length ++ 7 :: left))
    (word (before ++ List.ofFn original ++ after) ++ right) inputValid
  obtain ⟨ticks, bound, write⟩ := realizes replacement original before after retained left right retainedValid positive
  have result := Tape.sequence_steps (.inl (.inl 3) : State width) initialized
    (by intro symbol; exact AddressMachine.ZeroWindow.halt symbol) write
  refine ⟨3 * length + 3 + (ticks + 1), ?_, ?_⟩
  · dsimp only [length]
    ring_nf at bound ⊢
    nlinarith
  · simpa only [Tape.configuration] using result

/-- Accept the evaluator's unary address and retained fields, prepare navigation,
initialize scratch, and write the runtime replacement into the selected field.
One reserved blank becomes the boundary marker; both caller regions survive. -/
theorem realizes_evaluated_address_reserved (replacement original : Fin width → Bool) (before after : List Bool)
    (inputSymbol : Symbol) (retained caller right : List Symbol)
    (inputValid : inputSymbol ≠ 4)
    (retainedValid : ∀ symbol ∈ retained, symbol ≠ 3 ∧ symbol ≠ 6)
    (positive : 0 < width) :
    let length := before.length + width + after.length
    ∃ ticks, ticks ≤ 1024 * (length + retained.length + 1) ^ 2 ∧
      Tape.Steps (Tape.sequence RetainedLookupMachine.Entry.machine
        (Tape.sequence AddressMachine.ZeroWindow.machine (machine (width := width)) (.inl (.inl 3))) (.inl 0)) ticks
        (Tape.configuration (.inl 0) (0 :: caller)
          (UnaryMachine.units before.length ++ 1 :: (retained ++ word (List.ofFn replacement) ++ 3 ::
            (List.replicate length inputSymbol ++ 4 :: (word (before ++ List.ofFn original ++ after) ++ right)))))
        (Tape.configuration (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr .halt)))))))))
          (retained.reverse ++ 6 :: (List.replicate before.length 0 ++ 7 :: caller))
          (word (List.ofFn replacement) ++ 3 :: (List.replicate length (data true) ++
            4 :: (word before ++ word (List.ofFn replacement) ++ word after ++ right)))) := by
  dsimp only
  let length := before.length + width + after.length
  let gap := retained ++ word (List.ofFn replacement)
  have gapValid : ∀ symbol ∈ gap, symbol ≠ 3 := by
    intro symbol member
    simp only [gap, List.mem_append] at member
    rcases member with member | member
    · exact (retainedValid symbol member).1
    · obtain ⟨bit, _, equality⟩ := List.mem_map.mp member
      subst symbol; cases bit <;> decide
  have positioned := RetainedLookupMachine.Entry.realizes_reserved before.length gap caller
    (List.replicate length inputSymbol ++ 4 :: (word (before ++ List.ofFn original ++ after) ++ right)) gapValid
  obtain ⟨ticks, bound, write⟩ := realizes_from_uniform replacement original before after inputSymbol
    retained caller right inputValid retainedValid positive
  have positioned' : Tape.Steps RetainedLookupMachine.Entry.machine (before.length + retained.length + width + 6)
      (Tape.configuration 0 (0 :: caller)
        (UnaryMachine.units before.length ++ 1 :: (retained ++ word (List.ofFn replacement) ++ 3 ::
          (List.replicate length inputSymbol ++ 4 :: (word (before ++ List.ofFn original ++ after) ++ right)))))
      (Tape.configuration 5
        (3 :: ((word (List.ofFn replacement)).reverse ++ retained.reverse ++ 6 :: (UnaryMachine.units before.length ++ 7 :: caller)))
        (List.replicate length inputSymbol ++ 4 :: (word (before ++ List.ofFn original ++ after) ++ right))) := by
    simpa [gap, List.reverse_append, List.append_assoc, Nat.add_assoc] using positioned
  have result := Tape.sequence_steps (.inl 0 : Sum (Fin 4) (State width)) positioned'
    (by intro symbol; exact RetainedLookupMachine.Entry.halt symbol) write
  refine ⟨before.length + retained.length + width + 6 + (ticks + 1), ?_, ?_⟩
  · ring_nf at bound ⊢
    nlinarith
  · simpa only [Tape.configuration] using result

/-- Specialize the reserved-entry adapter to blank left storage. -/
theorem realizes_evaluated_address (replacement original : Fin width → Bool) (before after : List Bool)
    (inputSymbol : Symbol) (retained right : List Symbol)
    (inputValid : inputSymbol ≠ 4)
    (retainedValid : ∀ symbol ∈ retained, symbol ≠ 3 ∧ symbol ≠ 6)
    (positive : 0 < width) :
    let length := before.length + width + after.length
    ∃ ticks, ticks ≤ 1024 * (length + retained.length + 1) ^ 2 ∧
      Tape.Steps (Tape.sequence RetainedLookupMachine.Entry.machine
        (Tape.sequence AddressMachine.ZeroWindow.machine (machine (width := width)) (.inl (.inl 3))) (.inl 0)) ticks
        (Tape.configuration (.inl 0) []
          (UnaryMachine.units before.length ++ 1 :: (retained ++ word (List.ofFn replacement) ++ 3 ::
            (List.replicate length inputSymbol ++ 4 :: (word (before ++ List.ofFn original ++ after) ++ right)))))
        (Tape.configuration (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr .halt)))))))))
          (retained.reverse ++ 6 :: (List.replicate before.length 0 ++ [7]))
          (word (List.ofFn replacement) ++ 3 :: (List.replicate length (data true) ++
            4 :: (word before ++ word (List.ofFn replacement) ++ word after ++ right)))) := by
  simpa only [show (0 :: ([] : List Symbol)) = [] ++ [default] from rfl,
    Tape.configuration_append_blank] using
    realizes_evaluated_address_reserved replacement original before after inputSymbol retained [] right
      inputValid retainedValid positive

noncomputable section ComputedAddress

/-- Evaluate an address and write a block in the same reserved frame. Both
caller regions survive; the certificate chooses all capacity and controller data. -/
theorem realizes_computed_address_reserved {ctx : SizeContext}
    (input retained : List (SizeExpression ctx)) (address : SizeExpression ctx)
    (evaluation : SizeFrame.Realizes input (address :: retained)) (positive : 0 < width) :
    ∃ (reserve : SizePolynomial ctx) (Controller : Type) (_finite : Fintype Controller)
      (inhabited : Inhabited Controller),
      let _controllerInhabited : Inhabited Controller := inhabited
      ∃ (entry exit : Controller) (program : Turing.TM0.Machine Symbol Controller)
        (cost : SizePolynomial ctx),
        (∀ symbol, program exit symbol = none) ∧
        (∀ assignment, (SizeFrame.headerWidth input).eval assignment ≤ reserve.eval assignment ∧
          (SizeFrame.headerWidth (address :: retained)).eval assignment + 1 ≤ reserve.eval assignment) ∧
        ∀ (assignment : SizeAssignment ctx) (replacement original : Fin width → Bool) (before after : List Bool)
          (extra : List ℕ) (caller right : List Symbol) (inputSymbol : Symbol)
          (_addressCorrect : before.length = address.eval assignment)
          (_inputValid : inputSymbol ≠ 4),
          let length := before.length + width + after.length
          let saved := UnaryMachine.fields (retained.map (·.eval assignment) ++ extra)
          ∃ ticks, ticks ≤ cost.eval assignment + 1024 * (length + saved.length + 1) ^ 2 + 1 ∧
            Tape.Steps program ticks
              (Tape.configuration entry
                (List.replicate (reserve.eval assignment - (SizeFrame.headerWidth input).eval assignment) 0 ++ caller)
                (UnaryMachine.fields (input.map (·.eval assignment) ++ extra) ++ word (List.ofFn replacement) ++ 3 ::
                  (List.replicate length inputSymbol ++ 4 :: (word (before ++ List.ofFn original ++ after) ++ right))))
              (Tape.configuration exit
                (saved.reverse ++ 6 :: (List.replicate before.length 0 ++ 7 ::
                  (List.replicate (reserve.eval assignment -
                    (SizeFrame.headerWidth (address :: retained)).eval assignment - 1) 0 ++ caller)))
                (word (List.ofFn replacement) ++ 3 :: (List.replicate length (data true) ++
                  4 :: (word before ++ word (List.ofFn replacement) ++ word after ++ right)))) := by
  obtain ⟨capacity, fits, ArithmeticState, finite, inhabited, arithmeticEntry, arithmeticExit,
    arithmetic, cost, arithmeticHalt, runs⟩ := evaluation
  let _arithmeticFinite : Fintype ArithmeticState := finite
  let _arithmeticInhabited : Inhabited ArithmeticState := inhabited
  let WriterState := Sum (Fin 6) (Sum (Fin 4) (State width))
  let writer : Turing.TM0.Machine Symbol WriterState := Tape.sequence RetainedLookupMachine.Entry.machine
    (Tape.sequence AddressMachine.ZeroWindow.machine (machine (width := width)) (.inl (.inl 3))) (.inl 0)
  let writerEntry : WriterState := .inl 0
  let writerExit : WriterState := .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr .halt))))))))
  refine ⟨capacity + 1, Sum ArithmeticState WriterState, inferInstance, inferInstance,
    .inl arithmeticEntry, .inr writerExit, Tape.sequence arithmetic writer writerEntry, cost, ?_, ?_, ?_⟩
  · intro symbol
    simp [Tape.sequence, writer, writerExit, halt]
  · intro assignment
    simp only [SizePolynomial.eval_add, SizePolynomial.eval_one]
    exact ⟨(fits assignment).1.trans (Nat.le_succ _), Nat.add_le_add_right (fits assignment).2 1⟩
  · intro assignment replacement original before after extra caller right inputSymbol addressCorrect inputValid
    dsimp only
    let length := before.length + width + after.length
    let saved := UnaryMachine.fields (retained.map (·.eval assignment) ++ extra)
    let margin := capacity.eval assignment + 1 - (SizeFrame.headerWidth (address :: retained)).eval assignment - 1
    let tail := UnaryMachine.fields extra ++ word (List.ofFn replacement) ++ 3 :: (List.replicate length inputSymbol ++ 4 :: (word (before ++ List.ofFn original ++ after) ++ right))
    let environment : SizeFrame.Caller capacity assignment :=
      (⟨capacity.eval assignment + 1, Nat.le_succ _⟩, caller, tail)
    obtain ⟨result, final, arithmeticTicks, arithmeticCost, evaluated, _, represented⟩ :=
      runs assignment environment () _ trivial rfl
    change final = (Tape.configuration ()
      (List.replicate (capacity.eval assignment + 1 - (SizeFrame.headerWidth (address :: retained)).eval assignment) 0 ++ caller)
      (UnaryMachine.fields ((address :: retained).map (·.eval assignment)) ++ tail)).Tape at represented
    rw [represented] at evaluated
    have marginEq : capacity.eval assignment + 1 - (SizeFrame.headerWidth (address :: retained)).eval assignment = margin + 1 := by
      have enough := (fits assignment).2
      dsimp only [margin]
      omega
    have marginCells : List.replicate (capacity.eval assignment + 1 - (SizeFrame.headerWidth (address :: retained)).eval assignment) (0 : Symbol) ++ caller =
        0 :: (List.replicate margin 0 ++ caller) := by
      rw [marginEq, List.replicate_succ]; rfl
    have savedValid : ∀ symbol ∈ saved, symbol ≠ 3 ∧ symbol ≠ 6 := by
      intro symbol member
      simp only [saved, UnaryMachine.fields, List.mem_flatMap, List.mem_append,
        List.mem_cons, List.mem_nil_iff, or_false, UnaryMachine.units, List.mem_replicate] at member
      obtain ⟨value, _, member⟩ := member
      rcases member with ⟨_, equality⟩ | equality <;> subst symbol <;> decide
    obtain ⟨writeTicks, writeCost, written⟩ := realizes_evaluated_address_reserved replacement original before after inputSymbol
      saved (List.replicate margin 0 ++ caller) right inputValid savedValid positive
    have evaluated' : Tape.Steps arithmetic arithmeticTicks
        (Tape.configuration arithmeticEntry
          (List.replicate ((capacity + 1).eval assignment - (SizeFrame.headerWidth input).eval assignment) 0 ++ caller)
          (UnaryMachine.fields (input.map (·.eval assignment)) ++ tail))
        (Tape.configuration arithmeticExit (0 :: (List.replicate margin 0 ++ caller))
          (UnaryMachine.units before.length ++ 1 :: (saved ++ word (List.ofFn replacement) ++ 3 ::
            (List.replicate length inputSymbol ++ 4 :: (word (before ++ List.ofFn original ++ after) ++ right))))) := by
      simpa only [SizePolynomial.eval_add, SizePolynomial.eval_one, SizeFrame.representation,
        environment, UnaryMachine.fields_cons, List.map_cons, marginCells, addressCorrect,
        saved, tail, UnaryMachine.fields_append, List.append_assoc, List.cons_append, Tape.configuration] using evaluated
    simp only [tail, List.append_assoc] at evaluated' written
    have trace := Tape.sequence_steps writerEntry evaluated' arithmeticHalt written
    dsimp only [saved] at writeCost
    refine ⟨arithmeticTicks + (writeTicks + 1), by omega, ?_⟩
    simpa only [writer, writerEntry, writerExit, tail, margin, saved,
      SizePolynomial.eval_add, SizePolynomial.eval_one, Tape.configuration, length, UnaryMachine.fields_append, List.append_assoc] using trace

/-- The computed-address adapter also supplies the original blank-left convention. -/
theorem realizes_computed_address {ctx : SizeContext}
    (input retained : List (SizeExpression ctx)) (address : SizeExpression ctx)
    (evaluation : SizeFrame.Realizes input (address :: retained)) (positive : 0 < width) :
    ∃ (Controller : Type) (_finite : Fintype Controller)
      (inhabited : Inhabited Controller),
      let _controllerInhabited : Inhabited Controller := inhabited
      ∃ (entry exit : Controller) (program : Turing.TM0.Machine Symbol Controller)
        (cost : SizePolynomial ctx),
        (∀ symbol, program exit symbol = none) ∧
        ∀ (assignment : SizeAssignment ctx) (replacement original : Fin width → Bool) (before after : List Bool)
          (extra : List ℕ) (right : List Symbol) (inputSymbol : Symbol)
          (_addressCorrect : before.length = address.eval assignment)
          (_inputValid : inputSymbol ≠ 4),
          let length := before.length + width + after.length
          let saved := UnaryMachine.fields (retained.map (·.eval assignment) ++ extra)
          ∃ ticks, ticks ≤ cost.eval assignment + 1024 * (length + saved.length + 1) ^ 2 + 1 ∧
            Tape.Steps program ticks
              (Tape.configuration entry
                []
                (UnaryMachine.fields (input.map (·.eval assignment) ++ extra) ++ word (List.ofFn replacement) ++ 3 ::
                  (List.replicate length inputSymbol ++ 4 :: (word (before ++ List.ofFn original ++ after) ++ right))))
              (Tape.configuration exit
                (saved.reverse ++ 6 :: (List.replicate before.length 0 ++ [7]))
                (word (List.ofFn replacement) ++ 3 :: (List.replicate length (data true) ++
                  4 :: (word before ++ word (List.ofFn replacement) ++ word after ++ right)))) := by
  obtain ⟨reserve, Controller, finite, inhabited, entry, exit, program, cost, halt, _fits, runs⟩ :=
    realizes_computed_address_reserved input retained address evaluation positive
  refine ⟨Controller, finite, inhabited, entry, exit, program, cost, halt, ?_⟩
  intro assignment replacement original before after extra right inputSymbol addressCorrect inputValid
  obtain ⟨ticks, bound, trace⟩ := runs assignment replacement original before after extra [] right inputSymbol
    addressCorrect inputValid
  refine ⟨ticks, bound, ?_⟩
  simp only [List.append_nil] at trace
  have finalCells :
      (UnaryMachine.fields (retained.map (·.eval assignment) ++ extra)).reverse ++ 6 ::
        (List.replicate before.length (0 : Symbol) ++ 7 ::
          List.replicate (reserve.eval assignment -
            (SizeFrame.headerWidth (address :: retained)).eval assignment - 1) 0) =
      ((UnaryMachine.fields (retained.map (·.eval assignment) ++ extra)).reverse ++ 6 ::
        (List.replicate before.length 0 ++ [7])) ++
          List.replicate (reserve.eval assignment -
            (SizeFrame.headerWidth (address :: retained)).eval assignment - 1) default := by
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    rfl
  rw [finalCells] at trace
  simpa only [show (0 : Symbol) = default from rfl,
    Tape.configuration_append_blanks, Tape.configuration_replicate_blank] using trace

end ComputedAddress

end Polytime1.RetainedWriteMachine
