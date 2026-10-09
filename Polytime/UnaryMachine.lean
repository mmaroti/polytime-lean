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

import Polytime.Frame

/-! # Unary multiplication on an actual one-tape machine

The alphabet is the existing eight-symbol alphabet. Unary size fields use the
same data symbols as the external header. Temporary cursors are restored. The
controller is independent of both operand values and preserves trailing input.
-/

namespace Polytime.UnaryMachine

abbrev Symbol := TupleMachine.Symbol
abbrev State := Fin 20
instance : Inhabited State := ⟨0⟩

def units (value : ℕ) : List Symbol := List.replicate value 2

def fields (values : List ℕ) : List Symbol := values.flatMap fun value => units value ++ [1]

def configuration (phase : State) (left right : List Symbol) := Tape.configuration phase left right

/-- Optional final increment gives the motivating capacity K*L+1. -/
def machine (increment : Bool) (copyMode : Bool := false) : Turing.TM0.Machine Symbol State := fun phase symbol =>
  match phase.val with
  | 0 => some (1, .move .left)
  | 1 => some (2, .write 5)
  | 2 => some (3, .move .right)
  | 3 => if copyMode then some (6, .write symbol)
      else if symbol = 2 then some (4, .write 3)
      else if symbol = 1 then some (14, .write 1) else none
  | 4 => some (5, .move .right)
  | 5 => if symbol = 1 then some (6, .move .right) else some (5, .move .right)
  | 6 => if symbol = 2 then some (7, .write 4)
      else if symbol = 1 then some (if copyMode then 14 else 12, .write 1) else none
  | 7 => if symbol = 5 then some (8, .write 5) else some (7, .move .left)
  | 8 => if symbol = 0 then some (9, .write 2) else some (8, .move .left)
  | 9 => if symbol = 4 then some (10, .write 2) else some (9, .move .right)
  | 10 => some (6, .move .right)
  | 12 => if symbol = 3 then some (13, .write 2) else some (12, .move .left)
  | 13 => some (3, .move .right)
  | 14 => if symbol = 5 then
        if increment then some (15, .write 5) else some (18, .write 1)
      else some (14, .move .left)
  | 15 => if symbol = 0 then some (16, .write 2) else some (15, .move .left)
  | 16 => if symbol = 5 then some (18, .write 1) else some (16, .move .right)
  | 18 => if symbol = 0 then some (19, .move .right) else some (18, .move .left)
  | _ => none

abbrev Steps (increment : Bool) := Tape.Steps (machine increment)

abbrev CopySteps (increment copyMode : Bool) := Tape.Steps (machine increment copyMode)

@[simp] theorem units_length (value : ℕ) : (units value).length = value := by simp [units]
@[simp] theorem units_reverse (value : ℕ) : (units value).reverse = units value := by simp [units]
@[simp] theorem units_add (left right : ℕ) : units (left + right) = units left ++ units right := by
  simp [units, List.replicate_append_replicate]

/-- A finite list may explicitly show one of the infinitely many trailing blanks. -/
@[simp] theorem left_blank (phase : State) (left right : List Symbol) :
    configuration phase (left ++ [0]) right = configuration phase left right := by
  simpa [configuration, TupleMachine.instInhabitedSymbol] using
    Tape.configuration_append_blank phase left right


/-- Copy one unary unit into free storage, restoring the source cursor. -/
theorem copy_one (increment : Bool) (gap right : List Symbol) (output : ℕ)
    (safe : ∀ symbol ∈ gap, symbol ≠ 4 ∧ symbol ≠ 5) (copyMode : Bool := false) :
    CopySteps increment copyMode (2 * gap.length + 2 * output + 9)
      (configuration 6 (gap.reverse ++ 5 :: units output) (2 :: right))
      (configuration 6 (2 :: gap.reverse ++ 5 :: units (output + 1)) right) := by
  have mark := Tape.write (machine := machine increment copyMode) (state := 6) (nextState := 7)
    (gap.reverse ++ 5 :: units output) right 2 4 (by rfl)
  have seek := Tape.scan_left (machine := machine increment copyMode) (state := 7)
    gap.reverse (units output) right 5 4
    (by intro symbol member; rcases List.mem_cons.mp member with rfl | member
        · rfl
        · simp [machine, (safe symbol (List.mem_reverse.mp member)).2])
  have enter := Tape.write (machine := machine increment copyMode) (state := 7) (nextState := 8)
    (units output) (gap ++ 4 :: right) 5 5 (by rfl)
  have reserve := Tape.scan_left (machine := machine increment copyMode) (state := 8)
    (units output) [] (gap ++ 4 :: right) 0 5
    (by intro symbol member; rcases List.mem_cons.mp member with rfl | member
        · rfl
        · have equality := List.eq_of_mem_replicate member; subst symbol; rfl)
  have reserve' : CopySteps increment copyMode (output + 1)
      (configuration 8 (units output) (5 :: (gap ++ 4 :: right)))
      (configuration 8 [] (0 :: (units output ++ 5 :: (gap ++ 4 :: right)))) := by
    have padding := left_blank (8 : State) (units output) (5 :: (gap ++ 4 :: right))
    change Tape.configuration (8 : State) _ _ = _ at padding
    rw [padding] at reserve
    simpa only [configuration, units_length, units_reverse, List.nil_append] using reserve
  have append := Tape.write (machine := machine increment copyMode) (state := 8) (nextState := 9)
    [] (units output ++ 5 :: (gap ++ 4 :: right)) 0 2 (by rfl)
  have back := Tape.scan_right (machine := machine increment copyMode) (state := 9)
    (2 :: (units output ++ [5] ++ gap)) [] (4 :: right)
    (by
      intro symbol member
      have distinct : symbol ≠ (4 : Symbol) := by
        rcases List.mem_cons.mp member with equality | member
        · subst symbol; decide
        · rcases List.mem_append.mp member with member | member
          · rcases List.mem_append.mp member with member | member
            · have equality := List.eq_of_mem_replicate member; subst symbol; decide
            · have equality : symbol = 5 := by simpa using member
              subst symbol; decide
          · exact (safe symbol member).1
      simp [machine, distinct])
  have restore := Tape.write (machine := machine increment copyMode) (state := 9) (nextState := 10)
    ((2 :: (units output ++ [5] ++ gap)).reverse) right 4 2 (by rfl)
  have advance := Tape.move_right (machine := machine increment copyMode) (state := 10) (nextState := 6)
    ((2 :: (units output ++ [5] ++ gap)).reverse) right 2 (by rfl)
  simp only [List.reverse_reverse] at seek
  simp only [List.append_nil, List.append_assoc, List.cons_append] at back restore advance
  have trace := Tape.Steps.next mark (seek.trans (Tape.Steps.next enter
    (reserve'.trans (Tape.Steps.next append (back.trans
      (Tape.Steps.next restore (Tape.Steps.next advance (.zero _))))))))
  convert trace using 1 <;>
    simp [configuration, units, List.reverse_append, List.reverse_cons, List.reverse_replicate,
      List.append_assoc, List.replicate_succ', Nat.two_mul]; omega

private theorem replicate_cons (count : ℕ) (rest : List Symbol) :
    List.replicate count (2 : Symbol) ++ 2 :: rest = 2 :: (List.replicate count 2 ++ rest) := by
  calc
    _ = (List.replicate count 2 ++ [2]) ++ rest := by simp
    _ = List.replicate (count + 1) 2 ++ rest := by rw [List.replicate_succ']
    _ = _ := by rw [List.replicate_succ]; rfl

/-- Copy an entire unary field while leaving its source and surrounding input intact. -/
def copyTicks (gap output count : ℕ) : ℕ := 2 * count ^ 2 + (2 * gap + 2 * output + 7) * count

theorem copy_loop (increment : Bool) (count output : ℕ) (gap right : List Symbol)
    (safe : ∀ symbol ∈ gap, symbol ≠ 4 ∧ symbol ≠ 5) (copyMode : Bool := false) :
    CopySteps increment copyMode (copyTicks gap.length output count)
      (configuration 6 (gap.reverse ++ 5 :: units output) (units count ++ 1 :: right))
      (configuration 6 (units count ++ gap.reverse ++ 5 :: units (output + count)) (1 :: right)) := by
  induction count generalizing gap output with
  | zero => simpa [copyTicks, units] using (Tape.Steps.zero
      (configuration 6 (gap.reverse ++ 5 :: units output) (1 :: right)))
  | succ count hypothesis =>
    have first := copy_one increment gap (units count ++ 1 :: right) output safe (copyMode := copyMode)
    have rest := hypothesis (output + 1) (gap ++ [2])
      (by intro symbol member; rcases List.mem_append.mp member with member | member
          · exact safe symbol member
          · simp only [List.mem_singleton] at member; subst symbol; decide)
    simp only [List.reverse_append, List.reverse_singleton, List.cons_append, List.nil_append, List.append_assoc] at rest
    have trace := first.trans rest
    have ticks : 2 * gap.length + 2 * output + 9 + copyTicks (gap ++ [2]).length (output + 1) count =
        copyTicks gap.length output (count + 1) := by simp only [copyTicks, List.length_append, List.length_singleton]; ring
    rw [ticks] at trace
    simpa [configuration, units, List.replicate_succ, List.reverse_append, List.append_assoc,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, replicate_cons] using trace

/-- One outer multiplication iteration copies the second operand once. -/
theorem outer_unit (increment : Bool) (past remaining multiplier output : ℕ)
    (right : List Symbol) :
    Steps increment
      (copyTicks (past + remaining + 2) output multiplier + 2 * remaining + multiplier + 8)
      (configuration 3 (units past ++ 5 :: units output)
        (2 :: (units remaining ++ 1 :: (units multiplier ++ 1 :: right))))
      (configuration 3 (units (past + 1) ++ 5 :: units (output + multiplier))
        (units remaining ++ 1 :: (units multiplier ++ 1 :: right))) := by
  let gap := units past ++ 3 :: (units remaining ++ [1])
  have mark := Tape.write (machine := machine increment) (state := 3) (nextState := 4)
    (units past ++ 5 :: units output) (units remaining ++ 1 :: (units multiplier ++ 1 :: right))
    2 3 (by rfl)
  have advance := Tape.move_right (machine := machine increment) (state := 4) (nextState := 5)
    (units past ++ 5 :: units output) (units remaining ++ 1 :: (units multiplier ++ 1 :: right))
    3 (by rfl)
  have scan := Tape.scan_right (machine := machine increment) (state := 5)
    (units remaining) (3 :: (units past ++ 5 :: units output))
    (1 :: (units multiplier ++ 1 :: right))
    (by intro symbol member; have equality := List.eq_of_mem_replicate member; subst symbol; rfl)
  have enter := Tape.move_right (machine := machine increment) (state := 5) (nextState := 6)
    (units remaining ++ 3 :: (units past ++ 5 :: units output)) (units multiplier ++ 1 :: right) 1 (by rfl)
  have copies := copy_loop increment multiplier output gap right
    (by
      intro symbol member
      have options : symbol = 2 ∨ symbol = 3 ∨ symbol = 1 := by
        simp [gap, units] at member
        aesop
      rcases options with rfl | rfl | rfl <;> decide)
  have enterBack := Tape.write (machine := machine increment) (state := 6) (nextState := 12)
    (units multiplier ++ 1 :: (units remaining ++ 3 :: (units past ++ 5 :: units (output + multiplier))))
    right 1 1 (by rfl)
  have back := Tape.scan_left (machine := machine increment) (state := 12)
    (units multiplier ++ 1 :: units remaining) (units past ++ 5 :: units (output + multiplier))
    right 3 1
    (by
      intro symbol member
      have distinct : symbol ≠ (3 : Symbol) := by
        simp [units] at member
        aesop
      simp [machine, distinct])
  have restore := Tape.write (machine := machine increment) (state := 12) (nextState := 13)
    (units past ++ 5 :: units (output + multiplier))
    (units remaining ++ 1 :: (units multiplier ++ 1 :: right)) 3 2 (by rfl)
  have next := Tape.move_right (machine := machine increment) (state := 13) (nextState := 3)
    (units past ++ 5 :: units (output + multiplier))
    (units remaining ++ 1 :: (units multiplier ++ 1 :: right)) 2 (by rfl)
  simp only [units_reverse] at scan
  simp only [gap, List.reverse_append, List.reverse_cons,
    units_reverse, List.append_assoc, List.cons_append, List.nil_append] at copies back
  have forward := Tape.Steps.next mark (Tape.Steps.next advance
    (scan.trans (Tape.Steps.next enter copies)))
  have returning := Tape.Steps.next enterBack
    (back.trans (Tape.Steps.next restore (Tape.Steps.next next (.zero _))))
  have trace := forward.trans returning
  convert trace using 1 <;> simp [configuration, units, List.replicate_succ, copyTicks]; ring

/-- Repeated multiplication iterations have a polynomial bound in operand and
output values, while preserving the complete unary header and trailing data. -/
theorem outer_loop (increment : Bool) (remaining past multiplier output : ℕ)
    (right : List Symbol) :
    ∃ ticks, ticks ≤ remaining * 32 *
      (past + remaining + multiplier + output + remaining * multiplier + 1) ^ 2 ∧
      Steps increment ticks
        (configuration 3 (units past ++ 5 :: units output)
          (units remaining ++ 1 :: (units multiplier ++ 1 :: right)))
        (configuration 3 (units (past + remaining) ++ 5 :: units (output + remaining * multiplier))
          (1 :: (units multiplier ++ 1 :: right))) := by
  induction remaining generalizing past output with
  | zero => refine ⟨0, by simp, ?_⟩; simp only [Nat.zero_mul, Nat.add_zero, units, List.replicate_zero, List.nil_append]; exact .zero _
  | succ remaining hypothesis =>
    have first := outer_unit increment past remaining multiplier output right
    obtain ⟨ticks, bound, rest⟩ := hypothesis (past + 1) (output + multiplier)
    have trace := first.trans rest
    refine ⟨copyTicks (past + remaining + 2) output multiplier + 2 * remaining + multiplier + 8 + ticks, ?_, ?_⟩
    · have frameEquality : past + 1 + remaining + multiplier + (output + multiplier) + remaining * multiplier + 1 =
          past + (remaining + 1) + multiplier + output + (remaining + 1) * multiplier + 1 := by ring
      rw [frameEquality] at bound
      have unitBound : copyTicks (past + remaining + 2) output multiplier + 2 * remaining + multiplier + 8 ≤
          32 * (past + (remaining + 1) + multiplier + output + (remaining + 1) * multiplier + 1) ^ 2 := by
        simp only [copyTicks]
        nlinarith [sq_nonneg (past + remaining + output), sq_nonneg multiplier,
          Nat.zero_le (remaining * multiplier)]
      nlinarith
    · simpa [configuration, units, List.replicate_succ, Nat.add_mul, Nat.mul_add,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using trace

/-- Return to the first output cell, including when the output field is empty. -/
theorem return_output (increment : Bool) (output : ℕ) (right : List Symbol) (copyMode : Bool := false) :
    CopySteps increment copyMode (output + 2)
      (configuration 18 (units output) (1 :: right))
      (configuration 19 [] (units output ++ 1 :: right)) := by
  have scan := Tape.scan_left (machine := machine increment copyMode) (state := 18)
    (units output) [] right 0 1
    (by intro symbol member; rcases List.mem_cons.mp member with rfl | member
        · rfl
        · have equality := List.eq_of_mem_replicate member; subst symbol; rfl)
  have padding := left_blank (18 : State) (units output) (1 :: right)
  change Tape.configuration (18 : State) _ _ = _ at padding
  rw [padding] at scan
  simp only [units_length, units_reverse] at scan
  have move := Tape.move_right (machine := machine increment copyMode) (state := 18) (nextState := 19)
    [] (units output ++ 1 :: right) 0 (by rfl)
  have trace := scan.trans (Tape.Steps.next move (.zero _))
  have finalPadding := left_blank (19 : State) [] (units output ++ 1 :: right)
  change Tape.configuration (19 : State) [0] _ = _ at finalPadding
  rw [finalPadding] at trace
  simpa [configuration, Nat.add_assoc] using trace

/-- Increment the computed product and replace its temporary boundary by an
ordinary unary terminator. Only the newly allocated output region changes. -/
theorem increment_output (output : ℕ) (right : List Symbol) :
    Steps true (2 * output + 5)
      (configuration 14 (units output) (5 :: right))
      (configuration 18 (units (output + 1)) (1 :: right)) := by
  have enter := Tape.write (machine := machine true) (state := 14) (nextState := 15)
    (units output) right 5 5 (by rfl)
  have reserve := Tape.scan_left (machine := machine true) (state := 15)
    (units output) [] right 0 5
    (by intro symbol member; rcases List.mem_cons.mp member with rfl | member
        · rfl
        · have equality := List.eq_of_mem_replicate member; subst symbol; rfl)
  have padding := left_blank (15 : State) (units output) (5 :: right)
  change Tape.configuration (15 : State) _ _ = _ at padding
  rw [padding] at reserve
  simp only [units_length, units_reverse] at reserve
  have append := Tape.write (machine := machine true) (state := 15) (nextState := 16)
    [] (units output ++ 5 :: right) 0 2 (by rfl)
  have scan := Tape.scan_right (machine := machine true) (state := 16)
    (2 :: units output) [] (5 :: right)
    (by intro symbol member; have equality : symbol = 2 := by simp [units] at member; aesop
        subst symbol; rfl)
  simp only [List.append_nil, List.reverse_cons, units_reverse] at scan
  have restore := Tape.write (machine := machine true) (state := 16) (nextState := 18)
    (units output ++ [2]) right 5 1 (by rfl)
  have trace := Tape.Steps.next enter (reserve.trans
    (Tape.Steps.next append (scan.trans (Tape.Steps.next restore (.zero _)))))
  convert trace using 1 <;> simp [configuration, units, List.replicate_succ', Nat.two_mul]; omega

/-- Finish multiplication with the header restored and the head on the result. -/
theorem finish (increment : Bool) (multiplicand multiplier output : ℕ) (right : List Symbol) :
    ∃ ticks, ticks ≤ 8 * (multiplicand + output + 1) + 20 ∧
      Steps increment ticks
        (configuration 3 (units multiplicand ++ 5 :: units output)
          (1 :: (units multiplier ++ 1 :: right)))
        (configuration 19 []
          (units (output + increment.toNat) ++ 1 ::
            (units multiplicand ++ 1 :: (units multiplier ++ 1 :: right)))) := by
  have enter := Tape.write (machine := machine increment) (state := 3) (nextState := 14)
    (units multiplicand ++ 5 :: units output) (units multiplier ++ 1 :: right) 1 1 (by rfl)
  have scan := Tape.scan_left (machine := machine increment) (state := 14)
    (units multiplicand) (units output) (units multiplier ++ 1 :: right) 5 1
    (by intro symbol member; have equality : symbol = 1 ∨ symbol = 2 := by simp [units] at member; aesop
        rcases equality with rfl | rfl <;> rfl)
  simp only [units_length, units_reverse] at scan
  have entryTrace := Tape.Steps.next enter scan
  cases increment with
  | false =>
    have boundary := Tape.write (machine := machine false) (state := 14) (nextState := 18)
      (units output) (units multiplicand ++ 1 :: (units multiplier ++ 1 :: right)) 5 1 (by rfl)
    have tail := return_output false output (units multiplicand ++ 1 :: (units multiplier ++ 1 :: right))
    have trace := entryTrace.trans (Tape.Steps.next boundary tail)
    refine ⟨multiplicand + output + 5, by omega, ?_⟩
    convert trace using 1
    all_goals first | omega | rfl
  | true =>
    have incrementTrace := increment_output output (units multiplicand ++ 1 :: (units multiplier ++ 1 :: right))
    have tail := return_output true (output + 1) (units multiplicand ++ 1 :: (units multiplier ++ 1 :: right))
    have trace := entryTrace.trans (incrementTrace.trans tail)
    refine ⟨multiplicand + 3 * output + 10, by omega, ?_⟩
    convert trace using 1
    all_goals first | omega | rfl

/-- In copy mode, restore the source prefix and close the newly copied field. -/
theorem finish_copy (gap right : List Symbol) (output : ℕ)
    (safe : ∀ symbol ∈ gap, symbol ≠ 5) :
    CopySteps false true (gap.length + output + 5)
      (configuration 6 (gap.reverse ++ 5 :: units output) (1 :: right))
      (configuration 19 [] (units output ++ 1 :: (gap ++ 1 :: right))) := by
  have enter := Tape.write (machine := machine false true) (state := 6) (nextState := 14)
    (gap.reverse ++ 5 :: units output) right 1 1 (by rfl)
  have scan := Tape.scan_left (machine := machine false true) (state := 14)
    gap.reverse (units output) right 5 1
    (by intro symbol member; rcases List.mem_cons.mp member with rfl | member
        · rfl
        · simp [machine, safe symbol (List.mem_reverse.mp member)])
  simp only [List.length_reverse, List.reverse_reverse] at scan
  have boundary := Tape.write (machine := machine false true) (state := 14) (nextState := 18)
    (units output) (gap ++ 1 :: right) 5 1 (by rfl)
  have tail := return_output false output (gap ++ 1 :: right) (copyMode := true)
  have trace := Tape.Steps.next enter (scan.trans (Tape.Steps.next boundary tail))
  convert trace using 1 <;> first | rfl | omega

@[simp] theorem fields_cons (value : ℕ) (values : List ℕ) :
    fields (value :: values) = units value ++ 1 :: fields values := by simp [fields]

@[simp] theorem fields_append (left right : List ℕ) : fields (left ++ right) = fields left ++ fields right := by
  simp [fields]

@[simp] theorem fields_length (values : List ℕ) : (fields values).length = values.sum + values.length := by
  induction values with
  | nil => rfl
  | cons value values hypothesis => simp [fields] at *; omega

theorem fields_symbols (values : List ℕ) (symbol : Symbol) (member : symbol ∈ fields values) :
    symbol = 1 ∨ symbol = 2 := by
  obtain ⟨value, _, member⟩ := List.mem_flatMap.mp member
  simp [units] at member
  aesop

/-- Complete unary multiplication (optionally plus one) from an ordinary size
header. All operands and arbitrary trailing input are preserved. -/
theorem realizes (increment : Bool) (multiplicand multiplier : ℕ) (right : List Symbol) :
    ∃ ticks, ticks ≤ 256 * (multiplicand + multiplier + 1) ^ 5 ∧
      Steps increment ticks
        (configuration 0 [] (units multiplicand ++ 1 :: (units multiplier ++ 1 :: right)))
        (configuration 19 [] (units (multiplicand * multiplier + increment.toNat) ++ 1 ::
          (units multiplicand ++ 1 :: (units multiplier ++ 1 :: right)))) := by
  have bootstrap : Steps increment 3
      (configuration 0 [] (units multiplicand ++ 1 :: (units multiplier ++ 1 :: right)))
      (configuration 3 [5] (units multiplicand ++ 1 :: (units multiplier ++ 1 :: right))) := by
    let input := units multiplicand ++ 1 :: (units multiplier ++ 1 :: right)
    have move := Tape.move_left_empty (machine := machine increment) (state := 0) (nextState := 1)
      input (by intro symbol; rfl)
    have mark := Tape.write (machine := machine increment) (state := 1) (nextState := 2)
      [] input 0 5 (by rfl)
    have enter := Tape.move_right (machine := machine increment) (state := 2) (nextState := 3)
      [] input 5 (by rfl)
    exact Tape.Steps.next move (Tape.Steps.next mark (Tape.Steps.next enter (.zero _)))
  obtain ⟨loopTicks, loopBound, loopTrace⟩ := outer_loop increment multiplicand 0 multiplier 0 right
  obtain ⟨finishTicks, finishBound, finishTrace⟩ := finish increment multiplicand multiplier (multiplicand * multiplier) right
  simp only [Nat.zero_add, units, List.replicate_zero, List.nil_append] at loopTrace
  have trace := bootstrap.trans (loopTrace.trans finishTrace)
  refine ⟨3 + (loopTicks + finishTicks), ?_, trace⟩
  have productBound : multiplicand * multiplier ≤ (multiplicand + multiplier + 1) ^ 2 := by nlinarith
  have frameBound : multiplicand + multiplier + multiplicand * multiplier + 1 ≤
      2 * (multiplicand + multiplier + 1) ^ 2 := by nlinarith
  simp only [Nat.zero_add, Nat.add_zero] at loopBound
  have squared := Nat.pow_le_pow_left frameBound 2
  have factor : multiplicand ≤ multiplicand + multiplier + 1 := by omega
  have loops := Nat.mul_le_mul (Nat.mul_le_mul_right 32 factor) squared
  have bound' : loopTicks ≤ 128 * (multiplicand + multiplier + 1) ^ 5 := by
    calc
      loopTicks ≤ _ := loopBound
      _ ≤ _ := loops
      _ = _ := by ring
  have degree : (multiplicand + multiplier + 1) ^ 2 ≤ (multiplicand + multiplier + 1) ^ 5 :=
    Nat.pow_le_pow_right (by omega) (by decide)
  have positive : 1 ≤ (multiplicand + multiplier + 1) ^ 5 := by
    have positivePower := pow_pos (by omega : 0 < multiplicand + multiplier + 1) 5
    omega
  have finishBound' : finishTicks ≤ 36 * (multiplicand + multiplier + 1) ^ 5 := by
    calc
      finishTicks ≤ 36 * (multiplicand + multiplier + 1) ^ 2 := by nlinarith
      _ ≤ _ := Nat.mul_le_mul_left 36 degree
  omega

@[simp] theorem halt (increment : Bool) (left right : List Symbol) :
    Turing.TM0.step (machine increment) (configuration 19 left right) = none := by
  simp [Turing.TM0.step, configuration, Tape.configuration, machine]

end Polytime.UnaryMachine
