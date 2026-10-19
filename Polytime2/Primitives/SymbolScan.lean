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

import Polytime2.Arithmetic.ScanMath
import Polytime2.Machine.CallingConvention
import Polytime2.Primitives.FixedCopy
import Polytime2.Primitives.ScanReturn

/-! # Immutable-input scans with arbitrary output symbols

The source fixes the width and remains unchanged. Every output cell is written
regardless of old contents; both heads return without boundary markers.
The output map may write blanks, for internal unary headers and fresh scratch.
-/

namespace Polytime2.SymbolScan

open MultiTape CallingConvention
open Binary (Symbol data word)
open Copy (frame)

-- memoryLevel: the finite specialization-dependent controller memory.
universe memoryLevel
variable {Memory : Type memoryLevel}

abbrev Alphabet := fun _ : Bool => Symbol
abbrev State (Memory : Type memoryLevel) := Sum Memory (Memory × Bool)
abbrev run := @BinaryScan.run

variable (update : Memory → Bool → Memory × Bool) (write : Bool → Symbol)

def machine : Machine Alphabet (State Memory)
  | .inl memory, symbols =>
    if symbols false = 0 then
      some (.inr (memory, false), fun name => (symbols name, some .left))
    else
      let next := update memory (symbols false == 2)
      some (.inl next.1, fun name =>
        (if name then write next.2 else symbols false, some .right))
  | .inr (memory, finished), symbols =>
    if finished then none
    else if symbols false = 0 then
      some (.inr (memory, true), fun name => (symbols name, some .right))
    else some (.inr (memory, false), fun name => (symbols name, some .left))

private theorem forward (memory : Memory) (bits : List Bool) (old : List Symbol)
    (sameLength : old.length = bits.length)
    (sourceLeft sourceRight targetLeft targetRight : List Symbol) :
    Steps (machine update write) bits.length
      (.inl memory, frame sourceLeft (word bits ++ sourceRight) targetLeft (old ++ targetRight))
      (.inl (run update memory bits).1,
        frame ((word bits).reverse ++ sourceLeft) sourceRight
          ((((run update memory bits).2.map write)).reverse ++ targetLeft) targetRight) := by
  induction bits generalizing memory old sourceLeft targetLeft with
  | nil =>
    have empty : old = [] := List.eq_nil_of_length_eq_zero sameLength
    subst old
    simpa [run, BinaryScan.run, word] using Steps.zero (machine := machine update write)
      (.inl memory, frame sourceLeft sourceRight targetLeft targetRight)
  | cons bit bits hypothesis =>
    cases old with
    | nil => simp at sameLength
    | cons previous old =>
      have first : step (machine update write)
          (.inl memory, frame sourceLeft (word (bit :: bits) ++ sourceRight)
            targetLeft ((previous :: old) ++ targetRight)) =
          some (.inl (update memory bit).1,
            frame (data bit :: sourceLeft) (word bits ++ sourceRight)
              (write (update memory bit).2 :: targetLeft) (old ++ targetRight)) := by
        have nonblank : data bit ≠ 0 := by cases bit <;> decide
        have digit : (data bit == 2) = bit := by cases bit <;> decide
        simp only [step, machine, MultiTape.read, frame, word, List.map_cons, List.cons_append,
          Turing.Tape.mk'_head, Turing.ListBlank.head_mk, List.headI_cons,
          nonblank, ↓reduceIte, digit, Option.map_some]
        congr 2
        funext name
        cases name <;> simp [act, frame, Turing.Tape.write_mk',
          Turing.Tape.move_right_mk', Turing.ListBlank.cons_mk]
      have rest := hypothesis (update memory bit).1 old (by simpa using sameLength)
        (data bit :: sourceLeft) (write (update memory bit).2 :: targetLeft)
      simpa [run, BinaryScan.run, word, List.reverse_cons, List.append_assoc] using
        Steps.next first rest

/-- A full immutable-input scan, including empty words and arbitrary output. -/
theorem steps (memory : Memory) (bits : List Bool) (old : List Symbol)
    (sameLength : old.length = bits.length)
    (sourceLeft sourceRight targetLeft targetRight : List Symbol) :
    Steps (machine update write) (2 * bits.length + 2)
      (.inl memory, frame (0 :: sourceLeft) (word bits ++ 0 :: sourceRight)
        (0 :: targetLeft) (old ++ 0 :: targetRight))
      (.inr ((run update memory bits).1, true),
        frame (0 :: sourceLeft) (word bits ++ 0 :: sourceRight)
          (0 :: targetLeft) (((run update memory bits).2.map write) ++ 0 :: targetRight)) := by
  let result := (run update memory bits).2
  let finalMemory := (run update memory bits).1
  let atEnd := frame ((word bits).reverse ++ 0 :: sourceLeft) (0 :: sourceRight)
    ((result.map write).reverse ++ 0 :: targetLeft) (0 :: targetRight)
  have resultLength : result.length = bits.length := BinaryScan.run_length update memory bits
  have scanned := forward update write memory bits old sameLength (0 :: sourceLeft) (0 :: sourceRight)
    (0 :: targetLeft) (0 :: targetRight)
  have boundary : step (machine update write) (.inl finalMemory, atEnd) =
      some (.inr (finalMemory, false), ScanReturn.move (fun _ => true) .left atEnd) := by
    change (machine update write (.inl finalMemory) (MultiTape.read atEnd)).map _ = _
    rw [show machine update write (.inl finalMemory) (MultiTape.read atEnd) =
      some (.inr (finalMemory, false), fun name => ((atEnd name).head, some .left)) from rfl]
    exact congrArg (fun tapes => some ((Sum.inr (finalMemory, false) : State Memory), tapes))
      (ScanReturn.act_move (fun _ => true) .left atEnd)
  have returned := ScanReturn.from_end (machine update write) (.inl finalMemory)
    (.inr (finalMemory, false)) (.inr (finalMemory, true)) false (fun _ => true) rfl
    (by intro symbols nonblank; simp [machine, nonblank])
    (fun symbols name => (symbols name, some .right))
    (by intro symbols blank; simp [machine, blank]) bits.reverse sourceLeft sourceRight atEnd atEnd boundary
    (by simp [atEnd, frame, word, List.map_reverse])
  have restored : Steps (machine update write) (bits.length + 2) (.inl finalMemory, atEnd)
      (.inr (finalMemory, true), frame (0 :: sourceLeft) (word bits ++ 0 :: sourceRight)
        (0 :: targetLeft) (result.map write ++ 0 :: targetRight)) := by
    simp only [List.length_reverse] at returned
    convert returned using 1
    congr 1
    funext name
    cases name <;> simp only [act, MultiTape.read, Turing.Tape.write_self, ScanReturn.move_iterate, ite_true, atEnd, frame]
    · simpa [word, List.map_reverse] using
        (ScanReturn.restore_tape ((word bits).reverse) sourceLeft (0 :: sourceRight)).symm
    · simpa [word, List.map_reverse, resultLength] using
        (ScanReturn.restore_tape ((result.map write).reverse) targetLeft (0 :: targetRight)).symm
  convert scanned.trans restored using 1; omega

private def invariant (width : ℕ) (position : Bool → ℤ) (state : State Memory)
    (tapes : Tapes Alphabet) : Prop :=
  position true = position false ∧
    (∀ index : ℤ, (tapes false).nth (index - position false) = 0 ↔
      index < 0 ∨ (width : ℤ) ≤ index) ∧
    (match state with
     | .inl _ => 0 ≤ position false ∧ position false ≤ width
     | .inr (_, finished) => if finished then position false = 0
                            else -1 ≤ position false ∧ position false < width)

private theorem safe (width : ℕ) (position : Bool → ℤ) (state : State Memory)
    (tapes : Tapes (CallingConvention.Alphabet Bool))
    (nextState : State Memory) (actions : Actions (CallingConvention.Alphabet Bool))
    (valid : invariant width position state tapes)
    (instruction : machine update write state (read tapes) = some (nextState, actions)) :
    Allowed (fun _ : Bool => width) (fun name => !name) position (read tapes) actions ∧
      invariant width (fun name => position name + displacement (actions name).2)
        nextState (act actions tapes) := by
  obtain ⟨synchronized, shape, bounds⟩ := valid
  have atHead := shape (position false)
  simp only [sub_self, Turing.Tape.nth_zero] at atHead
  have preserveShape (source : (actions false).1 = (tapes false).head) :
      ∀ index : ℤ,
        (act actions tapes false).nth
          (index - (position false + displacement (actions false).2)) = 0 ↔
        index < 0 ∨ (width : ℤ) ≤ index := by
    intro index
    rw [action_nth]
    by_cases equal : index = position false
    · subst index
      simpa [source] using atHead
    · simpa [equal] using shape index
  cases state with
  | inl memory =>
    by_cases blank : (tapes false).head = 0
    · simp only [machine, MultiTape.read, blank, ↓reduceIte, Option.some.injEq,
        Prod.mk.injEq] at instruction
      obtain ⟨rfl, rfl⟩ := instruction
      refine ⟨(by intro name premise; rfl), ?_⟩
      refine ⟨by simpa [displacement] using synchronized, preserveShape rfl, ?_⟩
      simp only [displacement, Bool.false_eq_true, ↓reduceIte]
      have outside := atHead.mp blank
      norm_num at bounds ⊢
      omega
    · simp only [machine, MultiTape.read, blank, ↓reduceIte, Option.some.injEq,
        Prod.mk.injEq] at instruction
      obtain ⟨rfl, rfl⟩ := instruction
      have inside : ¬ (position false < 0 ∨ (width : ℤ) ≤ position false) := by
        exact fun outside => blank (atHead.mpr outside)
      refine ⟨?_, ?_⟩
      · intro name premise
        cases name with
        | false => rfl
        | true => simp only [Bool.not_true, Bool.false_eq_true, false_or] at premise
                  rw [synchronized] at premise
                  exact False.elim (inside premise)
      · refine ⟨by simpa [displacement] using synchronized, preserveShape rfl, ?_⟩
        simp only [displacement]
        omega
  | inr phase =>
    obtain ⟨memory, finished⟩ := phase
    cases finished with
    | false =>
      by_cases blank : (tapes false).head = 0
      · simp only [machine, MultiTape.read, blank, Bool.false_eq_true, ↓reduceIte, Option.some.injEq,
          Prod.mk.injEq] at instruction
        obtain ⟨rfl, rfl⟩ := instruction
        refine ⟨(by intro name premise; rfl), ?_⟩
        refine ⟨by simpa [displacement] using synchronized, preserveShape rfl, ?_⟩
        simp only [Bool.false_eq_true, ↓reduceIte] at bounds
        simp only [displacement, ↓reduceIte]
        have outside := atHead.mp blank
        omega
      · simp only [machine, MultiTape.read, blank, Bool.false_eq_true, ↓reduceIte, Option.some.injEq,
          Prod.mk.injEq] at instruction
        obtain ⟨rfl, rfl⟩ := instruction
        have inside : ¬ (position false < 0 ∨ (width : ℤ) ≤ position false) := by
          exact fun outside => blank (atHead.mpr outside)
        refine ⟨(by intro name premise; rfl), ?_⟩
        refine ⟨by simpa [displacement] using synchronized, preserveShape rfl, ?_⟩
        simp only [displacement, Bool.false_eq_true, ↓reduceIte]
        omega
    | true => simp [machine] at instruction

/-- The complete output is overwritten while the complete source and every
surrounding blank remain unchanged throughout execution. -/
theorem runs (memory : Memory) (bits : List Bool) (old : List Symbol)
    (sameLength : old.length = bits.length) :
    Runs (fun _ : Bool => bits.length) (fun name => !name) (machine update write)
      (2 * bits.length + 2) (.inl memory) (fun _ => 0)
      (frame [0] (word bits ++ [0]) [0] (old ++ [0]))
      (.inr ((run update memory bits).1, true)) (fun _ => 0)
      (frame [0] (word bits ++ [0]) [0] (((run update memory bits).2.map write) ++ [0])) := by
  have initial : invariant bits.length (fun _ => 0) (.inl memory)
      (frame [0] (word bits ++ [0]) [0] (old ++ [0])) := by
    refine ⟨rfl, ?_, ?_⟩
    · intro index
      simpa only [sub_zero, frame] using word_nth_blank_iff bits index
    · simp
  obtain ⟨finalPosition, trace, finalValid⟩ := Runs.of_steps_invariant (invariant bits.length)
    (safe update write bits.length) (steps update write memory bits old sameLength [] [] [] [])
    (fun _ => 0) initial
  have zero : finalPosition = fun _ => 0 := by
    obtain ⟨synchronized, shape, bounds⟩ := finalValid
    have atZero : finalPosition false = 0 := by simpa using bounds
    funext name
    cases name with
    | false => exact atZero
    | true => exact synchronized.trans atZero
  simpa only [zero] using trace

/-- The same scan stated directly on canonical buffers, including blank output. -/
theorem buffer_runs (memory : Memory) (bits : List Bool) (old : List Symbol)
    (sameLength : old.length = bits.length) :
    Runs (fun _ : Bool => bits.length) (fun name => !name) (machine update write)
      (2 * bits.length + 2) (.inl memory) (fun _ => 0)
      (fun name => if name then buffer old else buffer (word bits))
      (.inr ((run update memory bits).1, true)) (fun _ => 0)
      (fun name => if name then buffer ((run update memory bits).2.map write) else buffer (word bits)) := by
  have frameBuffer (source target : List Symbol) :
      Copy.frame [0] (source ++ [0]) [0] (target ++ [0]) =
        (fun name => if name then buffer target else buffer source) := by
    funext name
    cases name <;> exact buffer_padding _
  have trace := runs update write memory bits old sameLength
  rw [frameBuffer, frameBuffer] at trace
  exact trace

end Polytime2.SymbolScan
