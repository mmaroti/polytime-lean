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

import Polytime2.BinaryScan
import Polytime2.CallingConvention
import Polytime2.Copy
import Polytime2.StandardTerminatedCopy

/-! # Immutable-input finite-memory binary scans

The source fixes the width and remains unchanged. Every output bit is written
regardless of old contents; both heads return without boundary markers.
Clearing and binary shifts use the same scan with different finite memories.
-/

namespace Polytime2.StandardBinaryScan

open MultiTape CallingConvention
open Binary (Symbol data word)
open Copy (frame)

-- memoryLevel: the finite specialization-dependent controller memory.
universe memoryLevel
variable {Memory : Type memoryLevel}

abbrev Alphabet := fun _ : Bool => Symbol
abbrev State (Memory : Type memoryLevel) := Sum Memory (Memory × Bool)
abbrev run := @BinaryScan.run

variable (update : Memory → Bool → Memory × Bool)

def machine : Machine Alphabet (State Memory)
  | .inl memory, symbols =>
    if symbols false = 0 then
      some (.inr (memory, false), fun name => (symbols name, some .left))
    else
      let next := update memory (symbols false == 2)
      some (.inl next.1, fun name =>
        (if name then data next.2 else symbols false, some .right))
  | .inr (memory, finished), symbols =>
    if finished then none
    else if symbols false = 0 then
      some (.inr (memory, true), fun name => (symbols name, some .right))
    else some (.inr (memory, false), fun name => (symbols name, some .left))

private theorem forward (memory : Memory) (bits : List Bool) (old : List Symbol)
    (sameLength : old.length = bits.length)
    (sourceLeft sourceRight targetLeft targetRight : List Symbol) :
    Steps (machine update) bits.length
      (.inl memory, frame sourceLeft (word bits ++ sourceRight) targetLeft (old ++ targetRight))
      (.inl (run update memory bits).1,
        frame ((word bits).reverse ++ sourceLeft) sourceRight
          ((word (run update memory bits).2).reverse ++ targetLeft) targetRight) := by
  induction bits generalizing memory old sourceLeft targetLeft with
  | nil =>
    have empty : old = [] := List.eq_nil_of_length_eq_zero sameLength
    subst old
    simpa [run, BinaryScan.run, word] using Steps.zero (machine := machine update)
      (.inl memory, frame sourceLeft sourceRight targetLeft targetRight)
  | cons bit bits hypothesis =>
    cases old with
    | nil => simp at sameLength
    | cons previous old =>
      have first : step (machine update)
          (.inl memory, frame sourceLeft (word (bit :: bits) ++ sourceRight)
            targetLeft ((previous :: old) ++ targetRight)) =
          some (.inl (update memory bit).1,
            frame (data bit :: sourceLeft) (word bits ++ sourceRight)
              (data (update memory bit).2 :: targetLeft) (old ++ targetRight)) := by
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
        (data bit :: sourceLeft) (data (update memory bit).2 :: targetLeft)
      simpa [run, BinaryScan.run, word, List.reverse_cons, List.append_assoc] using
        Steps.next first rest

private theorem rewind (memory : Memory) (left right : List Bool)
    (sameLength : right.length = left.length)
    (currentFirst currentSecond : Symbol) (nonboundary : currentFirst ≠ 0)
    (leftFirst leftSecond tailFirst tailSecond : List Symbol) :
    Steps (machine update) (left.length + 2)
      (.inr (memory, false), frame (word left ++ 0 :: leftFirst) (currentFirst :: tailFirst)
        (word right ++ 0 :: leftSecond) (currentSecond :: tailSecond))
      (.inr (memory, true), frame (0 :: leftFirst) ((word left).reverse ++ currentFirst :: tailFirst)
        (0 :: leftSecond) ((word right).reverse ++ currentSecond :: tailSecond)) := by
  induction left generalizing right currentFirst currentSecond tailFirst tailSecond with
  | nil =>
    have empty : right = [] := List.eq_nil_of_length_eq_zero sameLength
    subst right
    have first : step (machine update)
        (.inr (memory, false), frame (0 :: leftFirst) (currentFirst :: tailFirst)
          (0 :: leftSecond) (currentSecond :: tailSecond)) =
        some (.inr (memory, false), frame leftFirst (0 :: currentFirst :: tailFirst)
          leftSecond (0 :: currentSecond :: tailSecond)) := by
      simp only [step, machine, MultiTape.read, frame, Turing.Tape.mk'_head,
        Turing.ListBlank.head_mk, List.headI_cons, nonboundary, ↓reduceIte, Bool.false_eq_true, Option.map_some]
      congr 2
      funext name
      cases name <;> simp [act, frame, Turing.Tape.write_mk', Turing.Tape.move_left_mk', Turing.ListBlank.cons_mk]
    have second : step (machine update)
        (.inr (memory, false), frame leftFirst (0 :: currentFirst :: tailFirst)
          leftSecond (0 :: currentSecond :: tailSecond)) =
        some (.inr (memory, true), frame (0 :: leftFirst) (currentFirst :: tailFirst)
          (0 :: leftSecond) (currentSecond :: tailSecond)) := by
      simp only [step, machine, MultiTape.read, frame, Turing.Tape.mk'_head,
        Turing.ListBlank.head_mk, List.headI_cons, ↓reduceIte, Bool.false_eq_true, Option.map_some]
      congr 2
      funext name
      cases name <;> simp [act, frame, Turing.Tape.write_mk', Turing.Tape.move_right_mk', Turing.ListBlank.cons_mk]
    simpa [word] using Steps.next first (Steps.next second (.zero _))
  | cons bit bits hypothesis =>
    cases right with
    | nil => simp at sameLength
    | cons other rest =>
      have first : step (machine update)
          (.inr (memory, false), frame (word (bit :: bits) ++ 0 :: leftFirst) (currentFirst :: tailFirst)
            (word (other :: rest) ++ 0 :: leftSecond) (currentSecond :: tailSecond)) =
          some (.inr (memory, false), frame (word bits ++ 0 :: leftFirst) (data bit :: currentFirst :: tailFirst)
            (word rest ++ 0 :: leftSecond) (data other :: currentSecond :: tailSecond)) := by
        simp only [step, machine, MultiTape.read, frame, word, List.map_cons, List.cons_append,
          Turing.Tape.mk'_head, Turing.ListBlank.head_mk, List.headI_cons, nonboundary,
          ↓reduceIte, Bool.false_eq_true, Option.map_some]
        congr 2
        funext name
        cases name <;> simp [act, frame, Turing.Tape.write_mk', Turing.Tape.move_left_mk', Turing.ListBlank.cons_mk]
      have dataNotBoundary : data bit ≠ 0 := by cases bit <;> decide
      have restTrace := hypothesis rest (by simpa using sameLength) (data bit) (data other) dataNotBoundary
        (currentFirst :: tailFirst) (currentSecond :: tailSecond)
      simpa [word, List.reverse_cons, List.append_assoc, Nat.add_assoc] using Steps.next first restTrace

/-- A full immutable-input scan, including empty words and arbitrary output. -/
theorem steps (memory : Memory) (bits : List Bool) (old : List Symbol)
    (sameLength : old.length = bits.length)
    (sourceLeft sourceRight targetLeft targetRight : List Symbol) :
    Steps (machine update) (2 * bits.length + 2)
      (.inl memory, frame (0 :: sourceLeft) (word bits ++ 0 :: sourceRight)
        (0 :: targetLeft) (old ++ 0 :: targetRight))
      (.inr ((run update memory bits).1, true),
        frame (0 :: sourceLeft) (word bits ++ 0 :: sourceRight)
          (0 :: targetLeft) (word (run update memory bits).2 ++ 0 :: targetRight)) := by
  let result := (run update memory bits).2
  let finalMemory := (run update memory bits).1
  have resultLength : result.length = bits.length := BinaryScan.run_length update memory bits
  have scanned := forward update memory bits old sameLength (0 :: sourceLeft) (0 :: sourceRight)
    (0 :: targetLeft) (0 :: targetRight)
  have finish : step (machine update)
      (.inl finalMemory, frame ((word bits).reverse ++ 0 :: sourceLeft) (0 :: sourceRight)
        ((word result).reverse ++ 0 :: targetLeft) (0 :: targetRight)) =
      some (.inr (finalMemory, false),
        frame (((word bits).reverse ++ 0 :: sourceLeft).tail)
          (((word bits).reverse ++ 0 :: sourceLeft).headI :: 0 :: sourceRight)
          (((word result).reverse ++ 0 :: targetLeft).tail)
          (((word result).reverse ++ 0 :: targetLeft).headI :: 0 :: targetRight)) := by
    simp only [step, machine, MultiTape.read, frame, Turing.Tape.mk'_head,
      Turing.ListBlank.head_mk, List.headI_cons, ↓reduceIte, Option.map_some]
    congr 2
    funext name
    cases name <;> simp [act, frame, Turing.Tape.write_mk', Turing.Tape.move_left_mk',
      Turing.ListBlank.tail_mk, Turing.ListBlank.head_mk, Turing.ListBlank.cons_mk]
  cases reversed : bits.reverse with
  | nil =>
    have empty : bits = [] := by simpa using congrArg List.reverse reversed
    subst bits
    have resultEmpty : result = [] := List.eq_nil_of_length_eq_zero resultLength
    have restored : step (machine update)
        (.inr (finalMemory, false),
          frame sourceLeft (0 :: 0 :: sourceRight) targetLeft (0 :: 0 :: targetRight)) =
        some (.inr (finalMemory, true),
          frame (0 :: sourceLeft) (0 :: sourceRight) (0 :: targetLeft) (0 :: targetRight)) := by
      simp only [step, machine, MultiTape.read, frame, Turing.Tape.mk'_head,
        Turing.ListBlank.head_mk, List.headI_cons, ↓reduceIte, Bool.false_eq_true, Option.map_some]
      congr 2
      funext name
      cases name <;> simp [act, frame, Turing.Tape.write_mk', Turing.Tape.move_right_mk',
        Turing.ListBlank.cons_mk]
    simp only [resultEmpty, word, List.map_nil, List.reverse_nil, List.nil_append,
      List.tail_cons, List.headI_cons] at finish
    simpa [run, BinaryScan.run, word, finalMemory] using
      scanned.trans (Steps.next finish (Steps.next restored (.zero _)))
  | cons bit remaining =>
    cases resultReverse : result.reverse with
    | nil => simp_all
    | cons output outputs =>
      have sourceReverse : (word bits).reverse = data bit :: word remaining := by
        simp [word, ← List.map_reverse, reversed]
      have targetReverse : (word result).reverse = data output :: word outputs := by
        simp [word, ← List.map_reverse, resultReverse]
      have length : bits.length = remaining.length + 1 := by
        simpa using congrArg List.length reversed
      have same : outputs.length = remaining.length := by
        have equal := congrArg List.length resultReverse
        simp only [List.length_reverse, List.length_cons] at equal
        omega
      have restored := rewind update finalMemory remaining outputs same (data bit) (data output)
        (by cases bit <;> decide) sourceLeft targetLeft (0 :: sourceRight) (0 :: targetRight)
      rw [sourceReverse, targetReverse] at finish
      simp only [List.cons_append, List.tail_cons, List.headI_cons] at finish
      change Steps (machine update) _ _ (Sum.inl finalMemory, frame _ _ ((word result).reverse ++ _) _) at scanned
      rw [sourceReverse, targetReverse] at scanned
      have trace := scanned.trans (Steps.next finish restored)
      have sourceReconstruct : (word remaining).reverse ++ [data bit] = word bits := by
        simpa using (congrArg List.reverse sourceReverse).symm
      have targetReconstruct : (word outputs).reverse ++ [data output] = word result := by
        simpa using (congrArg List.reverse targetReverse).symm
      have sourceEq : (word remaining).reverse ++ data bit :: 0 :: sourceRight =
          word bits ++ 0 :: sourceRight := by
        rw [← List.singleton_append, ← List.append_assoc, sourceReconstruct]
      have targetEq : (word outputs).reverse ++ data output :: 0 :: targetRight =
          word result ++ 0 :: targetRight := by
        rw [← List.singleton_append, ← List.append_assoc, targetReconstruct]
      rw [sourceEq, targetEq] at trace
      convert trace using 1; omega

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
    (instruction : machine update state (read tapes) = some (nextState, actions)) :
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
    Runs (fun _ : Bool => bits.length) (fun name => !name) (machine update)
      (2 * bits.length + 2) (.inl memory) (fun _ => 0)
      (frame [0] (word bits ++ [0]) [0] (old ++ [0]))
      (.inr ((run update memory bits).1, true)) (fun _ => 0)
      (frame [0] (word bits ++ [0]) [0] (word (run update memory bits).2 ++ [0])) := by
  have initial : invariant bits.length (fun _ => 0) (.inl memory)
      (frame [0] (word bits ++ [0]) [0] (old ++ [0])) := by
    refine ⟨rfl, ?_, ?_⟩
    · intro index
      simpa only [sub_zero, frame] using word_nth_blank_iff bits index
    · simp
  obtain ⟨finalPosition, trace, finalValid⟩ := Runs.of_steps_invariant (invariant bits.length)
    (safe update bits.length) (steps update memory bits old sameLength [] [] [] [])
    (fun _ => 0) initial
  have zero : finalPosition = fun _ => 0 := by
    obtain ⟨synchronized, shape, bounds⟩ := finalValid
    have atZero : finalPosition false = 0 := by simpa using bounds
    funext name
    cases name with
    | false => exact atZero
    | true => exact synchronized.trans atZero
  simpa only [zero] using trace

-- parameterLevel: size names; carrierLevel: mathematical input and output values.
universe parameterLevel carrierLevel
variable {Parameter : Type parameterLevel} [Fintype Parameter]

/-- The scan's mathematical domains can differ while their bit widths agree. -/
def domains (inputDomain outputDomain : EncodedDomain.{parameterLevel, carrierLevel} Parameter) :
    Sum Parameter Bool → EncodedDomain.{parameterLevel, carrierLevel} Parameter
  | .inl parameter => EncodedDomain.unary parameter
  | .inr false => inputDomain
  | .inr true => outputDomain

/-- A common exit hides the transducer's private final controller memory. -/
noncomputable def algorithm :
    Machine (CallingConvention.Alphabet (Sum Parameter Bool)) (Sum (State Memory) Unit) :=
  MultiTape.wire StandardTerminatedCopy.dataTapes (MultiTape.withExit (machine update))

/-- A finite-memory scan realizes any mathematical map whose encodings follow
its digit rule. Hypotheses and correctness remain mathematical propositions. -/
theorem contract [Fintype Memory] (memory : Memory)
    (inputDomain outputDomain : EncodedDomain.{parameterLevel, carrierLevel} Parameter)
    (sameWidth : ∀ assignment, outputDomain.width assignment = inputDomain.width assignment)
    (hypothesis : ∀ assignment, inputDomain.Carrier assignment → Prop)
    (compute : ∀ assignment, inputDomain.Carrier assignment → outputDomain.Carrier assignment)
    (correct : ∀ assignment value, hypothesis assignment value →
      (run update memory (List.ofFn (fun index : Fin (inputDomain.width assignment) =>
        (inputDomain.encode assignment value).getLsbD index.val))).2 =
      List.ofFn (fun index : Fin (outputDomain.width assignment) =>
        (outputDomain.encode assignment (compute assignment value)).getLsbD index.val)) :
    CallingConvention.Realizes (domains inputDomain outputDomain) StandardTerminatedCopy.readOnly
      StandardTerminatedCopy.sizeTapes (algorithm update) (.inl (.inl memory)) (.inr ())
      (fun assignment input => hypothesis assignment (input ⟨.inr false, rfl⟩))
      (fun assignment input output =>
        output ⟨.inr true, rfl⟩ = compute assignment (input ⟨.inr false, rfl⟩)) := by
  obtain ⟨bound, widthBound⟩ := inputDomain.polynomial_width
  refine ⟨(by intro parameter; rfl),
    (by intro symbols; simp [algorithm, MultiTape.wire, MultiTape.withExit]), 2 * bound + 3, ?_⟩
  intro assignment input initial valid represented sizes
  let bits := List.ofFn (fun index : Fin (inputDomain.width assignment) =>
    (inputDomain.encode assignment (input ⟨.inr false, rfl⟩)).getLsbD index.val)
  have bitsLength : bits.length = inputDomain.width assignment := List.length_ofFn
  obtain ⟨old, oldLength, target⟩ := represented.2 (.inr true) rfl
  have oldFits : old.length = bits.length := by
    exact oldLength.trans ((sameWidth assignment).trans bitsLength.symm)
  have sourceEq : initial (.inr false) = buffer (word bits) := represented.1 (.inr false) rfl
  have targetEq : initial (.inr true) = buffer old := target
  let wiring := StandardTerminatedCopy.dataTapes (Parameter := Parameter)
  have start : install wiring (frame [0] (word bits ++ [0]) [0] (old ++ [0])) initial = initial := by
    funext name
    cases name with
    | inl parameter =>
      apply install_outside
      rintro ⟨name, equal⟩
      cases equal
    | inr name =>
      rw [show Sum.inr name = wiring name from rfl, install_at]
      cases name with
      | false =>
        change Turing.Tape.mk' _ _ = initial (.inr false)
        rw [buffer_padding]
        exact sourceEq.symm
      | true =>
        change Turing.Tape.mk' _ _ = initial (.inr true)
        rw [buffer_padding]
        exact targetEq.symm
  have localTrace := (runs update memory bits old oldFits).withExit
    (by intro symbols; simp [machine])
  have trace := localTrace.wire wiring
    (fun name => (domains inputDomain outputDomain name).width assignment)
    StandardTerminatedCopy.readOnly
    (by intro name; cases name with
        | false => exact bitsLength.symm
        | true => exact (sameWidth assignment).trans bitsLength.symm)
    (by intro name premise; exact premise) initial (fun _ => 0)
  have positions : install wiring (fun _ : Bool => (0 : ℤ))
      (fun _ : Sum Parameter Bool => (0 : ℤ)) = fun _ => 0 :=
    install_self wiring (fun _ : Sum Parameter Bool => (0 : ℤ))
  rw [start, positions] at trace
  let output : Outputs (domains inputDomain outputDomain) StandardTerminatedCopy.readOnly assignment :=
    fun name => by
      rcases name with ⟨name, writable⟩
      cases name with
      | inl parameter => contradiction
      | inr name =>
        cases name with
        | false => contradiction
        | true => exact compute assignment (input ⟨.inr false, rfl⟩)
  refine ⟨2 * bits.length + 2 + 1, output,
    install wiring (frame [0] (word bits ++ [0]) [0] (word (run update memory bits).2 ++ [0])) initial,
    ?_, trace, rfl, ?_⟩
  · have bounded := widthBound assignment
    simp only [map_add, map_mul, map_ofNat]
    omega
  · intro name writable
    cases name with
    | inl parameter => contradiction
    | inr name =>
      cases name with
      | false => contradiction
      | true =>
        change install wiring _ initial (wiring true) = encoded outputDomain assignment _
        rw [install_at]
        change Turing.Tape.mk' _ _ = encoded outputDomain assignment _
        rw [buffer_padding]
        change buffer (word (run update memory bits).2) = buffer (word _)
        rw [correct assignment _ valid]

end Polytime2.StandardBinaryScan
