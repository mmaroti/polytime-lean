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

import Polytime2.ScanReturn
import Polytime2.BinaryRipple
import Polytime2.CallingConvention

/-! # Binary arithmetic with a separate carry tape

Two immutable operands produce a low-word result and a single carry/borrow
bit on separate output tapes. Every output symbol is overwritten. The finite
controller also retains the carry, and all heads return without markers.
-/

namespace Polytime2.StandardBinaryArithmetic

open MultiTape CallingConvention
open Binary (Symbol data word value)

abbrev Alphabet := fun _ : Fin 4 => Symbol
abbrev State := Sum Bool (Bool × Bool)
abbrev ripple := BinaryRipple.ripple

variable (digit carry : Bool → Bool → Bool → Bool)

@[simp] noncomputable def domainsSized {Parameter : Type} [Fintype Parameter] (capacity : Parameter) :
    Sum Parameter (Fin 4) → EncodedDomain Parameter
  | .inl parameter => EncodedDomain.unary parameter
  | .inr 0 => EncodedDomain.binaryNaturals capacity
  | .inr 1 => EncodedDomain.binaryNaturals capacity
  | .inr 2 => EncodedDomain.binaryNaturals capacity
  | .inr 3 => EncodedDomain.booleans

noncomputable abbrev domains : Sum Unit (Fin 4) → EncodedDomain Unit := domainsSized ()

def argumentReadOnly {Parameter : Type} : Sum Parameter (Fin 4) → Bool
  | .inl _ => true
  | .inr 0 => true
  | .inr 1 => true
  | .inr 2 => false
  | .inr 3 => false

def sizeTapes {Parameter : Type} : Parameter ↪ Sum Parameter (Fin 4) :=
  ⟨Sum.inl, by intro first second equal; exact Sum.inl.inj equal⟩

/-- False names the low result and true the carry or borrow. -/
def outputTapes {Parameter : Type} : Bool ↪ Sum Parameter (Fin 4) :=
  ⟨(fun | false => .inr 2 | true => .inr 3), by
    intro first second equal
    cases first <;> cases second <;> first | rfl | cases equal⟩

def dataTapes {Parameter : Type} : Fin 4 ↪ Sum Parameter (Fin 4) :=
  ⟨Sum.inr, by intro first second equal; cases equal; rfl⟩

def frame (leftFirst rightFirst leftSecond rightSecond leftOutput rightOutput : List Symbol)
    (flag : Symbol) : Tapes Alphabet := fun name =>
  if name = 0 then Turing.Tape.mk' (Turing.ListBlank.mk leftFirst) (Turing.ListBlank.mk rightFirst)
  else if name = 1 then Turing.Tape.mk' (Turing.ListBlank.mk leftSecond) (Turing.ListBlank.mk rightSecond)
  else if name = 2 then Turing.Tape.mk' (Turing.ListBlank.mk leftOutput) (Turing.ListBlank.mk rightOutput)
  else Turing.Tape.mk₁ [flag]

def machine : Machine Alphabet State
  | .inl previous, symbols =>
    if symbols 0 = 0 then
      some (.inr (previous, false), fun name =>
        (if name = 3 then data previous else symbols name,
          if name = 3 then none else some .left))
    else
      let left := symbols 0 == 2
      let right := symbols 1 == 2
      some (.inl (carry left right previous), fun name =>
        (if name = 2 then data (digit left right previous) else symbols name,
          if name = 3 then none else some .right))
  | .inr (memory, finished), symbols =>
    if finished then none
    else if symbols 0 = 0 then
      some (.inr (memory, true), fun name =>
        (symbols name, if name = 3 then none else some .right))
    else some (.inr (memory, false), fun name =>
      (symbols name, if name = 3 then none else some .left))

noncomputable def algorithm {Parameter : Type} (digit carry : Bool → Bool → Bool → Bool) :
    Machine (CallingConvention.Alphabet (Sum Parameter (Fin 4))) (Sum State Unit) :=
  MultiTape.wire dataTapes (MultiTape.withExit (machine digit carry))

def entry (previous : Bool) : Sum State Unit := .inl (.inl previous)

def exit : Sum State Unit := .inr ()

@[simp] theorem algorithm_halt {Parameter : Type} (digit carry : Bool → Bool → Bool → Bool)
    (symbols : Symbols (CallingConvention.Alphabet (Sum Parameter (Fin 4)))) :
    algorithm digit carry exit symbols = none := by
  simp [algorithm, exit, MultiTape.withExit, MultiTape.wire]

private theorem forward (previous : Bool) (left right : List Bool)
    (sameLength : right.length = left.length) (old : List Symbol)
    (oldLength : old.length = left.length)
    (leftFirst leftSecond leftOutput tailFirst tailSecond tailOutput : List Symbol) (flag : Symbol) :
    Steps (machine digit carry) left.length
      (.inl previous, frame leftFirst (word left ++ tailFirst)
        leftSecond (word right ++ tailSecond) leftOutput (old ++ tailOutput) flag)
      (.inl (ripple digit carry previous left right).2,
        frame ((word left).reverse ++ leftFirst) tailFirst
          ((word right).reverse ++ leftSecond) tailSecond
          ((word (ripple digit carry previous left right).1).reverse ++ leftOutput) tailOutput flag) := by
  induction left generalizing previous right old leftFirst leftSecond leftOutput with
  | nil =>
    have rightEmpty : right = [] := List.eq_nil_of_length_eq_zero sameLength
    have oldEmpty : old = [] := List.eq_nil_of_length_eq_zero oldLength
    subst right; subst old
    simpa [ripple, BinaryRipple.ripple, word] using Steps.zero (machine := (machine digit carry))
      (.inl previous, frame leftFirst tailFirst leftSecond tailSecond leftOutput tailOutput flag)
  | cons bit bits hypothesis =>
    cases right with
    | nil => simp at sameLength
    | cons other rest =>
      cases old with
      | nil => simp at oldLength
      | cons previousOutput old =>
        have first : step (machine digit carry)
            (.inl previous, frame leftFirst (word (bit :: bits) ++ tailFirst)
              leftSecond (word (other :: rest) ++ tailSecond) leftOutput ((previousOutput :: old) ++ tailOutput) flag) =
            some (.inl (carry bit other previous),
              frame (data bit :: leftFirst) (word bits ++ tailFirst)
                (data other :: leftSecond) (word rest ++ tailSecond)
                (data (digit bit other previous) :: leftOutput) (old ++ tailOutput) flag) := by
          have nonblank : data bit ≠ 0 := by cases bit <;> decide
          have leftDigit : (data bit == 2) = bit := by cases bit <;> decide
          have rightDigit : (data other == 2) = other := by cases other <;> decide
          have oneNotZero : (1 : Fin 4) ≠ 0 := by decide
          simp only [step, machine, MultiTape.read, frame, word, List.map_cons, List.cons_append,
            Turing.Tape.mk'_head, Turing.ListBlank.head_mk, List.headI_cons, nonblank,
            ↓reduceIte, oneNotZero, leftDigit, rightDigit, Option.map_some]
          congr 2
          funext name
          fin_cases name <;>
            simp [act, frame, Turing.Tape.mk₁, Turing.Tape.mk₂, Turing.Tape.write_mk', Turing.Tape.move_right_mk', Turing.ListBlank.cons_mk]
        have restTrace := hypothesis (carry bit other previous) rest (by simpa using sameLength)
          old (by simpa using oldLength) (data bit :: leftFirst) (data other :: leftSecond)
          (data (digit bit other previous) :: leftOutput)
        simpa [ripple, BinaryRipple.ripple, word, List.reverse_cons, List.append_assoc] using Steps.next first restTrace

/-- Exact linear execution for arbitrary low-word and carry output contents. -/
theorem steps (previous : Bool) (left right : List Bool) (sameLength : right.length = left.length)
    (old : List Symbol) (oldLength : old.length = left.length) (oldFlag : Symbol)
    (leftFirst leftSecond leftOutput tailFirst tailSecond tailOutput : List Symbol) :
    Steps (machine digit carry) (2 * left.length + 2)
      (.inl previous, frame (0 :: leftFirst) (word left ++ 0 :: tailFirst)
        (0 :: leftSecond) (word right ++ 0 :: tailSecond)
        (0 :: leftOutput) (old ++ 0 :: tailOutput) oldFlag)
      (.inr ((ripple digit carry previous left right).2, true),
        frame (0 :: leftFirst) (word left ++ 0 :: tailFirst)
          (0 :: leftSecond) (word right ++ 0 :: tailSecond)
          (0 :: leftOutput) (word (ripple digit carry previous left right).1 ++ 0 :: tailOutput)
          (data (ripple digit carry previous left right).2)) := by
  let low := (ripple digit carry previous left right).1
  let finalCarry := (ripple digit carry previous left right).2
  let atEnd := frame ((word left).reverse ++ 0 :: leftFirst) (0 :: tailFirst)
    ((word right).reverse ++ 0 :: leftSecond) (0 :: tailSecond)
    ((word low).reverse ++ 0 :: leftOutput) (0 :: tailOutput) oldFlag
  let prepared := frame ((word left).reverse ++ 0 :: leftFirst) (0 :: tailFirst)
    ((word right).reverse ++ 0 :: leftSecond) (0 :: tailSecond)
    ((word low).reverse ++ 0 :: leftOutput) (0 :: tailOutput) (data finalCarry)
  have lowLength : low.length = left.length :=
    BinaryRipple.ripple_length digit carry previous left right sameLength
  have scanned := forward digit carry previous left right sameLength old oldLength
    (0 :: leftFirst) (0 :: leftSecond) (0 :: leftOutput)
    (0 :: tailFirst) (0 :: tailSecond) (0 :: tailOutput) oldFlag
  have boundary : step (machine digit carry) (.inl finalCarry, atEnd) =
      some ((.inr (finalCarry, false)), ScanReturn.move (fun name : Fin 4 => decide (name ≠ 3)) .left prepared) := by
    simp only [step, machine, MultiTape.read, atEnd, frame, Turing.Tape.mk'_head,
      Turing.ListBlank.head_mk, List.headI_cons, ↓reduceIte, Option.map_some]
    congr 2
    funext name
    fin_cases name <;> simp [act, prepared, frame, ScanReturn.move, Turing.Tape.write_mk',
      Turing.Tape.move_left_mk', Turing.ListBlank.cons_mk, Turing.Tape.mk₁, Turing.Tape.mk₂]
  have returned := ScanReturn.from_end (machine digit carry) (.inl finalCarry)
    (.inr (finalCarry, false)) (.inr (finalCarry, true)) 0 (fun name : Fin 4 => decide (name ≠ 3)) rfl
    (by intro symbols nonblank; simp [machine, nonblank])
    (fun symbols name => (symbols name, if name = 3 then none else some .right))
    (by intro symbols blank; simp [machine, blank]) left.reverse leftFirst tailFirst atEnd prepared boundary
    (by simp [prepared, frame, word, List.map_reverse])
  have restored : Steps (machine digit carry) (left.length + 2) (.inl finalCarry, atEnd)
      ((.inr (finalCarry, true)), frame (0 :: leftFirst) (word left ++ 0 :: tailFirst)
        (0 :: leftSecond) (word right ++ 0 :: tailSecond)
        (0 :: leftOutput) (word low ++ 0 :: tailOutput) (data finalCarry)) := by
    simp only [List.length_reverse] at returned
    convert returned using 1
    congr 1
    funext name
    fin_cases name <;> simp only [act, MultiTape.read, Turing.Tape.write_self, ScanReturn.move_iterate,
      prepared, frame]
    · simpa [word, List.map_reverse, Turing.Tape.write_self] using
        (ScanReturn.restore_tape ((word left).reverse) leftFirst (0 :: tailFirst)).symm
    · simpa [word, List.map_reverse, sameLength, Turing.Tape.write_self] using
        (ScanReturn.restore_tape ((word right).reverse) leftSecond (0 :: tailSecond)).symm
    · simpa [word, List.map_reverse, lowLength, Turing.Tape.write_self] using
        (ScanReturn.restore_tape ((word low).reverse) leftOutput (0 :: tailOutput)).symm
    · rfl
  convert scanned.trans restored using 1; omega

def width (digits : ℕ) (name : Fin 4) : ℕ := if name = 3 then 1 else digits

def readOnly (name : Fin 4) : Bool := decide (name.val < 2)

private def invariant (digits : ℕ) (position : Fin 4 → ℤ) (state : State)
    (tapes : Tapes Alphabet) : Prop :=
  (∀ name, name ≠ 3 → position name = position 0) ∧ position 3 = 0 ∧
    (∀ index : ℤ, (tapes 0).nth (index - position 0) = 0 ↔
      index < 0 ∨ (digits : ℤ) ≤ index) ∧
    (match state with
     | .inl _ => 0 ≤ position 0 ∧ position 0 ≤ digits
     | .inr (_, finished) => if finished then position 0 = 0
                            else -1 ≤ position 0 ∧ position 0 < digits)

private theorem safe (digits : ℕ) (position : Fin 4 → ℤ) (state : State)
    (tapes : Tapes Alphabet) (nextState : State) (actions : Actions Alphabet)
    (valid : invariant digits position state tapes)
    (instruction : machine digit carry state (read tapes) = some (nextState, actions)) :
    Allowed (width digits) readOnly position (read tapes) actions ∧
      invariant digits (fun name => position name + displacement (actions name).2)
        nextState (act actions tapes) := by
  obtain ⟨synchronized, flagPosition, shape, bounds⟩ := valid
  have atHead := shape (position 0)
  simp only [sub_self, Turing.Tape.nth_zero] at atHead
  have preserveShape (source : (actions 0).1 = (tapes 0).head) :
      ∀ index : ℤ,
        (act actions tapes 0).nth
          (index - (position 0 + displacement (actions 0).2)) = 0 ↔
        index < 0 ∨ (digits : ℤ) ≤ index := by
    intro index
    rw [action_nth]
    by_cases equal : index = position 0
    · subst index
      simpa [source] using atHead
    · simpa [equal] using shape index
  cases state with
  | inl previous =>
    by_cases blank : (tapes 0).head = 0
    · simp only [machine, MultiTape.read, blank, ↓reduceIte, Option.some.injEq,
        Prod.mk.injEq] at instruction
      obtain ⟨rfl, rfl⟩ := instruction
      refine ⟨?_, ?_, ?_, preserveShape (by simp), ?_⟩
      · intro name premise
        by_cases flag : name = 3
        · subst name
          simp [readOnly, width, flagPosition] at premise
        · simp [flag, MultiTape.read]
      · intro name different
        simpa [displacement, different] using synchronized name different
      · simpa [displacement] using flagPosition
      · have outside := atHead.mp blank
        simp [displacement]
        omega
    · simp only [machine, MultiTape.read, blank, ↓reduceIte, Option.some.injEq,
        Prod.mk.injEq] at instruction
      obtain ⟨rfl, rfl⟩ := instruction
      have inside : ¬ (position 0 < 0 ∨ (digits : ℤ) ≤ position 0) := by
        exact fun outside => blank (atHead.mpr outside)
      refine ⟨?_, ?_, ?_, preserveShape (by simp), ?_⟩
      · intro name premise
        by_cases output : name = 2
        · subst name
          simp [readOnly, width] at premise
          rw [synchronized 2 (by decide)] at premise
          exact False.elim (inside premise)
        · simp [output, MultiTape.read]
      · intro name different
        simpa [displacement, different] using synchronized name different
      · simpa [displacement] using flagPosition
      · simp [displacement]
        omega
  | inr phase =>
    obtain ⟨memory, finished⟩ := phase
    cases finished with
    | false =>
      by_cases blank : (tapes 0).head = 0
      · simp only [machine, MultiTape.read, blank, Bool.false_eq_true, ↓reduceIte,
          Option.some.injEq, Prod.mk.injEq] at instruction
        obtain ⟨rfl, rfl⟩ := instruction
        refine ⟨(by intro name premise; rfl), ?_, ?_, preserveShape rfl, ?_⟩
        · intro name different
          simpa [displacement, different] using synchronized name different
        · simpa [displacement] using flagPosition
        · have outside := atHead.mp blank
          simp only [Bool.false_eq_true, ↓reduceIte] at bounds
          simp [displacement]
          omega
      · simp only [machine, MultiTape.read, blank, Bool.false_eq_true, ↓reduceIte,
          Option.some.injEq, Prod.mk.injEq] at instruction
        obtain ⟨rfl, rfl⟩ := instruction
        have inside : ¬ (position 0 < 0 ∨ (digits : ℤ) ≤ position 0) := by
          exact fun outside => blank (atHead.mpr outside)
        refine ⟨(by intro name premise; rfl), ?_, ?_, preserveShape rfl, ?_⟩
        · intro name different
          simpa [displacement, different] using synchronized name different
        · simpa [displacement] using flagPosition
        · simp [displacement]
          omega
    | true => simp [machine] at instruction

/-- Both operands stay immutable, all surrounding blanks stay blank, and the
low word and carry bit are fully overwritten even from uninitialized outputs. -/
theorem runs (previous : Bool) (left right : List Bool) (sameLength : right.length = left.length)
    (old : List Symbol) (oldLength : old.length = left.length) (oldFlag : Symbol) :
    Runs (width left.length) readOnly (machine digit carry) (2 * left.length + 2)
      (.inl previous) (fun _ => 0)
      (frame [0] (word left ++ [0]) [0] (word right ++ [0]) [0] (old ++ [0]) oldFlag)
      (.inr ((ripple digit carry previous left right).2, true)) (fun _ => 0)
      (frame [0] (word left ++ [0]) [0] (word right ++ [0]) [0]
        (word (ripple digit carry previous left right).1 ++ [0])
        (data (ripple digit carry previous left right).2)) := by
  have initial : invariant left.length (fun _ => 0) (.inl previous)
      (frame [0] (word left ++ [0]) [0] (word right ++ [0]) [0] (old ++ [0]) oldFlag) := by
    refine ⟨(by intro name different; rfl), rfl, ?_, ?_⟩
    · intro index
      simpa only [sub_zero, frame, ↓reduceIte] using word_nth_blank_iff left index
    · simp
  obtain ⟨finalPosition, trace, finalValid⟩ := Runs.of_steps_invariant (invariant left.length)
    (safe digit carry left.length)
    (steps digit carry previous left right sameLength old oldLength oldFlag [] [] [] [] [] [])
    (fun _ => 0) initial
  have zero : finalPosition = fun _ => 0 := by
    obtain ⟨synchronized, flagPosition, shape, bounds⟩ := finalValid
    have atZero : finalPosition 0 = 0 := by simpa using bounds
    funext name
    by_cases flag : name = 3
    · subst name; exact flagPosition
    · exact (synchronized name flag).trans atZero
  simpa only [zero, List.append_nil] using trace

/-- Two immutable binary operands produce their fixed-width ripple result and
carry on separate output tapes. -/
theorem contractSized {Parameter : Type} [Fintype Parameter] (capacity : Parameter) (digit carry : Bool → Bool → Bool → Bool) (previous : Bool) :
    CallingConvention.Realizes (domainsSized capacity) argumentReadOnly sizeTapes outputTapes
      (algorithm digit carry) (entry previous) exit
      (fun _assignment _input => True)
      (fun assignment input output =>
        (output false : Fin (2 ^ assignment capacity)).val =
          value (ripple digit carry previous
            (List.ofFn (fun index : Fin (assignment capacity) =>
              (BitVec.ofFin (input ⟨.inr 0, rfl⟩)).getLsbD index.val))
            (List.ofFn (fun index : Fin (assignment capacity) =>
              (BitVec.ofFin (input ⟨.inr 1, rfl⟩)).getLsbD index.val))).1 ∧
        output true =
          (ripple digit carry previous
            (List.ofFn (fun index : Fin (assignment capacity) =>
              (BitVec.ofFin (input ⟨.inr 0, rfl⟩)).getLsbD index.val))
            (List.ofFn (fun index : Fin (assignment capacity) =>
              (BitVec.ofFin (input ⟨.inr 1, rfl⟩)).getLsbD index.val))).2) := by
  refine ⟨(by intro parameter; rfl), (by intro name; cases name <;> rfl), ?_,
    2 * MvPolynomial.X capacity + MvPolynomial.C 3, ?_⟩
  · intro symbols
    simp [algorithm, exit, MultiTape.wire, MultiTape.withExit]
  · intro assignment input initial _ represented sizes
    let left := List.ofFn (fun index : Fin (assignment capacity) =>
      (BitVec.ofFin (input ⟨.inr 0, rfl⟩)).getLsbD index.val)
    let right := List.ofFn (fun index : Fin (assignment capacity) =>
      (BitVec.ofFin (input ⟨.inr 1, rfl⟩)).getLsbD index.val)
    have leftLength : left.length = assignment capacity := List.length_ofFn
    have rightLength : right.length = assignment capacity := List.length_ofFn
    obtain ⟨oldOutput, oldOutputLength, oldOutputEq⟩ := represented.2 (.inr 2) rfl
    obtain ⟨oldFlagList, oldFlagLength, oldFlagEq⟩ := represented.2 (.inr 3) rfl
    norm_num [domainsSized, EncodedDomain.booleans, EncodedDomain.fixed, EncodedDomain.ofCodec] at oldFlagLength
    obtain ⟨oldFlag, rfl⟩ := List.length_eq_one_iff.mp oldFlagLength
    simp only [domainsSized, EncodedDomain.binaryNaturals, EncodedDomain.ofCodec,
      EncodedDomain.width, MvPolynomial.eval_X] at oldOutputLength
    have leftValue : value left = (input ⟨.inr 0, rfl⟩ : Fin (2 ^ assignment capacity)).val :=
      Binary.value_bits (BitVec.ofFin (input ⟨.inr 0, rfl⟩))
    have rightValue : value right = (input ⟨.inr 1, rfl⟩ : Fin (2 ^ assignment capacity)).val :=
      Binary.value_bits (BitVec.ofFin (input ⟨.inr 1, rfl⟩))
    have leftFin : input ⟨.inr 0, rfl⟩ =
        (⟨value left, by simpa only [leftLength] using Binary.value_lt_pow_length left⟩ :
          Fin (2 ^ assignment capacity)) := Fin.ext leftValue.symm
    have rightFin : input ⟨.inr 1, rfl⟩ =
        (⟨value right, by simpa only [rightLength] using Binary.value_lt_pow_length right⟩ :
          Fin (2 ^ assignment capacity)) := Fin.ext rightValue.symm
    have leftEq : initial (.inr 0) = buffer (word left) := by
      rw [represented.1 (.inr 0) rfl]
      change encoded (EncodedDomain.binaryNaturals capacity) assignment (input ⟨.inr 0, rfl⟩) = _
      rw [leftFin]
      exact encoded_binaryNaturals capacity assignment left leftLength
    have rightEq : initial (.inr 1) = buffer (word right) := by
      rw [represented.1 (.inr 1) rfl]
      change encoded (EncodedDomain.binaryNaturals capacity) assignment (input ⟨.inr 1, rfl⟩) = _
      rw [rightFin]
      exact encoded_binaryNaturals capacity assignment right rightLength
    have localInitial :
        install dataTapes
          (frame [0] (word left ++ [0]) [0] (word right ++ [0]) [0]
            (oldOutput ++ [0]) oldFlag) initial = initial := by
      funext name
      cases name with
      | inl parameter =>
        apply install_outside
        rintro ⟨localName, equal⟩
        cases equal
      | inr name =>
        rw [show Sum.inr name = dataTapes name from rfl, install_at]
        fin_cases name
        · exact (buffer_padding (word left)).trans leftEq.symm
        · exact (buffer_padding (word right)).trans rightEq.symm
        · exact (buffer_padding oldOutput).trans oldOutputEq.symm
        · change buffer [oldFlag] = initial (.inr 3)
          exact oldFlagEq.symm
    let computed := ripple digit carry previous left right
    let outputWord : Fin (2 ^ assignment capacity) :=
      ⟨value computed.1, by
        have resultLength : computed.1.length = assignment capacity :=
          (BinaryRipple.ripple_length digit carry previous left right
            (rightLength.trans leftLength.symm)).trans leftLength
        simpa only [resultLength] using Binary.value_lt_pow_length computed.1⟩
    let output : Outputs (domainsSized capacity) outputTapes assignment
      | false => outputWord
      | true => computed.2
    have localTrace := runs digit carry previous left right
      (rightLength.trans leftLength.symm) oldOutput
      (by simpa [leftLength] using oldOutputLength) oldFlag
    have localTrace := localTrace.withExit (by
      intro symbols
      simp [machine])
    have wiredTrace := localTrace.wire dataTapes
      (fun name => ((domainsSized capacity) name).width assignment) argumentReadOnly
      (by
        intro name
        change ((domainsSized capacity) (.inr name)).width assignment = width left.length name
        fin_cases name <;> norm_num [domainsSized, dataTapes, width,
          EncodedDomain.binaryNaturals, EncodedDomain.booleans,
          EncodedDomain.fixed, leftLength, Nat.clog])
      (by
        intro name premise
        fin_cases name <;> simp [dataTapes, argumentReadOnly, readOnly] at premise ⊢)
      initial (fun _ => 0)
    rw [localInitial] at wiredTrace
    have positions : install dataTapes (fun _ : Fin 4 => (0 : ℤ))
        (fun _ : Sum Parameter (Fin 4) => (0 : ℤ)) = fun _ => 0 :=
      install_self dataTapes _
    rw [positions] at wiredTrace
    have trace : Runs (fun name => ((domainsSized capacity) name).width assignment) argumentReadOnly
        (algorithm digit carry) (2 * assignment capacity + 3) (entry previous)
        (fun _ => 0) initial exit (fun _ => 0)
        (install dataTapes
          (frame [0] (word left ++ [0]) [0] (word right ++ [0]) [0]
            (word computed.1 ++ [0]) (data computed.2)) initial) := by
      simpa [algorithm, entry, exit, computed, leftLength] using wiredTrace
    refine ⟨2 * assignment capacity + 3, output,
      install dataTapes
        (frame [0] (word left ++ [0]) [0] (word right ++ [0]) [0]
          (word computed.1 ++ [0]) (data computed.2)) initial, ?_, trace, ?_, ?_⟩
    · simp only [map_add, map_mul, map_ofNat, MvPolynomial.eval_X]
      omega
    · constructor
      · rfl
      · rfl
    · intro name
      cases name with
      | false =>
        change install dataTapes _ initial (dataTapes 2) = _
        rw [install_at]
        change Turing.Tape.mk' (Turing.ListBlank.mk [0])
          (Turing.ListBlank.mk (word computed.1 ++ [0])) =
            encoded (EncodedDomain.binaryNaturals capacity) assignment outputWord
        exact (buffer_padding (word computed.1)).trans (by
          simpa only [outputWord] using
            (encoded_binaryNaturals capacity assignment computed.1
              ((BinaryRipple.ripple_length digit carry previous left right
                (rightLength.trans leftLength.symm)).trans leftLength)).symm)
      | true =>
        change install dataTapes _ initial (dataTapes 3) = _
        rw [install_at]
        exact (encoded_booleans assignment computed.2).symm

/-- The original single-capacity calling convention is a specialization. -/
theorem contract (digit carry : Bool → Bool → Bool → Bool) (previous : Bool) :
    CallingConvention.Realizes domains argumentReadOnly sizeTapes outputTapes
      (algorithm digit carry) (entry previous) exit
      (fun _assignment _input => True)
      (fun assignment input output =>
        (output false : Fin (2 ^ assignment ())).val =
          value (ripple digit carry previous
            (List.ofFn (fun index : Fin (assignment ()) =>
              (BitVec.ofFin (input ⟨.inr 0, rfl⟩)).getLsbD index.val))
            (List.ofFn (fun index : Fin (assignment ()) =>
              (BitVec.ofFin (input ⟨.inr 1, rfl⟩)).getLsbD index.val))).1 ∧
        output true =
          (ripple digit carry previous
            (List.ofFn (fun index : Fin (assignment ()) =>
              (BitVec.ofFin (input ⟨.inr 0, rfl⟩)).getLsbD index.val))
            (List.ofFn (fun index : Fin (assignment ()) =>
              (BitVec.ofFin (input ⟨.inr 1, rfl⟩)).getLsbD index.val))).2) := by
  exact contractSized () digit carry previous

end Polytime2.StandardBinaryArithmetic
