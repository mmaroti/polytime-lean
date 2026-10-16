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

import Polytime2.CallingConvention
import Polytime2.Copy

/-! # Marker-free runtime-width copying

The source determines the extent of the copy. The destination may contain
blanks anywhere inside its reserved region. Both heads return to the first
cell, including when the source word is empty.
-/

namespace Polytime2.StandardTerminatedCopy

open MultiTape
open Binary (Symbol data word)
open Copy (frame)

def machine : Machine (fun _ : Bool => Symbol) (Fin 3) := fun state symbols =>
  match state.val with
  | 0 => if symbols false = 0 then
      some (1, fun name => (symbols name, some .left))
    else some (0, fun _ => (symbols false, some .right))
  | 1 => if symbols false = 0 then
      some (2, fun name => (symbols name, some .right))
    else some (1, fun name => (symbols name, some .left))
  | _ => none

private theorem forward (bits : List Bool) (old : List Symbol) (sameLength : old.length = bits.length)
    (sourceLeft sourceRight targetLeft targetRight : List Symbol) :
    Steps machine bits.length
      (0, frame sourceLeft (word bits ++ sourceRight) targetLeft (old ++ targetRight))
      (0, frame ((word bits).reverse ++ sourceLeft) sourceRight
        ((word bits).reverse ++ targetLeft) targetRight) := by
  induction bits generalizing old sourceLeft targetLeft with
  | nil =>
    have empty : old = [] := List.eq_nil_of_length_eq_zero sameLength
    subst old
    simpa [word] using Steps.zero (machine := machine) (0, frame sourceLeft sourceRight targetLeft targetRight)
  | cons bit bits hypothesis =>
    cases old with
    | nil => simp at sameLength
    | cons previous old =>
      have first : step machine
          (0, frame sourceLeft (word (bit :: bits) ++ sourceRight) targetLeft ((previous :: old) ++ targetRight)) =
          some (0, frame (data bit :: sourceLeft) (word bits ++ sourceRight)
            (data bit :: targetLeft) (old ++ targetRight)) := by
        have nonblank : data bit ≠ 0 := by cases bit <;> decide
        simp only [step, machine, Fin.val_zero, MultiTape.read, frame, word, List.map_cons, List.cons_append,
          Turing.Tape.mk'_head, Turing.ListBlank.head_mk, List.headI_cons, nonblank, ↓reduceIte, Option.map_some]
        congr 2
        funext name
        cases name <;>
          simp [act, frame, Turing.Tape.write_mk', Turing.Tape.move_right_mk', Turing.ListBlank.cons_mk]
      have rest := hypothesis old (by simpa using sameLength) (data bit :: sourceLeft) (data bit :: targetLeft)
      simpa [word, List.reverse_cons, List.append_assoc] using Steps.next first rest


private theorem return_head (bits : List Bool) (current : Symbol) (notBoundary : current ≠ 0)
    (sourceLeft sourceRight targetLeft targetRight : List Symbol) :
    Steps machine (bits.length + 2)
      (1, frame (word bits ++ 0 :: sourceLeft) (current :: sourceRight)
        (word bits ++ 0 :: targetLeft) (current :: targetRight))
      (2, frame (0 :: sourceLeft) ((word bits).reverse ++ current :: sourceRight)
        (0 :: targetLeft) ((word bits).reverse ++ current :: targetRight)) := by
  induction bits generalizing current sourceRight targetRight with
  | nil =>
    have first : step machine
        (1, frame (0 :: sourceLeft) (current :: sourceRight) (0 :: targetLeft) (current :: targetRight)) =
        some (1, frame sourceLeft (0 :: current :: sourceRight) targetLeft (0 :: current :: targetRight)) := by
      simp only [step, machine, Fin.val_one, MultiTape.read, frame, Turing.Tape.mk'_head,
        Turing.ListBlank.head_mk, List.headI_cons, notBoundary, ↓reduceIte, Option.map_some]
      congr 2
      funext name
      cases name <;> simp [act, frame, Turing.Tape.write_mk', Turing.Tape.move_left_mk', Turing.ListBlank.cons_mk]
    have second : step machine
        (1, frame sourceLeft (0 :: current :: sourceRight) targetLeft (0 :: current :: targetRight)) =
        some (2, frame (0 :: sourceLeft) (current :: sourceRight) (0 :: targetLeft) (current :: targetRight)) := by
      simp only [step, machine, Fin.val_one, MultiTape.read, frame, Turing.Tape.mk'_head,
        Turing.ListBlank.head_mk, List.headI_cons, ↓reduceIte, Option.map_some]
      congr 2
      funext name
      cases name <;> simp [act, frame, Turing.Tape.write_mk', Turing.Tape.move_right_mk', Turing.ListBlank.cons_mk]
    simpa [word] using Steps.next first (Steps.next second (.zero _))
  | cons bit bits hypothesis =>
    have first : step machine
        (1, frame (word (bit :: bits) ++ 0 :: sourceLeft) (current :: sourceRight)
          (word (bit :: bits) ++ 0 :: targetLeft) (current :: targetRight)) =
        some (1, frame (word bits ++ 0 :: sourceLeft) (data bit :: current :: sourceRight)
          (word bits ++ 0 :: targetLeft) (data bit :: current :: targetRight)) := by
      simp only [step, machine, Fin.val_one, MultiTape.read, frame, word, List.map_cons, List.cons_append,
        Turing.Tape.mk'_head, Turing.ListBlank.head_mk, List.headI_cons, notBoundary, ↓reduceIte, Option.map_some]
      congr 2
      funext name
      cases name <;> simp [act, frame, Turing.Tape.write_mk', Turing.Tape.move_left_mk', Turing.ListBlank.cons_mk]
    have notMarker : data bit ≠ 0 := by cases bit <;> decide
    have rest := hypothesis (data bit) notMarker (current :: sourceRight) (current :: targetRight)
    simpa [word, List.reverse_cons, List.append_assoc, Nat.add_assoc] using Steps.next first rest


/-- Copying uses a linear number of transitions and restores both heads. -/
theorem steps (bits : List Bool) (old : List Symbol)
    (sameLength : old.length = bits.length)
    (sourceLeft sourceRight targetLeft targetRight : List Symbol) :
    Steps machine (2 * bits.length + 2)
      (0, frame (0 :: sourceLeft) (word bits ++ 0 :: sourceRight)
        (0 :: targetLeft) (old ++ 0 :: targetRight))
      (2, frame (0 :: sourceLeft) (word bits ++ 0 :: sourceRight)
        (0 :: targetLeft) (word bits ++ 0 :: targetRight)) := by
  have copied := forward bits old sameLength (0 :: sourceLeft) (0 :: sourceRight)
    (0 :: targetLeft) (0 :: targetRight)
  have handover : step machine
      (0, frame ((word bits).reverse ++ 0 :: sourceLeft) (0 :: sourceRight)
        ((word bits).reverse ++ 0 :: targetLeft) (0 :: targetRight)) =
      some (1, frame (((word bits).reverse ++ 0 :: sourceLeft).tail)
        (((word bits).reverse ++ 0 :: sourceLeft).headI :: 0 :: sourceRight)
        (((word bits).reverse ++ 0 :: targetLeft).tail)
        (((word bits).reverse ++ 0 :: targetLeft).headI :: 0 :: targetRight)) := by
    simp only [step, machine, Fin.val_zero, MultiTape.read, frame, Turing.Tape.mk'_head,
      Turing.ListBlank.head_mk, List.headI_cons, ↓reduceIte, Option.map_some]
    congr 2
    funext name
    cases name <;> simp [act, frame, Turing.Tape.write_mk', Turing.Tape.move_left_mk',
      Turing.ListBlank.tail_mk, Turing.ListBlank.head_mk, Turing.ListBlank.cons_mk]
  cases reversed : bits.reverse with
  | nil =>
    have empty : bits = [] := by simpa using congrArg List.reverse reversed
    subst bits
    have finish : step machine
        (1, frame sourceLeft (0 :: 0 :: sourceRight) targetLeft (0 :: 0 :: targetRight)) =
        some (2, frame (0 :: sourceLeft) (0 :: sourceRight)
          (0 :: targetLeft) (0 :: targetRight)) := by
      simp only [step, machine, Fin.val_one, MultiTape.read, frame, Turing.Tape.mk'_head,
        Turing.ListBlank.head_mk, List.headI_cons, ↓reduceIte, Option.map_some]
      congr 2
      funext name
      cases name <;> simp [act, frame, Turing.Tape.write_mk', Turing.Tape.move_right_mk',
        Turing.ListBlank.cons_mk]
    simpa [word] using copied.trans (Steps.next handover (Steps.next finish (.zero _)))
  | cons bit remaining =>
    have restored := return_head remaining (data bit) (by cases bit <;> decide)
      sourceLeft (0 :: sourceRight) targetLeft (0 :: targetRight)
    have wordReverse : (word bits).reverse = data bit :: word remaining := by
      simp [word, ← List.map_reverse, reversed]
    have reconstruct : (word remaining).reverse ++ [data bit] = word bits := by
      have equal := congrArg List.reverse wordReverse
      simpa using equal.symm
    have length : bits.length = remaining.length + 1 := by
      have equal := congrArg List.length reversed
      simpa using equal
    simp only [wordReverse, List.cons_append, List.tail_cons, List.headI_cons] at handover
    rw [wordReverse] at copied
    have trace := copied.trans (Steps.next handover restored)
    have sourceEq : (word remaining).reverse ++ data bit :: 0 :: sourceRight =
        word bits ++ 0 :: sourceRight := by
      rw [← List.singleton_append, ← List.append_assoc, reconstruct]
    have targetEq : (word remaining).reverse ++ data bit :: 0 :: targetRight =
        word bits ++ 0 :: targetRight := by
      rw [← List.singleton_append, ← List.append_assoc, reconstruct]
    rw [sourceEq, targetEq] at trace
    convert trace using 1; omega

open CallingConvention

private def invariant (width : ℕ) (position : Bool → ℤ) (state : Fin 3)
    (tapes : Tapes (CallingConvention.Alphabet Bool)) : Prop :=
  position true = position false ∧
    (∀ index : ℤ, (tapes false).nth (index - position false) = 0 ↔
      index < 0 ∨ (width : ℤ) ≤ index) ∧
    (if state = 0 then 0 ≤ position false ∧ position false ≤ width
     else if state = 1 then -1 ≤ position false ∧ position false < width
     else position false = 0)

private theorem safe (width : ℕ) (position : Bool → ℤ) (state : Fin 3)
    (tapes : Tapes (CallingConvention.Alphabet Bool))
    (nextState : Fin 3) (actions : Actions (CallingConvention.Alphabet Bool))
    (valid : invariant width position state tapes)
    (instruction : machine state (read tapes) = some (nextState, actions)) :
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
  fin_cases state <;> simp only [machine] at instruction
  · by_cases blank : (tapes false).head = 0
    · simp only [MultiTape.read, blank, ↓reduceIte, Option.some.injEq,
        Prod.mk.injEq] at instruction
      obtain ⟨rfl, rfl⟩ := instruction
      refine ⟨(by intro name premise; rfl), ?_⟩
      refine ⟨by simpa [displacement] using synchronized, preserveShape rfl, ?_⟩
      simp only [Fin.zero_eta, Fin.isValue, ↓reduceIte] at bounds
      simp only [Fin.isValue, show (1 : Fin 3) ≠ 0 by decide, ↓reduceIte, displacement]
      have outside := atHead.mp blank
      norm_num at bounds ⊢
      omega
    · simp only [MultiTape.read, blank, ↓reduceIte, Option.some.injEq,
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
        simp only [Fin.isValue, ↓reduceIte, displacement]
        omega
  · by_cases blank : (tapes false).head = 0
    · simp only [MultiTape.read, blank, ↓reduceIte, Option.some.injEq,
        Prod.mk.injEq] at instruction
      obtain ⟨rfl, rfl⟩ := instruction
      refine ⟨(by intro name premise; rfl), ?_⟩
      refine ⟨by simpa [displacement] using synchronized, preserveShape rfl, ?_⟩
      simp only [Fin.isValue] at bounds
      simp only [Fin.isValue, show (2 : Fin 3) ≠ 0 by decide,
        show (2 : Fin 3) ≠ 1 by decide, ↓reduceIte, displacement]
      have outside := atHead.mp blank
      norm_num at bounds ⊢
      omega
    · simp only [MultiTape.read, blank, ↓reduceIte, Option.some.injEq,
        Prod.mk.injEq] at instruction
      obtain ⟨rfl, rfl⟩ := instruction
      have inside : ¬ (position false < 0 ∨ (width : ℤ) ≤ position false) := by
        exact fun outside => blank (atHead.mpr outside)
      refine ⟨(by intro name premise; rfl), ?_⟩
      refine ⟨by simpa [displacement] using synchronized, preserveShape rfl, ?_⟩
      simp only [Fin.isValue, show (1 : Fin 3) ≠ 0 by decide, ↓reduceIte, displacement]
      omega
  · simp at instruction

/-- The marker-free controller obeys the convention at every transition,
including on an empty region and while crossing either surrounding blank. -/
theorem runs (bits : List Bool) (old : List Symbol) (sameLength : old.length = bits.length) :
    Runs (fun _ : Bool => bits.length) (fun name => !name) machine
      (2 * bits.length + 2) 0 (fun _ => 0)
      (frame [0] (word bits ++ [0]) [0] (old ++ [0]))
      2 (fun _ => 0) (frame [0] (word bits ++ [0]) [0] (word bits ++ [0])) := by
  have initial : invariant bits.length (fun _ => 0) 0
      (frame [0] (word bits ++ [0]) [0] (old ++ [0])) := by
    refine ⟨rfl, ?_, ?_⟩
    · intro index
      simpa only [sub_zero, frame] using word_nth_blank_iff bits index
    · simp
  obtain ⟨finalPosition, trace, finalValid⟩ := Runs.of_steps_invariant (invariant bits.length)
    (safe bits.length) (steps bits old sameLength [] [] [] []) (fun _ => 0) initial
  have zero : finalPosition = fun _ => 0 := by
    obtain ⟨synchronized, shape, bounds⟩ := finalValid
    have atZero : finalPosition false = 0 := by simpa using bounds
    funext name
    cases name with
    | false => exact atZero
    | true => exact synchronized.trans atZero
  simpa only [zero] using trace

-- parameterLevel: size names bounding the runtime number of copied bits.
universe parameterLevel

-- carrierLevel: mathematical elements copied by the routine.
universe carrierLevel

variable {Parameter : Type parameterLevel} [Fintype Parameter]

/-- Size arguments and the source are immutable; only the result is writable. -/
def readOnly : Sum Parameter Bool → Bool
  | .inl _ => true
  | .inr name => !name

/-- Every argument tape, including each unary size argument, has a domain. -/
def domains (domain : EncodedDomain.{parameterLevel, carrierLevel} Parameter) :
    Sum Parameter Bool → EncodedDomain.{parameterLevel, carrierLevel} Parameter
  | .inl parameter => EncodedDomain.unary parameter
  | .inr _ => domain

def sizeTapes : Parameter ↪ Sum Parameter Bool :=
  ⟨Sum.inl, by intro first second equal; cases equal; rfl⟩

def dataTapes : Bool ↪ Sum Parameter Bool :=
  ⟨Sum.inr, by intro first second equal; cases equal; rfl⟩

/-- Only the result tape is a public output. -/
def outputTapes : Unit ↪ Sum Parameter Bool := oneTape (.inr true)

/-- The controller is independent of the runtime width. Size inputs are idle. -/
noncomputable def algorithm : Machine (CallingConvention.Alphabet (Sum Parameter Bool)) (Fin 3) :=
  MultiTape.wire dataTapes machine

/-- Copy any polynomial-width encoded domain, including its immutable unary
size inputs, with arbitrary initial output contents and restored heads. -/
theorem contract (domain : EncodedDomain.{parameterLevel, carrierLevel} Parameter) :
    CallingConvention.Realizes (domains domain) readOnly sizeTapes outputTapes algorithm 0 2
      (fun _ _ => True)
      (fun _ input output => output () = input ⟨.inr false, rfl⟩) := by
  obtain ⟨bound, widthBound⟩ := domain.polynomial_width
  refine ⟨(by intro parameter; rfl), (by intro name; rfl), (by intro symbols; simp [algorithm, MultiTape.wire, machine]),
    2 * bound + 2, ?_⟩
  intro assignment input initial valid represented sizes
  let bits := List.ofFn (fun index : Fin (domain.width assignment) =>
    (domain.encode assignment (input ⟨.inr false, rfl⟩)).getLsbD index.val)
  have bitsLength : bits.length = domain.width assignment := List.length_ofFn
  obtain ⟨old, oldLength, target⟩ := represented.2 (.inr true) rfl
  have source := represented.1 (.inr false) rfl
  have sourceEq : initial (.inr false) = buffer (word bits) := source
  have targetEq : initial (.inr true) = buffer old := target
  have start : install dataTapes (frame [0] (word bits ++ [0]) [0] (old ++ [0])) initial = initial := by
    funext name
    cases name with
    | inl parameter =>
      apply install_outside
      rintro ⟨name, equal⟩
      cases equal
    | inr name =>
      rw [show Sum.inr name = dataTapes name from rfl, install_at]
      cases name with
      | false =>
        change Turing.Tape.mk' _ _ = initial (.inr false)
        rw [buffer_padding]
        exact sourceEq.symm
      | true =>
        change Turing.Tape.mk' _ _ = initial (.inr true)
        rw [buffer_padding]
        exact targetEq.symm
  have trace := (runs bits old (oldLength.trans bitsLength.symm)).wire dataTapes
    (fun name => (domains domain name).width assignment) readOnly
    (by intro name; exact bitsLength.symm) (by intro name premise; exact premise) initial (fun _ => 0)
  have positions : install (dataTapes (Parameter := Parameter)) (fun _ : Bool => (0 : ℤ))
      (fun _ : Sum Parameter Bool => (0 : ℤ)) = fun _ => 0 := by
    exact install_self dataTapes (fun _ : Sum Parameter Bool => (0 : ℤ))
  rw [start, positions] at trace
  let output : Outputs (domains domain) outputTapes assignment := fun _ => input ⟨.inr false, rfl⟩
  refine ⟨2 * bits.length + 2, output,
    install dataTapes (frame [0] (word bits ++ [0]) [0] (word bits ++ [0])) initial,
    ?_, ?_, rfl, ?_⟩
  · have bounded := widthBound assignment
    simp only [map_add, map_mul, map_ofNat]
    omega
  · exact trace
  · intro name
    cases name
    change install dataTapes _ initial (dataTapes true) = encoded domain assignment _
    rw [install_at]
    exact buffer_padding (word bits)

end Polytime2.StandardTerminatedCopy
