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
import Polytime2.StandardBinaryScan

/-! # A marker-free binary nonzero test

An immutable runtime-width binary word produces one Boolean bit on a separate
tape. The output may initially be blank; both heads finish at their starts.
-/

namespace Polytime2.StandardBinaryGuard

open MultiTape CallingConvention
open Binary (Symbol data word)
open Copy (frame)

abbrev State := Bool × Fin 3
abbrev Alphabet := CallingConvention.Alphabet Bool

def machine : Machine Alphabet State := fun (flag, phase) symbols =>
  match phase.val with
  | 0 => if symbols false = 0 then
      some ((flag, 1), fun name => (symbols name, if name then none else some .left))
    else some ((flag || decide (symbols false = 2), 0),
      fun name => if name then (symbols name, none) else (symbols name, some .right))
  | 1 => if symbols false = 0 then
      some ((false, 2), fun name => if name then (data flag, none) else (symbols name, some .right))
    else some ((flag, 1), fun name => if name then (symbols name, none) else (symbols name, some .left))
  | _ => none

private theorem forward (bits : List Bool) (flag : Bool)
    (sourceLeft sourceRight flagLeft flagRight : List Symbol) (oldFlag : Symbol) :
    Steps machine bits.length
      ((flag, 0), frame sourceLeft (word bits ++ sourceRight) flagLeft (oldFlag :: flagRight))
      ((flag || bits.any id, 0), frame ((word bits).reverse ++ sourceLeft) sourceRight flagLeft (oldFlag :: flagRight)) := by
  induction bits generalizing flag sourceLeft with
  | nil => simpa [word] using Steps.zero (machine := machine) ((flag, 0), frame sourceLeft sourceRight flagLeft (oldFlag :: flagRight))
  | cons bit bits hypothesis =>
    have nonblank : data bit ≠ 0 := by cases bit <;> decide
    have digitFlag : decide (data bit = 2) = bit := by cases bit <;> decide
    have first : step machine
        ((flag, 0), frame sourceLeft (word (bit :: bits) ++ sourceRight) flagLeft (oldFlag :: flagRight)) =
        some ((flag || bit, 0), frame (data bit :: sourceLeft) (word bits ++ sourceRight) flagLeft (oldFlag :: flagRight)) := by
      simp only [step, machine, Fin.val_zero, MultiTape.read, frame, word, List.map_cons, List.cons_append,
        Turing.Tape.mk'_head, Turing.ListBlank.head_mk, List.headI_cons, nonblank,
        digitFlag, ↓reduceIte, Option.map_some]
      congr 2
      funext name
      cases name <;>
        simp [act, frame, Turing.Tape.write_mk', Turing.Tape.move_right_mk', Turing.ListBlank.cons_mk]
    have rest := hypothesis (flag || bit) (data bit :: sourceLeft)
    simpa [word, List.reverse_cons, List.append_assoc, Bool.or_assoc] using Steps.next first rest

private theorem return_head (bits : List Bool) (current : Symbol) (notBoundary : current ≠ 0)
    (flag : Bool) (sourceLeft sourceRight flagLeft flagRight : List Symbol) (oldFlag : Symbol) :
    Steps machine (bits.length + 2)
      ((flag, 1), frame (word bits ++ 0 :: sourceLeft) (current :: sourceRight) flagLeft (oldFlag :: flagRight))
      ((false, 2), frame (0 :: sourceLeft) ((word bits).reverse ++ current :: sourceRight) flagLeft (data flag :: flagRight)) := by
  induction bits generalizing current sourceRight with
  | nil =>
    have first : step machine
        ((flag, 1), frame (0 :: sourceLeft) (current :: sourceRight) flagLeft (oldFlag :: flagRight)) =
        some ((flag, 1), frame sourceLeft (0 :: current :: sourceRight) flagLeft (oldFlag :: flagRight)) := by
      simp only [step, machine, Fin.val_one, MultiTape.read, frame, Turing.Tape.mk'_head,
        Turing.ListBlank.head_mk, List.headI_cons, notBoundary, ↓reduceIte, Option.map_some]
      congr 2
      funext name
      cases name <;>
        simp [act, frame, Turing.Tape.write_mk', Turing.Tape.move_left_mk', Turing.ListBlank.cons_mk]
    have second : step machine
        ((flag, 1), frame sourceLeft (0 :: current :: sourceRight) flagLeft (oldFlag :: flagRight)) =
        some ((false, 2), frame (0 :: sourceLeft) (current :: sourceRight) flagLeft (data flag :: flagRight)) := by
      simp only [step, machine, Fin.val_one, MultiTape.read, frame, Turing.Tape.mk'_head,
        Turing.ListBlank.head_mk, List.headI_cons, ↓reduceIte, Option.map_some]
      congr 2
      funext name
      cases name <;>
        simp [act, frame, Turing.Tape.write_mk', Turing.Tape.move_right_mk', Turing.ListBlank.cons_mk]
    simpa [word] using Steps.next first (Steps.next second (.zero _))
  | cons bit bits hypothesis =>
    have first : step machine
        ((flag, 1), frame (word (bit :: bits) ++ 0 :: sourceLeft) (current :: sourceRight) flagLeft (oldFlag :: flagRight)) =
        some ((flag, 1), frame (word bits ++ 0 :: sourceLeft) (data bit :: current :: sourceRight) flagLeft (oldFlag :: flagRight)) := by
      simp only [step, machine, Fin.val_one, MultiTape.read, frame, word, List.map_cons, List.cons_append,
        Turing.Tape.mk'_head, Turing.ListBlank.head_mk, List.headI_cons, notBoundary, ↓reduceIte, Option.map_some]
      congr 2
      funext name
      cases name <;>
        simp [act, frame, Turing.Tape.write_mk', Turing.Tape.move_left_mk', Turing.ListBlank.cons_mk]
    have notMarker : data bit ≠ 0 := by cases bit <;> decide
    have rest := hypothesis (data bit) notMarker (current :: sourceRight)
    simpa [word, List.reverse_cons, List.append_assoc, Nat.add_assoc] using Steps.next first rest

theorem steps (bits : List Bool) (oldFlag : Symbol) :
    Steps machine (2 * bits.length + 2)
      ((false, 0), frame [0] (word bits ++ [0]) [0] [oldFlag, 0])
      ((false, 2), frame [0] (word bits ++ [0]) [0] [data (bits.any id), 0]) := by
  cases reversed : bits.reverse with
  | nil =>
    have empty : bits = [] := List.reverse_eq_nil_iff.mp reversed
    subst bits
    have first : step machine ((false, 0), frame [0] [0] [0] [oldFlag, 0]) =
        some ((false, 1), frame [] [0, 0] [0] [oldFlag, 0]) := by
      simp only [step, machine, Fin.val_zero, MultiTape.read, frame, Turing.Tape.mk'_head,
        Turing.ListBlank.head_mk, List.headI_cons, ↓reduceIte, Option.map_some]
      congr 2
      funext name
      cases name <;> simp [act, frame, Turing.Tape.write_mk', Turing.Tape.move_left_mk', Turing.ListBlank.cons_mk]
    have second : step machine ((false, 1), frame [] [0, 0] [0] [oldFlag, 0]) =
        some ((false, 2), frame [0] [0] [0] [data false, 0]) := by
      simp only [step, machine, Fin.val_one, MultiTape.read, frame, Turing.Tape.mk'_head,
        Turing.ListBlank.head_mk, List.headI_cons, ↓reduceIte, Option.map_some]
      congr 2
      funext name
      cases name <;> simp [act, frame, Turing.Tape.write_mk', Turing.Tape.move_right_mk', Turing.ListBlank.cons_mk]
    exact Steps.next first (Steps.next second (.zero _))
  | cons last rest =>
    have original : bits = (last :: rest).reverse := by rw [← reversed, List.reverse_reverse]
    have scanned := forward bits false [0] [0] [0] [0] oldFlag
    simp only [Bool.false_or, word, ← List.map_reverse, reversed, List.map_cons, List.cons_append] at scanned
    have handover : step machine
        ((bits.any id, 0), frame (data last :: word rest ++ [0]) [0] [0] [oldFlag, 0]) =
        some ((bits.any id, 1), frame (word rest ++ [0]) [data last, 0] [0] [oldFlag, 0]) := by
      simp only [step, machine, Fin.val_zero, MultiTape.read, frame, Turing.Tape.mk'_head,
        Turing.ListBlank.head_mk, List.headI_cons, ↓reduceIte, Option.map_some]
      congr 2
      funext name
      cases name <;> simp [act, frame, Turing.Tape.write_mk', Turing.Tape.move_left_mk', Turing.ListBlank.cons_mk]
    have nonblank : data last ≠ 0 := by cases last <;> decide
    have returned := return_head rest (data last) nonblank (bits.any id) [] [0] [0] [0] oldFlag
    have complete := scanned.trans (Steps.next handover returned)
    have length : bits.length = rest.length + 1 := by
      have lengths := congrArg List.length reversed
      simpa using lengths
    convert complete using 1 <;>
      simp [word, original, List.reverse_cons, List.append_assoc]
    omega

def widths (digits : ℕ) (name : Bool) : ℕ := if name then 1 else digits

def readOnly (name : Bool) : Bool := !name

private def invariant (digits : ℕ) (position : Bool → ℤ) (state : State)
    (tapes : Tapes Alphabet) : Prop :=
  position true = 0 ∧
    (∀ index : ℤ, (tapes false).nth (index - position false) = 0 ↔
      index < 0 ∨ (digits : ℤ) ≤ index) ∧
    (if state.2 = 0 then 0 ≤ position false ∧ position false ≤ digits
     else if state.2 = 1 then -1 ≤ position false ∧ position false < digits
     else position false = 0)

private theorem safe (digits : ℕ) (position : Bool → ℤ) (state : State)
    (tapes : Tapes Alphabet) (nextState : State) (actions : Actions Alphabet)
    (valid : invariant digits position state tapes)
    (instruction : machine state (MultiTape.read tapes) = some (nextState, actions)) :
    Allowed (widths digits) readOnly position (MultiTape.read tapes) actions ∧
      invariant digits (fun name => position name + displacement (actions name).2)
        nextState (act actions tapes) := by
  obtain ⟨flagPosition, shape, bounds⟩ := valid
  have atHead := shape (position false)
  simp only [sub_self, Turing.Tape.nth_zero] at atHead
  have allowed (source : (actions false).1 = (tapes false).head) :
      Allowed (widths digits) readOnly position (MultiTape.read tapes) actions := by
    intro name premise
    cases name with
    | false => exact source
    | true => simp [readOnly, widths, flagPosition] at premise
  have preserveShape (source : (actions false).1 = (tapes false).head) :
      ∀ index : ℤ, (act actions tapes false).nth
        (index - (position false + displacement (actions false).2)) = 0 ↔
        index < 0 ∨ (digits : ℤ) ≤ index := by
    intro index
    rw [action_nth]
    by_cases equal : index = position false
    · subst index
      simpa [source] using atHead
    · simpa [equal] using shape index
  obtain ⟨flag, phase⟩ := state
  fin_cases phase
  · by_cases blank : (tapes false).head = 0
    · simp only [machine, MultiTape.read, blank, ↓reduceIte,
        Option.some.injEq, Prod.mk.injEq] at instruction
      obtain ⟨rfl, rfl⟩ := instruction
      refine ⟨allowed rfl, ?_⟩
      refine ⟨by simpa [displacement] using flagPosition, preserveShape rfl, ?_⟩
      have outside := atHead.mp blank
      simp at bounds
      simp [displacement]
      omega
    · simp only [machine, MultiTape.read, blank, ↓reduceIte,
        Option.some.injEq, Prod.mk.injEq] at instruction
      obtain ⟨rfl, rfl⟩ := instruction
      refine ⟨allowed rfl, ?_⟩
      refine ⟨by simpa [displacement] using flagPosition, preserveShape rfl, ?_⟩
      have inside : ¬ (position false < 0 ∨ (digits : ℤ) ≤ position false) :=
        fun outside => blank (atHead.mpr outside)
      simp at bounds
      simp [displacement]
      omega
  · by_cases blank : (tapes false).head = 0
    · simp only [machine, MultiTape.read, blank, ↓reduceIte,
        Option.some.injEq, Prod.mk.injEq] at instruction
      obtain ⟨rfl, rfl⟩ := instruction
      refine ⟨allowed rfl, ?_⟩
      refine ⟨by simpa [displacement] using flagPosition, preserveShape rfl, ?_⟩
      have outside := atHead.mp blank
      simp at bounds
      simp [displacement]
      omega
    · simp only [machine, MultiTape.read, blank, ↓reduceIte,
        Option.some.injEq, Prod.mk.injEq] at instruction
      obtain ⟨rfl, rfl⟩ := instruction
      refine ⟨allowed rfl, ?_⟩
      refine ⟨by simpa [displacement] using flagPosition, preserveShape rfl, ?_⟩
      have inside : ¬ (position false < 0 ∨ (digits : ℤ) ≤ position false) :=
        fun outside => blank (atHead.mpr outside)
      simp at bounds
      simp [displacement]
      omega
  · simp [machine] at instruction

/-- The source and outside cells stay unchanged at every transition. The one-bit
output is overwritten even when blank, including for a zero-width source. -/
theorem runs (bits : List Bool) (oldFlag : Symbol) :
    Runs (widths bits.length) readOnly machine (2 * bits.length + 2)
      (false, 0) (fun _ => 0) (frame [0] (word bits ++ [0]) [0] [oldFlag, 0])
      (false, 2) (fun _ => 0) (frame [0] (word bits ++ [0]) [0] [data (bits.any id), 0]) := by
  have initial : invariant bits.length (fun _ => 0) (false, 0)
      (frame [0] (word bits ++ [0]) [0] [oldFlag, 0]) := by
    refine ⟨rfl, ?_, by simp⟩
    intro index
    simpa only [sub_zero, frame] using word_nth_blank_iff bits index
  obtain ⟨finalPosition, trace, finalValid⟩ := Runs.of_steps_invariant (invariant bits.length)
    (safe bits.length) (steps bits oldFlag) (fun _ => 0) initial
  have zero : finalPosition = fun _ => 0 := by
    obtain ⟨flagAtZero, shape, bounds⟩ := finalValid
    funext name
    cases name with
    | false => simpa using bounds
    | true => exact flagAtZero
  simpa only [zero] using trace

/-- The result is a one-bit Boolean, independently of the counter's capacity. -/
abbrev domains : Sum Unit Bool → EncodedDomain Unit :=
  StandardBinaryScan.domains (EncodedDomain.binaryNaturals ()) EncodedDomain.booleans

noncomputable def algorithm : Machine (CallingConvention.Alphabet (Sum Unit Bool)) State :=
  MultiTape.wire StandardTerminatedCopy.dataTapes machine

/-- A polynomial-time nonzero test on a canonical bounded natural argument. -/
theorem contract : CallingConvention.Realizes domains StandardTerminatedCopy.readOnly
    StandardTerminatedCopy.sizeTapes StandardTerminatedCopy.outputTapes algorithm (false, 0) (false, 2)
    (fun _ _ => True) (fun assignment input output =>
      output () = decide (0 < (input ⟨.inr false, rfl⟩ : Fin (2 ^ assignment ())).val)) := by
  refine ⟨(by intro parameter; rfl), (by intro name; rfl), (by intro symbols; simp [algorithm, MultiTape.wire, machine]),
    2 * MvPolynomial.X () + 2, ?_⟩
  intro assignment input initial valid represented sizes
  let bits := List.ofFn (fun index : Fin (assignment ()) =>
    (BitVec.ofFin (input ⟨.inr false, rfl⟩)).getLsbD index.val)
  have bitsLength : bits.length = assignment () := List.length_ofFn
  have bitsValue : Binary.value bits = (input ⟨.inr false, rfl⟩ : Fin (2 ^ assignment ())).val :=
    Binary.value_bits (BitVec.ofFin (input ⟨.inr false, rfl⟩))
  obtain ⟨old, oldLength, targetEq⟩ := represented.2 (.inr true) rfl
  change old.length = 1 at oldLength
  obtain ⟨oldFlag, rfl⟩ := List.length_eq_one_iff.mp oldLength
  have sourceEq : initial (.inr false) = buffer (word bits) := represented.1 (.inr false) rfl
  have start : install StandardTerminatedCopy.dataTapes
      (frame [0] (word bits ++ [0]) [0] [oldFlag, 0]) initial = initial := by
    funext name
    cases name with
    | inl parameter =>
      apply install_outside
      rintro ⟨name, equal⟩
      cases equal
    | inr name =>
      change install StandardTerminatedCopy.dataTapes _ _ (StandardTerminatedCopy.dataTapes name) = _
      rw [install_at]
      cases name with
      | false => exact (buffer_padding (word bits)).trans sourceEq.symm
      | true => exact (buffer_padding [oldFlag]).trans targetEq.symm
  have trace := (runs bits oldFlag).wire StandardTerminatedCopy.dataTapes
    (fun name => (domains name).width assignment) StandardTerminatedCopy.readOnly
    (by
      intro name
      change (StandardBinaryScan.domains (EncodedDomain.binaryNaturals ()) EncodedDomain.booleans (.inr name)).width assignment = _
      cases name <;> norm_num [StandardBinaryScan.domains, EncodedDomain.binaryNaturals,
        EncodedDomain.booleans, EncodedDomain.fixed, widths, bitsLength])
    (by intro name premise; exact premise) initial (fun _ => 0)
  have positions : install StandardTerminatedCopy.dataTapes (fun _ : Bool => (0 : ℤ))
      (fun _ : Sum Unit Bool => (0 : ℤ)) = fun _ => 0 := install_self StandardTerminatedCopy.dataTapes _
  rw [positions, start] at trace
  let output : Outputs domains StandardTerminatedCopy.outputTapes assignment := fun _ => bits.any id
  refine ⟨2 * bits.length + 2, output,
    install StandardTerminatedCopy.dataTapes
      (frame [0] (word bits ++ [0]) [0] [data (bits.any id), 0]) initial,
    ?_, trace, ?_, ?_⟩
  · simp only [map_add, map_mul, map_ofNat, MvPolynomial.eval_X]
    omega
  · change bits.any id = decide (0 < _)
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq, bitsValue] using Binary.any_iff_positive bits
  · intro name
    cases name
    change install StandardTerminatedCopy.dataTapes _ _ (StandardTerminatedCopy.dataTapes true) = _
    rw [install_at]
    exact (buffer_padding [data (bits.any id)]).trans (encoded_booleans assignment (bits.any id)).symm

end Polytime2.StandardBinaryGuard
