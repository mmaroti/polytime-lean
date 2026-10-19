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

import Polytime2.Primitives.FixedHead
import Polytime2.Machine.CallingConvention

/-! # Safe movement within fixed tape regions

Movement writes every scanned symbol back unchanged. The fixed movement count
is a specialization constant, while head positions remain proof annotations.
-/

namespace Polytime2.StandardHead

open MultiTape CallingConvention

-- tapeLevel: the tape roles moved together by this command.
universe tapeLevel
variable {TapeName : Type tapeLevel}

private theorem remaining_runs (count remaining : ℕ) (fits : remaining < count + 1)
    (direction : Turing.Dir) (width : TapeName → ℕ) (readOnly : TapeName → Bool)
    (position : TapeName → ℤ) (tapes : Tapes (CallingConvention.Alphabet TapeName)) :
    Runs width readOnly (Move.machine count direction) remaining ⟨remaining, fits⟩ position tapes 0
      (fun name => position name + remaining * displacement (some direction))
      (fun name => (Turing.Tape.move direction)^[remaining] (tapes name)) := by
  induction remaining generalizing position tapes with
  | zero => simpa using Runs.zero (machine := Move.machine count direction) 0 position tapes
  | succ remaining hypothesis =>
    have smaller : remaining < count + 1 := by omega
    have instruction : Move.machine count direction ⟨remaining + 1, fits⟩ (MultiTape.read tapes) =
        some (⟨remaining, smaller⟩, fun name => (MultiTape.read tapes name, some direction)) := by
      simp [Move.machine]
    have rest := hypothesis smaller (fun name => position name + displacement (some direction))
      (fun name => (tapes name).move direction)
    have first := Runs.next instruction (by intro name premise; rfl) rest
    convert first using 1
    · funext name
      simp only [Nat.cast_add, Nat.cast_one]
      ring
    · funext name
      exact Function.iterate_succ_apply _ _ _

/-- Fixed movement preserves inputs and all cells outside declared regions. -/
theorem move_runs (count : ℕ) (direction : Turing.Dir)
    (width : TapeName → ℕ) (readOnly : TapeName → Bool) (position : TapeName → ℤ)
    (tapes : Tapes (CallingConvention.Alphabet TapeName)) :
    Runs width readOnly (Move.machine count direction) count (Fin.last count) position tapes 0
      (fun name => position name + count * displacement (some direction))
      (fun name => (Turing.Tape.move direction)^[count] (tapes name)) :=
  remaining_runs count count (Nat.lt_succ_self count) direction width readOnly position tapes


namespace BlankReturn

open Binary (Symbol data word)

abbrev Alphabet := CallingConvention.Alphabet Unit

def machine : Machine Alphabet (Fin 3) := fun phase symbols =>
  match phase.val with
  | 0 => if symbols () = 0 then some (2, stationary symbols) else some (1, stationary symbols)
  | 1 => if symbols () = 0 then some (2, fun _ => (symbols (), some .right))
      else some (1, fun _ => (symbols (), some .left))
  | _ => none

private theorem move_run (width : ℕ) (source : Turing.Tape Symbol) (offset : ℤ)
    (state nextState : Fin 3) (direction : Turing.Dir)
    (instruction : machine state (fun _ => source.head) =
      some (nextState, fun _ => (source.head, some direction))) :
    Runs (fun _ : Unit => width) (fun _ => true) machine 1 state (fun _ => offset) (fun _ => source)
      nextState (fun _ => offset + displacement (some direction)) (fun _ => source.move direction) := by
  apply Runs.next instruction (by intro name premise; rfl)
  have moved : act (fun _ : Unit => (source.head, some direction)) (fun _ => source) =
      fun _ => source.move direction := by
    funext name
    simp [MultiTape.act, Turing.Tape.write_self]
  rw [moved]
  exact .zero _ _ _

private theorem buffer_left_blank (contents : List Symbol) :
    Turing.Tape.mk' (Turing.ListBlank.mk [0]) (Turing.ListBlank.mk contents) = buffer contents := by
  have left : Turing.ListBlank.mk ([0] : List Symbol) = Turing.ListBlank.mk [] :=
    Quotient.sound (Or.inr ⟨1, by simp⟩)
  simp only [left, buffer, Turing.Tape.mk₁, Turing.Tape.mk₂]

private theorem buffer_append_blank (contents : List Symbol) :
    buffer (contents ++ [0]) = buffer contents :=
  (buffer_left_blank (contents ++ [0])).symm.trans (buffer_padding contents)

private theorem rewind_runs (left : List Bool) (current : Symbol) (nonblank : current ≠ 0)
    (right : List Symbol) (width : ℕ) :
    Runs (fun _ : Unit => width) (fun _ => true) machine (left.length + 2)
      1 (fun _ => (left.length : ℤ)) (Binary.tape (word left ++ [0]) (current :: right))
      2 (fun _ => 0) (fun _ => buffer (word left.reverse ++ current :: right)) := by
  induction left generalizing current right with
  | nil =>
    have first := move_run width
      (Turing.Tape.mk' (Turing.ListBlank.mk [0]) (Turing.ListBlank.mk (current :: right)))
      0 1 1 .left (by simp [machine, nonblank])
    simp [displacement, Turing.Tape.move_left_mk', Turing.ListBlank.cons_mk] at first
    have second := move_run width
      (Turing.Tape.mk' (Turing.ListBlank.mk []) (Turing.ListBlank.mk (0 :: current :: right)))
      (-1) 1 2 .right (by simp [machine])
    simp [displacement, Turing.Tape.move_right_mk', Turing.ListBlank.cons_mk] at second
    have complete := first.trans second
    simp only [List.length_nil, Nat.cast_zero, zero_add, word, List.map_nil,
      List.nil_append, List.reverse_nil, buffer_left_blank] at complete ⊢
    have canonical : Binary.tape [0] (current :: right) = fun _ => buffer (current :: right) := by
      funext name
      exact buffer_left_blank _
    rw [canonical]
    exact complete
  | cons bit bits hypothesis =>
    have first := move_run width
      (Turing.Tape.mk' (Turing.ListBlank.mk (word (bit :: bits) ++ [0])) (Turing.ListBlank.mk (current :: right)))
      ((bit :: bits).length : ℤ) 1 1 .left (by simp [machine, nonblank])
    simp [displacement, word, Turing.Tape.move_left_mk', Turing.ListBlank.cons_mk] at first
    have nextNonblank : data bit ≠ 0 := by cases bit <;> decide
    have rest := hypothesis (data bit) nextNonblank (current :: right)
    have complete := first.trans rest
    simp only [word, List.reverse_cons, List.map_cons,
      List.length_cons, Nat.cast_add, Nat.cast_one] at complete ⊢
    convert complete using 1 <;> first | rfl | omega | simp [List.append_assoc]

/-- Return from a selected array element to the first data cell. An empty
array stays at its designated blank cell. No boundary marker is needed. -/
theorem runs (beforeBits afterBits : List Bool) (valid : afterBits = [] → beforeBits = []) :
    ∃ ticks, ticks ≤ beforeBits.length + 3 ∧
      Runs (fun _ : Unit => beforeBits.length + afterBits.length) (fun _ => true) machine ticks
        0 (fun _ => (beforeBits.length : ℤ))
        (Binary.tape (word beforeBits.reverse ++ [0]) (word afterBits ++ [0]))
        2 (fun _ => 0) (fun _ => buffer (word (beforeBits ++ afterBits))) := by
  cases afterBits with
  | nil =>
    have empty := valid rfl
    subst beforeBits
    refine ⟨1, by decide, ?_⟩
    simp only [word, List.map_nil, List.reverse_nil, List.nil_append, List.length_nil, zero_add, Nat.cast_zero]
    apply Runs.next (nextState := (2 : Fin 3))
      (actions := stationary (MultiTape.read (Binary.tape [0] [0])))
      (by simp [machine, MultiTape.read, Binary.tape]) (by intro name premise; rfl)
    simp only [stationary, displacement, add_zero, act_stationary]
    have emptyTape : Binary.tape [0] [0] = fun _ => buffer [] := by
      funext name
      exact (buffer_left_blank [0]).trans (buffer_append_blank [])
    rw [emptyTape]
    exact .zero _ _ _
  | cons bit bits =>
    have nonblank : data bit ≠ 0 := by cases bit <;> decide
    have rewind := rewind_runs beforeBits.reverse (data bit) nonblank (word bits ++ [0])
      (beforeBits.length + (bit :: bits).length)
    simp only [List.length_reverse, List.reverse_reverse] at rewind
    have first : Runs (fun _ : Unit => beforeBits.length + (bit :: bits).length) (fun _ => true)
        machine 1 0 (fun _ => (beforeBits.length : ℤ))
        (Binary.tape (word beforeBits.reverse ++ [0]) (word (bit :: bits) ++ [0]))
        1 (fun _ => (beforeBits.length : ℤ))
        (Binary.tape (word beforeBits.reverse ++ [0]) (word (bit :: bits) ++ [0])) := by
      apply Runs.next (nextState := (1 : Fin 3))
        (actions := stationary (MultiTape.read (Binary.tape (word beforeBits.reverse ++ [0]) (word (bit :: bits) ++ [0]))))
        (by simp [machine, MultiTape.read, Binary.tape, word, nonblank]) (by intro name premise; rfl)
      simpa only [stationary, displacement, add_zero, act_stationary] using
        (Runs.zero (machine := machine) 1 (fun _ : Unit => (beforeBits.length : ℤ))
          (Binary.tape (word beforeBits.reverse ++ [0]) (word (bit :: bits) ++ [0])))
    simp only [word, List.map_cons, List.cons_append] at first
    have complete := first.trans rewind
    refine ⟨1 + (beforeBits.length + 2), by omega, ?_⟩
    simp only [word, List.map_append, List.map_cons,
      ← List.cons_append, ← List.append_assoc, buffer_append_blank] at complete ⊢
    exact complete

/-- Sequential traversal finishes just past the data, then restores the start. -/
def fromEnd : Machine Alphabet (Sum (Fin 2) (Fin 3)) :=
  MultiTape.sequence (Move.machine 1 .left) machine 1

/-- Return over a known binary prefix, preserving any following symbols. -/
theorem fromPrefix_runs (bits : List Bool) (right : List Symbol) :
    Runs (fun _ : Unit => bits.length) (fun _ => true) fromEnd (bits.length + 3)
      (.inl 1) (fun _ => (bits.length : ℤ))
      (Binary.tape (word bits.reverse ++ [0]) right)
      (.inr 2) (fun _ => 0) (fun _ => buffer (word bits ++ right)) := by
  let initial := Binary.tape (word bits.reverse ++ [0]) right
  have leftward := StandardHead.move_runs 1 .left (fun _ : Unit => bits.length)
    (fun _ => true) (fun _ => (bits.length : ℤ)) initial
  have scan : Runs (fun _ : Unit => bits.length) (fun _ => true) machine (bits.length + 1)
      1 (fun _ => (bits.length : ℤ) - 1)
      (fun name => (initial name).move .left)
      2 (fun _ => 0) (fun _ => buffer (word bits ++ right)) := by
    cases reversed : bits.reverse with
    | nil =>
      have empty : bits = [] := List.reverse_eq_nil_iff.mp reversed
      subst bits
      apply Runs.next (nextState := (2 : Fin 3))
        (actions := fun _ => (0, some Turing.Dir.right))
        (by simp [machine, initial, Binary.tape, word, MultiTape.read]) (by intro name premise; rfl)
      have moved : act (fun _ : Unit => (0, some Turing.Dir.right))
          (fun name => (initial name).move Turing.Dir.left) = fun _ => buffer right := by
        funext name
        simp [initial, Binary.tape, word, MultiTape.act, Turing.Tape.write_mk',
          Turing.Tape.move_left_mk', Turing.Tape.move_right_mk', Turing.ListBlank.cons_mk]
        exact buffer_left_blank right
      rw [moved]
      simpa [displacement, word] using
        Runs.zero (machine := machine) 2 (fun _ : Unit => (0 : ℤ)) (fun _ => buffer right)
    | cons bit rest =>
      have recover : bits = rest.reverse ++ [bit] := by
        have inverse := congrArg List.reverse reversed
        simpa using inverse
      have nonblank : data bit ≠ 0 := by cases bit <;> decide
      have trace := rewind_runs rest (data bit) nonblank right bits.length
      have length : bits.length = rest.length + 1 := by rw [recover]; simp
      simp only [initial, Binary.tape, reversed, word, List.map_cons, List.cons_append,
        Turing.Tape.move_left_mk', Turing.ListBlank.head_mk, List.headI_cons,
        Turing.ListBlank.tail_mk, List.tail_cons, Turing.ListBlank.cons_mk]
      rw [length, recover]
      simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right,
        List.map_append, List.map_reverse, List.map_singleton, List.append_assoc]
      rw [length] at trace
      convert trace using 1 <;> first | rfl | omega | (funext name; simp [word, List.map_reverse])
  simp only [Nat.cast_one, one_mul, displacement] at leftward
  have complete := leftward.sequence machine (1 : Fin 3)
    (by intro symbols; simp [Move.machine]) scan
  convert complete using 1 <;> first | rfl | omega

/-- Returning from the end also works for an empty data region. -/
theorem fromEnd_runs (bits : List Bool) :
    Runs (fun _ : Unit => bits.length) (fun _ => true) fromEnd (bits.length + 3)
      (.inl 1) (fun _ => (bits.length : ℤ))
      (Binary.tape (word bits.reverse ++ [0]) [0])
      (.inr 2) (fun _ => 0) (fun _ => buffer (word bits)) := by
  simpa only [buffer_append_blank] using fromPrefix_runs bits [0]

end BlankReturn
end Polytime2.StandardHead
