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

/-! # A restoring high-bit-first cursor loop

Multiplication and division consume an immutable binary input from high to low
bits. This controller shares their tape navigation: scan to the right blank,
call a restoring body for each bit, and finish with the source head at the start.
-/

namespace Polytime2.StandardBitFold

open MultiTape CallingConvention
open Binary (Symbol data word)

-- tapeLevel: tape roles; bodyLevel: finite body states; workLevel: proof workspace.
universe tapeLevel bodyLevel workLevel
variable {TapeName : Type tapeLevel} [DecidableEq TapeName]
variable {BodyState : Type bodyLevel} {Work : Type workLevel}

abbrev Alphabet (TapeName : Type tapeLevel) := CallingConvention.Alphabet TapeName
abbrev State (BodyState : Type bodyLevel) := Sum (Fin 4) BodyState

variable (cursor : TapeName)

/-- Only the immutable input's head moves between body calls. -/
def position (offset : ℤ) (name : TapeName) : ℤ := if name = cursor then offset else 0

/-- The workspace describes all other tapes; its value at the cursor is ignored. -/
def frame (storage : Work → Tapes (Alphabet TapeName)) (source : Turing.Tape Symbol)
    (work : Work) : Tapes (Alphabet TapeName) := Function.update (storage work) cursor source

variable (body : Machine (Alphabet TapeName) BodyState) (bodyEntry : Bool → BodyState)

noncomputable def machine : Machine (Alphabet TapeName) (State BodyState)
  | .inl phase, symbols => match phase.val with
    | 0 => if symbols cursor = 0 then some (.inl 1, stationary symbols)
      else some (.inl 0, fun name => (symbols name, if name = cursor then some .right else none))
    | 1 => some (.inl 2, fun name => (symbols name, if name = cursor then some .left else none))
    | 2 => if symbols cursor = 0 then
        some (.inl 3, fun name => (symbols name, if name = cursor then some .right else none))
      else some (.inr (bodyEntry (symbols cursor == 2)), stationary symbols)
    | _ => none
  | .inr state, symbols => match body state symbols with
    | some (next, actions) => some (.inr next, actions)
    | none => some (.inl 1, stationary symbols)

def entry : State BodyState := .inl 0
def exit : State BodyState := .inl 3

variable (storage : Work → Tapes (Alphabet TapeName))
variable (width : TapeName → ℕ) (readOnly : TapeName → Bool)

private theorem stationary_run (work : Work) (source : Turing.Tape Symbol) (offset : ℤ)
    (state nextState : State BodyState)
    (instruction : machine cursor body bodyEntry state (MultiTape.read (frame cursor storage source work)) =
      some (nextState, stationary (MultiTape.read (frame cursor storage source work)))) :
    Runs width readOnly (machine cursor body bodyEntry) 1
      state (position cursor offset) (frame cursor storage source work)
      nextState (position cursor offset) (frame cursor storage source work) := by
  apply Runs.next instruction (by intro name premise; rfl)
  simpa only [stationary, displacement, add_zero, act_stationary] using
    (Runs.zero (machine := machine cursor body bodyEntry) nextState
      (position cursor offset) (frame cursor storage source work))

private theorem move_run (work : Work) (source : Turing.Tape Symbol) (offset : ℤ)
    (state nextState : State BodyState) (direction : Turing.Dir)
    (instruction : machine cursor body bodyEntry state (MultiTape.read (frame cursor storage source work)) =
      some (nextState, fun name =>
        (MultiTape.read (frame cursor storage source work) name, if name = cursor then some direction else none))) :
    Runs width readOnly (machine cursor body bodyEntry) 1
      state (position cursor offset) (frame cursor storage source work)
      nextState (position cursor (offset + displacement (some direction)))
      (frame cursor storage (source.move direction) work) := by
  apply Runs.next instruction (by intro name premise; rfl)
  have positions : (fun name => position cursor offset name +
      displacement (if name = cursor then some direction else none)) =
      position cursor (offset + displacement (some direction)) := by
    funext name
    by_cases equal : name = cursor <;> simp [position, equal, displacement]
  have tapes : act (fun name =>
      (MultiTape.read (frame cursor storage source work) name, if name = cursor then some direction else none))
      (frame cursor storage source work) = frame cursor storage (source.move direction) work := by
    funext name
    by_cases equal : name = cursor
    · subst name
      simp [act, frame, MultiTape.read, Turing.Tape.write_self]
    · simp [act, frame, MultiTape.read, equal, Turing.Tape.write_self]
  rw [positions, tapes]
  exact .zero _ _ _

private theorem forward_runs (bits : List Bool) (left right : List Symbol)
    (work : Work) (offset : ℤ) :
    Runs width readOnly (machine cursor body bodyEntry) bits.length
      entry (position cursor offset)
      (frame cursor storage (Turing.Tape.mk' (Turing.ListBlank.mk left)
        (Turing.ListBlank.mk (word bits ++ right))) work)
      entry (position cursor (offset + bits.length))
      (frame cursor storage (Turing.Tape.mk' (Turing.ListBlank.mk ((word bits).reverse ++ left))
        (Turing.ListBlank.mk right)) work) := by
  induction bits generalizing left offset with
  | nil =>
    simpa [word] using (Runs.zero (machine := machine cursor body bodyEntry) entry
      (position cursor offset) (frame cursor storage
        (Turing.Tape.mk' (Turing.ListBlank.mk left) (Turing.ListBlank.mk right)) work))
  | cons bit bits hypothesis =>
    have nonblank : data bit ≠ 0 := by cases bit <;> decide
    have first := move_run cursor body bodyEntry storage width readOnly work
      (Turing.Tape.mk' (Turing.ListBlank.mk left) (Turing.ListBlank.mk (word (bit :: bits) ++ right)))
      offset entry entry .right (by simp [machine, entry, MultiTape.read, frame, word, nonblank])
    simp only [displacement] at first
    simp [word, Turing.Tape.move_right_mk', Turing.ListBlank.cons_mk] at first
    have rest := hypothesis (data bit :: left) (offset + 1)
    have complete := first.trans rest
    convert complete using 1 <;>
      simp [word, List.reverse_cons, List.append_assoc, Nat.add_comm,
        Int.add_comm, Int.add_left_comm]

/-- A mathematical fold records the workspace changes made by the body. -/
def fold (advance : Bool → Work → Work) : List Bool → Work → Work
  | [], work => work
  | bit :: bits, work => fold advance bits (advance bit work)

variable (advance : Bool → Work → Work) (invariant : Work → Prop)
variable (bodyExit : BodyState) (bodyTicks : ℕ)
variable (bodyHalt : ∀ symbols, body bodyExit symbols = none)
variable (advance_preserves : ∀ bit work, invariant work → invariant (advance bit work))
variable (body_runs : ∀ bit work, invariant work → ∀ source offset,
  Runs width readOnly body bodyTicks (bodyEntry bit) (position cursor offset)
    (frame cursor storage source work) bodyExit (position cursor offset)
    (frame cursor storage source (advance bit work)))

include bodyHalt advance_preserves body_runs in
private theorem loop_runs (bits processed : List Bool) (work : Work) (valid : invariant work) :
    Runs width readOnly (machine cursor body bodyEntry) (bits.length * (bodyTicks + 3) + 2)
      (.inl 1) (position cursor bits.length)
      (frame cursor storage (Turing.Tape.mk' (Turing.ListBlank.mk (word bits ++ [0]))
        (Turing.ListBlank.mk (word processed ++ [0]))) work)
      exit (position cursor 0)
      (frame cursor storage (buffer (word (bits.reverse ++ processed))) (fold advance bits work)) := by
  induction bits generalizing processed work with
  | nil =>
    have first := move_run cursor body bodyEntry storage width readOnly work
      (Turing.Tape.mk' (Turing.ListBlank.mk [0]) (Turing.ListBlank.mk (word processed ++ [0])))
      0 (.inl 1) (.inl 2) .left (by simp [machine])
    simp [displacement, Turing.Tape.move_left_mk', Turing.ListBlank.cons_mk] at first
    have second := move_run cursor body bodyEntry storage width readOnly work
      (Turing.Tape.mk' (Turing.ListBlank.mk []) (Turing.ListBlank.mk (0 :: word processed ++ [0])))
      (-1) (.inl 2) (.inl 3) .right (by simp [machine, MultiTape.read, frame])
    simp [displacement, Turing.Tape.move_right_mk', Turing.ListBlank.cons_mk] at second
    have complete := first.trans second
    simpa only [List.length_nil, CharP.cast_eq_zero, zero_mul, zero_add, word, List.map_nil,
      List.nil_append, List.reverse_nil, List.map_append, fold, exit, buffer_padding] using complete
  | cons bit bits hypothesis =>
    let source := Turing.Tape.mk' (Turing.ListBlank.mk (word bits ++ [0]))
      (Turing.ListBlank.mk (data bit :: word processed ++ [0]))
    have first := move_run cursor body bodyEntry storage width readOnly work
      (Turing.Tape.mk' (Turing.ListBlank.mk (word (bit :: bits) ++ [0]))
        (Turing.ListBlank.mk (word processed ++ [0])))
      ((bit :: bits).length : ℤ) (.inl 1) (.inl 2) .left (by simp [machine])
    have moved : ((bit :: bits).length : ℤ) + displacement (some Turing.Dir.left) = bits.length := by
      simp [displacement]
    simp only [moved] at first
    simp [word, Turing.Tape.move_left_mk', Turing.ListBlank.cons_mk] at first
    have nonblank : data bit ≠ 0 := by cases bit <;> decide
    have digit : (data bit == 2) = bit := by cases bit <;> decide
    have launch := stationary_run cursor body bodyEntry storage width readOnly work source bits.length
      (.inl 2) (.inr (bodyEntry bit)) (by simp [machine, MultiTape.read, frame, source, nonblank, digit])
    have run := (body_runs bit work valid source bits.length).rename Sum.inr
      (target := machine cursor body bodyEntry)
      (by intro state symbols next actions transition; simp [machine, transition])
    have restart := stationary_run cursor body bodyEntry storage width readOnly (advance bit work) source bits.length
      (.inr bodyExit) (.inl 1) (by simp [machine, bodyHalt])
    have rest := hypothesis (bit :: processed) (advance bit work) (advance_preserves bit work valid)
    have complete := first.trans (launch.trans (run.trans (restart.trans rest)))
    convert complete using 1 <;> simp [fold, word, List.reverse_cons, List.append_assoc]
    ring

include bodyHalt advance_preserves body_runs in
/-- A source word of length `m` calls the body exactly `m` times. Its cells are
never changed, and every head is restored on return. -/
theorem runs (bits : List Bool) (work : Work) (valid : invariant work) :
    Runs width readOnly (machine cursor body bodyEntry) (bits.length * (bodyTicks + 4) + 3)
      entry (fun _ => 0) (frame cursor storage (buffer (word bits)) work)
      exit (fun _ => 0) (frame cursor storage (buffer (word bits)) (fold advance bits.reverse work)) := by
  have scanned := forward_runs cursor body bodyEntry storage width readOnly bits [0] [0] work 0
  simp only [buffer_padding, zero_add] at scanned
  let source := Turing.Tape.mk' (Turing.ListBlank.mk ((word bits).reverse ++ [0])) (Turing.ListBlank.mk [0])
  have handover := stationary_run cursor body bodyEntry storage width readOnly work source bits.length
    entry (.inl 1) (by simp [machine, entry, MultiTape.read, frame, source])
  have loop := loop_runs cursor body bodyEntry storage width readOnly advance invariant bodyExit bodyTicks
    bodyHalt advance_preserves body_runs bits.reverse [] work valid
  simp only [word, List.map_reverse, List.reverse_reverse, List.length_reverse,
    List.append_nil, List.map_nil, List.nil_append] at loop
  have zero : position cursor 0 = fun _ : TapeName => (0 : ℤ) := by funext name; simp [position]
  rw [zero] at scanned loop
  have complete := scanned.trans (handover.trans loop)
  convert complete using 1 <;> first | rfl | ring

end Polytime2.StandardBitFold
