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

import Polytime2.Primitives.FixedCopy
import Polytime2.Primitives.Head
import Polytime2.Machine.CallingConventionRegions

/-! # Constructing a private unary sum capacity

Two immutable unary sizes determine a private header of their sum plus one.
The finite controller overwrites arbitrary destination contents and restores
all heads. This routine supplies internal sizes for certified computations.
-/

namespace Polytime2.StandardUnarySum

open MultiTape CallingConvention
open Binary (Symbol data word)

noncomputable section UnarySum

private def scan : Machine (CallingConvention.Alphabet Bool) Bool := fun finished symbols =>
  if finished then none
  else if symbols false = 0 then some (true, stationary symbols)
  else some (false, fun name => (if name then data true else symbols false, some .right))

private def sourceReturn : Machine (CallingConvention.Alphabet Bool)
    (Sum (Fin 2) (Fin 3)) :=
  MultiTape.wire (oneTape false) StandardHead.BlankReturn.fromEnd

private def appendMachine := MultiTape.sequence scan sourceReturn (.inl 1)

private def cells (count : ℕ) : List Symbol := List.replicate count (data true)

private def pair (leftSource rightSource leftTarget rightTarget : List Symbol) :
    Tapes (CallingConvention.Alphabet Bool) := Copy.frame leftSource rightSource leftTarget rightTarget

private theorem scan_runs (count : ℕ) (old : List Symbol) (length : old.length = count)
    (leftSource leftTarget rightTarget : List Symbol)
    (width : Bool → ℕ) (position : Bool → ℤ)
    (fits : 0 ≤ position true ∧ position true + count ≤ width true) :
    Runs width (fun name => !name) scan count false position
      (pair leftSource (cells count ++ [0]) leftTarget (old ++ rightTarget))
      false (fun name => position name + count)
      (pair (cells count ++ leftSource) [0] (cells count ++ leftTarget) rightTarget) := by
  induction count generalizing old leftSource leftTarget position with
  | zero =>
    have empty : old = [] := List.eq_nil_of_length_eq_zero length
    subst old
    simpa [cells, pair] using Runs.zero (machine := scan) false position
      (pair leftSource [0] leftTarget rightTarget)
  | succ count induction =>
    cases old with
    | nil => simp at length
    | cons previous old =>
      have smaller : old.length = count := by simpa using length
      let actions : Actions (CallingConvention.Alphabet Bool) :=
        fun _ => (data true, some .right)
      have instruction : scan false (MultiTape.read
          (pair leftSource (cells (count + 1) ++ [0]) leftTarget
            ((previous :: old) ++ rightTarget))) = some (false, actions) := by
        simp [scan, MultiTape.read, pair, Copy.frame, cells, List.replicate_succ, actions, data]
      have allowed : Allowed width (fun name => !name) position
          (MultiTape.read (pair leftSource (cells (count + 1) ++ [0]) leftTarget
            ((previous :: old) ++ rightTarget))) actions := by
        intro name outside
        cases name
        · simp [actions, MultiTape.read, pair, Copy.frame, cells, List.replicate_succ]
        · simp only [Bool.not_true, Bool.false_eq_true, false_or] at outside
          omega
      have moved : act actions
          (pair leftSource (cells (count + 1) ++ [0]) leftTarget
            ((previous :: old) ++ rightTarget)) =
          pair (data true :: leftSource) (cells count ++ [0])
            (data true :: leftTarget) (old ++ rightTarget) := by
        funext name
        cases name <;> simp [actions, act, pair, Copy.frame, cells, List.replicate_succ,
          Turing.Tape.write_mk', Turing.Tape.move_right_mk', Turing.ListBlank.cons_mk]
      have rest := induction old smaller (data true :: leftSource) (data true :: leftTarget)
        (fun name => position name + 1) (by constructor <;> omega)
      have complete := Runs.next instruction allowed (by
        simpa only [actions, displacement, moved] using rest)
      convert complete using 1
      · funext name; simp only [Nat.cast_add, Nat.cast_one]; omega
      · simp [cells, List.replicate_succ', List.append_assoc, pair]

private theorem append_runs (count : ℕ) (old : List Symbol) (length : old.length = count)
    (leftTarget rightTarget : List Symbol) :
    Runs (fun _ : Bool => count) (fun name => !name) appendMachine (2 * count + 5)
      (.inl false) (fun _ => 0)
      (pair [0] (cells count ++ [0]) leftTarget (old ++ rightTarget))
      (.inr (.inr 2)) (fun name => if name then count else 0)
      (pair [0] (cells count ++ [0]) (cells count ++ leftTarget) rightTarget) := by
  have forward := scan_runs count old length [0] leftTarget rightTarget
    (fun _ => count) (fun _ => 0) (by simp)
  have returned := (StandardHead.BlankReturn.fromEnd_runs (List.replicate count true)).wire
    (oneTape false) (fun _ : Bool => count) (fun name => !name)
    (by intro name; simp) (by intro name _; rfl)
    (pair (cells count ++ [0]) [0] (cells count ++ leftTarget) rightTarget)
    (fun _ => (count : ℤ))
  have source : Binary.tape (word (List.replicate count true).reverse ++ [0]) [0] =
      fun _ : Unit => pair (cells count ++ [0]) [0]
        (cells count ++ leftTarget) rightTarget false := by
    funext name
    simp [Binary.tape, pair, Copy.frame, word, cells]
  rw [source] at returned
  simp only [List.length_replicate] at returned
  change Runs _ _ _ (count + 3) _
    (install (oneTape false) (fun name => (fun _ : Bool => (count : ℤ)) (oneTape false name)) _)
    (install (oneTape false) (fun name =>
      pair (cells count ++ [0]) [0] (cells count ++ leftTarget) rightTarget (oneTape false name)) _)
    _ _ _ at returned
  rw [install_self] at returned
  have initialPosition : install (oneTape false) (fun _ : Unit => (count : ℤ))
      (fun _ : Bool => (count : ℤ)) = fun _ => (count : ℤ) := by
    funext name
    cases name
    · exact install_at (oneTape false) _ _ ()
    · simp [install_outside, oneTape]
  rw [initialPosition] at returned
  have finalTapes : install (oneTape false)
      (fun _ : Unit => buffer (word (List.replicate count true)))
      (pair (cells count ++ [0]) [0] (cells count ++ leftTarget) rightTarget) =
      pair [0] (cells count ++ [0]) (cells count ++ leftTarget) rightTarget := by
    funext name
    cases name
    · change install (oneTape false) _ _ (oneTape false ()) = _
      rw [install_at]
      simpa [cells, word, pair, Copy.frame] using (buffer_padding (cells count)).symm
    · simp [install_outside, pair, Copy.frame, oneTape]
  have finalPosition : install (oneTape false) (fun _ : Unit => (0 : ℤ))
      (fun _ : Bool => (count : ℤ)) = fun name => if name then count else 0 := by
    funext name
    cases name
    · exact install_at (oneTape false) _ _ ()
    · simp [install_outside, oneTape]
  rw [finalTapes, finalPosition] at returned
  have stopped : Runs (fun _ : Bool => count) (fun name => !name) scan 1
      false (fun _ => (count : ℤ))
      (pair (cells count ++ [0]) [0] (cells count ++ leftTarget) rightTarget)
      true (fun _ => (count : ℤ))
      (pair (cells count ++ [0]) [0] (cells count ++ leftTarget) rightTarget) := by
    apply Runs.next (nextState := true) (actions := stationary (MultiTape.read
      (pair (cells count ++ [0]) [0] (cells count ++ leftTarget) rightTarget)))
      (by simp [scan, MultiTape.read, pair, Copy.frame]) (by intro name premise; rfl)
    simpa only [stationary, displacement, add_zero, act_stationary] using Runs.zero
      (machine := scan) true (fun _ : Bool => (count : ℤ))
      (pair (cells count ++ [0]) [0] (cells count ++ leftTarget) rightTarget)
  simp only [zero_add] at forward
  have complete := (forward.trans stopped).sequence sourceReturn (.inl 1)
    (by intro symbols; rfl) returned
  convert complete using 1 <;> first | rfl | omega

-- tapeLevel: names of the enclosing finite tape collection.
universe tapeLevel
variable {TapeName : Type tapeLevel} [DecidableEq TapeName]

private def append (source target : TapeName) (distinct : source ≠ target) :
    Machine (CallingConvention.Alphabet TapeName) (Bool ⊕ (Fin 2 ⊕ Fin 3)) :=
  MultiTape.wire (twoTapes source target distinct) appendMachine

private theorem append_wired_runs (source target : TapeName) (distinct : source ≠ target)
    (width : TapeName → ℕ) (readOnly : TapeName → Bool) (writable : readOnly target = false)
    (count offset : ℕ) (fits : offset + count ≤ width target)
    (old left right : List Symbol) (length : old.length = count)
    (initial : Tapes (CallingConvention.Alphabet TapeName))
    (sourceEq : initial source = buffer (cells count))
    (targetEq : initial target = Turing.Tape.mk' (Turing.ListBlank.mk left)
      (Turing.ListBlank.mk (old ++ right))) :
    Runs width readOnly (append source target distinct) (2 * count + 5)
      (.inl false) (Function.update (fun _ : TapeName => (0 : ℤ)) target (offset : ℤ)) initial
      (.inr (.inr 2)) (Function.update (fun _ : TapeName => (0 : ℤ)) target ((offset + count : ℕ) : ℤ))
      (Function.update initial target (Turing.Tape.mk'
        (Turing.ListBlank.mk (cells count ++ left)) (Turing.ListBlank.mk right))) := by
  let wiring := twoTapes source target distinct
  let localOffset : Bool → ℤ := fun name => if name then offset else 0
  have trace := (append_runs count old length left right).regions
    (fun name => width (wiring name)) localOffset (by
      intro name premise
      cases name
      · contradiction
      · simp only [localOffset, ↓reduceIte, wiring, twoTapes_true]
        constructor <;> omega)
  have lifted := trace.wire wiring width readOnly (by intro name; rfl)
    (by intro name premise; cases name <;> simp_all [wiring])
    initial (Function.update (fun _ : TapeName => (0 : ℤ)) target (offset : ℤ))
  have startTapes : install wiring (pair [0] (cells count ++ [0]) left (old ++ right)) initial = initial := by
    funext name
    by_cases located : name ∈ Set.range wiring
    · obtain ⟨name, rfl⟩ := located
      rw [install_at]
      cases name
      · exact (buffer_padding (cells count)).trans sourceEq.symm
      · exact targetEq.symm
    · exact install_outside wiring _ _ name located
  have endTapes : install wiring
      (pair [0] (cells count ++ [0]) (cells count ++ left) right) initial =
      Function.update initial target (Turing.Tape.mk'
        (Turing.ListBlank.mk (cells count ++ left)) (Turing.ListBlank.mk right)) := by
    funext name
    by_cases located : name ∈ Set.range wiring
    · obtain ⟨name, rfl⟩ := located
      rw [install_at]
      cases name
      · simpa [wiring, distinct, pair, Copy.frame] using
          (buffer_padding (cells count)).trans sourceEq.symm
      · simp [wiring, pair, Copy.frame]
    · have different : name ≠ target := by
        intro equal; subst name; exact located ⟨true, rfl⟩
      simp [install_outside wiring _ _ name located, different]
  have startPosition : install wiring (fun name => (0 : ℤ) + localOffset name)
      (Function.update (fun _ : TapeName => (0 : ℤ)) target (offset : ℤ)) =
      Function.update (fun _ : TapeName => (0 : ℤ)) target (offset : ℤ) := by
    funext name
    by_cases located : name ∈ Set.range wiring
    · obtain ⟨name, rfl⟩ := located
      rw [install_at]
      cases name <;> simp [localOffset, wiring, distinct]
    · exact install_outside wiring _ _ name located
  have endPosition : install wiring
      (fun name => (if name then (count : ℤ) else 0) + localOffset name)
      (Function.update (fun _ : TapeName => (0 : ℤ)) target (offset : ℤ)) =
      Function.update (fun _ : TapeName => (0 : ℤ)) target ((offset + count : ℕ) : ℤ) := by
    funext name
    by_cases located : name ∈ Set.range wiring
    · obtain ⟨name, rfl⟩ := located
      rw [install_at]
      cases name <;> simp [localOffset, wiring, distinct, Nat.cast_add, add_comm]
    · have different : name ≠ target := by
        intro equal; subst name; exact located ⟨true, rfl⟩
      simp [install_outside wiring _ _ name located, different]
  simpa only [startTapes, endTapes, startPosition, endPosition, append, wiring] using lifted

private def writeOne : Machine (CallingConvention.Alphabet Unit) Bool
  | false, _ => some (true, fun _ => (data true, none))
  | true, _ => none

private def finish (target : TapeName) :
    Machine (CallingConvention.Alphabet TapeName) (Bool ⊕ Fin 3) :=
  MultiTape.wire (oneTape target)
    (MultiTape.sequence writeOne StandardHead.BlankReturn.machine 0)

private theorem finish_runs (target : TapeName) (width : TapeName → ℕ)
    (readOnly : TapeName → Bool) (writable : readOnly target = false)
    (count : ℕ) (fits : count + 1 ≤ width target) (old : Symbol)
    (initial : Tapes (CallingConvention.Alphabet TapeName))
    (targetEq : initial target = Turing.Tape.mk'
      (Turing.ListBlank.mk (cells count ++ [0])) (Turing.ListBlank.mk [old, 0])) :
    ∃ ticks, ticks ≤ count + 5 ∧
      Runs width readOnly (finish target) ticks (.inl false)
        (Function.update (fun _ : TapeName => (0 : ℤ)) target (count : ℤ)) initial
        (.inr 2) (fun _ => 0)
        (Function.update initial target (buffer (cells (count + 1)))) := by
  let start : Tapes (CallingConvention.Alphabet Unit) := fun _ =>
    Turing.Tape.mk' (Turing.ListBlank.mk (cells count ++ [0])) (Turing.ListBlank.mk [old, 0])
  let written : Tapes (CallingConvention.Alphabet Unit) := fun _ =>
    Turing.Tape.mk' (Turing.ListBlank.mk (cells count ++ [0])) (Turing.ListBlank.mk [data true, 0])
  have write : Runs (fun _ : Unit => count + 1) (fun _ => false) writeOne 1
      false (fun _ => (count : ℤ)) start true (fun _ => (count : ℤ)) written := by
    apply Runs.next (nextState := true) (actions := fun _ => (data true, none)) rfl
      (by intro name outside; simp only [Bool.false_eq_true, false_or] at outside; omega)
    have updated : act (fun _ : Unit => (data true, none)) start = written := by
      funext name
      simp [act, start, written, Turing.Tape.write_mk', Turing.ListBlank.cons_mk]
    simpa only [displacement, add_zero, updated] using Runs.zero (machine := writeOne)
      true (fun _ : Unit => (count : ℤ)) written
  obtain ⟨ticks, cost, returned⟩ := StandardHead.BlankReturn.runs
    (List.replicate count true) [true] (by simp)
  unfold Polytime2.Binary.tape at returned
  have returned' : Runs (fun _ : Unit => count + 1) (fun _ => false)
      StandardHead.BlankReturn.machine ticks 0 (fun _ => (count : ℤ)) written
      2 (fun _ => 0) (fun _ => buffer (cells (count + 1))) := by
    simpa only [written, Polytime2.Binary.tape, word, cells, List.replicate_succ',
      List.append_assoc, List.map_replicate, List.length_replicate, List.reverse_replicate,
      List.map_cons, List.map_nil, List.length_cons, List.length_nil, List.map_append, Nat.zero_add, List.cons_append, List.nil_append] using
      returned.readOnly_mono (targetReadOnly := fun _ => false) (by simp)
  have trace := write.sequence StandardHead.BlankReturn.machine 0
    (by intro symbols; rfl) returned'
  have lifted := (trace.regions (fun _ : Unit => width target) (fun _ => 0)
    (by intro name premise; constructor <;> omega)).wire (oneTape target) width readOnly
      (by intro name; rfl) (by intro name premise; simp [writable] at premise)
      initial (Function.update (fun _ : TapeName => (0 : ℤ)) target (count : ℤ))
  refine ⟨1 + (ticks + 1), ?_, ?_⟩
  · simp only [List.length_replicate] at cost
    omega
  · simpa [finish, install_one, start, ← targetEq, Nat.add_assoc] using lifted

/-- The controller depends only on static tape roles, never on runtime sizes. -/
def machine (first second target : TapeName) (firstDistinct : first ≠ target)
    (secondDistinct : second ≠ target) :=
  MultiTape.sequence (MultiTape.sequence (append first target firstDistinct)
    (append second target secondDistinct) (.inl false)) (finish target) (.inl false)

/-- The common exit halts independently of all tape contents. -/
theorem halt (first second target : TapeName) (firstDistinct : first ≠ target)
    (secondDistinct : second ≠ target) (symbols) :
    machine first second target firstDistinct secondDistinct (.inr (.inr 2)) symbols = none := by
  simp [machine, finish, MultiTape.sequence, MultiTape.wire, StandardHead.BlankReturn.machine]

/-- Construct a unary sum plus one from arbitrary private contents, preserving
both size tapes and all other storage and restoring every head. -/
theorem runs (first second target : TapeName) (firstDistinct : first ≠ target)
    (secondDistinct : second ≠ target) (width : TapeName → ℕ)
    (readOnly : TapeName → Bool) (writable : readOnly target = false)
    (rows columns : ℕ) (targetWidth : width target = rows + columns + 1)
    (initial : Tapes (CallingConvention.Alphabet TapeName))
    (firstEq : initial first = unary rows) (secondEq : initial second = unary columns)
    (targetRegion : Region (width target) 0 (initial target)) :
    ∃ ticks, ticks ≤ 3 * (rows + columns) + 17 ∧
      Runs width readOnly (machine first second target firstDistinct secondDistinct) ticks
        (.inl (.inl (.inl false))) (fun _ => 0) initial (.inr (.inr 2)) (fun _ => 0)
        (Function.update initial target (unary (rows + columns + 1))) := by
  obtain ⟨old, oldLength, oldEq⟩ := targetRegion.exists_buffer
  rw [targetWidth] at oldLength
  let firstOld := old.take rows
  let secondOld := (old.drop rows).take columns
  have firstLength : firstOld.length = rows := by simp [firstOld, oldLength]; omega
  have secondLength : secondOld.length = columns := by simp [secondOld, oldLength]; omega
  have lastLength : ((old.drop rows).drop columns).length = 1 := by simp [oldLength]
  obtain ⟨last, lastEq⟩ := List.length_eq_one_iff.mp lastLength
  have split : old = firstOld ++ secondOld ++ [last] := by
    dsimp [firstOld, secondOld]
    rw [← lastEq, List.append_assoc, List.take_append_drop, List.take_append_drop]
  have firstTrace := append_wired_runs first target firstDistinct width readOnly writable
    rows 0 (by omega) firstOld [0] (secondOld ++ [last, 0]) firstLength initial
    (by simpa [unary, tape, buffer, word, cells] using firstEq)
    (by rw [oldEq]; simpa [split, List.append_assoc] using (buffer_padding old).symm)
  let middle := Function.update initial target (Turing.Tape.mk'
    (Turing.ListBlank.mk (cells rows ++ [0])) (Turing.ListBlank.mk (secondOld ++ [last, 0])))
  have secondTrace := append_wired_runs second target secondDistinct width readOnly writable
    columns rows (by omega) secondOld (cells rows ++ [0]) [last, 0] secondLength middle
    (by simpa [middle, secondDistinct, unary, tape, buffer, word, cells] using secondEq)
    (by simp [middle])
  let prepared := Function.update middle target (Turing.Tape.mk'
    (Turing.ListBlank.mk (cells columns ++ (cells rows ++ [0]))) (Turing.ListBlank.mk [last, 0]))
  obtain ⟨finishTicks, finishCost, finishTrace⟩ := finish_runs target width readOnly writable
    (rows + columns) (by omega) last prepared (by
      simp only [prepared, Function.update_self, cells]
      rw [← List.append_assoc, ← List.replicate_add, Nat.add_comm columns rows])
  have appendHalt (source : TapeName) (distinct : source ≠ target) (symbols) :
      append source target distinct (.inr (.inr 2)) symbols = none := by
    simp [append, appendMachine, sourceReturn, MultiTape.sequence, MultiTape.wire,
      StandardHead.BlankReturn.fromEnd, StandardHead.BlankReturn.machine]
  simp only [Nat.cast_zero, zero_add, Function.update_eq_self] at firstTrace
  have combined := firstTrace.sequence (append second target secondDistinct) (.inl false)
    (appendHalt first firstDistinct) secondTrace
  have complete := combined.sequence (finish target) (.inl false)
    (by intro symbols; simp [MultiTape.sequence, appendHalt]) finishTrace
  refine ⟨(2 * rows + 5) + ((2 * columns + 5) + 1) + (finishTicks + 1), by omega, ?_⟩
  simpa [machine, middle, prepared, Function.update_idem, cells, unary, tape, buffer, word, Nat.add_assoc] using complete

end UnarySum
end Polytime2.StandardUnarySum
