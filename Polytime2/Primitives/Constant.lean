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

import Polytime2.Primitives.Head
import Polytime2.Primitives.FixedCopy

/-! # Writing specialization-fixed binary words

Finite operation tables and field constants must overwrite arbitrary output
cells without a prepared source tape or boundary markers.
-/

namespace Polytime2.StandardConstant

open MultiTape CallingConvention
open Binary (Symbol data word)

abbrev Alphabet := CallingConvention.Alphabet Unit

/-- The countdown and the word are fixed by specialization. -/
def machineSized (width : ℕ) (bits : List Bool) : Machine Alphabet (Copy.State width)
  | (false, remaining), symbols =>
    if finished : remaining.val = 0 then
      some ((true, Fin.last width), stationary symbols)
    else some ((false, ⟨remaining.val - 1, by omega⟩),
      fun _ => (data ((bits[width - remaining.val]?).getD false), some .right))
  | (true, remaining), symbols =>
    if finished : remaining.val = 0 then none
    else some ((true, ⟨remaining.val - 1, by omega⟩),
      fun _ => (symbols (), some .left))

def machine (bits : List Bool) : Machine Alphabet (Copy.State bits.length) :=
  machineSized bits.length bits

private theorem forward (bits before rest : List Bool) (split : bits = before ++ rest)
    (old : List Symbol) (sameLength : old.length = rest.length)
    (left right : List Symbol) :
    Runs (fun _ : Unit => bits.length) (fun _ => false) (machine bits) rest.length
      (false, ⟨rest.length, by rw [split, List.length_append]; omega⟩)
      (fun _ => before.length)
      (fun _ => Turing.Tape.mk' (Turing.ListBlank.mk left) (Turing.ListBlank.mk (old ++ right)))
      (false, 0) (fun _ => bits.length)
      (fun _ => Turing.Tape.mk' (Turing.ListBlank.mk ((word rest).reverse ++ left))
        (Turing.ListBlank.mk right)) := by
  induction rest generalizing before old left with
  | nil =>
    have empty : old = [] := List.eq_nil_of_length_eq_zero sameLength
    subst old
    have length : before.length = bits.length := by simp [split]
    simpa [word, length] using Runs.zero (machine := machine bits) (false, 0)
      (fun _ : Unit => (bits.length : ℤ))
      (fun _ => Turing.Tape.mk' (Turing.ListBlank.mk left) (Turing.ListBlank.mk right))
  | cons bit rest hypothesis =>
    cases old with
    | nil => simp at sameLength
    | cons previous old =>
      have nextSplit : bits = (before ++ [bit]) ++ rest := by simp [split, List.append_assoc]
      have nextLength : old.length = rest.length := by simpa using sameLength
      have selected : (bits[bits.length - (bit :: rest).length]?).getD false = bit := by
        rw [split, List.length_append, Nat.add_sub_cancel_right,
          List.getElem?_append_right (Nat.le_refl _)]
        simp
      simp only [List.length_cons] at selected
      have instruction : machine bits
          (false, ⟨(bit :: rest).length, by rw [split, List.length_append]; omega⟩)
          (MultiTape.read (fun _ : Unit => Turing.Tape.mk' (Turing.ListBlank.mk left)
            (Turing.ListBlank.mk ((previous :: old) ++ right)))) =
          some ((false, ⟨rest.length, by rw [split, List.length_append]; simp; omega⟩),
            fun _ => (data bit, some .right)) := by
        simp [machine, machineSized, selected]
      have restTrace := hypothesis (before ++ [bit]) nextSplit old nextLength (data bit :: left)
      have safe : Allowed (fun _ : Unit => bits.length) (fun _ => false)
          (fun _ => before.length)
          (MultiTape.read (fun _ : Unit => Turing.Tape.mk' (Turing.ListBlank.mk left)
            (Turing.ListBlank.mk ((previous :: old) ++ right))))
          (fun _ => (data bit, some .right)) := by
        intro name outside
        have bound : before.length < bits.length := by simp [split]
        simp only [Bool.false_eq_true, false_or] at outside
        omega
      have moved : act (fun _ : Unit => (data bit, some Turing.Dir.right))
          (fun _ : Unit => Turing.Tape.mk' (Turing.ListBlank.mk left)
            (Turing.ListBlank.mk ((previous :: old) ++ right))) =
          fun _ : Unit => Turing.Tape.mk' (Turing.ListBlank.mk (data bit :: left))
            (Turing.ListBlank.mk (old ++ right)) := by
        funext name
        simp [act, Turing.Tape.write_mk', Turing.Tape.move_right_mk', Turing.ListBlank.cons_mk]
      have positions : (fun _ : Unit => (before.length : ℤ) + displacement (some Turing.Dir.right)) =
          fun _ : Unit => ((before ++ [bit]).length : ℤ) := by
        funext name
        simp [displacement]
      rw [← moved, ← positions] at restTrace
      have complete := Runs.next instruction safe restTrace
      simpa [word, List.reverse_cons, List.append_assoc] using complete

private theorem left_list (payload left right : List Symbol) :
    (Turing.Tape.move .left)^[payload.length]
      (Turing.Tape.mk' (Turing.ListBlank.mk (payload ++ left)) (Turing.ListBlank.mk right)) =
      Turing.Tape.mk' (Turing.ListBlank.mk left) (Turing.ListBlank.mk (payload.reverse ++ right)) := by
  induction payload generalizing right with
  | nil => rfl
  | cons symbol payload hypothesis =>
    simp only [List.length_cons, Function.iterate_succ_apply, List.cons_append,
      Turing.Tape.move_left_mk', Turing.ListBlank.head_mk, List.headI_cons,
      Turing.ListBlank.tail_mk, List.tail_cons, Turing.ListBlank.cons_mk]
    simpa [List.reverse_cons, List.append_assoc] using hypothesis (symbol :: right)

/-- Every reserved cell is overwritten; no surrounding cell is changed, and
zero-width constants also restore their head. -/
theorem runsWithContext (bits : List Bool) (old : List Symbol) (sameLength : old.length = bits.length) (left right : List Symbol) :
    Runs (fun _ : Unit => bits.length) (fun _ => false) (machine bits) (2 * bits.length + 1)
      (false, Fin.last bits.length) (fun _ => 0) (fun _ => Turing.Tape.mk' (Turing.ListBlank.mk left) (Turing.ListBlank.mk (old ++ right)))
      (true, 0) (fun _ => 0) (fun _ => Turing.Tape.mk' (Turing.ListBlank.mk left)
        (Turing.ListBlank.mk (word bits ++ right))) := by
  have written := forward bits [] bits rfl old sameLength left right
  simp only [List.length_nil, Nat.cast_zero] at written
  let middle := fun _ : Unit => Turing.Tape.mk'
    (Turing.ListBlank.mk ((word bits).reverse ++ left)) (Turing.ListBlank.mk right)
  have switch : Runs (fun _ : Unit => bits.length) (fun _ => false) (machine bits) 1
      (false, 0) (fun _ => bits.length) middle
      (true, Fin.last bits.length) (fun _ => bits.length) middle := by
    apply Runs.next (nextState := (true, Fin.last bits.length))
      (actions := stationary (MultiTape.read middle)) (by simp [machine, machineSized])
      (by intro name premise; rfl)
    simpa only [act_stationary, stationary, displacement, add_zero] using
      Runs.zero (machine := machine bits) (true, Fin.last bits.length) (fun _ => bits.length) middle
  have returned := (StandardHead.move_runs bits.length .left
    (fun _ : Unit => bits.length) (fun _ => false) (fun _ => bits.length) middle).rename
    (fun remaining => (true, remaining)) (target := machine bits) (by
      intro state symbols next actions instruction
      simpa [Move.machine, machine, machineSized] using instruction)
  have finalPosition : (fun _ : Unit => (bits.length : ℤ) +
      bits.length * displacement (some Turing.Dir.left)) = fun _ => (0 : ℤ) := by
    funext name
    simp [displacement]
  have finalTapes : (fun name : Unit => (Turing.Tape.move Turing.Dir.left)^[bits.length]
      (middle name)) = fun _ => Turing.Tape.mk' (Turing.ListBlank.mk left)
        (Turing.ListBlank.mk (word bits ++ right)) := by
    funext name
    have trace := left_list (word bits).reverse left right
    simpa only [middle, List.length_reverse, word, List.length_map, List.reverse_reverse] using trace
  rw [finalPosition, finalTapes] at returned
  have complete := written.trans (switch.trans returned)
  convert complete using 1 <;> first | rfl | omega

/-- The public writer uses a standalone fixed-width output region. -/
theorem runs (bits : List Bool) (old : List Symbol) (sameLength : old.length = bits.length) :
    Runs (fun _ : Unit => bits.length) (fun _ => false) (machine bits) (2 * bits.length + 1)
      (false, Fin.last bits.length) (fun _ => 0) (fun _ => buffer old)
      (true, 0) (fun _ => 0) (fun _ => buffer (word bits)) := by
  simpa only [buffer_padding] using runsWithContext bits old sameLength [0] [0]

/-- The same writer with a state type indexed directly by bit-vector width. -/
def ofBitVec {width : ℕ} (bits : BitVec width) : Machine Alphabet (Copy.State width) :=
  machineSized width (List.ofFn (fun index : Fin width => bits.getLsbD index.val))

private theorem sized_runs (width : ℕ) (bits : List Bool) (bitsLength : bits.length = width)
    (old : List Symbol) (oldLength : old.length = width) :
    Runs (fun _ : Unit => width) (fun _ => false) (machineSized width bits) (2 * width + 1)
      (false, Fin.last width) (fun _ => 0) (fun _ => buffer old)
      (true, 0) (fun _ => 0) (fun _ => buffer (word bits)) := by
  subst width
  exact runs bits old oldLength

theorem ofBitVec_runs {width : ℕ} (bits : BitVec width) (old : List Symbol)
    (length : old.length = width) :
    Runs (fun _ : Unit => width) (fun _ => false) (ofBitVec bits) (2 * width + 1)
      (false, Fin.last width) (fun _ => 0) (fun _ => buffer old)
      (true, 0) (fun _ => 0)
      (fun _ => buffer (word (List.ofFn (fun index : Fin width => bits.getLsbD index.val)))) :=
  sized_runs width (List.ofFn (fun index : Fin width => bits.getLsbD index.val))
    List.length_ofFn old length

private theorem sized_runsWithContext (width : ℕ) (bits : List Bool)
    (bitsLength : bits.length = width) (old : List Symbol) (oldLength : old.length = width)
    (left right : List Symbol) :
    Runs (fun _ : Unit => width) (fun _ => false) (machineSized width bits) (2 * width + 1)
      (false, Fin.last width) (fun _ => 0)
      (fun _ => Turing.Tape.mk' (Turing.ListBlank.mk left) (Turing.ListBlank.mk (old ++ right)))
      (true, 0) (fun _ => 0)
      (fun _ => Turing.Tape.mk' (Turing.ListBlank.mk left) (Turing.ListBlank.mk (word bits ++ right))) := by
  subst width
  exact runsWithContext bits old oldLength left right

/-- Array traversal can write one scalar block while retaining its neighbors. -/
theorem ofBitVec_runsWithContext {width : ℕ} (bits : BitVec width) (old : List Symbol)
    (length : old.length = width) (left right : List Symbol) :
    Runs (fun _ : Unit => width) (fun _ => false) (ofBitVec bits) (2 * width + 1)
      (false, Fin.last width) (fun _ => 0)
      (fun _ => Turing.Tape.mk' (Turing.ListBlank.mk left) (Turing.ListBlank.mk (old ++ right)))
      (true, 0) (fun _ => 0)
      (fun _ => Turing.Tape.mk' (Turing.ListBlank.mk left)
        (Turing.ListBlank.mk (word (List.ofFn (fun index : Fin width => bits.getLsbD index.val)) ++ right))) :=
  sized_runsWithContext width (List.ofFn (fun index : Fin width => bits.getLsbD index.val))
    List.length_ofFn old length left right

/-- A constant command needs no runtime size arguments. -/
def sizeTapes : Empty ↪ Unit := ⟨Empty.elim, by intro parameter; cases parameter⟩

-- carrierLevel: mathematical values of the specialization-fixed output domain.
universe carrierLevel

/-- Any specialization-fixed encoded value can be written from arbitrary output
contents. Encoding is compiled into finite control, rather than executed as an
uncertified mathematical operation at runtime. -/
theorem contract (domain : EncodedDomain.{0, carrierLevel} Empty)
    (constant : ∀ assignment, domain.Carrier assignment) :
    let assignment : Empty → ℕ := Empty.elim
    let bits := List.ofFn (fun index : Fin (domain.width assignment) =>
      (domain.encode assignment (constant assignment)).getLsbD index.val)
    CallingConvention.Realizes (fun _ : Unit => domain) (fun _ => false) sizeTapes (Function.Embedding.refl Unit)
      (machine bits) (false, Fin.last bits.length) (true, 0)
      (fun _ _ => True) (fun assignment _ output => output () = constant assignment) := by
  intro defaultAssignment bits
  refine ⟨(by intro parameter; cases parameter), (by intro name; rfl),
    (by intro symbols; simp [machine, machineSized]), MvPolynomial.C (2 * bits.length + 1), ?_⟩
  intro assignment input initial valid represented sizes
  have sameAssignment : assignment = defaultAssignment := Subsingleton.elim _ _
  subst assignment
  obtain ⟨old, oldLength, oldEq⟩ := represented.2 () rfl
  have length : bits.length = domain.width defaultAssignment := List.length_ofFn
  have initialEq : initial = fun _ : Unit => buffer old := by
    funext name
    cases name
    exact oldEq
  refine ⟨2 * bits.length + 1, (fun _ => constant defaultAssignment),
    (fun _ => buffer (word bits)), by simp, ?_, rfl, ?_⟩
  · rw [initialEq]
    have trace := runs bits old (oldLength.trans length.symm)
    simpa only [length] using trace
  · intro name
    cases name
    rfl

end Polytime2.StandardConstant
