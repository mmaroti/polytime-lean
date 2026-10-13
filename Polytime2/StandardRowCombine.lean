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

import Polytime2.StandardFiniteTable

/-! # A finite scalar operation on corresponding row entries

The coefficient, source entry, and target entry are separate immutable inputs.
Two separate outputs carry the replacement source and target entries. Only
specialization-fixed scalar blocks are stored in the finite controller.
-/

namespace Polytime2.StandardRowCombine

open MultiTape CallingConvention
open Binary (Symbol word)

abbrev Alphabet := CallingConvention.Alphabet (Fin 5)
abbrev Register := StandardFixedRead.Memory
abbrev Triple (width : ℕ) := Register width × Register width × Register width
abbrev State (width : ℕ) := Sum (StandardFixedRead.State width)
  (Sum (Register width × StandardFixedRead.State width)
    (Sum ((Register width × Register width) × StandardFixedRead.State width)
      (Sum (Triple width × Copy.State width) (Sum (Triple width × Copy.State width) Unit))))

variable {width : ℕ}

def readOnly (name : Fin 5) : Bool := decide (name.val < 3)

def frame (coefficient source target : List Bool) (first second : List Symbol) : Tapes Alphabet :=
  fun name => if name = 0 then buffer (word coefficient)
    else if name = 1 then buffer (word source) else if name = 2 then buffer (word target)
    else if name = 3 then buffer first else buffer second

noncomputable def read (name : Fin 5) (width : ℕ) : Machine Alphabet (StandardFixedRead.State width) :=
  MultiTape.wire (oneTape name) (StandardFixedRead.machine width)

noncomputable def write (name : Fin 5) (bits : BitVec width) : Machine Alphabet (Copy.State width) :=
  MultiTape.wire (oneTape name) (StandardConstant.ofBitVec bits)

noncomputable def machine (table : Register width → Register width → Register width → BitVec width × BitVec width) :
    Machine Alphabet (State width)
  | .inl state, symbols => match read 0 width state symbols with
    | some (next, actions) => some (.inl next, actions)
    | none => some ⟨.inr (.inl (state.2, ((false, Fin.last width), fun _ => false))), stationary symbols⟩
  | .inr (.inl (coefficient, state)), symbols => match read 1 width state symbols with
    | some (next, actions) => some (.inr (.inl (coefficient, next)), actions)
    | none => some ⟨.inr (.inr (.inl ((coefficient, state.2), ((false, Fin.last width), fun _ => false)))), stationary symbols⟩
  | .inr (.inr (.inl ((coefficient, source), state))), symbols => match read 2 width state symbols with
    | some (next, actions) => some (.inr (.inr (.inl ((coefficient, source), next))), actions)
    | none => some ⟨.inr (.inr (.inr (.inl ((coefficient, source, state.2), (false, Fin.last width))))), stationary symbols⟩
  | .inr (.inr (.inr (.inl (values, state)))), symbols =>
    match write 3 (table values.1 values.2.1 values.2.2).1 state symbols with
    | some (next, actions) => some (.inr (.inr (.inr (.inl (values, next)))), actions)
    | none => some ⟨.inr (.inr (.inr (.inr (.inl (values, (false, Fin.last width)))))), stationary symbols⟩
  | .inr (.inr (.inr (.inr (.inl (values, state))))), symbols =>
    match write 4 (table values.1 values.2.1 values.2.2).2 state symbols with
    | some (next, actions) => some (.inr (.inr (.inr (.inr (.inl (values, next))))), actions)
    | none => some ⟨.inr (.inr (.inr (.inr (.inr ())))), stationary symbols⟩
  | .inr (.inr (.inr (.inr (.inr _)))), _ => none

def entry : State width := .inl ((false, Fin.last width), fun _ => false)
def exit : State width := .inr (.inr (.inr (.inr (.inr ()))))

@[simp] theorem halt
    (table : Register width → Register width → Register width → BitVec width × BitVec width)
    (symbols : Symbols Alphabet) : machine table exit symbols = none := rfl

private theorem read_runs (name : Fin 5) (bits : List Bool) (length : bits.length = width)
    (initial : Tapes Alphabet) (source : initial name = buffer (word bits)) :
    Runs (fun _ => width) readOnly (read name width) (2 * width + 1)
      ((false, Fin.last width), fun _ => false) (fun _ => 0) initial
      ((true, 0), fun index => (bits[index.val]?).getD false) (fun _ => 0) initial := by
  exact (StandardFixedRead.runs width bits length (fun _ => false)).wire_of_eq
    (oneTape name) (fun _ => width) readOnly (by intro localName; rfl)
    (by intro localName premise; rfl) initial initial
    (by intro localName; exact source) (by intro localName; exact source)
    (by intro localName outside; rfl)

private theorem write_runs (name : Fin 5) (writable : readOnly name = false)
    (bits : BitVec width) (old : List Symbol) (length : old.length = width)
    (initial : Tapes Alphabet) (source : initial name = buffer old) :
    Runs (fun _ => width) readOnly (write name bits) (2 * width + 1)
      (false, Fin.last width) (fun _ => 0) initial (true, 0) (fun _ => 0)
      (Function.update initial name (buffer (word (List.ofFn (fun index : Fin width => bits.getLsbD index.val))))) := by
  apply (StandardConstant.ofBitVec_runs bits old length).wire_of_eq (oneTape name)
    (fun _ => width) readOnly (by intro localName; rfl)
  · intro localName premise
    change readOnly name = true at premise
    rw [writable] at premise
    contradiction
  · intro localName
    exact source
  · intro localName
    exact Function.update_self _ _ _
  · intro localName outside
    have distinct : localName ≠ name := by
      intro equal
      subst localName
      exact outside ⟨(), rfl⟩
    exact Function.update_of_ne distinct _ _

private theorem stationary_run
    (table : Register width → Register width → Register width → BitVec width × BitVec width)
    (initial : Tapes Alphabet) (state nextState : State width)
    (instruction : machine table state (MultiTape.read initial) =
      some (nextState, stationary (MultiTape.read initial))) :
    Runs (fun _ => width) readOnly (machine table) 1 state (fun _ => 0) initial
      nextState (fun _ => 0) initial := by
  apply Runs.next instruction (by intro name premise; rfl)
  simpa only [stationary, displacement, add_zero, act_stationary] using
    (Runs.zero (machine := machine table) nextState (fun _ => (0 : ℤ)) initial)

/-- Both result words are completely overwritten; even zero-bit scalar domains
use the same finite controller and restored-head convention. -/
theorem runs
    (table : Register width → Register width → Register width → BitVec width × BitVec width)
    (coefficient source target : List Bool)
    (coefficientLength : coefficient.length = width) (sourceLength : source.length = width)
    (targetLength : target.length = width) (oldFirst oldSecond : List Symbol)
    (firstLength : oldFirst.length = width) (secondLength : oldSecond.length = width) :
    let coefficientRegister : Register width := fun index => (coefficient[index.val]?).getD false
    let sourceRegister : Register width := fun index => (source[index.val]?).getD false
    let targetRegister : Register width := fun index => (target[index.val]?).getD false
    let result := table coefficientRegister sourceRegister targetRegister
    Runs (fun _ => width) readOnly (machine table) (10 * width + 10)
      entry (fun _ => 0) (frame coefficient source target oldFirst oldSecond)
      exit (fun _ => 0)
      (frame coefficient source target
        (word (List.ofFn (fun index : Fin width => result.1.getLsbD index.val)))
        (word (List.ofFn (fun index : Fin width => result.2.getLsbD index.val)))) := by
  intro coefficientRegister sourceRegister targetRegister result
  let initial := frame coefficient source target oldFirst oldSecond
  let firstBits := word (List.ofFn (fun index : Fin width => result.1.getLsbD index.val))
  let secondBits := word (List.ofFn (fun index : Fin width => result.2.getLsbD index.val))
  let middle := frame coefficient source target firstBits oldSecond
  let final := frame coefficient source target firstBits secondBits
  let values : Triple width := (coefficientRegister, sourceRegister, targetRegister)
  have first := (read_runs 0 coefficient coefficientLength initial rfl).rename Sum.inl
    (target := machine table) (by intro state symbols next actions instruction; simp [machine, instruction])
  have firstHandover := stationary_run table initial (.inl ((true, 0), coefficientRegister))
    (.inr (.inl (coefficientRegister, ((false, Fin.last width), fun _ => false))))
    (by simp [machine, read, MultiTape.wire, StandardFixedRead.machine])
  have second := (read_runs 1 source sourceLength initial rfl).rename
    (fun state => .inr (.inl (coefficientRegister, state))) (target := machine table)
    (by intro state symbols next actions instruction; simp [machine, instruction])
  have secondHandover := stationary_run table initial
    (.inr (.inl (coefficientRegister, ((true, 0), sourceRegister))))
    (.inr (.inr (.inl ((coefficientRegister, sourceRegister), ((false, Fin.last width), fun _ => false)))))
    (by simp [machine, read, MultiTape.wire, StandardFixedRead.machine])
  have third := (read_runs 2 target targetLength initial rfl).rename
    (fun state => .inr (.inr (.inl ((coefficientRegister, sourceRegister), state)))) (target := machine table)
    (by intro state symbols next actions instruction; simp [machine, instruction])
  have thirdHandover := stationary_run table initial
    (.inr (.inr (.inl ((coefficientRegister, sourceRegister), ((true, 0), targetRegister)))))
    (.inr (.inr (.inr (.inl (values, (false, Fin.last width))))))
    (by simp [machine, read, MultiTape.wire, StandardFixedRead.machine, values])
  have firstWriter := (write_runs 3 (by decide) result.1 oldFirst firstLength initial rfl).rename
    (fun state => .inr (.inr (.inr (.inl (values, state))))) (target := machine table)
    (by
      intro state symbols next actions instruction
      dsimp only [result] at instruction
      simp [machine, values, instruction])
  have firstUpdate : Function.update initial (3 : Fin 5) (buffer firstBits) = middle := by
    funext name
    fin_cases name <;> rfl
  rw [firstUpdate] at firstWriter
  have fourthHandover := stationary_run table middle
    (.inr (.inr (.inr (.inl (values, (true, 0))))))
    (.inr (.inr (.inr (.inr (.inl (values, (false, Fin.last width)))))))
    (by simp [machine, write, MultiTape.wire, StandardConstant.ofBitVec, StandardConstant.machineSized])
  have secondWriter := (write_runs 4 (by decide) result.2 oldSecond secondLength middle rfl).rename
    (fun state => .inr (.inr (.inr (.inr (.inl (values, state)))))) (target := machine table)
    (by
      intro state symbols next actions instruction
      dsimp only [result] at instruction
      simp [machine, values, instruction])
  have secondUpdate : Function.update middle (4 : Fin 5) (buffer secondBits) = final := by
    funext name
    fin_cases name <;> rfl
  rw [secondUpdate] at secondWriter
  have lastHandover := stationary_run table final
    (.inr (.inr (.inr (.inr (.inl (values, (true, 0))))))) exit
    (by simp [machine, write, MultiTape.wire, StandardConstant.ofBitVec, StandardConstant.machineSized, exit])
  have complete := first.trans (firstHandover.trans (second.trans (secondHandover.trans
    (third.trans (thirdHandover.trans (firstWriter.trans (fourthHandover.trans (secondWriter.trans lastHandover))))))))
  convert complete using 1 <;> first | rfl | omega

end Polytime2.StandardRowCombine
