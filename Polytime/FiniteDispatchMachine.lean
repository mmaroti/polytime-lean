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

import Polytime.BlockLookupMachine

/-! # Runtime selection among a fixed finite family of machines

Read a fixed-width scalar into controller bits, erase its consumed input slot,
and dispatch to a branch with blank left storage. All branches are part of one
fixed finite controller; the runtime bits do not become specialization data.
-/

namespace Polytime.FiniteDispatchMachine

open TupleMachine (Symbol data word)

namespace Read

abbrev State (width : ℕ) := Fin (width + 1) × (Fin width → Bool) × Fin 4

/-- Read, erase backward, return across blanks, and halt with the bits stored. -/
def machine (width : ℕ) : Turing.TM0.Machine Symbol (State width) := fun (position, bits, phase) symbol =>
  match phase.val with
  | 0 => if valid : position.val < width then
      some ((⟨position.val + 1, by omega⟩,
        BoolTuple.update bits ⟨position.val, valid⟩ (symbol = data true), 0), .move .right)
      else some ((position, bits, 1), .write symbol)
  | 1 => if position.val > 0 then some ((⟨position.val - 1, by omega⟩, bits, 2), .move .left)
      else some ((Fin.last width, bits, 3), .write symbol)
  | 2 => some ((position, bits, 1), .write 0)
  | _ => if position.val > 0 then some ((⟨position.val - 1, by omega⟩, bits, 3), .move .right) else none

variable {width : ℕ}

private theorem reads (bits : Fin width → Bool) (tail : List Symbol) :
    Tape.Steps (machine width) width
      (Tape.configuration (0, (fun _ => false), 0) [] (word (List.ofFn bits) ++ tail))
      (Tape.configuration (Fin.last width, bits, 0) (word (List.ofFn bits)).reverse tail) := by
  have trace := FiniteTableMachine.reads (id : (Fin width → Bool) → (Fin width → Bool)) bits [] tail
  let rename : FiniteTableMachine.State width width → State width
    | .read position stored => (position, stored, 0)
    | _ => (0, (fun _ => false), 0)
  have lifted := (trace.rename_until rename BlockLookupMachine.reading
    (fun state symbol next => BlockLookupMachine.reading_predecessor state next symbol)
    (targetMachine := machine width) (by
      intro state symbol next action allowed nextAllowed command
      cases state with
      | read position stored =>
        by_cases valid : position.val < width
        · simp only [FiniteTableMachine.machine, valid, ↓reduceDIte, Option.some.injEq,
            Prod.mk.injEq] at command
          obtain ⟨rfl, rfl⟩ := command
          simp [machine, rename, valid]
        · simp only [FiniteTableMachine.machine, valid, ↓reduceDIte, Option.some.injEq,
            Prod.mk.injEq] at command
          obtain ⟨rfl, _⟩ := command
          exact nextAllowed.elim
      | rewind | emit | write | halt => exact allowed.elim) trivial).2
  simpa [rename, Tape.configuration] using lifted

private theorem erase (cells : List Symbol) (position : Fin (width + 1))
    (count : position.val = cells.length) (bits : Fin width → Bool) (tail : List Symbol) :
    Tape.Steps (machine width) (2 * cells.length)
      (Tape.configuration (position, bits, 1) cells tail)
      (Tape.configuration (0, bits, 1) [] (List.replicate cells.length 0 ++ tail)) := by
  induction cells generalizing position tail with
  | nil =>
    have equality : position = 0 := Fin.ext count
    subst position
    exact .zero _
  | cons symbol cells hypothesis =>
    have positive : position.val > 0 := by simp at count; omega
    let next : Fin (width + 1) := ⟨position.val - 1, by omega⟩
    have move := Tape.move_left_list (machine := machine width) (state := (position, bits, 1))
      (nextState := (next, bits, 2)) cells tail symbol (by intro current; simp [machine, positive, next])
    have write := Tape.write (machine := machine width) (state := (next, bits, 2))
      (nextState := (next, bits, 1)) cells tail symbol 0 (by rfl)
    have rest := hypothesis next (by dsimp [next]; simp at count; omega) (0 :: tail)
    have trace := Tape.Steps.next move (Tape.Steps.next write rest)
    convert trace using 1
    simp [List.replicate_succ]
    have equality : (0 : Symbol) :: (List.replicate cells.length 0 ++ tail) =
        List.replicate cells.length 0 ++ 0 :: tail := by
      simpa only [List.cons_append, List.append_assoc, List.singleton_append, List.nil_append] using
        congrArg (fun values : List Symbol => values ++ tail)
          ((List.replicate_succ (n := cells.length) (a := (0 : Symbol))).symm.trans
            (List.replicate_succ' (n := cells.length) (a := (0 : Symbol))))
    rw [equality]

private theorem returns (position : Fin (width + 1)) (bits : Fin width → Bool) (tail : List Symbol) :
    Tape.Steps (machine width) position.val
      (Tape.configuration (position, bits, 3) [] (List.replicate position.val 0 ++ tail))
      (Tape.configuration (0, bits, 3) [] tail) := by
  generalize count : position.val = remaining
  induction remaining generalizing position with
  | zero =>
    have equality : position = 0 := Fin.ext count
    subst position
    simp only [List.replicate_zero, List.nil_append]
    exact .zero _
  | succ remaining hypothesis =>
    let next : Fin (width + 1) := ⟨position.val - 1, by omega⟩
    have positive : position.val > 0 := by omega
    have move := Tape.move_right (machine := machine width) (state := (position, bits, 3))
      (nextState := (next, bits, 3)) [] (List.replicate remaining 0 ++ tail) 0
      (by simp [machine, positive, next])
    have blank : Tape.configuration ((next, bits, 3) : State width) [0] (List.replicate remaining 0 ++ tail) =
        Tape.configuration ((next, bits, 3) : State width) [] (List.replicate remaining 0 ++ tail) := by
      simpa [TupleMachine.instInhabitedSymbol] using
        Tape.configuration_append_blank (Symbol := Symbol)
          ((next, bits, 3) : State width) [] (List.replicate remaining 0 ++ tail)
    rw [blank] at move
    have rest := hypothesis next (by dsimp [next]; omega)
    simpa [count, List.replicate_succ] using Tape.Steps.next move rest

/-- Consume the scalar slot and restore blank left storage at the next field. -/
theorem realizes (bits : Fin width → Bool) (tail : List Symbol) :
    Tape.Steps (machine width) (4 * width + 2)
      (Tape.configuration (0, (fun _ => false), 0) [] (word (List.ofFn bits) ++ tail))
      (Tape.configuration (0, bits, 3) [] tail) := by
  have read := reads bits tail
  have enter := Tape.stay (machine := machine width) (state := (Fin.last width, bits, 0))
    (nextState := (Fin.last width, bits, 1)) (word (List.ofFn bits)).reverse tail
    (by intro symbol; simp [machine])
  have erased := erase (word (List.ofFn bits)).reverse (Fin.last width) (by simp [word]) bits tail
  have back := Tape.stay (machine := machine width) (state := (0, bits, 1))
    (nextState := (Fin.last width, bits, 3)) [] (List.replicate width 0 ++ tail)
    (by intro symbol; simp [machine])
  have returned := returns (Fin.last width) bits tail
  simp only [List.length_reverse, word, List.length_map, List.length_ofFn] at erased
  have trace := read.trans (Tape.Steps.next enter (erased.trans (Tape.Steps.next back returned)))
  convert trace using 1
  simp only [Fin.val_last]
  omega

@[simp] theorem halt (bits : Fin width → Bool) (symbol : Symbol) :
    machine width (0, bits, 3) symbol = none := rfl

end Read

-- branchLevel: the controller carrier of each fixed branch.
universe branchLevel
variable {width : ℕ} {Branch : (Fin width → Bool) → Type branchLevel}
variable [∀ bits, Inhabited (Branch bits)]

abbrev State (Branch : (Fin width → Bool) → Type branchLevel) :=
  Sum (Read.State width) (Sum (Sigma Branch) Unit)

/-- Dispatch after consuming the runtime selector; all branch controllers and
their transition tables are fixed components of the resulting machine. -/
def machine (branches : ∀ bits, Turing.TM0.Machine Symbol (Branch bits))
    (entries : ∀ bits, Branch bits) : Turing.TM0.Machine Symbol (State Branch)
  | .inl state, symbol => match Read.machine width state symbol with
    | some (next, action) => some (.inl next, action)
    | none => some (.inr (.inl ⟨state.2.1, entries state.2.1⟩), .write symbol)
  | .inr (.inl ⟨bits, state⟩), symbol => match branches bits state symbol with
    | some (next, action) => some (.inr (.inl ⟨bits, next⟩), action)
    | none => some (.inr (.inr ()), .write symbol)
  | .inr (.inr _), _ => none

theorem realizes (branches : ∀ bits, Turing.TM0.Machine Symbol (Branch bits))
    (entries : ∀ bits, Branch bits) (bits : Fin width → Bool) (exit : Branch bits)
    (ticks : ℕ) (input output : List Symbol)
    (branchHalt : ∀ symbol, branches bits exit symbol = none)
    (branchTrace : Tape.Steps (branches bits) ticks (Tape.configuration (entries bits) [] input)
      (Tape.configuration exit [] output)) :
    Tape.Steps (machine branches entries) (4 * width + ticks + 4)
      (Tape.configuration (.inl (0, (fun _ => false), 0)) [] (word (List.ofFn bits) ++ input))
      (Tape.configuration (.inr (.inr ())) [] output) := by
  have read := Read.realizes bits input
  have read' := read.rename Sum.inl (targetMachine := machine branches entries)
    (by intro state symbol next action command; simp [machine, command])
  have enter := Tape.stay (machine := machine branches entries) (state := .inl (0, bits, 3))
    (nextState := .inr (.inl ⟨bits, entries bits⟩)) [] input (by intro symbol; simp [machine])
  have branch := branchTrace.rename (fun state => .inr (.inl ⟨bits, state⟩))
    (targetMachine := machine branches entries)
    (by intro state symbol next action command; simp [machine, command])
  have leave := Tape.stay (machine := machine branches entries) (state := .inr (.inl ⟨bits, exit⟩))
    (nextState := .inr (.inr ())) [] output (by intro symbol; simp [machine, branchHalt])
  have trace := read'.trans (Tape.Steps.next enter (branch.trans (Tape.Steps.next leave (.zero _))))
  convert trace using 1
  · omega
  · rfl

@[simp] theorem halt (branches : ∀ bits, Turing.TM0.Machine Symbol (Branch bits))
    (entries : ∀ bits, Branch bits) (symbol : Symbol) :
    machine branches entries (.inr (.inr ())) symbol = none := rfl

end Polytime.FiniteDispatchMachine
