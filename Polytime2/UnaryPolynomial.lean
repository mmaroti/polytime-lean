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

import Polytime2.StandardHead
import Polytime2.Wiring
import Mathlib.Algebra.MvPolynomial.Eval

/-! # Unary evaluation of fixed polynomials

An appender uses one immutable unary tape per variable occurrence. Addition
composes appenders; multiplication by a variable repeats an appender using a
separate unary tape. The public evaluator prepares these private copies.
-/

namespace Polytime2.UnaryPolynomial

open MultiTape CallingConvention
open Binary (Symbol data word)

noncomputable section Appenders

variable {Parameter : Type}

/-- A unary word whose head is just past its last one. -/
def tail (count : ℕ) : Turing.Tape Symbol :=
  Turing.Tape.mk' (Turing.ListBlank.mk (List.replicate count (data true)))
    (Turing.ListBlank.mk [])

/-- Immutable occurrence tapes and an append-only unary result. -/
def frame {Source : Type} (role : Source → Parameter) (sizes : Parameter → ℕ)
    (written : ℕ) : Tapes (CallingConvention.Alphabet (Source ⊕ Unit))
  | .inl name => unary (sizes (role name))
  | .inr _ => tail written

/-- A fixed finite controller appends the value without changing its inputs. -/
def Appends {Source State : Type} (polynomial bound : MvPolynomial Parameter ℕ)
    (role : Source → Parameter) (machine : Machine (CallingConvention.Alphabet (Source ⊕ Unit)) State)
    (entry exit : State) : Prop :=
  (∀ symbols, machine exit symbols = none) ∧
  ∀ sizes written, ∃ ticks, ticks ≤ MvPolynomial.eval sizes bound ∧
    Steps machine ticks (entry, frame role sizes written)
      (exit, frame role sizes (written + MvPolynomial.eval sizes polynomial))

private def constant (count : ℕ) :
    Machine (CallingConvention.Alphabet (Empty ⊕ Unit)) (Fin (count + 1)) := fun state symbols =>
  if zero : state.val = 0 then none
  else some (⟨state.val - 1, by omega⟩, fun name => match name with
    | .inl empty => Empty.elim empty
    | .inr _ => (data true, some .right))

private theorem constant_steps (count remaining written : ℕ) (fits : remaining < count + 1)
    (role : Empty → Parameter) (sizes : Parameter → ℕ) :
    Steps (constant count) remaining (⟨remaining, fits⟩, frame role sizes written)
      (0, frame role sizes (written + remaining)) := by
  induction remaining generalizing written with
  | zero => simpa using Steps.zero (machine := constant count) (0, frame role sizes written)
  | succ remaining induction =>
    have transition : step (constant count) (⟨remaining + 1, fits⟩, frame role sizes written) =
        some (⟨remaining, by omega⟩, frame role sizes (written + 1)) := by
      simp only [step, constant, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, dite_false,
        Nat.add_sub_cancel, Option.map_some]
      congr 2
      funext name
      cases name with
      | inl empty => exact Empty.elim empty
      | inr name =>
        simp [act, frame, tail, Turing.Tape.write_mk', Turing.Tape.move_right_mk',
          Turing.ListBlank.cons_mk, List.replicate_succ]
    have rest := induction (written + 1) (by omega)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Steps.next transition rest

private theorem constant_appends (count : ℕ) :
    Appends (MvPolynomial.C count) (MvPolynomial.C count) (Empty.elim : Empty → Parameter)
      (constant count) (Fin.last count) 0 := by
  constructor
  · intro symbols; simp [constant]
  · intro sizes written
    refine ⟨count, by simp, ?_⟩
    convert constant_steps count count written (by omega) (Empty.elim : Empty → Parameter) sizes using 1 <;> simp [Fin.last]

private def leftWiring (Left Right : Type) : (Left ⊕ Unit) ↪ ((Left ⊕ Right) ⊕ Unit) :=
  ⟨Sum.map Sum.inl id, by intro first second equal; cases first <;> cases second <;> simp_all⟩

private def rightWiring (Left Right : Type) : (Right ⊕ Unit) ↪ ((Left ⊕ Right) ⊕ Unit) :=
  ⟨Sum.map Sum.inr id, by intro first second equal; cases first <;> cases second <;> simp_all⟩

private theorem add_appends {Left Right First Second : Type}
    (left leftBound right rightBound : MvPolynomial Parameter ℕ)
    (leftRole : Left → Parameter) (rightRole : Right → Parameter)
    (first : Machine (CallingConvention.Alphabet (Left ⊕ Unit)) First)
    (second : Machine (CallingConvention.Alphabet (Right ⊕ Unit)) Second)
    (firstEntry firstExit : First) (secondEntry secondExit : Second)
    (firstCorrect : Appends left leftBound leftRole first firstEntry firstExit)
    (secondCorrect : Appends right rightBound rightRole second secondEntry secondExit) :
    Appends (left + right) (leftBound + rightBound + 1) (Sum.elim leftRole rightRole)
      (MultiTape.sequence (wire (leftWiring Left Right) first) (wire (rightWiring Left Right) second) secondEntry)
      (.inl firstEntry) (.inr secondExit) := by
  classical
  constructor
  · intro symbols; simp [MultiTape.sequence, wire, secondCorrect.1]
  · intro sizes written
    obtain ⟨firstTicks, firstCost, firstTrace⟩ := firstCorrect.2 sizes written
    obtain ⟨secondTicks, secondCost, secondTrace⟩ := secondCorrect.2 sizes
      (written + MvPolynomial.eval sizes left)
    have liftedFirst := wire_steps_of_eq (leftWiring Left Right) first firstTrace
      (frame (Sum.elim leftRole rightRole) sizes written)
      (frame (Sum.elim leftRole rightRole) sizes (written + MvPolynomial.eval sizes left))
      (by intro name; cases name <;> rfl) (by intro name; cases name <;> rfl)
      (by intro name outside; cases name with
          | inl name => cases name with
            | inl name => exact False.elim (outside ⟨.inl name, rfl⟩)
            | inr name => rfl
          | inr name => exact False.elim (outside ⟨.inr name, rfl⟩))
    have liftedSecond := wire_steps_of_eq (rightWiring Left Right) second secondTrace
      (frame (Sum.elim leftRole rightRole) sizes (written + MvPolynomial.eval sizes left))
      (frame (Sum.elim leftRole rightRole) sizes
        (written + MvPolynomial.eval sizes left + MvPolynomial.eval sizes right))
      (by intro name; cases name <;> rfl) (by intro name; cases name <;> rfl)
      (by intro name outside; cases name with
          | inl name => cases name with
            | inl name => rfl
            | inr name => exact False.elim (outside ⟨.inl name, rfl⟩)
          | inr name => exact False.elim (outside ⟨.inr name, rfl⟩))
    refine ⟨firstTicks + secondTicks + 1, ?_, ?_⟩
    · simp only [map_add, map_one]; omega
    · simpa [Nat.add_assoc] using sequence_steps _ _ secondEntry liftedFirst
        (by intro symbols; simp [wire, firstCorrect.1]) liftedSecond

private def repeatWiring (Source : Type) :
    (Source ⊕ Unit) ↪ ((Unit ⊕ Source) ⊕ Unit) := rightWiring Unit Source

private def repeatMachine {Source State : Type} [DecidableEq Source]
    (machine : Machine (CallingConvention.Alphabet (Source ⊕ Unit)) State) (entry : State) :
    Machine (CallingConvention.Alphabet ((Unit ⊕ Source) ⊕ Unit)) (Bool ⊕ State)
  | .inl false, symbols =>
    if symbols (.inl (.inl ())) = 0 then some (.inl true, stationary symbols)
    else some (.inr entry, stationary symbols)
  | .inl true, _ => none
  | .inr state, symbols => match wire (repeatWiring Source) machine state symbols with
    | some (next, actions) => some (.inr next, actions)
    | none => some (.inl false, fun name =>
        (symbols name, if name = .inl (.inl ()) then some .right else none))

private def cursor (before after : ℕ) : Turing.Tape Symbol :=
  Turing.Tape.mk' (Turing.ListBlank.mk (List.replicate before (data true)))
    (Turing.ListBlank.mk (List.replicate after (data true)))

private def repeatFrame {Source : Type} (role : Source → Parameter) (sizes : Parameter → ℕ)
    (written before after : ℕ) : Tapes (CallingConvention.Alphabet ((Unit ⊕ Source) ⊕ Unit))
  | .inl (.inl _) => cursor before after
  | .inl (.inr name) => unary (sizes (role name))
  | .inr _ => tail written

private theorem repeat_steps {Source State : Type} [DecidableEq Source]
    (polynomial bound : MvPolynomial Parameter ℕ) (role : Source → Parameter)
    (machine : Machine (CallingConvention.Alphabet (Source ⊕ Unit)) State) (entry exit : State)
    (correct : Appends polynomial bound role machine entry exit)
    (sizes : Parameter → ℕ) (remaining before written : ℕ) :
    ∃ ticks, ticks ≤ remaining * (MvPolynomial.eval sizes bound + 2) + 1 ∧
      Steps (repeatMachine machine entry) ticks (.inl false, repeatFrame role sizes written before remaining)
        (.inl true, repeatFrame role sizes
          (written + remaining * MvPolynomial.eval sizes polynomial) (before + remaining) 0) := by
  induction remaining generalizing before written with
  | zero =>
    refine ⟨1, by omega, ?_⟩
    have transition : step (repeatMachine machine entry)
        (.inl false, repeatFrame role sizes written before 0) =
        some (.inl true, repeatFrame role sizes written before 0) := by
      simp [step, repeatMachine, MultiTape.read, repeatFrame, cursor, act_stationary]
    simpa using Steps.next transition (Steps.zero _)
  | succ remaining induction =>
    obtain ⟨childTicks, childCost, childTrace⟩ := correct.2 sizes written
    have lifted := wire_steps_of_eq (repeatWiring Source) machine childTrace
      (repeatFrame role sizes written before (remaining + 1))
      (repeatFrame role sizes (written + MvPolynomial.eval sizes polynomial) before (remaining + 1))
      (by intro name; cases name <;> rfl) (by intro name; cases name <;> rfl)
      (by intro name outside; cases name with
          | inl name => cases name with
            | inl name => rfl
            | inr name => exact False.elim (outside ⟨.inl name, rfl⟩)
          | inr name => exact False.elim (outside ⟨.inr name, rfl⟩))
    have executing := lifted.rename Sum.inr (target := repeatMachine machine entry)
      (by intro state symbols next actions instruction; simp [repeatMachine, instruction])
    have launch : step (repeatMachine machine entry)
        (.inl false, repeatFrame role sizes written before (remaining + 1)) =
        some (.inr entry, repeatFrame role sizes written before (remaining + 1)) := by
      simp [step, repeatMachine, MultiTape.read, repeatFrame, cursor, List.replicate_succ, data,
        act_stationary]
    have advance : step (repeatMachine machine entry)
        (.inr exit, repeatFrame role sizes (written + MvPolynomial.eval sizes polynomial) before (remaining + 1)) =
        some (.inl false, repeatFrame role sizes
          (written + MvPolynomial.eval sizes polynomial) (before + 1) remaining) := by
      simp only [step, repeatMachine, wire, correct.1, Option.map_none, Option.map_some]
      congr 2
      funext name
      cases name with
      | inl name => cases name with
        | inl name =>
          simp [act, MultiTape.read, repeatFrame, cursor, List.replicate_succ,
            Turing.Tape.move_right_mk', Turing.ListBlank.cons_mk]
        | inr name => simp [act, MultiTape.read, repeatFrame, Turing.Tape.write_self]
      | inr name => simp [act, MultiTape.read, repeatFrame, Turing.Tape.write_self]
    obtain ⟨restTicks, restCost, restTrace⟩ := induction (before + 1)
      (written + MvPolynomial.eval sizes polynomial)
    refine ⟨childTicks + restTicks + 2, ?_, ?_⟩
    · nlinarith
    · have complete := (Steps.next launch executing).trans (Steps.next advance restTrace)
      convert complete using 1 <;> first | omega | congr 2 <;> ring

private def returnWiring (Source : Type) : Unit ↪ ((Unit ⊕ Source) ⊕ Unit) :=
  oneTape (.inl (.inl ()))

private theorem mul_X_appends {Source State : Type} [DecidableEq Source]
    (polynomial bound : MvPolynomial Parameter ℕ) (parameter : Parameter)
    (role : Source → Parameter) (machine : Machine (CallingConvention.Alphabet (Source ⊕ Unit)) State)
    (entry exit : State) (correct : Appends polynomial bound role machine entry exit) :
    Appends (polynomial * MvPolynomial.X parameter)
      (MvPolynomial.X parameter * (bound + 3) + 5) (Sum.elim (fun _ : Unit => parameter) role)
      (MultiTape.sequence (repeatMachine machine entry)
        (wire (returnWiring Source) StandardHead.BlankReturn.fromEnd) (.inl 1))
      (.inl (.inl false)) (.inr (.inr 2)) := by
  constructor
  · intro symbols
    simp [MultiTape.sequence, wire, StandardHead.BlankReturn.fromEnd, MultiTape.sequence,
      StandardHead.BlankReturn.machine]
  · intro sizes written
    obtain ⟨ticks, cost, trace⟩ := repeat_steps polynomial bound role machine entry exit correct
      sizes (sizes parameter) 0 written
    simp only [zero_add] at trace
    have returned := (StandardHead.BlankReturn.fromEnd_runs (List.replicate (sizes parameter) true)).steps
    simp only [List.length_replicate] at returned
    have blank : (Turing.ListBlank.mk [0] : Turing.ListBlank Symbol) = Turing.ListBlank.mk [] :=
      Binary.mk_append_blank []
    have restore := wire_steps_of_eq (returnWiring Source) StandardHead.BlankReturn.fromEnd returned
      (repeatFrame role sizes (written + sizes parameter * MvPolynomial.eval sizes polynomial) (sizes parameter) 0)
      (frame (Sum.elim (fun _ : Unit => parameter) role) sizes
        (written + sizes parameter * MvPolynomial.eval sizes polynomial))
      (by
        intro name; cases name
        change cursor (sizes parameter) 0 = _
        simp [cursor, Binary.tape, word, Binary.mk_append_blank, blank])
      (by
        intro name; cases name
        change unary (sizes parameter) = _
        simp [unary, CallingConvention.tape, word, buffer])
      (by intro name outside; cases name with
          | inl name => cases name with
            | inl name => exact False.elim (outside ⟨(), rfl⟩)
            | inr name => rfl
          | inr name => rfl)
    refine ⟨ticks + ((sizes parameter + 3) + 1), ?_, ?_⟩
    · simp only [map_add, map_mul, map_ofNat, MvPolynomial.eval_X]
      nlinarith
    · have complete := sequence_steps (repeatMachine machine entry)
        (wire (returnWiring Source) StandardHead.BlankReturn.fromEnd) (.inl 1) trace
        (by intro symbols; rfl) restore
      have initialEq : repeatFrame role sizes written 0 (sizes parameter) =
          frame (Sum.elim (fun _ : Unit => parameter) role) sizes written := by
        funext name
        cases name with
        | inl name => cases name with
          | inl name => simp [repeatFrame, cursor, frame, unary, CallingConvention.tape, word, Turing.Tape.mk₁, Turing.Tape.mk₂]
          | inr name => rfl
        | inr name => rfl
      rw [initialEq] at complete
      simpa [Nat.mul_comm, Nat.add_assoc] using complete

/-- Every fixed natural-coefficient polynomial has a finite unary appender.
Its tapes and runtime polynomial are specialization data, independent of sizes. -/
theorem exists_appender (polynomial : MvPolynomial Parameter ℕ) :
    ∃ (Source : Type) (_ : Fintype Source) (role : Source → Parameter)
      (State : Type) (_ : Fintype State)
      (machine : Machine (CallingConvention.Alphabet (Source ⊕ Unit)) State)
      (entry exit : State) (bound : MvPolynomial Parameter ℕ),
      Appends polynomial bound role machine entry exit := by
  classical
  induction polynomial using MvPolynomial.induction_on with
  | C count =>
    exact ⟨Empty, inferInstance, Empty.elim, Fin (count + 1), inferInstance,
      constant count, Fin.last count, 0, MvPolynomial.C count, constant_appends count⟩
  | add left right leftExists rightExists =>
    obtain ⟨Left, leftFinite, leftRole, First, firstFinite, first, firstEntry, firstExit, leftBound, firstCorrect⟩ := leftExists
    obtain ⟨Right, rightFinite, rightRole, Second, secondFinite, second, secondEntry, secondExit, rightBound, secondCorrect⟩ := rightExists
    let leftFiniteInstance := leftFinite
    let rightFiniteInstance := rightFinite
    let firstFiniteInstance := firstFinite
    let secondFiniteInstance := secondFinite
    exact ⟨Left ⊕ Right, inferInstance, Sum.elim leftRole rightRole, First ⊕ Second, inferInstance,
      MultiTape.sequence (wire (leftWiring Left Right) first) (wire (rightWiring Left Right) second) secondEntry,
      .inl firstEntry, .inr secondExit, leftBound + rightBound + 1,
      add_appends left leftBound right rightBound leftRole rightRole first second firstEntry firstExit
        secondEntry secondExit firstCorrect secondCorrect⟩
  | mul_X polynomial parameter hypothesis =>
    obtain ⟨Source, sourceFinite, role, State, stateFinite, machine, entry, exit, bound, correct⟩ := hypothesis
    let sourceFiniteInstance := sourceFinite
    let stateFiniteInstance := stateFinite
    exact ⟨Unit ⊕ Source, inferInstance, Sum.elim (fun _ : Unit => parameter) role,
      (Bool ⊕ State) ⊕ (Fin 2 ⊕ Fin 3), inferInstance,
      MultiTape.sequence (repeatMachine machine entry) (wire (returnWiring Source) StandardHead.BlankReturn.fromEnd) (.inl 1),
      .inl (.inl false), .inr (.inr 2), MvPolynomial.X parameter * (bound + 3) + 5,
      mul_X_appends polynomial bound parameter role machine entry exit correct⟩

end Appenders
end Polytime2.UnaryPolynomial
