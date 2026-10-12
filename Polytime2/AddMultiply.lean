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

import Polytime2.BinaryMultiplication

/-! # Addition followed by multiplication on shared tapes

A single fixed finite controller computes `(left + right) * multiplier`.
The addition writes directly into the multiplicand tape of the multiplication
routine. The two input operands share a runtime digit capacity, and the
multiplier has an independent runtime capacity. Working buffers are prepared
zero words; this is an internal calling convention, not an external parser.
-/

namespace Polytime2.AddMultiply

open MultiTape
open Binary (Symbol word value)

abbrev Alphabet := fun _ : Fin 7 => Symbol

/-- The original addends and multiplier; their lists include capacity padding. -/
abbrev Input := List Bool × (List Bool × List Bool)

/-- Original addends, multiplier, and the computed sum passed to multiplication. -/
abbrev Middle := List Bool × (List Bool × (List Bool × List Bool))

def workWiring : Fin 5 ↪ Fin 7 :=
  ⟨fun name => ⟨name.val, by omega⟩, by intro left right equal; exact Fin.ext (congrArg (fun name : Fin 7 => name.val) equal)⟩

def additionWiring : Fin 3 ↪ Fin 7 where
  toFun name := if name = 0 then 5 else if name = 1 then 6 else 1
  inj' := by intro left right equal; fin_cases left <;> fin_cases right <;> simp_all

def frame (left right : List Bool) (work : Tapes BinaryMultiplication.Alphabet) : Tapes Alphabet :=
  fun name => if small : name.val < 5 then work ⟨name.val, small⟩
    else if name = 5 then BinaryMultiplication.tape left else BinaryMultiplication.tape right

def inputRepresentation (input : Input) (tapes : Tapes Alphabet) : Prop :=
  tapes = frame input.1 input.2.1
    (BinaryMultiplication.frame (BinaryMultiplication.tape input.2.2)
      (List.replicate input.1.length false)
      (List.replicate (input.1.length + 1) false)
      (List.replicate (input.1.length + 1) false)
      (List.replicate (input.1.length + 1) false))

def middleRepresentation (middle : Middle) (tapes : Tapes Alphabet) : Prop :=
  tapes = frame middle.1 middle.2.1
    (BinaryMultiplication.frame (BinaryMultiplication.tape middle.2.2.1) middle.2.2.2
      (List.replicate middle.2.2.2.length false)
      (List.replicate middle.2.2.2.length false)
      (List.replicate middle.2.2.2.length false))

def outputRepresentation (sizes : Bool → ℕ) (result : ℕ) (tapes : Tapes Alphabet) : Prop :=
  ∃ bits, value bits = result ∧ bits.length ≤ sizes false + 1 + sizes true ∧
    tapes 2 = BinaryMultiplication.tape bits

def firstMap (input : Input) : Middle :=
  (input.1, input.2.1, input.2.2, BinaryAddition.add input.1 input.2.1)

noncomputable def first : Machine Alphabet BinaryAddition.State :=
  wire additionWiring BinaryAddition.machine

noncomputable def second : Machine Alphabet BinaryMultiplication.State :=
  wire workWiring BinaryMultiplication.machine

noncomputable def machine : Machine Alphabet (Sum BinaryAddition.State BinaryMultiplication.State) :=
  sequence first second BinaryMultiplication.entry

/-- Addition exposes only the mathematical intermediate sum and storage contract. -/
theorem first_contract :
    Computes first (.inl false) (.inr 1)
      (fun _sizes : Bool → ℕ => inputRepresentation) (fun _ => middleRepresentation)
      (fun sizes input => input.2.1.length = input.1.length ∧
        input.1.length ≤ sizes false ∧ input.2.2.length ≤ sizes true)
      (fun _ => firstMap) := by
  refine ⟨by intro symbols; simp [first, wire, BinaryAddition.machine],
    2 * MvPolynomial.X false + 3, ?_⟩
  intro sizes input initial valid represented
  subst initial
  let updated := BinaryAddition.add input.1 input.2.1
  have updatedLength : updated.length = input.1.length + 1 := BinaryAddition.add_length _ _ valid.1
  have trace := BinaryAddition.steps input.1 input.2.1 valid.1
    (word (List.replicate input.1.length false)) (by simp [word]) [] [] [] [] [] [0]
  have lifted : Steps first (2 * input.1.length + 3)
      (.inl false, frame input.1 input.2.1
        (BinaryMultiplication.frame (BinaryMultiplication.tape input.2.2)
          (List.replicate input.1.length false)
          (List.replicate (input.1.length + 1) false)
          (List.replicate (input.1.length + 1) false)
          (List.replicate (input.1.length + 1) false)))
      (.inr 1, frame input.1 input.2.1
        (BinaryMultiplication.frame (BinaryMultiplication.tape input.2.2) updated
          (List.replicate (input.1.length + 1) false)
          (List.replicate (input.1.length + 1) false)
          (List.replicate (input.1.length + 1) false))) := by
    apply wire_steps_of_eq additionWiring _ trace
    · intro name
      fin_cases name
      · rfl
      · rfl
      · change BinaryMultiplication.tape _ = Turing.Tape.mk' _ _
        simp [BinaryMultiplication.tape, Binary.tape, Binary.mk_append_blank]
    · intro name
      fin_cases name <;> rfl
    · intro name outside
      fin_cases name <;> first
        | rfl
        | exact False.elim (outside ⟨0, rfl⟩)
        | exact False.elim (outside ⟨1, rfl⟩)
        | exact False.elim (outside ⟨2, rfl⟩)
  refine ⟨_, _, ?_, lifted, ?_⟩
  · simp only [map_add, map_mul, map_ofNat, MvPolynomial.eval_X]
    omega
  · dsimp only [middleRepresentation, firstMap]
    rw [BinaryAddition.add_length input.1 input.2.1 valid.1]


/-- Multiplication accepts the intermediate sum under its derived capacity. -/
theorem second_contract :
    Computes second BinaryMultiplication.entry BinaryMultiplication.exit
      (fun _sizes : Bool → ℕ => middleRepresentation) outputRepresentation
      (fun sizes middle => middle.2.2.2.length ≤ sizes false + 1 ∧ middle.2.2.1.length ≤ sizes true)
      (fun _ middle => value middle.2.2.2 * value middle.2.2.1) := by
  refine ⟨by intro symbols; simp [second, wire, BinaryMultiplication.machine, BinaryMultiplication.exit, withExit],
    MvPolynomial.X true * (4 * (MvPolynomial.X false + 1 + MvPolynomial.X true) + 23) + 1, ?_⟩
  intro sizes middle initial valid represented
  subst initial
  obtain ⟨ticks, scratch, cost, scratchLength, trace⟩ :=
    BinaryMultiplication.steps middle.2.2.2 middle.2.2.1
  let finalWork := BinaryMultiplication.frame
    (Binary.tape (word middle.2.2.1.reverse ++ [3]) [0] ())
    (List.replicate middle.2.2.1.length false ++ middle.2.2.2)
    (BinaryMultiplication.accumulate middle.2.2.2 (List.replicate middle.2.2.2.length false) middle.2.2.1)
    scratch (List.replicate (middle.2.2.2.length + middle.2.2.1.length) false)
  have lifted : Steps second ticks
      (BinaryMultiplication.entry, frame middle.1 middle.2.1
        (BinaryMultiplication.frame (BinaryMultiplication.tape middle.2.2.1) middle.2.2.2
          (List.replicate middle.2.2.2.length false)
          (List.replicate middle.2.2.2.length false)
          (List.replicate middle.2.2.2.length false)))
      (BinaryMultiplication.exit, frame middle.1 middle.2.1 finalWork) := by
    apply wire_steps_of_eq workWiring _ trace
    · intro name; fin_cases name <;> rfl
    · intro name; fin_cases name <;> rfl
    · intro name outside
      fin_cases name <;> first
        | rfl
        | exact False.elim (outside ⟨0, rfl⟩)
        | exact False.elim (outside ⟨1, rfl⟩)
        | exact False.elim (outside ⟨2, rfl⟩)
        | exact False.elim (outside ⟨3, rfl⟩)
        | exact False.elim (outside ⟨4, rfl⟩)
  refine ⟨ticks, _, ?_, lifted, ?_⟩
  · simp only [map_add, map_mul, map_ofNat, map_one, MvPolynomial.eval_X]
    have inner : 4 * (middle.2.2.2.length + middle.2.2.1.length) + 23 ≤
        4 * (sizes false + 1 + sizes true) + 23 := by omega
    exact cost.trans (Nat.add_le_add_right (Nat.mul_le_mul valid.2 inner) 1)
  · refine ⟨BinaryMultiplication.accumulate middle.2.2.2
      (List.replicate middle.2.2.2.length false) middle.2.2.1, ?_, ?_, rfl⟩
    · have product := BinaryMultiplication.accumulate_value middle.2.2.2
        (List.replicate middle.2.2.2.length false) middle.2.2.1 (by simp)
      have zero : value (List.replicate middle.2.2.2.length false) = 0 := by
        induction middle.2.2.2.length with
        | zero => rfl
        | succ count hypothesis => simp [List.replicate_succ, Binary.value, hypothesis]
      simpa [zero] using product
    · rw [BinaryMultiplication.accumulate_length middle.2.2.2
        (List.replicate middle.2.2.2.length false) middle.2.2.1 (by simp), List.length_replicate]
      omega

/-- One finite multi-tape machine computes addition followed by multiplication.
Polynomial witnesses and handovers are hidden by the composition rule. -/
theorem contract :
    Computes machine (.inl (.inl false)) (.inr BinaryMultiplication.exit)
      (fun _sizes : Bool → ℕ => inputRepresentation) outputRepresentation
      (fun sizes input => input.2.1.length = input.1.length ∧
        input.1.length ≤ sizes false ∧ input.2.2.length ≤ sizes true)
      (fun _ input => (value input.1 + value input.2.1) * value input.2.2) := by
  have composed := first_contract.sequence second_contract
    (by intro sizes input valid
        simp only [firstMap, BinaryAddition.add_length _ _ valid.1]
        exact ⟨by omega, valid.2.2⟩)
  apply composed.congr
  intro sizes input valid
  simp only [firstMap, BinaryAddition.add_value input.1 input.2.1 valid.1]


end Polytime2.AddMultiply
