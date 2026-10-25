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

import Polytime2.Computation.Specification
import Polytime2.Arrays.FoldContract
import Mathlib.Data.List.FinRange
import Mathlib.Data.Finset.Card
import Mathlib.SetTheory.Cardinal.Finite
import Polytime2.Primitives.BitOperations
import Polytime2.Computation.Branch
import Polytime2.Computation.Arguments
import Polytime2.Computation.Composition

/-! # Counting Boolean flags with a private polynomial-width accumulator -/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

variable {Parameter : Type} [Fintype Parameter]

/-- Mathematical counter update, shared by the fold and its correctness proof. -/
def addFlag {width : ℕ} (current : BitVec width) (flag : Bool) : BitVec width :=
  if flag then BitVec.ofNat width (current.toNat + 1) else current

/-- Add one for a true flag, using modular arithmetic at the fixed bit width. -/
private noncomputable def countFlagImplementation (capacity : MvPolynomial Parameter ℕ) :
    Computation Parameter Bool :=
  (incrementBits capacity).choose
    (encodingMap (EncodedDomain.bitVectors capacity) (EncodedDomain.bitVectors capacity) (fun _ value => value))
    (fun _ => rfl) rfl |>.withArguments
      (fun choice => if choice then EncodedDomain.booleans else EncodedDomain.bitVectors capacity)
      ⟨(fun name => match name with | .inl _ => false | .inr _ => true), by
        rintro (⟨⟩ | ⟨⟩) (⟨⟩ | ⟨⟩) equal <;> first | rfl | cases equal⟩
      (by rintro (name | name); cases name; rfl; cases name; rfl)

private theorem countFlagImplementation_realizable (capacity : MvPolynomial Parameter ℕ) :
    (countFlagImplementation capacity).Realizable := by
  have choose := (incrementBits_realizable capacity).choose
    (encodingMap_realizable (EncodedDomain.bitVectors capacity) (EncodedDomain.bitVectors capacity)
      (fun _ value => value) (by intros; rfl) (by intros; rfl)) (fun _ => rfl) rfl
  exact choose.withArguments _ _ _

/-- Total conditional increment, with its branching implementation hidden. -/
noncomputable def countFlagStep (capacity : MvPolynomial Parameter ℕ) : Computation Parameter Bool where
  inputDomains choice := if choice then EncodedDomain.booleans else EncodedDomain.bitVectors capacity
  outputDomain := EncodedDomain.bitVectors capacity
  precondition _ _ := True
  compute _ arguments := addFlag (arguments.val false) (arguments.val true)

theorem countFlagStep_realizable (capacity : MvPolynomial Parameter ℕ) :
    (countFlagStep capacity).Realizable := by
  exact (countFlagImplementation_realizable capacity).withSpecification
    (countFlagStep capacity).precondition (countFlagStep capacity).compute (by
      intro sizes arguments valid
      simp [countFlagImplementation, Computation.withArguments, choose, incrementBits, encodingMap, unaryMap]
      split <;> trivial) (by
      intro sizes arguments valid
      simp only [countFlagImplementation, Computation.withArguments, choose, incrementBits,
        encodingMap, unaryMap, countFlagStep]
      split <;> rename_i selected
      · change arguments true = true at selected
        simp only [addFlag, selected, ite_true]
        rfl
      · change arguments true = false at selected
        simp only [addFlag, selected, Bool.false_eq_true, ite_false]
        rfl)

/-- The mathematical fold counts true flags modulo the counter capacity. -/
theorem countFlag_fold {width : ℕ} (flags : List Bool) (initial : BitVec width) :
    (flags.foldl addFlag initial).toNat = (initial.toNat + flags.count true) % 2 ^ width := by
  induction flags generalizing initial with
  | nil => simp [Nat.mod_eq_of_lt initial.isLt]
  | cons flag rest hypothesis =>
    cases flag <;> simp [List.foldl_cons, addFlag, hypothesis, BitVec.toNat_ofNat,
      Nat.add_comm, Nat.add_left_comm]

/-- The count width is one more than the array length; its seed is private. -/
private noncomputable def implementation (length : MvPolynomial Parameter ℕ) : Computation Parameter Unit where
  inputDomains _ := EncodedDomain.booleans.arrayOfLength length
  outputDomain := EncodedDomain.bitVectors (length + 1)
  precondition _ _ := True
  compute sizes arguments := ArrayFold.prefixValue
    addFlag
    (arguments.val ()) (BitVec.ofNat (MvPolynomial.eval sizes (length + 1)) 0) (MvPolynomial.eval sizes length)

private theorem implementation_realizable (length : MvPolynomial Parameter ℕ) : (implementation length).Realizable := by
  let accumulator := EncodedDomain.bitVectors (length + 1)
  let computation := implementation length
  have step := (countFlagStep_realizable (length + 1)).withArguments
    (arrayFoldStep Empty.elim EncodedDomain.booleans accumulator (fun _ _ _ _ => True)
      (fun _ _ current flag => addFlag current flag)).inputDomains
    ⟨Sum.inr, Sum.inr_injective⟩ (by intro choice; cases choice <;> rfl)
  have folded := arrayFold_total_realizable Empty.elim EncodedDomain.booleans accumulator length
    (fun _ _ current flag => addFlag current flag) step
  have seed := (zeroBits_realizable (length + 1)).withArguments computation.inputDomains
    ⟨Empty.elim, by intro impossible; exact impossible.elim⟩ (by intro impossible; exact impossible.elim)
  let domains : Unit ⊕ Unit → EncodedDomain Parameter := Sum.elim computation.inputDomains (fun _ => accumulator)
  have continuation := folded.withArguments domains
    ⟨(fun name => match name with | .inl impossible => impossible.elim | .inr false => .inr () | .inr true => .inl ()), by
      rintro (impossible | first) (impossible' | second) equal
      all_goals first | exact impossible.elim | exact impossible'.elim | (cases first <;> cases second <;> simp_all)⟩
    (by rintro (impossible | choice); exact impossible.elim; cases choice <;> rfl)
  have combined := seed.letThen continuation (fun _ => rfl) rfl (by intros; trivial)
  exact combined.withSpecification computation.precondition computation.compute (by intros; trivial) (by intros; rfl)

/-- Boolean array counts equal the cardinality of their active positions. -/
theorem count_flags_card {length : ℕ} (flags : Fin length → Bool) :
    (List.ofFn flags).count true = Nat.card {index : Fin length // flags index = true} := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have counted := (List.nodup_finRange length).card_eq_countP (P := fun index => flags index = true)
  have allIndices : (List.finRange length).toFinset = Finset.univ := by ext index; simp
  rw [allIndices] at counted
  rw [counted, List.ofFn_eq_map, List.count_eq_countP, List.countP_map]
  simp [Function.comp_def]

/-- The private capacity prevents overflow: the result is the exact count. -/
private theorem implementation_correct (length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (flags : Fin (MvPolynomial.eval sizes length) → Bool) :
    ((implementation length).compute sizes ⟨(fun _ => flags), trivial⟩).toNat = (List.ofFn flags).count true := by
  change (ArrayFold.prefixValue addFlag flags _ _).toNat = _
  unfold ArrayFold.prefixValue
  rw [List.take_of_length_le (by simp), countFlag_fold]
  simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_add]
  apply Nat.mod_eq_of_lt
  have bounded := List.count_le_length (a := true) (l := List.ofFn flags)
  have exponential := Nat.lt_two_pow_self (n := MvPolynomial.eval sizes length + 1)
  simp only [List.length_ofFn] at bounded
  simpa only [map_add, map_one] using lt_of_le_of_lt bounded (by omega :
    MvPolynomial.eval sizes length < 2 ^ (MvPolynomial.eval sizes length + 1))
/-- Specify the cardinality of the true positions mathematically.
The finite-memory traversal and counter implementation stay private. -/
noncomputable def countFlags (length : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  specificationBy (fun _ => EncodedDomain.booleans.arrayOfLength length)
    (EncodedDomain.bitVectors (length + 1)) (fun _ _ => True) (fun _ => BitVec.toNat)
    (fun sizes arguments => Nat.card {index : Fin (MvPolynomial.eval sizes length) // arguments.val () index = true})
    (fun sizes arguments => ⟨(implementation length).compute sizes arguments,
      (implementation_correct length sizes (arguments.val ())).trans (count_flags_card (arguments.val ()))⟩)

theorem countFlags_realizable (length : MvPolynomial Parameter ℕ) : (countFlags length).Realizable := by
  apply (implementation_realizable length).specificationBy
  · intro sizes first second same
    exact BitVec.eq_of_toNat_eq same
  · intro sizes arguments valid
    exact (implementation_correct length sizes (arguments ())).trans (count_flags_card (arguments ()))

/-- Evaluate the mathematical observation without unfolding the traversal. -/
theorem countFlags_correct (length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (flags : Fin (MvPolynomial.eval sizes length) → Bool) :
    ((countFlags length).compute sizes ⟨(fun _ => flags), trivial⟩).toNat = (List.ofFn flags).count true := by
  rw [count_flags_card]
  simp only [countFlags, specificationBy_correct]

end Polytime2.Computation
