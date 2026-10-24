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

import Polytime2.Matrices.DiagonalCleanupStep
import Polytime2.Matrices.DiagonalBoundsMath
import Polytime2.Arrays.FoldContract
import Polytime2.Arrays.Indices

/-! # Bounded diagonal cleanup in a fixed polynomial workspace

The state is a natural diagonal and two ordinary bounded integer matrices.
For a product bound P, initial basis width B, and iteration budget F, reserve
B + F * (4 * (P + 1) + 3) basis bits. The logical prefix invariant bounds the
actual entries more tightly after each iteration. It supplies the guarded
step's precondition without runtime bound checks. Every prefix agrees with
the existing mathematical recursion, including stopped states.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation.Realizable.Internal

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

/-- A fixed workspace for every prefix of the bounded cleanup. -/
noncomputable def diagonalCleanupWorkspace (productWidth steps initialBasisWidth : MvPolynomial Parameter ℕ) :=
  initialBasisWidth + steps * (4 * (productWidth + 1) + 3)

/-- Ordinary diagonal entries and both accumulated bases. -/
noncomputable def diagonalCleanupState (length productWidth basisWidth : MvPolynomial Parameter ℕ) : EncodedDomain Parameter :=
  (diagonalCleanupStep length productWidth basisWidth).outputDomain

private def stateArguments (length productWidth basisWidth : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (state : (diagonalCleanupState length productWidth basisWidth).Carrier sizes) :
    (diagonalCleanupStep length productWidth basisWidth).Arguments sizes
  | 0 => state.1
  | 1 => state.2.1
  | 2 => state.2.2

private def stateAllowed (length productWidth basisWidth : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (state : (diagonalCleanupState length productWidth basisWidth).Carrier sizes) :=
  (diagonalCleanupStep length productWidth basisWidth).precondition sizes
    (stateArguments length productWidth basisWidth sizes state)

private noncomputable def stateAdvance (length productWidth basisWidth : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ) (state : (diagonalCleanupState length productWidth basisWidth).Carrier sizes) :
    (diagonalCleanupState length productWidth basisWidth).Carrier sizes := by
  classical
  exact if valid : stateAllowed length productWidth basisWidth sizes state then
    (diagonalCleanupStep length productWidth basisWidth).compute sizes
      ⟨stateArguments length productWidth basisWidth sizes state, valid⟩ else state

private def stateValues (length productWidth basisWidth : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (state : (diagonalCleanupState length productWidth basisWidth).Carrier sizes) :=
  ((fun index => (state.1 index).val), (state.2.1.val, state.2.2.val))

private theorem stateAdvance_realizable (length productWidth basisWidth : MvPolynomial Parameter ℕ) :
    (unaryMap (diagonalCleanupState length productWidth basisWidth)
      (diagonalCleanupState length productWidth basisWidth) (stateAllowed length productWidth basisWidth)
      (fun sizes state => stateAdvance length productWidth basisWidth sizes state.val)).Realizable := by
  let domain := diagonalCleanupState length productWidth basisWidth
  let inputs := fun _ : Unit => domain
  let allowed sizes (arguments : ∀ name, (inputs name).Carrier sizes) :=
    stateAllowed length productWidth basisWidth sizes (arguments ())
  let values := (binaryNaturalsOfWidth (productWidth + 1)).arrayOfLength length
  let matrix := integerMatrices length length basisWidth
  have bases := (pairProjection_realizable values (matrix.prod matrix) true).withPrecondition allowed (by intros; trivial)
  have step := (diagonalCleanupStep_realizable length productWidth basisWidth).onResults inputs allowed
    (fun name sizes arguments => stateArguments length productWidth basisWidth sizes (arguments.val ()) name)
    (fun _ arguments => arguments.property) (by
      intro name
      fin_cases name
      · exact (pairProjection_realizable values (matrix.prod matrix) false).withPrecondition allowed (by intros; trivial)
      · exact bases.followedBy (pairProjection_realizable matrix matrix false) rfl (by intros; trivial)
      · exact bases.followedBy (pairProjection_realizable matrix matrix true) rfl (by intros; trivial))
  apply step.withSpecification allowed _ (by intros; assumption)
  intro sizes arguments valid
  dsimp only [stateAdvance]
  rw [dite_eq_left valid]
  rfl

private theorem stateAdvance_correct (length productWidth basisWidth : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ) (state : (diagonalCleanupState length productWidth basisWidth).Carrier sizes)
    (valid : stateAllowed length productWidth basisWidth sizes state) :
    stateValues length productWidth basisWidth sizes (stateAdvance length productWidth basisWidth sizes state) =
      IntegerMatrix.diagonalCleanupWithBases 1 (stateValues length productWidth basisWidth sizes state).1
        (stateValues length productWidth basisWidth sizes state).2.1
        (stateValues length productWidth basisWidth sizes state).2.2 := by
  dsimp only [stateAdvance]
  rw [dite_eq_left valid]
  exact diagonalCleanupStep_correct length productWidth basisWidth sizes
    ⟨stateArguments length productWidth basisWidth sizes state, valid⟩

private def initialAllowed (length productWidth steps initialBasisWidth : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (state : (diagonalCleanupState length productWidth (diagonalCleanupWorkspace productWidth steps initialBasisWidth)).Carrier sizes) :=
  (∀ index, 0 < (state.1 index).val) ∧
    (∏ index, (state.1 index).val) ≤ 2 ^ MvPolynomial.eval sizes productWidth ∧
    (∀ row column, (state.2.1.val row column).natAbs < 2 ^ MvPolynomial.eval sizes initialBasisWidth) ∧
    (∀ row column, (state.2.2.val row column).natAbs < 2 ^ MvPolynomial.eval sizes initialBasisWidth)

private def prefixInvariant (length productWidth steps initialBasisWidth : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (initial : (diagonalCleanupState length productWidth (diagonalCleanupWorkspace productWidth steps initialBasisWidth)).Carrier sizes)
    (count : ℕ)
    (state : (diagonalCleanupState length productWidth (diagonalCleanupWorkspace productWidth steps initialBasisWidth)).Carrier sizes) :=
  (∀ index, 0 < (state.1 index).val) ∧
    (∏ index, (state.1 index).val) ≤ 2 ^ MvPolynomial.eval sizes productWidth ∧
    (∀ row column, (state.2.1.val row column).natAbs < 2 ^ (MvPolynomial.eval sizes initialBasisWidth +
      count * (4 * MvPolynomial.eval sizes (productWidth + 1) + 3))) ∧
    (∀ row column, (state.2.2.val row column).natAbs < 2 ^ (MvPolynomial.eval sizes initialBasisWidth +
      count * (4 * MvPolynomial.eval sizes (productWidth + 1) + 3))) ∧
    stateValues length productWidth (diagonalCleanupWorkspace productWidth steps initialBasisWidth) sizes state =
      IntegerMatrix.diagonalCleanupWithBases count (fun index => (initial.1 index).val) initial.2.1.val initial.2.2.val

private theorem prefixInvariant_starts (length productWidth steps initialBasisWidth : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (initial : (diagonalCleanupState length productWidth (diagonalCleanupWorkspace productWidth steps initialBasisWidth)).Carrier sizes)
    (valid : initialAllowed length productWidth steps initialBasisWidth sizes initial) :
    prefixInvariant length productWidth steps initialBasisWidth sizes initial 0 initial := by
  exact ⟨valid.1, valid.2.1, by simpa using valid.2.2.1, by simpa using valid.2.2.2, rfl⟩

private theorem prefixInvariant_permits (length productWidth steps initialBasisWidth : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (initial state : (diagonalCleanupState length productWidth (diagonalCleanupWorkspace productWidth steps initialBasisWidth)).Carrier sizes)
    (index : Fin (MvPolynomial.eval sizes steps))
    (valid : prefixInvariant length productWidth steps initialBasisWidth sizes initial index.val state) :
    stateAllowed length productWidth (diagonalCleanupWorkspace productWidth steps initialBasisWidth) sizes state := by
  refine ⟨valid.1, valid.2.1, MvPolynomial.eval sizes initialBasisWidth +
    index.val * (4 * MvPolynomial.eval sizes (productWidth + 1) + 3), valid.2.2.1, valid.2.2.2.1, ?_⟩
  have budget := Nat.mul_le_mul_right (4 * MvPolynomial.eval sizes (productWidth + 1) + 3)
    (Nat.succ_le_of_lt index.isLt)
  simp only [diagonalCleanupWorkspace, map_add, map_mul, map_ofNat, map_one] at budget ⊢
  nlinarith

private theorem prefixInvariant_preserves (length productWidth steps initialBasisWidth : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (initial state : (diagonalCleanupState length productWidth (diagonalCleanupWorkspace productWidth steps initialBasisWidth)).Carrier sizes)
    (index : Fin (MvPolynomial.eval sizes steps))
    (valid : prefixInvariant length productWidth steps initialBasisWidth sizes initial index.val state) :
    prefixInvariant length productWidth steps initialBasisWidth sizes initial (index.val + 1)
      (stateAdvance length productWidth (diagonalCleanupWorkspace productWidth steps initialBasisWidth) sizes state) := by
  let workspace := diagonalCleanupWorkspace productWidth steps initialBasisWidth
  have permitted := prefixInvariant_permits length productWidth steps initialBasisWidth sizes initial state index valid
  have computed := stateAdvance_correct length productWidth workspace sizes state permitted
  have diagonal := congrArg Prod.fst computed
  have bases := congrArg Prod.snd computed
  have pureDiagonal := IntegerMatrix.diagonalCleanupWithBases_diagonal 1
    (fun index => (state.1 index).val) state.2.1.val state.2.2.val
  have positive := IntegerMatrix.diagonalCleanup_correct 1 (fun index => (state.1 index).val) valid.1
  have bound := IntegerMatrix.diagonalCleanupWithBases_bound 1 (MvPolynomial.eval sizes productWidth)
    (MvPolynomial.eval sizes initialBasisWidth + index.val * (4 * MvPolynomial.eval sizes (productWidth + 1) + 3))
    (fun index => (state.1 index).val) state.2.1.val state.2.2.val valid.1 valid.2.1 valid.2.2.1 valid.2.2.2.1
  have prefixWidth : MvPolynomial.eval sizes initialBasisWidth + index.val * (4 * MvPolynomial.eval sizes (productWidth + 1) + 3) +
      1 * (4 * (MvPolynomial.eval sizes productWidth + 1) + 3) =
      MvPolynomial.eval sizes initialBasisWidth + (index.val + 1) * (4 * MvPolynomial.eval sizes (productWidth + 1) + 3) := by
    simp only [map_add, map_one]
    ring
  rw [prefixWidth] at bound
  have diagonalEqual := diagonal.trans pureDiagonal
  change (fun position => ((stateAdvance length productWidth workspace sizes state).1 position).val) = _ at diagonalEqual
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro position
    rw [congrFun diagonalEqual position]
    exact positive.1 position
  · rw [diagonalEqual, positive.2.1]
    exact valid.2.1
  · have leftEqual := congrArg Prod.fst bases
    dsimp only [stateValues] at leftEqual
    rw [leftEqual]
    exact bound.1
  · have rightEqual := congrArg Prod.snd bases
    dsimp only [stateValues] at rightEqual
    rw [rightEqual]
    exact bound.2
  · exact computed.trans ((congrArg (fun value => IntegerMatrix.diagonalCleanupWithBases 1 value.1 value.2.1 value.2.2)
      valid.2.2.2.2).trans (IntegerMatrix.diagonalCleanupWithBases_succ_last index.val
        (fun index => (initial.1 index).val) initial.2.1.val initial.2.2.val).symm)

private noncomputable def controllerFold (length productWidth steps initialBasisWidth : MvPolynomial Parameter ℕ) :=
  arrayFold (Empty.elim : Empty → EncodedDomain Parameter) (arrayPosition steps)
    (diagonalCleanupState length productWidth (diagonalCleanupWorkspace productWidth steps initialBasisWidth)) steps
    (fun sizes _context _array initial => initialAllowed length productWidth steps initialBasisWidth sizes initial)
    (fun sizes _context state _token => stateAdvance length productWidth
      (diagonalCleanupWorkspace productWidth steps initialBasisWidth) sizes state)

private theorem controllerFold_realizable (length productWidth steps initialBasisWidth : MvPolynomial Parameter ℕ) :
    (controllerFold length productWidth steps initialBasisWidth).Realizable := by
  let context := (Empty.elim : Empty → EncodedDomain Parameter)
  let workspace := diagonalCleanupWorkspace productWidth steps initialBasisWidth
  let domain := diagonalCleanupState length productWidth workspace
  let admissible sizes (_context : ∀ name, (context name).Carrier sizes) (_array : ((arrayPosition steps).arrayOfLength steps).Carrier sizes)
      (initial : domain.Carrier sizes) := initialAllowed length productWidth steps initialBasisWidth sizes initial
  let update sizes (_context : ∀ name, (context name).Carrier sizes) (state : domain.Carrier sizes)
      (_token : (arrayPosition steps).Carrier sizes) := stateAdvance length productWidth workspace sizes state
  let allowed sizes (_context : ∀ name, (context name).Carrier sizes) (state : domain.Carrier sizes)
      (_token : (arrayPosition steps).Carrier sizes) := stateAllowed length productWidth workspace sizes state
  have step : (arrayFoldStep context (arrayPosition steps) domain allowed update).Realizable := by
    have ready := (stateAdvance_realizable length productWidth workspace).withArguments
      (arrayFoldStep context (arrayPosition steps) domain allowed update).inputDomains
      (MultiTape.oneTape (.inr false)) (fun _ => rfl)
    exact ready.withSpecification _ _ (by intros; assumption) (by intros; rfl)
  exact arrayFold_realizable context (arrayPosition steps) domain steps admissible update allowed step
    (fun sizes _context _array initial count state => prefixInvariant length productWidth steps initialBasisWidth sizes initial count state)
    (fun sizes _context _array initial valid => prefixInvariant_starts length productWidth steps initialBasisWidth sizes initial valid)
    (fun sizes _context _array initial _valid index state invariant =>
      prefixInvariant_permits length productWidth steps initialBasisWidth sizes initial state index invariant)
    (fun sizes _context _array initial _valid index state invariant =>
      prefixInvariant_preserves length productWidth steps initialBasisWidth sizes initial state index invariant)

/-- Repeat the guarded update for the supplied polynomial iteration budget. -/
noncomputable def diagonalCleanupController (length productWidth steps initialBasisWidth : MvPolynomial Parameter ℕ) :
    Computation Parameter Unit :=
  unaryMap (diagonalCleanupState length productWidth (diagonalCleanupWorkspace productWidth steps initialBasisWidth))
    (diagonalCleanupState length productWidth (diagonalCleanupWorkspace productWidth steps initialBasisWidth))
    (initialAllowed length productWidth steps initialBasisWidth)
    (fun sizes initial => ArrayFold.prefixValue
      (fun state (_token : Fin (MvPolynomial.eval sizes steps)) => stateAdvance length productWidth
        (diagonalCleanupWorkspace productWidth steps initialBasisWidth) sizes state)
      id initial.val (MvPolynomial.eval sizes steps))

theorem diagonalCleanupController_realizable (length productWidth steps initialBasisWidth : MvPolynomial Parameter ℕ) :
    (diagonalCleanupController length productWidth steps initialBasisWidth).Realizable := by
  let computation := diagonalCleanupController length productWidth steps initialBasisWidth
  let results (name : Empty ⊕ Bool) (sizes : Parameter → ℕ)
      (arguments : {arguments : computation.Arguments sizes // computation.precondition sizes arguments}) :
      ((controllerFold length productWidth steps initialBasisWidth).inputDomains name).Carrier sizes :=
    match name with
    | .inl impossible => nomatch impossible
    | .inr false => arguments.val ()
    | .inr true => id
  have complete := (controllerFold_realizable length productWidth steps initialBasisWidth).onResults
    computation.inputDomains computation.precondition results (fun _ arguments => arguments.property) (by
      intro name
      rcases name with impossible | choice
      · exact impossible.elim
      · cases choice
        · exact Realizable.argument computation.inputDomains () computation.precondition
        · exact (arrayPositions_realizable steps).onResults computation.inputDomains computation.precondition
            (fun impossible => impossible.elim) (by intros; trivial) (fun impossible => impossible.elim))
  exact complete.withSpecification computation.precondition computation.compute
    (by intros; assumption) (by intros; rfl)

/-- The bounded controller returns exactly the existing mathematical recursion. -/
theorem diagonalCleanupController_correct (length productWidth steps initialBasisWidth : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (diagonalCleanupController length productWidth steps initialBasisWidth).Arguments sizes //
      (diagonalCleanupController length productWidth steps initialBasisWidth).precondition sizes arguments}) :
    let result := (diagonalCleanupController length productWidth steps initialBasisWidth).compute sizes arguments
    ((fun index => (result.1 index).val), (result.2.1.val, result.2.2.val)) =
      IntegerMatrix.diagonalCleanupWithBases (MvPolynomial.eval sizes steps) (fun index => ((arguments.val ()).1 index).val)
        (arguments.val ()).2.1.val (arguments.val ()).2.2.val := by
  have invariant := ArrayFold.prefix_invariant
    (fun state (_token : Fin (MvPolynomial.eval sizes steps)) => stateAdvance length productWidth
      (diagonalCleanupWorkspace productWidth steps initialBasisWidth) sizes state)
    (id : Fin (MvPolynomial.eval sizes steps) → Fin (MvPolynomial.eval sizes steps)) (arguments.val ())
    (prefixInvariant length productWidth steps initialBasisWidth sizes (arguments.val ()))
    (prefixInvariant_starts length productWidth steps initialBasisWidth sizes (arguments.val ()) arguments.property)
    (fun index state valid => prefixInvariant_preserves length productWidth steps initialBasisWidth sizes
      (arguments.val ()) state index valid) (MvPolynomial.eval sizes steps) le_rfl
  exact invariant.2.2.2.2

end Polytime2.Computation.Realizable.Internal
