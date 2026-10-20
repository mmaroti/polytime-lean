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

import Polytime2.Examples.SMP.PreparedConversion
import Polytime2.Arithmetic.UnaryComparison
import Polytime2.Computation.Variants

/-! # Preparation returns an explicit obstruction or an exact prepared input -/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.SMP.Prepared

open FirstOrder FirstOrder.Language CoordinateReduction
open Polytime2.Computation EncodedDomain

variable {L : Language.{0, 0}} [L.IsAlgebraic] {Carrier Parameter : Type}
variable [L.Structure Carrier] [Finite Carrier] [Fintype Parameter]

/-- Acceptance flags are ordinary Boolean arrays over the original coordinates.
-/
noncomputable def convertedFlags (coordinates generators : MvPolynomial Parameter ℕ) :
    Computation Parameter Unit where
  inputDomains _ := (convertAllCoordinates (L := L) (Carrier := Carrier) coordinates generators).outputDomain
  outputDomain := booleans.arrayOfLength coordinates
  precondition _ _ := True
  compute _ arguments := fun coordinate => (arguments.val () coordinate).2.1.isSome

theorem convertedFlags_realizable (coordinates generators : MvPolynomial Parameter ℕ) :
    (convertedFlags (L := L) (Carrier := Carrier) coordinates generators).Realizable := by
  apply (conversionAcceptance_realizable (L := L) (Carrier := Carrier) coordinates generators).withEncodedOutput
    (booleans.arrayOfLength coordinates) (convertedFlags (L := L) (Carrier := Carrier) coordinates generators).compute
  · intro sizes
    simp [conversionAcceptance, booleans, width, arrayOfLength, mapArray]
  · intro sizes arguments
    apply congrArg CallingConvention.tape
    simp only [conversionAcceptance, coordinateAccepted, convertedFlags, mapArray,
      arrayOfLength_encode_bits, ArrayEncoding.bits_encode, constant_encode_bits,
      booleans, fixed_encode_bits]

noncomputable def convertedRejection (coordinates generators : MvPolynomial Parameter ℕ) :
    Computation Parameter Unit :=
  (convertedFlags (L := L) (Carrier := Carrier) coordinates generators).followedBy
    (leadingUnarySize coordinates) rfl (by intros; trivial)

theorem convertedRejection_realizable (coordinates generators : MvPolynomial Parameter ℕ) :
    (convertedRejection (L := L) (Carrier := Carrier) coordinates generators).Realizable :=
  (convertedFlags_realizable coordinates generators).followedBy (leadingUnarySize_realizable coordinates)
    rfl (by intros; trivial)

noncomputable def convertedAllAccepted (coordinates generators : MvPolynomial Parameter ℕ) :
    Computation Parameter Unit :=
  (convertedRejection (L := L) (Carrier := Carrier) coordinates generators).followedBy
    (boundedUnaryIsFull coordinates) rfl (by intros; trivial)

theorem convertedAllAccepted_realizable (coordinates generators : MvPolynomial Parameter ℕ) :
    (convertedAllAccepted (L := L) (Carrier := Carrier) coordinates generators).Realizable :=
  (convertedRejection_realizable coordinates generators).followedBy (boundedUnaryIsFull_realizable coordinates)
    rfl (by intros; trivial)

/-- Tag zero carries an original coordinate obstruction. Tag one carries only
the natural prepared sizes and the ordinary prepared input. -/
noncomputable def preparationAlternatives (coordinates generators : MvPolynomial Parameter ℕ) :
    Fin 2 → EncodedDomain Parameter :=
  ![boundedUnary coordinates,
    atComputedSizeDomain (sizeBounds (L := L) (Carrier := Carrier) coordinates generators)
      (Multisorted.preparedDomain (enumeration (L := L) (Carrier := Carrier)))]

noncomputable def prepareConvertedOutcome (coordinates generators : MvPolynomial Parameter ℕ) :
    Computation Parameter Unit where
  inputDomains _ := (convertAllCoordinates (L := L) (Carrier := Carrier) coordinates generators).outputDomain
  outputDomain := variant 2 (preparationAlternatives (L := L) (Carrier := Carrier) coordinates generators)
  precondition _ _ := True
  compute sizes arguments :=
    let accepted : Bool := (convertedAllAccepted (L := L) (Carrier := Carrier) coordinates generators).compute sizes
      ⟨arguments.val, trivial⟩
    if accepted then
      ⟨1, (prepareConverted (L := L) (Carrier := Carrier) coordinates generators).compute sizes ⟨arguments.val, trivial⟩⟩
    else ⟨0, (convertedRejection (L := L) (Carrier := Carrier) coordinates generators).compute sizes ⟨arguments.val, trivial⟩⟩

theorem prepareConvertedOutcome_realizable (coordinates generators : MvPolynomial Parameter ℕ) :
    (prepareConvertedOutcome (L := L) (Carrier := Carrier) coordinates generators).Realizable := by
  let computation := prepareConvertedOutcome (L := L) (Carrier := Carrier) coordinates generators
  let alternatives := preparationAlternatives (L := L) (Carrier := Carrier) coordinates generators
  have accepted := (prepareConverted_realizable (L := L) (Carrier := Carrier) coordinates generators).followedBy
    (variantInjection_realizable 2 alternatives 1) rfl (by intros; trivial)
  have rejected := (convertedRejection_realizable (L := L) (Carrier := Carrier) coordinates generators).followedBy
    (variantInjection_realizable 2 alternatives 0) rfl (by intros; trivial)
  exact Realizable.conditional computation.inputDomains computation.outputDomain computation.precondition
    (fun sizes arguments => (convertedAllAccepted (L := L) (Carrier := Carrier) coordinates generators).compute sizes
      ⟨arguments.val, trivial⟩)
    (fun sizes arguments => ⟨1, (prepareConverted (L := L) (Carrier := Carrier) coordinates generators).compute sizes
      ⟨arguments.val, trivial⟩⟩)
    (fun sizes arguments => ⟨0, (convertedRejection (L := L) (Carrier := Carrier) coordinates generators).compute sizes
      ⟨arguments.val, trivial⟩⟩)
    (convertedAllAccepted_realizable coordinates generators) accepted rejected

/-- The public preparation computation handles both coordinate rejection and
exact-size preparation, with only the original size parameters. -/
noncomputable def prepare (coordinates generators : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  (convertAllCoordinates (L := L) (Carrier := Carrier) coordinates generators).followedBy
    (prepareConvertedOutcome coordinates generators) rfl (by intros; trivial)

theorem prepare_realizable (coordinates generators : MvPolynomial Parameter ℕ) :
    (prepare (L := L) (Carrier := Carrier) coordinates generators).Realizable :=
  (convertAllCoordinates_realizable coordinates generators).followedBy
    (prepareConvertedOutcome_realizable coordinates generators) rfl (by intros; trivial)

/-- The sentinel test accepts exactly when every coordinate flag is true. -/
theorem convertedAllAccepted_correct (coordinates generators : MvPolynomial Parameter ℕ)
    (hostSizes : Parameter → ℕ)
    (arguments : (convertedFlags (L := L) (Carrier := Carrier) coordinates generators).Arguments hostSizes) :
    (convertedAllAccepted (L := L) (Carrier := Carrier) coordinates generators).compute hostSizes
      ⟨arguments, trivial⟩ = true ↔ ∀ coordinate, (arguments () coordinate).2.1.isSome = true := by
  let flags := fun coordinate => (arguments () coordinate).2.1.isSome
  change decide ((List.ofFn flags).findIdx (! ·) = MvPolynomial.eval hostSizes coordinates) = true ↔ _
  rw [decide_eq_true_eq]
  have sentinel := firstFalse_sentinel coordinates hostSizes flags
  rw [firstFalse_correct] at sentinel
  exact sentinel

/-- Actual conversion flags express coordinate-image membership, including
empty generated images and singleton source algebras. -/
theorem convertedFlags_valid (coordinates generators : MvPolynomial Parameter ℕ)
    (hostSizes : Parameter → ℕ)
    (arguments : (convertAllCoordinates (L := L) (Carrier := Carrier) coordinates generators).Arguments hostSizes)
    (coordinate : Fin (MvPolynomial.eval hostSizes coordinates)) :
    (((convertAllCoordinates (L := L) (Carrier := Carrier) coordinates generators).compute hostSizes
      ⟨arguments, trivial⟩ coordinate).2.1).isSome = true ↔
      conversionTarget coordinates generators hostSizes arguments coordinate ∈
        images (L := L) (conversionGenerators coordinates generators hostSizes arguments) coordinate := by
  change (checkedQuotientBlock _ _).isSome = true ↔ _
  simp only [Option.isSome_iff_ne_none, ne_eq, checkedQuotientBlock_none, not_not]
  rfl

theorem prepare_accepted_iff (coordinates generators : MvPolynomial Parameter ℕ)
    (hostSizes : Parameter → ℕ)
    (arguments : (convertAllCoordinates (L := L) (Carrier := Carrier) coordinates generators).Arguments hostSizes) :
    (convertedAllAccepted (L := L) (Carrier := Carrier) coordinates generators).compute hostSizes
      ⟨(fun _ => (convertAllCoordinates (L := L) (Carrier := Carrier) coordinates generators).compute
        hostSizes ⟨arguments, trivial⟩), trivial⟩ = true ↔
      ∀ coordinate, conversionTarget coordinates generators hostSizes arguments coordinate ∈
        images (L := L) (conversionGenerators coordinates generators hostSizes arguments) coordinate := by
  rw [convertedAllAccepted_correct]
  exact forall_congr' (convertedFlags_valid coordinates generators hostSizes arguments)

/-- A failed sentinel test returns an actual rejected original coordinate,
rather than the all-accepted sentinel. -/
theorem convertedRejection_found (coordinates generators : MvPolynomial Parameter ℕ)
    (hostSizes : Parameter → ℕ)
    (arguments : (convertedFlags (L := L) (Carrier := Carrier) coordinates generators).Arguments hostSizes)
    (failed : (convertedAllAccepted (L := L) (Carrier := Carrier) coordinates generators).compute hostSizes
      ⟨arguments, trivial⟩ = false) :
    ∃ coordinate : Fin (MvPolynomial.eval hostSizes coordinates),
      ((convertedRejection (L := L) (Carrier := Carrier) coordinates generators).compute hostSizes
        ⟨arguments, trivial⟩).val = coordinate.val ∧ (arguments () coordinate).2.1 = none := by
  let selected := (convertedRejection (L := L) (Carrier := Carrier) coordinates generators).compute hostSizes
    ⟨arguments, trivial⟩
  have notFull : selected.val ≠ MvPolynomial.eval hostSizes coordinates := by
    intro equal
    have accepted : (convertedAllAccepted (L := L) (Carrier := Carrier) coordinates generators).compute
        hostSizes ⟨arguments, trivial⟩ = true := by
      change decide (selected.val = MvPolynomial.eval hostSizes coordinates) = true
      exact decide_eq_true equal
    rw [failed] at accepted
    cases accepted
  have before : selected.val < MvPolynomial.eval hostSizes coordinates := by
    have bound := selected.isLt
    omega
  let flags := fun coordinate => (arguments () coordinate).2.1.isSome
  have sourceValue : ((firstFalse coordinates).compute hostSizes ⟨(fun _ => flags), trivial⟩).toNat = selected.val := by
    rw [firstFalse_correct]
    rfl
  have found := firstFalse_found coordinates hostSizes flags (sourceValue.trans_lt before)
  have rejected : (arguments () ⟨selected.val, before⟩).2.1.isSome = false := by
    simpa only [sourceValue] using found
  refine ⟨⟨selected.val, before⟩, rfl, ?_⟩
  simpa only [Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] using rejected

/-- Mathematical correctness of the single public rejection/preparation output.
-/
noncomputable def OutcomeCorrect (coordinates generators : MvPolynomial Parameter ℕ)
    (hostSizes : Parameter → ℕ)
    (arguments : (convertAllCoordinates (L := L) (Carrier := Carrier) coordinates generators).Arguments hostSizes)
    (output : (variant 2 (preparationAlternatives (L := L) (Carrier := Carrier) coordinates generators)).Carrier hostSizes) : Prop :=
    let input := conversionGenerators (L := L) coordinates generators hostSizes arguments
    let target := conversionTarget coordinates generators hostSizes arguments
    (∃ coordinate : Fin (MvPolynomial.eval hostSizes coordinates),
      output = ⟨0, coordinate.castSucc⟩ ∧ target coordinate ∉ images (L := L) input coordinate ∧
        target ∉ Substructure.closure L (Set.range input)) ∨
    (∃ result : (atComputedSizeDomain (sizeBounds (L := L) (Carrier := Carrier) coordinates generators)
        (Multisorted.preparedDomain (enumeration (L := L) (Carrier := Carrier)))).Carrier hostSizes,
      output = ⟨1, result⟩ ∧
      computedSizeAssignment (sizeBounds (L := L) (Carrier := Carrier) coordinates generators) hostSizes result.1 = sizes (L := L) input ∧
      Multisorted.IsPrepared (L := L) (fun sort => catalogueMonolith L Carrier (entry sort))
        (graph (L := L) (Carrier := Carrier)) (Nat.card Carrier * Nat.card Carrier) result.2.1 result.2.2 ∧
      (Multisorted.IsMember (L := L) result.2.1 ↔ target ∈ Substructure.closure L (Set.range input)))

/-- Complete preparation either returns a genuine coordinate obstruction to the
original SMP instance, or an exact-size monolith-prepared equivalent instance. -/
theorem prepare_specification (coordinates generators : MvPolynomial Parameter ℕ)
    (hostSizes : Parameter → ℕ)
    (arguments : (convertAllCoordinates (L := L) (Carrier := Carrier) coordinates generators).Arguments hostSizes) :
    OutcomeCorrect coordinates generators hostSizes arguments
      ((prepare (L := L) (Carrier := Carrier) coordinates generators).compute hostSizes ⟨arguments, trivial⟩) := by
  let converted := (convertAllCoordinates (L := L) (Carrier := Carrier) coordinates generators).compute hostSizes ⟨arguments, trivial⟩
  let accepted : Bool := (convertedAllAccepted (L := L) (Carrier := Carrier) coordinates generators).compute
    hostSizes ⟨(fun _ => converted), trivial⟩
  cases selected : accepted with
  | false =>
    have failed : (convertedAllAccepted (L := L) (Carrier := Carrier) coordinates generators).compute
        hostSizes ⟨(fun _ => converted), trivial⟩ = false := selected
    obtain ⟨coordinate, same, rejected⟩ := convertedRejection_found coordinates generators hostSizes (fun _ => converted) failed
    left
    refine ⟨coordinate, ?_, ?_, ?_⟩
    · change (if accepted then _ else _) = _
      rw [selected]
      apply congrArg (fun index : Fin (MvPolynomial.eval hostSizes coordinates + 1) =>
        (⟨0, index⟩ : (variant 2 (preparationAlternatives (L := L) (Carrier := Carrier) coordinates generators)).Carrier hostSizes))
      exact Fin.ext same
    · exact (checkedQuotientBlock_none _ _).mp rejected
    · exact convertAllCoordinates_obstruction coordinates generators hostSizes arguments coordinate rejected
  | true =>
    have valid := (prepare_accepted_iff coordinates generators hostSizes arguments).mp selected
    let result := (prepareInput (L := L) (Carrier := Carrier) coordinates generators).compute hostSizes ⟨arguments, trivial⟩
    right
    refine ⟨result, ?_, prepareInput_sizes coordinates generators hostSizes arguments,
      (prepareInput_specification coordinates generators hostSizes arguments valid).1,
      (prepareInput_specification coordinates generators hostSizes arguments valid).2⟩
    change (if accepted then (⟨1, result⟩ :
      (variant 2 (preparationAlternatives (L := L) (Carrier := Carrier) coordinates generators)).Carrier hostSizes) else _) = _
    rw [selected]
    rfl

/-- One specialization-fixed TM0 program includes coordinate conversion,
rejection, runtime size preparation, and exact prepared output extraction. -/
theorem prepare_tm0 :
    (prepare (L := L) (Carrier := Carrier)
      (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℕ) (MvPolynomial.X 1)).TM0Realizable :=
  (prepare_realizable _ _).tm0

end Polytime2.SMP.Prepared
