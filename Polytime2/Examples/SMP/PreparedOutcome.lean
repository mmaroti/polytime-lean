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
import Polytime2.Computation.Sums

/-! # Preparation returns an explicit obstruction or an exact prepared input -/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.SMP.Prepared

open FirstOrder FirstOrder.Language CoordinateReduction
open Polytime2.Computation EncodedDomain

variable {L : Language.{0, 0}} [L.IsAlgebraic] {Carrier Parameter : Type}
variable [L.Structure Carrier] [Finite Carrier] [Fintype Parameter]

/-- Acceptance flags are ordinary Boolean arrays over the original coordinates.
-/
private noncomputable def convertedFlags (coordinates generators : MvPolynomial Parameter ℕ) :
    Computation Parameter Unit where
  inputDomains _ := (convertAllCoordinates (L := L) (Carrier := Carrier) coordinates generators).outputDomain
  outputDomain := booleans.arrayOfLength coordinates
  precondition _ _ := True
  compute _ arguments := fun coordinate => (arguments.val () coordinate).2.1.isSome

private theorem convertedFlags_realizable (coordinates generators : MvPolynomial Parameter ℕ) :
    (convertedFlags (L := L) (Carrier := Carrier) coordinates generators).Realizable := by
  apply (conversionAcceptance_realizable (L := L) (Carrier := Carrier) coordinates generators).reinterpretOutput
    (booleans.arrayOfLength coordinates) (fun _ value => value)
  · intro sizes
    simp [conversionAcceptance, booleans, width, arrayOfLength, mapArray]
  · intro sizes value
    simp only [conversionAcceptance, mapArray, arrayOfLength_encode_bits,
      ArrayEncoding.bits_encode, constant_encode_bits, booleans, fixed_encode_bits]

private noncomputable def convertedRejection (coordinates generators : MvPolynomial Parameter ℕ) :
    Computation Parameter Unit :=
  (convertedFlags (L := L) (Carrier := Carrier) coordinates generators).followedBy
    (leadingUnarySize coordinates) rfl (by intros; trivial)

private theorem convertedRejection_realizable (coordinates generators : MvPolynomial Parameter ℕ) :
    (convertedRejection (L := L) (Carrier := Carrier) coordinates generators).Realizable :=
  (convertedFlags_realizable coordinates generators).followedBy (leadingUnarySize_realizable coordinates)
    rfl (by intros; trivial)

private noncomputable def convertedAllAccepted (coordinates generators : MvPolynomial Parameter ℕ) :
    Computation Parameter Unit :=
  (convertedRejection (L := L) (Carrier := Carrier) coordinates generators).followedBy
    (boundedUnaryIsFull coordinates) rfl (by intros; trivial)

private theorem convertedAllAccepted_realizable (coordinates generators : MvPolynomial Parameter ℕ) :
    (convertedAllAccepted (L := L) (Carrier := Carrier) coordinates generators).Realizable :=
  (convertedRejection_realizable coordinates generators).followedBy (boundedUnaryIsFull_realizable coordinates)
    rfl (by intros; trivial)

/-- The sentinel test accepts exactly when every coordinate flag is true. -/
private theorem convertedAllAccepted_correct (coordinates generators : MvPolynomial Parameter ℕ)
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
private theorem convertedFlags_valid (coordinates generators : MvPolynomial Parameter ℕ)
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

private theorem prepare_accepted_iff (coordinates generators : MvPolynomial Parameter ℕ)
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
private theorem convertedRejection_found (coordinates generators : MvPolynomial Parameter ℕ)
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

/-- An obstruction is a genuine original coordinate. Unary digits agree with
the internal search result, but the all-accepted sentinel is not a value. -/
noncomputable def preparationDomain (coordinates generators : MvPolynomial Parameter ℕ) : EncodedDomain Parameter :=
  (unaryIndex coordinates).sum
    (atComputedSizeDomain (sizeBounds (L := L) (Carrier := Carrier) coordinates generators)
      (Multisorted.preparedDomain (enumeration (L := L) (Carrier := Carrier))))

private theorem rejection_lt (coordinates generators : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : (convertedFlags (L := L) (Carrier := Carrier) coordinates generators).Arguments sizes)
    (failed : (convertedAllAccepted (L := L) (Carrier := Carrier) coordinates generators).compute sizes
      ⟨arguments, trivial⟩ ≠ true) :
    ((convertedRejection (L := L) (Carrier := Carrier) coordinates generators).compute sizes
      ⟨arguments, trivial⟩).val < MvPolynomial.eval sizes coordinates := by
  have rejected : (convertedAllAccepted (L := L) (Carrier := Carrier) coordinates generators).compute sizes
      ⟨arguments, trivial⟩ = false := Bool.eq_false_iff.mpr failed
  obtain ⟨coordinate, equal, _⟩ := convertedRejection_found coordinates generators sizes arguments rejected
  exact equal.trans_lt coordinate.isLt

/-- Preparation returns an actual rejected coordinate or exact prepared data. -/
noncomputable def prepareConvertedOutcome (coordinates generators : MvPolynomial Parameter ℕ) :
    Computation Parameter Unit := by
  classical
  exact {
    inputDomains _ := (convertAllCoordinates (L := L) (Carrier := Carrier) coordinates generators).outputDomain
    outputDomain := preparationDomain (L := L) (Carrier := Carrier) coordinates generators
    precondition _ _ := True
    compute sizes arguments :=
      if accepted : (convertedAllAccepted (L := L) (Carrier := Carrier) coordinates generators).compute sizes
          ⟨arguments.val, trivial⟩ = true then
        Sum.inr ((prepareConverted (L := L) (Carrier := Carrier) coordinates generators).compute sizes ⟨arguments.val, trivial⟩)
      else Sum.inl ⟨((convertedRejection (L := L) (Carrier := Carrier) coordinates generators).compute sizes
        ⟨arguments.val, trivial⟩).val, rejection_lt coordinates generators sizes arguments.val accepted⟩ }

theorem prepareConvertedOutcome_realizable (coordinates generators : MvPolynomial Parameter ℕ) :
    (prepareConvertedOutcome (L := L) (Carrier := Carrier) coordinates generators).Realizable := by
  let computation := prepareConvertedOutcome (L := L) (Carrier := Carrier) coordinates generators
  let frame := atComputedSizeDomain (sizeBounds (L := L) (Carrier := Carrier) coordinates generators)
    (Multisorted.preparedDomain (enumeration (L := L) (Carrier := Carrier)))
  let accepted := fun sizes (arguments : computation.Arguments sizes) =>
    (convertedAllAccepted (L := L) (Carrier := Carrier) coordinates generators).compute sizes ⟨arguments, trivial⟩
  apply Realizable.byCases computation accepted (convertedAllAccepted_realizable coordinates generators)
  · have ready := (prepareConverted_realizable (L := L) (Carrier := Carrier) coordinates generators).followedBy
      (sumInr_realizable (unaryIndex coordinates) frame) rfl (by intros; trivial)
    exact ready.withSpecification _ _ (by intros; trivial) (by
      intro sizes arguments valid
      dsimp only [computation, prepareConvertedOutcome]
      rw [dite_eq_left valid.2]
      rfl)
  · let rejected := (convertedRejection (L := L) (Carrier := Carrier) coordinates generators).withPrecondition
      (fun sizes arguments => True ∧ accepted sizes arguments = false) (by intros; trivial)
    have bounded := ((convertedRejection_realizable (L := L) (Carrier := Carrier) coordinates generators).withPrecondition
      rejected.precondition (by intros; trivial)).refineOutput
      (fun sizes value => value.val < MvPolynomial.eval sizes coordinates) (by
        intro sizes arguments
        exact rejection_lt coordinates generators sizes arguments.val
          (by simp [accepted, arguments.property.2]))
    have found := bounded.reinterpretOutput (unaryIndex coordinates)
      (fun _ value => ⟨value.val.val, value.property⟩)
      (by intros; rfl) (by intros; rfl)
    have ready := found.followedBy (sumInl_realizable (unaryIndex coordinates) frame) rfl (by intros; trivial)
    exact ready.withSpecification _ _ (by intro sizes arguments valid; exact valid) (by
      intro sizes arguments valid
      dsimp only [computation, prepareConvertedOutcome]
      rw [dite_eq_right (by simp [accepted, valid.2])]
      rfl)

/-- The public preparation computation handles both coordinate rejection and
exact-size preparation, with only the original size parameters. -/
noncomputable def prepare (coordinates generators : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  (convertAllCoordinates (L := L) (Carrier := Carrier) coordinates generators).followedBy
    (prepareConvertedOutcome coordinates generators) rfl (by intros; trivial)

theorem prepare_realizable (coordinates generators : MvPolynomial Parameter ℕ) :
    (prepare (L := L) (Carrier := Carrier) coordinates generators).Realizable :=
  (convertAllCoordinates_realizable coordinates generators).followedBy
    (prepareConvertedOutcome_realizable coordinates generators) rfl (by intros; trivial)

/-- Mathematical correctness of the single public rejection/preparation output.
-/
noncomputable def OutcomeCorrect (coordinates generators : MvPolynomial Parameter ℕ)
    (hostSizes : Parameter → ℕ)
    (arguments : (convertAllCoordinates (L := L) (Carrier := Carrier) coordinates generators).Arguments hostSizes)
    (output : (preparationDomain (L := L) (Carrier := Carrier) coordinates generators).Carrier hostSizes) : Prop :=
    let input := conversionGenerators (L := L) coordinates generators hostSizes arguments
    let target := conversionTarget coordinates generators hostSizes arguments
    (∃ coordinate : Fin (MvPolynomial.eval hostSizes coordinates),
      output = Sum.inl coordinate ∧ target coordinate ∉ images (L := L) input coordinate ∧
        target ∉ Substructure.closure L (Set.range input)) ∨
    (∃ result : (atComputedSizeDomain (sizeBounds (L := L) (Carrier := Carrier) coordinates generators)
        (Multisorted.preparedDomain (enumeration (L := L) (Carrier := Carrier)))).Carrier hostSizes,
      output = Sum.inr result ∧
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
    · dsimp only [prepare, followedBy, prepareConvertedOutcome]
      rw [dite_eq_right (show accepted ≠ true by simp [selected])]
      apply congrArg Sum.inl
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
    dsimp only [prepare, followedBy, prepareConvertedOutcome]
    rw [dite_eq_left selected]
    rfl

/-- One specialization-fixed TM0 program includes coordinate conversion,
rejection, runtime size preparation, and exact prepared output extraction. -/
theorem prepare_tm0 :
    (prepare (L := L) (Carrier := Carrier)
      (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℕ) (MvPolynomial.X 1)).TM0Realizable :=
  (prepare_realizable _ _).tm0

end Polytime2.SMP.Prepared
