import Polytime2.Complexity.CookLevin.BlockBase
import Polytime2.Arithmetic.SignedAddition
import Polytime2.Computation.Conditional

/-! # Final-layer source wire coordinates

A positive time allowance selects the last transition block and its final
wire. Zero time selects the initial one-hot bit directly. Arithmetic widths
and positivity guards are internal to the construction.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Complexity.CookLevin

open Circuit EncodedDomain Polytime2.Computation
open Polytime2.Computation.Realizable.Internal

variable {Symbol State : Type} [Inhabited Symbol] [Fintype Symbol] [Fintype State]

private noncomputable def lastTime : Computation Unit Empty where
  inputDomains := Empty.elim
  outputDomain := arrayPosition (MvPolynomial.X ())
  precondition sizes _ := 0 < sizes ()
  compute sizes arguments := ⟨sizes () - 1, by simpa using Nat.sub_lt arguments.property (by decide : 0 < 1)⟩

private theorem lastTime_realizable : lastTime.Realizable := by
  let width : MvPolynomial Unit ℕ := MvPolynomial.X () + 1
  let allowed := lastTime.precondition
  let one := (integerBooleanOperation (Parameter := Unit) (Argument := Empty) (fun _ => ⟨1, by decide⟩)).followedBy
    (integerWidenTo 1 (MvPolynomial.X ()) width (by dsimp [width]; ring)) rfl (by intros; trivial)
  have oneReady : one.Realizable :=
    (integerBooleanOperation_realizable (Parameter := Unit) (Argument := Empty) (fun _ => ⟨1, by decide⟩)).followedBy
      (integerWidenTo_realizable 1 (MvPolynomial.X ()) width (by dsimp [width]; ring)) rfl (by intros; trivial)
  let fixedOne := one.onResults (Empty.elim : Empty → EncodedDomain Unit) (fun _ _ => True)
    (fun empty => nomatch empty) (by intros; trivial)
  have fixedOneReady : fixedOne.Realizable := by
    apply oneReady.onResults
    intro empty
    exact nomatch empty
  let difference := (integerSubtract width).onResults Empty.elim allowed
    (fun choice sizes arguments => if choice then fixedOne.compute sizes ⟨arguments.val, trivial⟩
      else (polynomialIntegerSize (MvPolynomial.X ())).compute sizes ⟨arguments.val, trivial⟩)
    (by intros; trivial)
  have differenceReady : difference.Realizable := by
    apply (integerSubtract_realizable width).onResults
    intro choice
    cases choice
    · exact (polynomialIntegerSize_realizable (MvPolynomial.X ())).withPrecondition allowed (by intros; trivial)
    · exact fixedOneReady.withPrecondition allowed (by intros; trivial)
  have narrowed := differenceReady.followedBy
    (integerNarrowAtWidths_realizable (width + 1) width (by intro sizes; simp only [map_add]; omega)) rfl (by
      intro sizes arguments positive
      change ((MvPolynomial.eval sizes (MvPolynomial.X ()) : ℤ) - 1).natAbs <
        2 ^ MvPolynomial.eval sizes width
      rw [MvPolynomial.eval_X]
      have equality : (sizes () : ℤ) - 1 = ((sizes () - 1 : ℕ) : ℤ) := by
        change 0 < sizes () at positive
        omega
      rw [equality, Int.natAbs_natCast]
      dsimp only [width]
      simp only [map_add, map_one, MvPolynomial.eval_X]
      exact (Nat.sub_le _ _).trans_lt ((Nat.le_succ _).trans_lt Nat.lt_two_pow_self))
  have magnitude := narrowed.followedBy (integerMagnitude_realizable width) rfl (by intros; trivial)
  exact magnitude.withEncodedOutput lastTime.outputDomain lastTime.compute (by intros; rfl) (by
    intro sizes arguments
    apply congrArg CallingConvention.tape
    apply arrayPosition_binary_bits (MvPolynomial.X ()) sizes
    change ((MvPolynomial.eval sizes (MvPolynomial.X ()) : ℤ) - 1).natAbs = sizes () - 1
    rw [MvPolynomial.eval_X]
    have equality : (sizes () : ℤ) - 1 = ((sizes () - 1 : ℕ) : ℤ) := by
      have positive : 0 < sizes () := arguments.property
      omega
    rw [equality, Int.natAbs_natCast])

private noncomputable def finalBlockArguments (sizes : Unit → ℕ)
    (cell : Fin (MvPolynomial.eval sizes layoutPositions)) (positive : 0 < sizes ()) :
    ∀ name, (blockBaseInputs name).Carrier sizes :=
  fun name => match name with
    | false => lastTime.compute sizes ⟨(fun empty => nomatch empty), positive⟩
    | true => cell

private theorem finalBit_bounded (sizes : Unit → ℕ) (bit : Fin (cellWidth Symbol State)) :
    bit.val < MvPolynomial.eval sizes (layoutWires Symbol State) := by
  have positionsPositive : 1 ≤ MvPolynomial.eval sizes layoutPositions := by simp [layoutPositions]
  have scaled := Nat.mul_le_mul_right (cellWidth Symbol State) positionsPositive
  simp only [Nat.one_mul] at scaled
  have bitBound := bit.isLt
  simp only [layoutWires, layoutWidth, map_add, map_mul, MvPolynomial.eval_C]
  omega

/-- Wire carrying a selected cell bit after the full time allowance. -/
noncomputable def finalWire (bit : Fin (cellWidth Symbol State)) : Computation Unit Unit :=
  specification (fun _ => arrayPosition layoutPositions) (arrayPosition (layoutWires Symbol State))
    (fun _ _ => True) (fun sizes arguments =>
      if positive : 0 < sizes () then
        ⟨((blockBase bit).compute sizes ⟨finalBlockArguments sizes (arguments.val ()) positive, trivial⟩).val +
          (cellBlockSize Symbol State - 1), by
            have fits := blockBase_result_fits bit sizes (finalBlockArguments sizes (arguments.val ()) positive)
            have blockPositive := cellBlockSize_positive (Symbol := Symbol) (State := State)
            change ((blockBase bit).compute sizes
              ⟨finalBlockArguments sizes (arguments.val ()) positive, trivial⟩).val +
                (cellBlockSize Symbol State - 1) < MvPolynomial.eval sizes (layoutWires Symbol State)
            omega⟩
      else ⟨bit.val, finalBit_bounded sizes bit⟩)

/-- Final coordinates are exactly the output names of uniform unrolling. -/
theorem finalWire_correct (bit : Fin (cellWidth Symbol State)) (sizes : Unit → ℕ)
    (arguments : (finalWire bit).Arguments sizes) :
    ((finalWire bit).compute sizes ⟨arguments, trivial⟩).val =
      stepInputWire (MvPolynomial.eval sizes layoutPositions * cellWidth Symbol State)
        (cellBlockSize Symbol State) (sizes ()) (finProdFinEquiv (arguments (), bit)) := by
  cases time : sizes () with
  | zero =>
    have cellZero : (arguments ()).val = 0 := by
      have bounded : (arguments ()).val < MvPolynomial.eval sizes layoutPositions := (arguments ()).isLt
      simp only [layoutPositions, map_add, map_mul, map_ofNat, map_one, MvPolynomial.eval_X, time] at bounded
      omega
    simp [finalWire, specification_compute, time, stepInputWire, finProdFinEquiv, cellZero]
  | succ previous =>
    have positive : 0 < sizes () := by omega
    simp only [finalWire, specification_compute, dif_pos positive]
    simp only [blockBase_correct,
      finalBlockArguments, lastTime, MvPolynomial.eval_X, time, Nat.add_sub_cancel,
      stepInputWire, layoutLayerGates, layoutWidth, map_mul, MvPolynomial.eval_C,
      finProdFinEquiv, Equiv.coe_fn_mk]
    rw [← Nat.add_sub_assoc (Nat.succ_le_of_lt (cellBlockSize_positive (Symbol := Symbol) (State := State)))]
    congr 1
    ring

theorem finalWire_realizable (bit : Fin (cellWidth Symbol State)) : (finalWire bit).Realizable := by
  let computation := finalWire bit
  let inputs : Unit → EncodedDomain Unit := fun _ => arrayPosition layoutPositions
  let condition := fun (sizes : Unit → ℕ) (_ : computation.Arguments sizes) => decide (sizes () = 0)
  apply Realizable.ofCases condition
  · have tested := (polynomialIntegerSize_realizable (MvPolynomial.X ())).followedBy
      (integerIsZero_realizable (MvPolynomial.X () + 1)) rfl (by intros; trivial)
    have prepared := tested.onResults inputs (fun _ _ => True) (fun empty => nomatch empty)
      (by intros; trivial) (fun empty => nomatch empty)
    exact prepared.withSpecification computation.precondition (fun sizes arguments => condition sizes arguments.val)
      (by intros; trivial) (by intro sizes arguments accepted; simp [condition, onResults, followedBy,
        polynomialIntegerSize, integerIsZero, unaryMap])
  · let allowed := fun sizes (arguments : ∀ name, (inputs name).Carrier sizes) =>
      computation.precondition sizes arguments ∧ condition sizes arguments = true
    have constant := (positionPolynomial_realizable (MvPolynomial.C bit.val) (layoutWires Symbol State)).onResults
      inputs allowed (fun empty => nomatch empty) (by
        intro sizes arguments
        change MvPolynomial.eval sizes (MvPolynomial.C bit.val) < _
        simpa only [MvPolynomial.eval_C] using finalBit_bounded sizes bit) (fun empty => nomatch empty)
    apply constant.withSpecification _ _ (by intros; assumption)
    intro sizes arguments accepted
    have zero : sizes () = 0 := by simpa [condition] using accepted.2
    apply Fin.ext
    simp [computation, finalWire, specification_compute, zero, onResults, positionPolynomial]
  · let allowed := fun sizes (arguments : ∀ name, (inputs name).Carrier sizes) =>
      computation.precondition sizes arguments ∧ condition sizes arguments = false
    have positive : ∀ sizes (arguments : {arguments // allowed sizes arguments}), 0 < sizes () := by
      intro sizes arguments
      have nonzero : sizes () ≠ 0 := by simpa [condition] using arguments.property.2
      omega
    let base := (blockBase bit).onResults inputs allowed
      (fun name sizes arguments => finalBlockArguments sizes (arguments.val ()) (positive sizes arguments) name)
      (by intros; trivial)
    have baseReady : base.Realizable := by
      apply (blockBase_realizable bit).onResults
      intro name
      cases name
      · exact lastTime_realizable.onResults inputs allowed (fun empty => nomatch empty)
          (by intro sizes arguments; exact positive sizes arguments) (fun empty => nomatch empty)
      · exact Realizable.argument inputs () allowed
    have shifted := (wireShift_realizable (layoutWires Symbol State) (cellBlockSize Symbol State - 1)).onResults
      inputs allowed (fun _ sizes arguments => base.compute sizes arguments) (by
        intro sizes arguments
        have fits := blockBase_result_fits bit sizes
          (finalBlockArguments sizes (arguments.val ()) (positive sizes arguments))
        have blockPositive := cellBlockSize_positive (Symbol := Symbol) (State := State)
        change ((blockBase bit).compute sizes
          ⟨finalBlockArguments sizes (arguments.val ()) (positive sizes arguments), trivial⟩).val +
            (cellBlockSize Symbol State - 1) < MvPolynomial.eval sizes (layoutWires Symbol State)
        omega) (fun _ => baseReady)
    apply shifted.withSpecification _ _ (by intros; assumption)
    intro sizes arguments accepted
    have nonzero : 0 < sizes () := positive sizes ⟨arguments, accepted⟩
    apply Fin.ext
    simp [computation, finalWire, specification_compute, nonzero, onResults, base, wireShift, unaryMap]

end Polytime2.Complexity.CookLevin
