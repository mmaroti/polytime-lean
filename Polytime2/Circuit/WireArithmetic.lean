import Polytime2.Circuit.Construction
import Polytime2.Arithmetic.NaturalArithmetic
import Polytime2.Arrays.PositionArithmetic

/-! # Certified wire-coordinate arithmetic

Gate templates refer to a fresh base wire plus a bounded offset. Addition is
performed using the existing unsigned adder at the coordinate codec's derived
width. The sole public condition is that the mathematical result is a valid
wire coordinate; no binary overflow condition is exposed.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Circuit

open EncodedDomain Polytime2.Computation
open Polytime2.Computation.Realizable.Internal

variable {Parameter : Type} [Fintype Parameter]

/-- Add two wire coordinates whenever their sum is still a wire. -/
noncomputable def wireAdd (wires : MvPolynomial Parameter ℕ) : Computation Parameter Bool where
  inputDomains _ := arrayPosition wires
  outputDomain := arrayPosition wires
  precondition sizes arguments := (arguments false).val + (arguments true).val < MvPolynomial.eval sizes wires
  compute _ arguments := ⟨(arguments.val false).val + (arguments.val true).val, arguments.property⟩

theorem wireAdd_realizable (wires : MvPolynomial Parameter ℕ) : (wireAdd wires).Realizable := by
  let computation := wireAdd wires
  have raw := (naturalAdd_realizable (wires + 1)).reinterpretInputs computation.inputDomains
    (fun _ sizes coordinate => ⟨coordinate.val, by
      simp only [map_add, map_one]
      exact coordinate.isLt.trans_le ((Nat.le_succ _).trans Nat.lt_two_pow_self.le)⟩)
    (by intros; rfl)
    (by
      intro name sizes coordinate
      exact arrayPosition_binary_bits wires sizes coordinate _ rfl)
    computation.precondition (by
      intro sizes arguments fits
      change (arguments false).val + (arguments true).val < 2 ^ MvPolynomial.eval sizes (wires + 1)
      simp only [map_add, map_one]
      exact fits.trans_le ((Nat.le_succ _).trans Nat.lt_two_pow_self.le))
  exact raw.withEncodedOutput (arrayPosition wires) computation.compute (by intros; rfl) (by
    intro sizes arguments
    apply congrArg CallingConvention.tape
    apply arrayPosition_binary_bits wires sizes
    rfl)

/-- Advance to the next mathematical wire coordinate. -/
noncomputable def wireSuccessor (wires : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  unaryMap (arrayPosition wires) (arrayPosition wires)
    (fun sizes coordinate => coordinate.val + 1 < MvPolynomial.eval sizes wires)
    (fun _ coordinate => ⟨coordinate.val.val + 1, coordinate.property⟩)

/-- Add a specialization-fixed template offset to a runtime base wire. -/
noncomputable def wireShift (wires : MvPolynomial Parameter ℕ) (offset : ℕ) : Computation Parameter Unit :=
  unaryMap (arrayPosition wires) (arrayPosition wires)
    (fun sizes coordinate => coordinate.val + offset < MvPolynomial.eval sizes wires)
    (fun _ coordinate => ⟨coordinate.val.val + offset, coordinate.property⟩)

/-- Read a polynomial mathematical size as a wire coordinate. Working word
widths are derived internally; admissibility is precisely the coordinate bound. -/
noncomputable def wirePolynomial (value wires : MvPolynomial Parameter ℕ) : Computation Parameter Empty where
  inputDomains := Empty.elim
  outputDomain := arrayPosition wires
  precondition sizes _ := MvPolynomial.eval sizes value < MvPolynomial.eval sizes wires
  compute sizes arguments := ⟨MvPolynomial.eval sizes value, arguments.property⟩

theorem wirePolynomial_realizable (value wires : MvPolynomial Parameter ℕ) :
    (wirePolynomial value wires).Realizable := by
  have widened := (polynomialIntegerSize_realizable value).followedBy
    (integerWiden_realizable (value + 1) (wires + 1)) rfl (by intros; trivial)
  have allowed := widened.withPrecondition (wirePolynomial value wires).precondition (by intros; trivial)
  have narrowed := allowed.followedBy
    (integerNarrowAtWidths_realizable ((value + 1) + (wires + 1)) (wires + 1)
      (by intro sizes; simp only [map_add]; omega)) rfl (by
        intro sizes arguments allowed
        change (MvPolynomial.eval sizes value : ℤ).natAbs < 2 ^ MvPolynomial.eval sizes (wires + 1)
        simp only [Int.natAbs_natCast, map_add, map_one]
        exact allowed.trans_le ((Nat.le_succ _).trans Nat.lt_two_pow_self.le))
  have magnitude := narrowed.followedBy (integerMagnitude_realizable (wires + 1)) rfl (by intros; trivial)
  exact magnitude.withEncodedOutput (arrayPosition wires) (wirePolynomial value wires).compute
    (by intros; rfl) (by
      intro sizes arguments
      apply congrArg CallingConvention.tape
      apply arrayPosition_binary_bits wires sizes
      rfl)

/-- Affine wire addressing with a specialization-fixed stride and a
polynomial base. Admissibility is precisely the mathematical result bound. -/
noncomputable def wireAffine (wires base : MvPolynomial Parameter ℕ) (stride : ℕ) : Computation Parameter Unit :=
  unaryMap (arrayPosition wires) (arrayPosition wires)
    (fun sizes coordinate => MvPolynomial.eval sizes base + stride * coordinate.val < MvPolynomial.eval sizes wires)
    (fun sizes coordinate => ⟨MvPolynomial.eval sizes base + stride * coordinate.val.val, coordinate.property⟩)

theorem wireAffine_value (wires base : MvPolynomial Parameter ℕ) (stride : ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (wireAffine wires base stride).Arguments sizes //
      (wireAffine wires base stride).precondition sizes arguments}) :
    ((wireAffine wires base stride).compute sizes arguments).val =
      MvPolynomial.eval sizes base + stride * (arguments.val ()).val := rfl

theorem wireAffine_realizable (wires base : MvPolynomial Parameter ℕ) (stride : ℕ) :
    (wireAffine wires base stride).Realizable := by
  induction stride with
  | zero =>
    have constant := (wirePolynomial_realizable base wires).onResults
      (wireAffine wires base 0).inputDomains (wireAffine wires base 0).precondition
      (fun empty => nomatch empty) (by
        intro sizes arguments
        change MvPolynomial.eval sizes base < MvPolynomial.eval sizes wires
        simpa only [wireAffine, unaryMap, Nat.zero_mul, Nat.add_zero] using arguments.property)
      (fun empty => nomatch empty)
    exact constant.withSpecification _ _ (by intros; assumption) (by intros; apply Fin.ext; simp [onResults, wirePolynomial, wireAffine, unaryMap])
  | succ stride induction =>
    let computation := wireAffine wires base (stride + 1)
    let previous := (wireAffine wires base stride).withPrecondition computation.precondition (by
      intro sizes arguments fits
      change MvPolynomial.eval sizes base + stride * (arguments ()).val < MvPolynomial.eval sizes wires
      have bound : MvPolynomial.eval sizes base + (stride + 1) * (arguments ()).val <
          MvPolynomial.eval sizes wires := fits
      rw [Nat.succ_mul] at bound
      omega)
    have previousReady : previous.Realizable := induction.withPrecondition _ _
    have added := (wireAdd_realizable wires).onResults computation.inputDomains computation.precondition
      (fun choice sizes arguments => if choice then arguments.val () else previous.compute sizes arguments) (by
        intro sizes arguments
        change MvPolynomial.eval sizes base + stride * (arguments.val ()).val + (arguments.val ()).val <
          MvPolynomial.eval sizes wires
        have bound : MvPolynomial.eval sizes base + (stride + 1) * (arguments.val ()).val <
            MvPolynomial.eval sizes wires := arguments.property
        rwa [Nat.succ_mul, ← Nat.add_assoc] at bound) (by
        intro choice
        cases choice
        · exact previousReady
        · exact Realizable.argument computation.inputDomains () computation.precondition)
    exact added.withSpecification computation.precondition computation.compute (by intros; assumption) (by
      intros
      apply Fin.ext
      simp [computation, onResults, wireAdd, previous, withPrecondition, wireAffine, unaryMap, Nat.succ_mul, Nat.add_assoc])

theorem wireSuccessor_realizable (wires : MvPolynomial Parameter ℕ) : (wireSuccessor wires).Realizable := by
  apply (wireAffine_realizable wires 1 1).withSpecification (wireSuccessor wires).precondition
    (wireSuccessor wires).compute (by
      intro sizes arguments allowed
      simpa only [wireAffine, wireSuccessor, unaryMap, map_one, Nat.one_mul, Nat.add_comm] using allowed)
  intros
  apply Fin.ext
  simp [wireAffine, wireSuccessor, unaryMap, Nat.add_comm]

theorem wireShift_realizable (wires : MvPolynomial Parameter ℕ) (offset : ℕ) :
    (wireShift wires offset).Realizable := by
  apply (wireAffine_realizable wires (MvPolynomial.C offset) 1).withSpecification (wireShift wires offset).precondition
    (wireShift wires offset).compute (by
      intro sizes arguments allowed
      simpa only [wireAffine, wireShift, unaryMap, MvPolynomial.eval_C, Nat.one_mul, Nat.add_comm] using allowed)
  intros
  apply Fin.ext
  simp [wireAffine, wireShift, unaryMap, Nat.add_comm]

/-- Multiply coordinates when their product names an existing wire. -/
noncomputable def wireMultiply (wires : MvPolynomial Parameter ℕ) : Computation Parameter Bool where
  inputDomains _ := arrayPosition wires
  outputDomain := arrayPosition wires
  precondition sizes arguments := (arguments false).val * (arguments true).val < MvPolynomial.eval sizes wires
  compute _ arguments := ⟨(arguments.val false).val * (arguments.val true).val, arguments.property⟩

theorem wireMultiply_realizable (wires : MvPolynomial Parameter ℕ) : (wireMultiply wires).Realizable := by
  let computation := wireMultiply wires
  have raw := (naturalMultiplyAtWidths_realizable (wires + 1) (wires + 1)).reinterpretInputs computation.inputDomains
    (fun name sizes coordinate => by
      cases name <;> exact ⟨coordinate.val,
        coordinate.isLt.trans_le (by simp only [ite_self, map_add, map_one]; exact (Nat.le_succ _).trans Nat.lt_two_pow_self.le)⟩)
    (by intro name sizes; cases name <;> rfl)
    (by intro name sizes coordinate; cases name <;> exact arrayPosition_binary_bits wires sizes coordinate _ rfl)
    computation.precondition (by
      intro sizes arguments fits
      change (arguments false).val * (arguments true).val < 2 ^ MvPolynomial.eval sizes (wires + 1)
      simp only [map_add, map_one]
      exact fits.trans_le ((Nat.le_succ _).trans Nat.lt_two_pow_self.le))
  exact raw.withEncodedOutput (arrayPosition wires) computation.compute (by intros; rfl) (by
    intro sizes arguments
    apply congrArg CallingConvention.tape
    apply arrayPosition_binary_bits wires sizes
    rfl)

/-- Subtract an earlier coordinate, with its ordinary mathematical ordering
condition. This supplies predecessor offsets after the zero case is handled. -/
noncomputable def wireSubtract (wires : MvPolynomial Parameter ℕ) : Computation Parameter Bool where
  inputDomains _ := arrayPosition wires
  outputDomain := arrayPosition wires
  precondition _ arguments := (arguments true).val ≤ (arguments false).val
  compute _ arguments := ⟨(arguments.val false).val - (arguments.val true).val,
    (Nat.sub_le _ _).trans_lt (arguments.val false).isLt⟩

theorem wireSubtract_realizable (wires : MvPolynomial Parameter ℕ) : (wireSubtract wires).Realizable := by
  let computation := wireSubtract wires
  have raw := (naturalSubtract_realizable (wires + 1)).reinterpretInputs computation.inputDomains
    (fun _ sizes coordinate => ⟨coordinate.val, by
      simp only [map_add, map_one]
      exact coordinate.isLt.trans_le ((Nat.le_succ _).trans Nat.lt_two_pow_self.le)⟩)
    (by intros; rfl)
    (by intro name sizes coordinate; exact arrayPosition_binary_bits wires sizes coordinate _ rfl)
    computation.precondition (by intros; assumption)
  exact raw.withEncodedOutput (arrayPosition wires) computation.compute (by intros; rfl) (by
    intro sizes arguments
    apply congrArg CallingConvention.tape
    apply arrayPosition_binary_bits wires sizes
    rfl)

/-- Regard an ordinary coordinate in a smaller mathematical interval as a
wire coordinate. Temporary word widths remain private. -/
noncomputable def wireOfPosition (length wires : MvPolynomial Parameter ℕ)
    (bounded : ∀ sizes, MvPolynomial.eval sizes length ≤ MvPolynomial.eval sizes wires) :
    Computation Parameter Unit :=
  unaryMap (arrayPosition length) (arrayPosition wires) (fun _ _ => True)
    (fun sizes coordinate => ⟨coordinate.val.val, coordinate.val.isLt.trans_le (bounded sizes)⟩)

/-- Observe a coordinate coercion without reducing its source and target
polynomials while comparing the two finite carrier types. -/
theorem wireOfPosition_value (length wires : MvPolynomial Parameter ℕ)
    (bounded : ∀ sizes, MvPolynomial.eval sizes length ≤ MvPolynomial.eval sizes wires)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (wireOfPosition length wires bounded).Arguments sizes // True}) :
    ((wireOfPosition length wires bounded).compute sizes arguments).val = (arguments.val ()).val := rfl

/-- Change a coordinate bound when the mathematical value fits the target.
The target interval may be smaller than the source interval. -/
noncomputable def wireCast (length wires : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  unaryMap (arrayPosition length) (arrayPosition wires)
    (fun sizes coordinate => coordinate.val < MvPolynomial.eval sizes wires)
    (fun _ coordinate => ⟨coordinate.val.val, coordinate.property⟩)

theorem wireCast_value (length wires : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (wireCast length wires).Arguments sizes //
      (wireCast length wires).precondition sizes arguments}) :
    ((wireCast length wires).compute sizes arguments).val = (arguments.val ()).val := rfl

theorem wireCast_realizable (length wires : MvPolynomial Parameter ℕ) :
    (wireCast length wires).Realizable := by
  have extended := positionInteger_realizable length (wires + 1) ((length + 1) + (wires + 1)) rfl
  have permitted := extended.withPrecondition (wireCast length wires).precondition (by intros; trivial)
  have narrowed := permitted.followedBy
    (integerNarrowAtWidths_realizable ((length + 1) + (wires + 1)) (wires + 1)
      (by intro sizes; simp only [map_add]; omega)) rfl (by
        intro sizes arguments allowed
        change ((arguments ()).val : ℤ).natAbs < 2 ^ MvPolynomial.eval sizes (wires + 1)
        simp only [Int.natAbs_natCast, map_add, map_one]
        exact allowed.trans_le
          ((Nat.le_succ _).trans Nat.lt_two_pow_self.le))
  have magnitude := narrowed.followedBy (integerMagnitude_realizable (wires + 1)) rfl (by intros; trivial)
  exact magnitude.withEncodedOutput (arrayPosition wires) (wireCast length wires).compute
    (by intros; rfl) (by
      intro sizes arguments
      apply congrArg CallingConvention.tape
      apply arrayPosition_binary_bits wires sizes
      rfl)


theorem wireOfPosition_realizable (length wires : MvPolynomial Parameter ℕ)
    (bounded : ∀ sizes, MvPolynomial.eval sizes length ≤ MvPolynomial.eval sizes wires) :
    (wireOfPosition length wires bounded).Realizable := by
  exact (wireCast_realizable length wires).withSpecification (fun _ _ => True)
    (wireOfPosition length wires bounded).compute
    (by intro sizes arguments _; exact (arguments ()).isLt.trans_le (bounded sizes))
    (by intros; rfl)

/-- Coordinate of a gate after the input wires and earlier gates. -/
noncomputable def gateOutputWire (inputs count : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  unaryMap (arrayPosition count) (arrayPosition (inputs + count)) (fun _ _ => True)
    (fun sizes position => ⟨MvPolynomial.eval sizes inputs + position.val.val, by
      have bounded : position.val.val < MvPolynomial.eval sizes count := position.val.isLt
      simp only [map_add]
      omega⟩)

theorem gateOutputWire_realizable (inputs count : MvPolynomial Parameter ℕ) : (gateOutputWire inputs count).Realizable := by
  have widened := wireOfPosition_realizable count (inputs + count) (by intro sizes; simp only [map_add]; omega)
  have added := widened.followedBy (wireAffine_realizable (inputs + count) inputs 1) rfl (by
    intro sizes arguments accepted
    change MvPolynomial.eval sizes inputs + 1 *
      ((wireOfPosition count (inputs + count) (by intro assignment; simp only [map_add]; omega)).compute sizes
        ⟨arguments, accepted⟩).val < _
    rw [wireOfPosition_value]
    have bounded : (arguments ()).val < MvPolynomial.eval sizes count := (arguments ()).isLt
    simp only [one_mul, map_add]
    omega)
  apply added.withSpecification (fun _ _ => True) (gateOutputWire inputs count).compute (by intros; trivial)
  intro sizes arguments accepted
  apply Fin.ext
  simp only [followedBy, wireAffine_value, wireOfPosition_value, one_mul, gateOutputWire, unaryMap]

end Polytime2.Circuit
