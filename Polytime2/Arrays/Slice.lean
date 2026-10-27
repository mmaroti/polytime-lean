import Polytime2.Arrays.PackingResult
import Polytime2.Arrays.PositionArithmetic
import Polytime2.Arrays.Tabulate

/-! # Exact finite-array slices

Endpoints are ordinary coordinates in `Fin (length + 1)`, so empty slices and
an endpoint at the array's end are admissible. The result contains exactly the
selected interval. Reversed endpoints give an empty slice. Stable packing owns
all storage and traversal details.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.ArrayPacking

/-- Select a half-open interval of source coordinates. -/
def intervalFlags {length : ℕ} (lower upper : ℕ) (index : Fin length) : Bool :=
  decide (lower ≤ index.val ∧ index.val < upper)

private def intervalOrderIso {length : ℕ} (lower upper : Fin (length + 1)) :
    Fin (upper.val - lower.val) ≃o {index : Fin length // intervalFlags (length := length) lower.val upper.val index = true} where
  toFun index := ⟨⟨lower.val + index.val, by have := upper.isLt; omega⟩, by
    simp only [intervalFlags, decide_eq_true_eq]
    have := index.isLt
    constructor <;> omega⟩
  invFun index := ⟨index.val.val - lower.val, by
    have active := of_decide_eq_true index.property
    change lower.val ≤ index.val.val ∧ index.val.val < upper.val at active
    omega⟩
  left_inv := by intro index; apply Fin.ext; dsimp; omega
  right_inv := by
    intro index
    apply Subtype.ext
    apply Fin.ext
    have active := of_decide_eq_true index.property
    change lower.val ≤ index.val.val ∧ index.val.val < upper.val at active
    dsimp
    omega
  map_rel_iff' := by intros; change lower.val + _ ≤ lower.val + _ ↔ _ ≤ _; omega

theorem interval_count {length : ℕ} (lower upper : Fin (length + 1)) :
    count (intervalFlags (length := length) lower.val upper.val) = upper.val - lower.val := by
  simpa only [Nat.card_fin] using Nat.card_congr
    ((selection (intervalFlags (length := length) lower.val upper.val)).trans (intervalOrderIso lower upper).symm).toEquiv

theorem interval_selection {length : ℕ} (lower upper : Fin (length + 1))
    (index : Fin (count (intervalFlags (length := length) lower.val upper.val))) :
    (selection (intervalFlags (length := length) lower.val upper.val) index).val.val = lower.val + index.val := by
  have coordinate := Fin.coe_orderIso_apply
    ((selection (intervalFlags (length := length) lower.val upper.val)).trans (intervalOrderIso lower upper).symm) index
  change (selection (intervalFlags (length := length) lower.val upper.val) index).val.val - lower.val = index.val at coordinate
  have active := of_decide_eq_true (selection_active (intervalFlags (length := length) lower.val upper.val) index)
  change lower.val ≤ (selection (intervalFlags (length := length) lower.val upper.val) index).val.val ∧ _ at active
  omega

/-- Stable interval selection is exactly ordinary list drop followed by take. -/
theorem interval_pack {Element : Type*} {length : ℕ} (lower upper : Fin (length + 1))
    (values : Fin length → Element) :
    List.ofFn (pack (intervalFlags (length := length) lower.val upper.val) values) =
      ((List.ofFn values).drop lower.val).take (upper.val - lower.val) := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_take, List.length_drop, interval_count]
    have := upper.isLt
    omega
  · intro index packedBound sliceBound
    simp only [List.getElem_ofFn, List.getElem_take, List.getElem_drop]
    apply congrArg values
    apply Fin.ext
    exact interval_selection lower upper ⟨index, by simpa only [List.length_ofFn] using packedBound⟩

end Polytime2.ArrayPacking

namespace Polytime2.Computation

open EncodedDomain ArrayPacking
open Realizable.Internal

variable {Parameter : Type} [Fintype Parameter]

private noncomputable def intervalMask (length : MvPolynomial Parameter ℕ) : Computation Parameter Bool :=
  arrayTabulate (fun _ : Bool => arrayPosition (length + 1)) booleans length
    (fun _ endpoints index => intervalFlags (endpoints false).val (endpoints true).val index)

private theorem intervalMask_realizable (length : MvPolynomial Parameter ℕ) :
    (intervalMask length).Realizable := by
  apply arrayTabulate_realizable
  let step := arrayTransformStep (fun _ : Bool => arrayPosition (length + 1))
    (arrayPosition length) booleans
    (fun _ endpoints index => intervalFlags (endpoints false).val (endpoints true).val index)
  have before (endpoint : Bool) := (positionsLess_realizable length (length + 1)).onArguments
    step.inputDomains step.precondition
    (fun choice => match choice with | false => .inr () | true => .inl endpoint)
    (by intro choice; cases choice <;> rfl) (by intros; trivial)
  have combined := (booleanOperation_realizable (Parameter := Parameter) (Argument := Bool)
    (fun flags => !flags false && flags true)).onResults step.inputDomains step.precondition
    (fun endpoint _ arguments => decide ((arguments.val (.inr ())).val < (arguments.val (.inl endpoint)).val))
    (by intros; trivial) before
  apply combined.withSpecification step.precondition step.compute (by intros; trivial)
  intro sizes arguments valid
  apply Bool.eq_iff_iff.mpr
  simp only [onResults, booleanOperation, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    decide_eq_true_eq, step, arrayTransformStep, intervalFlags]
  omega

/-- Extract an exact half-open interval. None names the source array; some
false and some true name the lower and upper endpoints, respectively. -/
noncomputable def arraySlice (element : EncodedDomain Parameter) (length : MvPolynomial Parameter ℕ) :
    Computation Parameter (Option Bool) where
  inputDomains name := match name with
    | none => element.arrayOfLength length
    | some _ => arrayPosition (length + 1)
  outputDomain := boundedArray element length
  precondition _ _ := True
  compute _ arguments :=
    let flags := intervalFlags (arguments.val (some false)).val (arguments.val (some true)).val
    ⟨⟨count flags, Nat.lt_succ_of_le (count_le flags)⟩, pack flags (arguments.val none)⟩

theorem arraySlice_realizable (element : EncodedDomain Parameter) (length : MvPolynomial Parameter ℕ) :
    (arraySlice element length).Realizable := by
  let computation := arraySlice element length
  have mask := (intervalMask_realizable length).onArguments computation.inputDomains computation.precondition
    some (by intros; rfl) (by intros; trivial)
  exact (arrayPack_realizable element length).onResults computation.inputDomains computation.precondition
    (fun choice _ arguments => match choice with
    | false => intervalFlags (arguments.val (some false)).val (arguments.val (some true)).val
    | true => arguments.val none)
    (by intros; trivial) (by
      intro choice
      cases choice
      · exact mask
      · exact Realizable.argument computation.inputDomains none computation.precondition)

/-- The public slice returns the actual mathematical sublist, with no padding. -/
theorem arraySlice_correct (element : EncodedDomain Parameter) (length : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ) (arguments : (arraySlice element length).Arguments sizes) :
    List.ofFn ((arraySlice element length).compute sizes ⟨arguments, trivial⟩).2 =
      ((List.ofFn (arguments none)).drop (arguments (some false)).val).take
        ((arguments (some true)).val - (arguments (some false)).val) :=
  by
    let lower : Fin (MvPolynomial.eval sizes length + 1) :=
      ⟨(arguments (some false)).val, by
        simpa only [map_add, map_one] using (arguments (some false)).isLt⟩
    let upper : Fin (MvPolynomial.eval sizes length + 1) :=
      ⟨(arguments (some true)).val, by
        simpa only [map_add, map_one] using (arguments (some true)).isLt⟩
    exact interval_pack lower upper (arguments none)

end Polytime2.Computation
