import Polytime2.Arithmetic.NaturalArithmetic
import Polytime2.Arrays.Indices
import Polytime2.Computation.RecordArguments

/-! # Coordinates retained by nested-witness normalization

Given outer-input and inner-witness lengths, produce the outer-prefix end and
the inner-witness interval endpoints. The precondition states precisely that
both nested headers and the witness fit in the original word.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Complexity

open EncodedDomain Polytime2.Computation Polytime2.Computation.Realizable.Internal

/-- Prefix end, witness start, and witness end within the original word. -/
noncomputable def witnessEndpoints (capacity : MvPolynomial Unit ℕ) : Computation Unit Bool where
  inputDomains _ := boundedIndex (capacity + 1)
  outputDomain := record 3 (fun _ => arrayPosition (capacity + 1))
  precondition sizes arguments := 2 * (arguments false).val + 2 * (arguments true).val + 2 ≤ MvPolynomial.eval sizes capacity
  compute sizes arguments index := ⟨match index with
    | 0 => 2 * (arguments.val false).val + 1
    | 1 => 2 * (arguments.val false).val + (arguments.val true).val + 2
    | 2 => 2 * (arguments.val false).val + 2 * (arguments.val true).val + 2, by
      have fits := arguments.property
      simp only [map_add, map_one]
      fin_cases index <;> dsimp <;> omega⟩

theorem witnessEndpoints_realizable (capacity : MvPolynomial Unit ℕ) : (witnessEndpoints capacity).Realizable := by
  let inputs := (witnessEndpoints capacity).inputDomains
  let allowed := (witnessEndpoints capacity).precondition
  let width := (capacity + 1) + 1
  have power (sizes : Unit → ℕ) : MvPolynomial.eval sizes capacity < 2 ^ MvPolynomial.eval sizes width := by
    have bound := Nat.lt_two_pow_self (n := MvPolynomial.eval sizes width)
    simp only [width, map_add, map_one] at *
    omega
  let scalar (name : Bool) (sizes : Unit → ℕ) (arguments : {arguments : ∀ name, (inputs name).Carrier sizes // allowed sizes arguments}) :
      (binaryNaturalsOfWidth width).Carrier sizes :=
    ⟨(arguments.val name).val, by
      have bound := (arguments.val name).isLt
      have limit := power sizes
      change (arguments.val name).val < 2 ^ MvPolynomial.eval sizes width
      change (arguments.val name).val < MvPolynomial.eval sizes (capacity + 1) at bound
      simp only [map_add, map_one] at bound
      omega⟩
  have scalarReady (name : Bool) : (Computation.mk inputs (binaryNaturalsOfWidth width) allowed (scalar name)).Realizable := by
    have wide := ((naturalWiden_realizable (capacity + 1) 1).reinterpretInputs
      (fun _ : Unit => boundedIndex (capacity + 1))
      (fun _ sizes value => ⟨value.val, value.isLt.trans_le Nat.lt_two_pow_self.le⟩)
      (by intros; rfl) (by intros; rfl) (fun _ _ => True) (by intros; trivial)).onArguments inputs allowed
        (fun _ => name) (by intros; rfl) (by intros; trivial)
    exact wide.withSpecification allowed (scalar name) (by intros; trivial) (by intros; apply Fin.ext; rfl)
  have add (first second : ∀ sizes, {arguments : ∀ name, (inputs name).Carrier sizes // allowed sizes arguments} →
      (binaryNaturalsOfWidth width).Carrier sizes)
      (firstReady : (Computation.mk inputs (binaryNaturalsOfWidth width) allowed first).Realizable)
      (secondReady : (Computation.mk inputs (binaryNaturalsOfWidth width) allowed second).Realizable)
      (bounded : ∀ sizes arguments, (first sizes arguments).val + (second sizes arguments).val ≤ MvPolynomial.eval sizes capacity) :
      (Computation.mk inputs (binaryNaturalsOfWidth width) allowed (fun sizes arguments =>
        ⟨(first sizes arguments).val + (second sizes arguments).val, (bounded sizes arguments).trans_lt (power sizes)⟩)).Realizable := by
    exact (naturalAdd_realizable width).onResults inputs allowed
      (fun name sizes arguments => if name then second sizes arguments else first sizes arguments)
      (by intro sizes arguments; exact (bounded sizes arguments).trans_lt (power sizes))
      (by intro name; cases name; exact firstReady; exact secondReady)
  have increment (value : ∀ sizes, {arguments : ∀ name, (inputs name).Carrier sizes // allowed sizes arguments} →
      (binaryNaturalsOfWidth width).Carrier sizes)
      (valueReady : (Computation.mk inputs (binaryNaturalsOfWidth width) allowed value).Realizable)
      (bounded : ∀ sizes arguments, (value sizes arguments).val + 1 ≤ MvPolynomial.eval sizes capacity) :
      (Computation.mk inputs (binaryNaturalsOfWidth width) allowed (fun sizes arguments =>
        ⟨(value sizes arguments).val + 1, (bounded sizes arguments).trans_lt (power sizes)⟩)).Realizable := by
    have next := valueReady.followedBy (naturalIncrement_realizable width) rfl (by intros; trivial)
    exact next.withSpecification allowed _ (by intros; assumption) (by
      intro sizes arguments accepted
      apply Fin.ext
      exact Nat.mod_eq_of_lt ((bounded sizes ⟨arguments, accepted⟩).trans_lt (power sizes)))
  let doubleValue := fun sizes arguments =>
    (scalar false sizes arguments).val + (scalar false sizes arguments).val
  have doubleBound : ∀ sizes arguments, doubleValue sizes arguments ≤ MvPolynomial.eval sizes capacity := by
    intro sizes arguments
    have fits := arguments.property
    change 2 * (arguments.val false).val + 2 * (arguments.val true).val + 2 ≤ _ at fits
    dsimp [doubleValue, scalar]
    omega
  let twice := fun sizes arguments => (⟨doubleValue sizes arguments,
    (doubleBound sizes arguments).trans_lt (power sizes)⟩ : (binaryNaturalsOfWidth width).Carrier sizes)
  have twiceReady : (Computation.mk inputs (binaryNaturalsOfWidth width) allowed twice).Realizable :=
    add (scalar false) (scalar false) (scalarReady false) (scalarReady false) doubleBound
  have prefixBound : ∀ sizes arguments, (twice sizes arguments).val + 1 ≤ MvPolynomial.eval sizes capacity := by
    intro sizes arguments
    have fits := arguments.property
    change 2 * (arguments.val false).val + 2 * (arguments.val true).val + 2 ≤ _ at fits
    dsimp [twice, doubleValue, scalar]
    omega
  let prefixEnd := fun sizes arguments => (⟨(twice sizes arguments).val + 1,
    (prefixBound sizes arguments).trans_lt (power sizes)⟩ : (binaryNaturalsOfWidth width).Carrier sizes)
  have prefixReady : (Computation.mk inputs (binaryNaturalsOfWidth width) allowed prefixEnd).Realizable :=
    increment twice twiceReady prefixBound
  have partialBound : ∀ sizes arguments, (prefixEnd sizes arguments).val + (scalar true sizes arguments).val ≤
      MvPolynomial.eval sizes capacity := by
    intro sizes arguments
    have fits := arguments.property
    change 2 * (arguments.val false).val + 2 * (arguments.val true).val + 2 ≤ _ at fits
    dsimp [prefixEnd, twice, doubleValue, scalar]
    omega
  let partialEnd := fun sizes arguments => (⟨(prefixEnd sizes arguments).val + (scalar true sizes arguments).val,
    (partialBound sizes arguments).trans_lt (power sizes)⟩ : (binaryNaturalsOfWidth width).Carrier sizes)
  have partialReady : (Computation.mk inputs (binaryNaturalsOfWidth width) allowed partialEnd).Realizable :=
    add prefixEnd (scalar true) prefixReady (scalarReady true) partialBound
  have startBound : ∀ sizes arguments, (partialEnd sizes arguments).val + 1 ≤ MvPolynomial.eval sizes capacity := by
    intro sizes arguments
    have fits := arguments.property
    change 2 * (arguments.val false).val + 2 * (arguments.val true).val + 2 ≤ _ at fits
    dsimp [partialEnd, prefixEnd, twice, doubleValue, scalar]
    omega
  let witnessStart := fun sizes arguments => (⟨(partialEnd sizes arguments).val + 1,
    (startBound sizes arguments).trans_lt (power sizes)⟩ : (binaryNaturalsOfWidth width).Carrier sizes)
  have startReady : (Computation.mk inputs (binaryNaturalsOfWidth width) allowed witnessStart).Realizable :=
    increment partialEnd partialReady startBound
  have endBound : ∀ sizes arguments, (witnessStart sizes arguments).val + (scalar true sizes arguments).val ≤
      MvPolynomial.eval sizes capacity := by
    intro sizes arguments
    have fits := arguments.property
    change 2 * (arguments.val false).val + 2 * (arguments.val true).val + 2 ≤ _ at fits
    dsimp [witnessStart, partialEnd, prefixEnd, twice, doubleValue, scalar]
    omega
  let witnessEnd := fun sizes arguments => (⟨(witnessStart sizes arguments).val + (scalar true sizes arguments).val,
    (endBound sizes arguments).trans_lt (power sizes)⟩ : (binaryNaturalsOfWidth width).Carrier sizes)
  have endReady : (Computation.mk inputs (binaryNaturalsOfWidth width) allowed witnessEnd).Realizable :=
    add witnessStart (scalar true) startReady (scalarReady true) endBound
  have coordinate (value : ∀ sizes, {arguments : ∀ name, (inputs name).Carrier sizes // allowed sizes arguments} →
      (binaryNaturalsOfWidth width).Carrier sizes)
      (ready : (Computation.mk inputs (binaryNaturalsOfWidth width) allowed value).Realizable)
      (bounded : ∀ sizes arguments, (value sizes arguments).val ≤ MvPolynomial.eval sizes capacity) :
      (Computation.mk inputs (arrayPosition (capacity + 1)) allowed (fun sizes arguments =>
        ⟨(value sizes arguments).val, by simp only [map_add, map_one]; have bound := bounded sizes arguments; omega⟩)).Realizable := by
    have selected := ready.refineOutput (fun sizes result => result.val ≤ MvPolynomial.eval sizes capacity) bounded
    exact selected.reinterpretOutput (arrayPosition (capacity + 1))
      (fun sizes result => ⟨result.val.val, by simp only [map_add, map_one]; have bound := result.property; omega⟩)
      (by intros; rfl) (by intros; rfl)
  have prefixCoordinate := coordinate prefixEnd prefixReady prefixBound
  have startCoordinate := coordinate witnessStart startReady startBound
  have endCoordinate := coordinate witnessEnd endReady endBound
  apply Realizable.recordOutputs
  intro index
  fin_cases index
  · apply prefixCoordinate.withSpecification allowed _ (by intros; assumption)
    intro sizes arguments accepted
    apply Fin.ext
    dsimp [prefixEnd, twice, doubleValue, scalar, witnessEndpoints]
    omega
  · apply startCoordinate.withSpecification allowed _ (by intros; assumption)
    intro sizes arguments accepted
    apply Fin.ext
    dsimp [witnessStart, partialEnd, prefixEnd, twice, doubleValue, scalar, witnessEndpoints]
    omega
  · apply endCoordinate.withSpecification allowed _ (by intros; assumption)
    intro sizes arguments accepted
    apply Fin.ext
    dsimp [witnessEnd, witnessStart, partialEnd, prefixEnd, twice, doubleValue, scalar, witnessEndpoints]
    omega

end Polytime2.Complexity
