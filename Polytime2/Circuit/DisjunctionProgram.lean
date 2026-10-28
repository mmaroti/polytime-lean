import Polytime2.Circuit.WireArithmetic
import Polytime2.Circuit.UniformObserve
import Polytime2.Arrays.PositionReverse
import Polytime2.Arrays.Tabulate
import Polytime2.Arrays.Operations

/-! # Certified uniform disjunction construction

The constructor tabulates the prefix and reversed suffix blocks of anyWire.
Its inputs are ordinary bounded wire references. The supplied base and length
are mathematical size polynomials; all arithmetic widths follow from the
resulting circuit's exact wire count.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Circuit

open EncodedDomain Polytime2.Computation
open Polytime2.Computation.Realizable.Internal

variable {Parameter : Type} [Fintype Parameter]

/-- Exact wire count after appending a disjunction to the given base. -/
noncomputable def disjunctionWires (base length : MvPolynomial Parameter ℕ) : MvPolynomial Parameter ℕ :=
  base + 5 * length + 1

private theorem length_le_disjunctionWires (base length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ) :
    MvPolynomial.eval sizes length ≤ MvPolynomial.eval sizes (disjunctionWires base length) := by
  simp only [disjunctionWires, map_add, map_mul, map_ofNat, map_one]
  omega

private noncomputable def observerAddress (base length : MvPolynomial Parameter ℕ)
    (isPrefix : Bool) (offset : Fin 3) : Computation Parameter Unit :=
  (wireOfPosition length (disjunctionWires base length) (length_le_disjunctionWires base length)).followedBy
    (wireAffine (disjunctionWires base length)
      (if isPrefix then base + MvPolynomial.C offset.val else base + 3 * length + MvPolynomial.C offset.val)
      (if isPrefix then 3 else 2)) rfl (by
        intro sizes arguments allowed
        change MvPolynomial.eval sizes (if isPrefix then base + MvPolynomial.C offset.val
          else base + 3 * length + MvPolynomial.C offset.val) + (if isPrefix then 3 else 2) *
          ((wireOfPosition length (disjunctionWires base length) (length_le_disjunctionWires base length)).compute
            sizes ⟨arguments, allowed⟩).val < MvPolynomial.eval sizes (disjunctionWires base length)
        rw [wireOfPosition_value]
        have bounded : (arguments ()).val < MvPolynomial.eval sizes length := (arguments ()).isLt
        have small := offset.isLt
        cases isPrefix <;> simp only [Bool.false_eq_true, ↓reduceIte, disjunctionWires,
          map_add, map_mul, map_ofNat, map_one, MvPolynomial.eval_C] <;> omega)

private theorem observerAddress_realizable (base length : MvPolynomial Parameter ℕ)
    (isPrefix : Bool) (offset : Fin 3) : (observerAddress base length isPrefix offset).Realizable :=
  (wireOfPosition_realizable length (disjunctionWires base length) (length_le_disjunctionWires base length)).followedBy
    (wireAffine_realizable (disjunctionWires base length)
      (if isPrefix then base + MvPolynomial.C offset.val else base + 3 * length + MvPolynomial.C offset.val)
      (if isPrefix then 3 else 2)) rfl _

private theorem observerAddress_value (base length : MvPolynomial Parameter ℕ) (isPrefix : Bool) (offset : Fin 3)
    (sizes : Parameter → ℕ) (arguments : {arguments : (observerAddress base length isPrefix offset).Arguments sizes // True}) :
    ((observerAddress base length isPrefix offset).compute sizes arguments).val =
      MvPolynomial.eval sizes base + (if isPrefix then 0 else 3 * MvPolynomial.eval sizes length) +
        (if isPrefix then 3 else 2) * (arguments.val ()).val + offset.val := by
  change MvPolynomial.eval sizes (if isPrefix then base + MvPolynomial.C offset.val
    else base + 3 * length + MvPolynomial.C offset.val) + (if isPrefix then 3 else 2) *
      ((wireOfPosition length (disjunctionWires base length) (length_le_disjunctionWires base length)).compute
        sizes arguments).val = _
  rw [wireOfPosition_value]
  cases isPrefix <;> simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

private noncomputable def observerInputs (base length : MvPolynomial Parameter ℕ) : Bool → EncodedDomain Parameter :=
  fun name => if name then (arrayPosition (disjunctionWires base length)).arrayOfLength length else arrayPosition length

private noncomputable def observerPrefix (base length : MvPolynomial Parameter ℕ) : Computation Parameter Bool :=
  (instantiateProgram (disjunctionWires base length)
    (![.inl true, .inr (0, 1), .inr (0, 0)] : Fin 3 → Bool ⊕ (Fin 2 × Fin 2))).onResults
    (observerInputs base length) (fun _ _ => True)
    (fun port sizes arguments => if port = 0 then arguments.val true (arguments.val false)
      else (observerAddress base length true 0).compute sizes ⟨(fun _ => arguments.val false), trivial⟩)
    (by intros; trivial)

private theorem observerPrefix_realizable (base length : MvPolynomial Parameter ℕ) :
    (observerPrefix base length).Realizable := by
  unfold observerPrefix
  apply (instantiateProgram_realizable _ _).onResults
  intro port
  fin_cases port
  · have read := (arrayLookupWithIndex_realizable (arrayPosition (disjunctionWires base length))
      (arrayPosition length) (fun _ index => index.val) (arrayPosition_value length) length).onArguments
        (observerInputs base length) (fun _ _ => True) id
        (by intro name; cases name <;> rfl)
        (by intro sizes arguments; exact (arguments.val false).isLt)
    exact read.withSpecification (fun _ _ => True) _ (by intros; trivial) (by intros; rfl)
  · exact (observerAddress_realizable base length true 0).withArguments
      (observerInputs base length) (MultiTape.oneTape false) (fun _ => rfl)

private noncomputable def observerSuffix (base length : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  (instantiateProgram (disjunctionWires base length)
    (![.inr (0, 1), .inr (2, 3)] : Fin 2 → Bool ⊕ (Fin 4 × Fin 4))).onResults
    (fun _ => arrayPosition length) (fun _ _ => True)
    (fun port sizes arguments => match port with
      | 0 => (observerAddress base length true 2).compute sizes ⟨(fun _ => (arguments.val ()).rev), trivial⟩
      | 1 => (observerAddress base length false 0).compute sizes arguments
      | 2 => (observerAddress base length true 1).compute sizes ⟨(fun _ => (arguments.val ()).rev), trivial⟩
      | 3 => (observerAddress base length false 1).compute sizes arguments)
    (by intros; trivial)

private theorem observerSuffix_realizable (base length : MvPolynomial Parameter ℕ) :
    (observerSuffix base length).Realizable := by
  unfold observerSuffix
  apply (instantiateProgram_realizable _ _).onResults
  intro port
  fin_cases port
  · exact (arrayPositionReverse_realizable length).followedBy (observerAddress_realizable base length true 2) rfl (by intros; trivial)
  · exact observerAddress_realizable base length false 0
  · exact (arrayPositionReverse_realizable length).followedBy (observerAddress_realizable base length true 1) rfl (by intros; trivial)
  · exact observerAddress_realizable base length false 1

private theorem observerPrefix_value (base length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (observerPrefix base length).Arguments sizes // True}) :
    List.ofFn (fun slot => gateValue ((observerPrefix base length).compute sizes arguments slot)) =
      [.inl true, .inr ((arguments.val true (arguments.val false)).val,
        MvPolynomial.eval sizes base + 3 * (arguments.val false).val),
        .inr ((arguments.val true (arguments.val false)).val, (arguments.val true (arguments.val false)).val)] := by
  simp [observerPrefix, onResults, instantiateProgram, gateValue, observerAddress_value, List.ofFn_succ]

private theorem observerSuffix_value (base length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (observerSuffix base length).Arguments sizes // True}) :
    List.ofFn (fun slot => gateValue ((observerSuffix base length).compute sizes arguments slot)) =
      [.inr (MvPolynomial.eval sizes base + 3 * (MvPolynomial.eval sizes length - 1 - (arguments.val ()).val) + 2,
          MvPolynomial.eval sizes base + 3 * MvPolynomial.eval sizes length + 2 * (arguments.val ()).val),
        .inr (MvPolynomial.eval sizes base + 3 * (MvPolynomial.eval sizes length - 1 - (arguments.val ()).val) + 1,
          MvPolynomial.eval sizes base + 3 * MvPolynomial.eval sizes length + 2 * (arguments.val ()).val + 1)] := by
  simp [observerSuffix, onResults, instantiateProgram, gateValue, observerAddress_value, List.ofFn_succ, Fin.rev]
  omega

private noncomputable def observerPrefixArray (base length : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  arrayTabulate (fun _ => (arrayPosition (disjunctionWires base length)).arrayOfLength length)
    (observerPrefix base length).outputDomain length (fun sizes arguments index =>
      (observerPrefix base length).compute sizes
        ⟨(fun name => match name with | false => index | true => arguments ()), trivial⟩)

private theorem observerPrefixArray_realizable (base length : MvPolynomial Parameter ℕ) :
    (observerPrefixArray base length).Realizable := by
  unfold observerPrefixArray
  apply arrayTabulate_realizable
  let inputs : Unit ⊕ Unit → EncodedDomain Parameter :=
    Sum.elim (fun _ => (arrayPosition (disjunctionWires base length)).arrayOfLength length)
      (fun _ => arrayPosition length)
  have prepared := (observerPrefix_realizable base length).onArguments inputs (fun _ _ => True)
    (fun name => match name with | false => Sum.inr () | true => Sum.inl ())
    (by intro name; cases name <;> rfl) (by intros; trivial)
  apply prepared.withSpecification (fun _ _ => True) _ (by intros; trivial)
  intro sizes arguments allowed
  apply congrArg ((observerPrefix base length).compute sizes)
  apply Subtype.ext
  funext name
  cases name <;> rfl

private noncomputable def observerSuffixArray (base length : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  arrayTabulate (fun _ => (arrayPosition (disjunctionWires base length)).arrayOfLength length)
    (observerSuffix base length).outputDomain length (fun sizes _ index =>
      (observerSuffix base length).compute sizes ⟨(fun _ => index), trivial⟩)

private theorem observerSuffixArray_realizable (base length : MvPolynomial Parameter ℕ) :
    (observerSuffixArray base length).Realizable := by
  unfold observerSuffixArray
  apply arrayTabulate_realizable
  let inputs : Unit ⊕ Unit → EncodedDomain Parameter :=
    Sum.elim (fun _ => (arrayPosition (disjunctionWires base length)).arrayOfLength length)
      (fun _ => arrayPosition length)
  have prepared := (observerSuffix_realizable base length).onArguments inputs (fun _ _ => True)
    (fun _ => Sum.inr ()) (by intros; rfl) (by intros; trivial)
  exact prepared.withSpecification (fun _ _ => True) _ (by intros; trivial) (by intros; rfl)

/-- Emit a disjunction as prefix blocks, its false constant, and suffix blocks,
using the canonical product, array, and record codecs. -/
noncomputable def disjunctionProgram (base length : MvPolynomial Parameter ℕ) : Computation Parameter Unit where
  inputDomains _ := (arrayPosition (disjunctionWires base length)).arrayOfLength length
  outputDomain := (observerPrefixArray base length).outputDomain.prod
    ((gateDomain (disjunctionWires base length)).prod (observerSuffixArray base length).outputDomain)
  precondition _ _ := True
  compute sizes arguments := ((observerPrefixArray base length).compute sizes arguments,
    (.inl false, (observerSuffixArray base length).compute sizes arguments))

theorem disjunctionProgram_realizable (base length : MvPolynomial Parameter ℕ) :
    (disjunctionProgram base length).Realizable := by
  have constant := (instantiateGate_realizable (disjunctionWires base length) (arity := 0) (.inl false)).onResults
    (disjunctionProgram base length).inputDomains (fun _ _ => True) (fun port => Fin.elim0 port)
    (by intros; trivial) (fun port => Fin.elim0 port)
  have collected := (observerPrefixArray_realizable base length).prodMk
    (constant.prodMk (observerSuffixArray_realizable base length))
  exact collected.withSpecification (disjunctionProgram base length).precondition
    (disjunctionProgram base length).compute (by intros; trivial) (by intros; rfl)

/-- Forget the nested storage without changing the emitted gate order. -/
noncomputable def disjunctionGateList {base length : MvPolynomial Parameter ℕ} (sizes : Parameter → ℕ)
    (program : (disjunctionProgram base length).outputDomain.Carrier sizes) : List Gate :=
  (List.ofFn (fun index => List.ofFn (fun slot => gateValue (program.1 index slot)))).flatten ++
    [gateValue program.2.1] ++
    (List.ofFn (fun index => List.ofFn (fun slot => gateValue (program.2.2 index slot)))).flatten

/-- The uniform gate emitter agrees with the mathematical expression compiler
on the entire gate list, with no nonempty-array hypothesis. -/
theorem disjunctionProgram_value (base length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (disjunctionProgram base length).Arguments sizes // True}) :
    disjunctionGateList sizes ((disjunctionProgram base length).compute sizes arguments) =
      ((Expression.anyWire (List.ofFn (fun index => (arguments.val () index).val))).compile
        (MvPolynomial.eval sizes base)).1 := by
  rw [Expression.anyWire_compile_blocks]
  simp only [disjunctionGateList, disjunctionProgram, observerPrefixArray, observerSuffixArray, arrayTabulate]
  congr 2
  · apply congrArg List.flatten
    apply congrArg List.ofFn
    funext index
    exact observerPrefix_value base length sizes
      ⟨(fun name => match name with | false => index | true => arguments.val ()), trivial⟩
  · apply congrArg List.ofFn
    funext index
    exact observerSuffix_value base length sizes ⟨(fun _ => index), trivial⟩

end Polytime2.Circuit
