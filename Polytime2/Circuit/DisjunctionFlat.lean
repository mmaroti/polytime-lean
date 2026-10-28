import Polytime2.Circuit.DisjunctionProgram
import Polytime2.Arrays.FlattenRecords
import Polytime2.Arrays.Snoc
import Polytime2.Arrays.Append

/-! # Canonical flat disjunction gate arrays

Flattening the fixed records, appending the false constant, and concatenating
the suffix retain the observer's gate order and existing element encodings.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Circuit

open EncodedDomain Polytime2.Computation

variable {Parameter : Type} [Fintype Parameter]

/-- Exact gate count, expressed in the constructor's consecutive groups. -/
noncomputable def disjunctionGateCount (length : MvPolynomial Parameter ℕ) : MvPolynomial Parameter ℕ :=
  (length * MvPolynomial.C 3 + 1) + length * MvPolynomial.C 2

private noncomputable def disjunctionFlatten (base length : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  let program := (disjunctionProgram base length).outputDomain
  let element := gateDomain (disjunctionWires base length)
  let prefixDomain := (record 3 (fun _ => element)).arrayOfLength length
  let suffixDomain := (record 2 (fun _ => element)).arrayOfLength length
  let first := (pairProjection prefixDomain (element.prod suffixDomain) false).followedBy
    (arrayFlattenRecords element 3 length) rfl (by intros; trivial)
  let tail := pairProjection prefixDomain (element.prod suffixDomain) true
  let constant := tail.followedBy (pairProjection element suffixDomain false) rfl (by intros; trivial)
  let last := (tail.followedBy (pairProjection element suffixDomain true) rfl (by intros; trivial)).followedBy
    (arrayFlattenRecords element 2 length) rfl (by intros; trivial)
  let snoc := (arraySnoc element (length * MvPolynomial.C 3)).onResults (fun _ => program) (fun _ _ => True)
    (fun name sizes arguments => match name with
      | false => first.compute sizes arguments | true => constant.compute sizes arguments) (by intros; trivial)
  (Computation.mk (fun _ => program) (snoc.outputDomain.prod last.outputDomain) (fun _ _ => True)
    (fun sizes arguments => (snoc.compute sizes arguments, last.compute sizes arguments))).followedBy (arrayAppend element (length * MvPolynomial.C 3 + 1) (length * MvPolynomial.C 2))
    rfl (by intros; trivial)

private theorem disjunctionFlatten_realizable (base length : MvPolynomial Parameter ℕ) :
    (disjunctionFlatten base length).Realizable := by
  let program := (disjunctionProgram base length).outputDomain
  let element := gateDomain (disjunctionWires base length)
  let prefixDomain := (record 3 (fun _ => element)).arrayOfLength length
  let suffixDomain := (record 2 (fun _ => element)).arrayOfLength length
  have first := (pairProjection_realizable prefixDomain (element.prod suffixDomain) false).followedBy
    (arrayFlattenRecords_realizable element 3 length) rfl (by intros; trivial)
  have tail := pairProjection_realizable prefixDomain (element.prod suffixDomain) true
  have constant := tail.followedBy (pairProjection_realizable element suffixDomain false) rfl (by intros; trivial)
  have last := (tail.followedBy (pairProjection_realizable element suffixDomain true) rfl (by intros; trivial)).followedBy
    (arrayFlattenRecords_realizable element 2 length) rfl (by intros; trivial)
  unfold disjunctionFlatten
  apply Realizable.followedBy ?_
    (arrayAppend_realizable element (length * MvPolynomial.C 3 + 1) (length * MvPolynomial.C 2)) rfl (by intros; trivial)
  apply Realizable.prodMk ?_ last
  apply (arraySnoc_realizable element (length * MvPolynomial.C 3)).onResults
  intro name
  cases name
  · exact first
  · exact constant

private theorem disjunctionFlatten_list (base length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (disjunctionFlatten base length).Arguments sizes // True}) :
    List.ofFn ((disjunctionFlatten base length).compute sizes arguments) =
      (List.ofFn (fun index => List.ofFn ((arguments.val ()).1 index))).flatten ++
        [(arguments.val ()).2.1] ++
        (List.ofFn (fun index => List.ofFn ((arguments.val ()).2.2 index))).flatten := by
  simp only [disjunctionFlatten, followedBy]
  rw [arrayAppend_list]
  simp only [onResults, arraySnoc, pairProjection, unaryMap]
  rw [ofFn_snocValues, arrayFlattenRecords_list, arrayFlattenRecords_list]
  rfl

/-- Emit the disjunction as one canonical gate array. -/
noncomputable def disjunctionFlatProgram (base length : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  (disjunctionProgram base length).followedBy (disjunctionFlatten base length) rfl (by intros; trivial)

theorem disjunctionFlatProgram_realizable (base length : MvPolynomial Parameter ℕ) :
    (disjunctionFlatProgram base length).Realizable :=
  (disjunctionProgram_realizable base length).followedBy (disjunctionFlatten_realizable base length) rfl (by intros; trivial)

/-- Flat output is exactly the canonical expression compiler's gate sequence. -/
theorem disjunctionFlatProgram_value (base length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (disjunctionFlatProgram base length).Arguments sizes // True}) :
    List.ofFn (fun index => gateValue ((disjunctionFlatProgram base length).compute sizes arguments index)) =
      ((Expression.anyWire (List.ofFn (fun index => (arguments.val () index).val))).compile
        (MvPolynomial.eval sizes base)).1 := by
  simp only [disjunctionFlatProgram, followedBy]
  rw [List.ofFn_comp' _ gateValue, disjunctionFlatten_list]
  simp only [List.map_append, List.map_cons, List.map_nil, List.map_flatten, List.map_ofFn, Function.comp_def]
  change disjunctionGateList sizes ((disjunctionProgram base length).compute sizes arguments) = _
  exact disjunctionProgram_value base length sizes arguments

end Polytime2.Circuit
