import Polytime2.Circuit.WireSplice

/-! # Gate relocation with runtime input aliases

Constants retain their values; each NAND operand uses the certified wire
relocation operation. The alias array is shared immutable input.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Circuit

open EncodedDomain Polytime2.Computation

variable {Parameter : Type} [Fintype Parameter]

/-- False names the source gate; true names the replacement input wires. -/
noncomputable def gateSpliceInputs (source target count : MvPolynomial Parameter ℕ) :
    Bool → EncodedDomain Parameter :=
  fun name => if name then (arrayPosition target).arrayOfLength source else gateDomain (source + count)

/-- Relocate both operands of a gate through the same mathematical input aliases. -/
noncomputable def gateSplice (source target count : MvPolynomial Parameter ℕ) : Computation Parameter Bool :=
  specification (gateSpliceInputs source target count) (gateDomain (target + count)) (fun _ _ => True)
    (fun sizes arguments => (arguments.val false).map id (fun pair =>
      ((wireSplice source target count).compute sizes
        ⟨(fun name => match name with | false => pair.1 | true => arguments.val true), trivial⟩,
       (wireSplice source target count).compute sizes
        ⟨(fun name => match name with | false => pair.2 | true => arguments.val true), trivial⟩)))

theorem gateSplice_value (source target count : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (gateSplice source target count).Arguments sizes // True}) :
    gateValue ((gateSplice source target count).compute sizes arguments) =
      (gateValue (arguments.val false)).rename
        (spliceNames (MvPolynomial.eval sizes source) (MvPolynomial.eval sizes target)
          (fun index => (arguments.val true index).val)) := by
  simp only [gateSplice, specification_compute]
  cases arguments.val false with
  | inl value => rfl
  | inr pair =>
    change Sum.inr (_, _) = Sum.inr (_, _)
    rw [wireSplice_value, wireSplice_value]

theorem gateSplice_realizable (source target count : MvPolynomial Parameter ℕ) :
    (gateSplice source target count).Realizable := by
  let inputs := gateSpliceInputs source target count
  let operands := (arrayPosition (source + count)).prod (arrayPosition (source + count))
  let alternatives := SumEncoding.alternatives (booleans : EncodedDomain Parameter) operands
  let encode := SumEncoding.equivalence (booleans : EncodedDomain Parameter) operands
  let condition := fun sizes (arguments : (gateSplice source target count).Arguments sizes) =>
    decide ((encode sizes (arguments false)).1 = 0)
  have projection (index : Fin 2) :
      ((variantProjection 2 alternatives index).reinterpretInputs
        (fun _ => gateDomain (source + count)) (fun _ sizes value => encode sizes value)
        (fun sizes arguments => (encode sizes (arguments ())).1 = index) (by intros; assumption)).Realizable :=
    (variantProjection_realizable 2 alternatives index).reinterpretInputs
      (fun _ => gateDomain (source + count)) (fun _ sizes value => encode sizes value)
      (by intros; rfl) (by intros; rfl) _ (by intros; assumption)
  apply Realizable.ofCases condition
  · have tested := ((variantIs_realizable 2 alternatives 0).reinterpretInputs
      (fun _ => gateDomain (source + count)) (fun _ sizes value => encode sizes value)
      (by intros; rfl) (by intros; rfl) (fun _ _ => True) (by intros; trivial)).withArguments
        inputs (MultiTape.oneTape false) (fun _ => rfl)
    exact tested.withSpecification _ _ (by intros; trivial) (by intros; rfl)
  · let allowed := fun sizes (arguments : ∀ name, (inputs name).Carrier sizes) =>
      True ∧ condition sizes arguments = true
    have extracted := ((projection 0).withArguments inputs (MultiTape.oneTape false) (fun _ => rfl)).withPrecondition
      allowed (by
        intro sizes arguments accepted
        change (encode sizes (arguments false)).1 = 0
        exact of_decide_eq_true accepted.2)
    have injected := extracted.followedBy
      (sumInl_realizable booleans ((arrayPosition (target + count)).prod (arrayPosition (target + count))))
      rfl (by intros; trivial)
    apply injected.withSpecification _ _ (by intros; assumption)
    intro sizes arguments accepted
    generalize equal : arguments false = gate at *
    cases gate with
    | inl value =>
      simp [gateSplice, specification_compute, followedBy, withPrecondition, withArguments,
        reinterpretInputs, variantProjection, unaryMap, sumInl, MultiTape.oneTape,
        encode, SumEncoding.equivalence, equal]
      apply congrArg Sum.inl
      apply eq_of_heq
      simp only [eqRec_heq_iff]
      rw [equal]
    | inr pair =>
      have selected : (encode sizes (arguments false)).1 = 0 := of_decide_eq_true accepted.2
      simp [equal, encode, SumEncoding.equivalence] at selected
  · let allowed := fun sizes (arguments : ∀ name, (inputs name).Carrier sizes) =>
      True ∧ condition sizes arguments = false
    have selectedTag : ∀ sizes (arguments : ∀ name, (inputs name).Carrier sizes),
        allowed sizes arguments → (encode sizes (arguments false)).1 = 1 := by
      intro sizes arguments accepted
      have selected : (encode sizes (arguments false)).1 ≠ 0 := of_decide_eq_false accepted.2
      have bounded := (encode sizes (arguments false)).1.isLt
      apply Fin.ext
      have different : (encode sizes (arguments false)).1.val ≠ 0 := by
        intro equal; exact selected (Fin.ext equal)
      omega
    let payload := (((variantProjection 2 alternatives 1).reinterpretInputs
      (fun _ => gateDomain (source + count)) (fun _ sizes value => encode sizes value)
      (fun sizes arguments => (encode sizes (arguments ())).1 = 1) (by intros; assumption)).withArguments
        inputs (MultiTape.oneTape false) (fun _ => rfl)).withPrecondition allowed selectedTag
    have extracted : payload.Realizable :=
      ((projection 1).withArguments inputs (MultiTape.oneTape false) (fun _ => rfl)).withPrecondition allowed selectedTag
    have first := extracted.fst
    have second := extracted.snd
    have relocatedFirst := (wireSplice_realizable source target count).onResults inputs allowed
      (fun name sizes arguments => match name with
        | false => (payload.compute sizes arguments).1
        | true => arguments.val true) (by intros; trivial) (by
          intro name
          cases name
          · exact first
          · exact Realizable.argument inputs true allowed)
    have relocatedSecond := (wireSplice_realizable source target count).onResults inputs allowed
      (fun name sizes arguments => match name with
        | false => (payload.compute sizes arguments).2
        | true => arguments.val true) (by intros; trivial) (by
          intro name
          cases name
          · exact second
          · exact Realizable.argument inputs true allowed)
    have injected := (relocatedFirst.prodMk relocatedSecond).followedBy
      (sumInr_realizable booleans ((arrayPosition (target + count)).prod (arrayPosition (target + count))))
      rfl (by intros; trivial)
    apply injected.withSpecification _ _ (by intros; assumption)
    intro sizes arguments accepted
    generalize equal : arguments false = gate at *
    cases gate with
    | inl value =>
      have selected : (encode sizes (arguments false)).1 ≠ 0 := of_decide_eq_false accepted.2
      simp [equal, encode, SumEncoding.equivalence] at selected
    | inr pair =>
      have payloadEqual : payload.compute sizes ⟨arguments, accepted⟩ = pair := by
        apply eq_of_heq
        simp only [payload, withPrecondition, withArguments, reinterpretInputs,
          variantProjection, unaryMap, MultiTape.oneTape, encode, SumEncoding.equivalence]
        simp only [eqRec_heq_iff]
        change HEq (encode sizes (arguments false)).2 pair
        rw [equal]
        rfl
      simp [gateSplice, specification_compute, followedBy, sumInr, unaryMap,
        payloadEqual, equal]

end Polytime2.Circuit
