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
  let condition := fun sizes (arguments : (gateSplice source target count).Arguments sizes) =>
    (arguments false).isLeft
  apply Realizable.ofCases condition
  · have tested := (sumIsLeft_realizable booleans operands).withArguments
      inputs (MultiTape.oneTape false) (fun _ => rfl)
    exact tested.withSpecification _ _ (by intros; trivial) (by intros; rfl)
  · let allowed := fun sizes (arguments : ∀ name, (inputs name).Carrier sizes) =>
      True ∧ condition sizes arguments = true
    have extracted := ((sumLeft_realizable booleans operands).withArguments inputs
      (MultiTape.oneTape false) (fun _ => rfl)).withPrecondition allowed
        (by intro sizes arguments accepted; exact accepted.2)
    have injected := extracted.followedBy
      (sumInl_realizable booleans ((arrayPosition (target + count)).prod (arrayPosition (target + count))))
      rfl (by intros; trivial)
    apply injected.withSpecification _ _ (by intros; assumption)
    intro sizes arguments accepted
    cases equal : arguments false with
    | inl value =>
      simp [gateSplice, specification_compute, followedBy, withPrecondition, withArguments,
        sumLeft, unaryMap, sumInl, MultiTape.oneTape, equal]
    | inr pair => simp [condition, equal] at accepted
  · let allowed := fun sizes (arguments : ∀ name, (inputs name).Carrier sizes) =>
      True ∧ condition sizes arguments = false
    let payload := ((sumRight booleans operands).withArguments inputs (MultiTape.oneTape false)
      (fun _ => rfl)).withPrecondition allowed (by intro sizes arguments accepted; exact accepted.2)
    have extracted : payload.Realizable := ((sumRight_realizable booleans operands).withArguments
      inputs (MultiTape.oneTape false) (fun _ => rfl)).withPrecondition allowed
        (by intro sizes arguments accepted; exact accepted.2)
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
    cases equal : arguments false with
    | inl value => simp [condition, equal] at accepted
    | inr pair =>
      have payloadEqual : payload.compute sizes ⟨arguments, accepted⟩ = pair := by
        simp [payload, withPrecondition, withArguments, sumRight, unaryMap,
          MultiTape.oneTape, equal]
      simp [gateSplice, specification_compute, followedBy, sumInr, unaryMap,
        payloadEqual, equal]

end Polytime2.Circuit
