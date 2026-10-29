import Polytime2.Circuit.WireArithmetic
import Polytime2.Circuit.Compose
import Polytime2.Computation.Conditional
import Polytime2.Arrays.Operations

/-! # Certified wire relocation for circuit composition

Existing inputs are replaced by an alias array. Fresh gate wires retain their
relative position after the new input block. Source and target input counts
may differ in either direction; working capacities stay internal.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Circuit

open EncodedDomain Polytime2.Computation
open Polytime2.Computation.Realizable.Internal

variable {Parameter : Type} [Fintype Parameter]

/-- Relocate a fresh gate wire after replacing the source input block.
Admissibility says precisely that the reference is a fresh gate wire. -/
noncomputable def freshWire (source target count : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  specification (fun _ => arrayPosition (source + count)) (arrayPosition (target + count))
    (fun sizes arguments => MvPolynomial.eval sizes source ≤ (arguments ()).val)
    (fun sizes arguments => ⟨MvPolynomial.eval sizes target + ((arguments.val ()).val - MvPolynomial.eval sizes source), by
      have fresh := arguments.property
      have bounded : (arguments.val ()).val < MvPolynomial.eval sizes (source + count) := (arguments.val ()).isLt
      simp only [map_add] at bounded ⊢
      omega⟩)

theorem freshWire_value (source target count : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (freshWire source target count).Arguments sizes //
      (freshWire source target count).precondition sizes arguments}) :
    ((freshWire source target count).compute sizes arguments).val =
      MvPolynomial.eval sizes target + ((arguments.val ()).val - MvPolynomial.eval sizes source) := by
  simp only [freshWire, specification_compute]

theorem freshWire_realizable (source target count : MvPolynomial Parameter ℕ) :
    (freshWire source target count).Realizable := by
  let inputs := (freshWire source target count).inputDomains
  let allowed := (freshWire source target count).precondition
  let capacity := source + target + count + 1
  let reference := (wireOfPosition (source + count) capacity
    (by intro sizes; simp only [capacity, map_add, map_one]; omega)).withPrecondition allowed (by intros; trivial)
  have referenceReady : reference.Realizable :=
    (wireOfPosition_realizable (source + count) capacity
      (by intro sizes; simp only [capacity, map_add, map_one]; omega)).withPrecondition allowed (by intros; trivial)
  let oldCount := (positionPolynomial source capacity).onResults inputs allowed (fun empty => nomatch empty)
    (by
      intro sizes arguments
      change MvPolynomial.eval sizes source < MvPolynomial.eval sizes capacity
      simp only [capacity, map_add, map_one]
      omega)
  have oldCountReady : oldCount.Realizable := by
    apply (positionPolynomial_realizable source capacity).onResults
    intro empty
    exact nomatch empty
  let difference := (wireSubtract capacity).onResults inputs allowed
    (fun choice sizes arguments => if choice then oldCount.compute sizes arguments else reference.compute sizes arguments)
    (by intro sizes arguments; exact arguments.property)
  have differenceReady : difference.Realizable := by
    apply (wireSubtract_realizable capacity).onResults
    intro choice
    cases choice
    · exact referenceReady
    · exact oldCountReady
  have resultBound (sizes : Parameter → ℕ) (arguments : ∀ name, (inputs name).Carrier sizes)
      (fresh : allowed sizes arguments) :
      MvPolynomial.eval sizes target + ((arguments ()).val - MvPolynomial.eval sizes source) <
        MvPolynomial.eval sizes (target + count) := by
    have bounded : (arguments ()).val < MvPolynomial.eval sizes (source + count) := (arguments ()).isLt
    change MvPolynomial.eval sizes source ≤ (arguments ()).val at fresh
    simp only [map_add] at bounded ⊢
    omega
  have narrowed := differenceReady.followedBy (wireCast_realizable capacity (target + count)) rfl (by
    intro sizes arguments fresh
    change (arguments ()).val - MvPolynomial.eval sizes source < MvPolynomial.eval sizes (target + count)
    have bounded := resultBound sizes arguments fresh
    omega)
  have relocated := narrowed.followedBy (wireAffine_realizable (target + count) target 1) rfl (by
    intro sizes arguments fresh
    change MvPolynomial.eval sizes target + 1 * ((arguments ()).val - MvPolynomial.eval sizes source) < _
    simpa only [one_mul] using resultBound sizes arguments fresh)
  apply relocated.withSpecification (freshWire source target count).precondition
    (freshWire source target count).compute (by intros; assumption)
  intro sizes arguments fresh
  apply Fin.ext
  rw [freshWire_value]
  change MvPolynomial.eval sizes target + 1 * ((arguments ()).val - MvPolynomial.eval sizes source) = _
  simp only [one_mul]

/-- False names a source reference, true its mathematical input-alias array. -/
noncomputable def wireSpliceInputs (source target count : MvPolynomial Parameter ℕ) : Bool → EncodedDomain Parameter :=
  fun name => if name then (arrayPosition target).arrayOfLength source else arrayPosition (source + count)

/-- Replace input references by aliases and relocate fresh references, exactly
as in mathematical circuit composition. No ordering between input counts is
assumed. -/
noncomputable def wireSplice (source target count : MvPolynomial Parameter ℕ) : Computation Parameter Bool :=
  specification (wireSpliceInputs source target count) (arrayPosition (target + count)) (fun _ _ => True)
    (fun sizes arguments => ⟨spliceNames (MvPolynomial.eval sizes source) (MvPolynomial.eval sizes target)
      (fun index => (arguments.val true index).val) (arguments.val false).val, by
        have bounded := spliceNames_bound (fun index => (arguments.val true index).val)
          (fun index => (arguments.val true index).isLt) (MvPolynomial.eval sizes count)
          (arguments.val false).val (by simpa only [map_add] using (arguments.val false).isLt)
        simpa only [map_add] using bounded⟩)

theorem wireSplice_value (source target count : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (wireSplice source target count).Arguments sizes // True}) :
    ((wireSplice source target count).compute sizes arguments).val =
      spliceNames (MvPolynomial.eval sizes source) (MvPolynomial.eval sizes target)
        (fun index => (arguments.val true index).val) (arguments.val false).val := by
  simp only [wireSplice, specification_compute]

theorem wireSplice_realizable (source target count : MvPolynomial Parameter ℕ) :
    (wireSplice source target count).Realizable := by
  let computation := wireSplice source target count
  let inputs := wireSpliceInputs source target count
  let condition := fun sizes (arguments : computation.Arguments sizes) =>
    decide ((arguments false).val < MvPolynomial.eval sizes source)
  apply Realizable.ofCases condition
  · have tested := (positionWithin_realizable (source + count) source).withArguments
      inputs (MultiTape.oneTape false) (fun _ => rfl)
    exact tested.withSpecification computation.precondition (fun sizes arguments => condition sizes arguments.val)
      (by intros; trivial) (by intros; rfl)
  · let allowed := fun sizes (arguments : ∀ name, (inputs name).Carrier sizes) =>
      computation.precondition sizes arguments ∧ condition sizes arguments = true
    let picked := (arrayLookupWithIndex (arrayPosition target) (arrayPosition (source + count))
      (fun _ index => index.val) source).onResults inputs allowed
        (fun name _ arguments => match name with | false => arguments.val false | true => arguments.val true) (by
          intro sizes arguments
          change (arguments.val false).val < MvPolynomial.eval sizes source
          simpa only [condition, decide_eq_true_eq] using arguments.property.2)
    have pickedReady : picked.Realizable := by
      apply (arrayLookupWithIndex_realizable (arrayPosition target) (arrayPosition (source + count))
        (fun _ index => index.val) (arrayPosition_value (source + count)) source).onResults
      intro name
      cases name
      · exact Realizable.argument inputs false allowed
      · exact Realizable.argument inputs true allowed
    have widened := pickedReady.followedBy
      (wireOfPosition_realizable target (target + count) (by intro sizes; simp only [map_add]; omega))
      rfl (by intros; trivial)
    apply widened.withSpecification _ _ (by intros; assumption)
    intro sizes arguments accepted
    apply Fin.ext
    have chosen : (arguments false).val < MvPolynomial.eval sizes source := by
      simpa only [condition, decide_eq_true_eq] using accepted.2
    simp only [computation, wireSplice, specification_compute, spliceNames, dite_eq_left chosen]
    change ((wireOfPosition target (target + count) (by intro assignment; simp only [map_add]; omega)).compute sizes
      ⟨(fun _ => picked.compute sizes ⟨arguments, accepted⟩), trivial⟩).val = _
    rw [wireOfPosition_value]
    rfl
  · let allowed := fun sizes (arguments : ∀ name, (inputs name).Carrier sizes) =>
      computation.precondition sizes arguments ∧ condition sizes arguments = false
    have relocated := ((freshWire_realizable source target count).withArguments inputs
      (MultiTape.oneTape false) (fun _ => rfl)).withPrecondition allowed (by
        intro sizes arguments accepted
        have outside : ¬ (arguments false).val < MvPolynomial.eval sizes source := by
          simpa only [condition, decide_eq_false_iff_not] using accepted.2
        exact Nat.le_of_not_gt outside)
    apply relocated.withSpecification _ _ (by intros; assumption)
    intro sizes arguments accepted
    apply Fin.ext
    have outside : ¬ (arguments false).val < MvPolynomial.eval sizes source := by
      simpa only [condition, decide_eq_false_iff_not] using accepted.2
    simp only [computation, wireSplice, specification_compute, withPrecondition, spliceNames, dite_eq_right outside,
      withArguments, freshWire_value, MultiTape.oneTape]
    rfl

end Polytime2.Circuit
