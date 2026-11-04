import Polytime2.CSP.QuotientProgram
import Polytime2.Arrays.PackingRead
import Polytime2.Computation.ComputedHost
import Polytime2.Computation.ComputedProjection

/-! # Dense quotient construction at its stored class count

The host input consists of the original instance, its vertex labels, and the
packed representatives. The stored representative count is promoted to a
mathematical size internally. The result retains that actual size together
with the canonical dense quotient instance.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.CSP

open EncodedDomain Polytime2.Computation

variable (L : FirstOrder.Language.{0, 0}) [L.IsRelational] [Fintype (RelationSymbol L)]

private noncomputable def labelDomain : EncodedDomain Unit :=
  (boundedIndex (MvPolynomial.X ())).arrayOfLength (MvPolynomial.X ())

private noncomputable def representativeDomain : EncodedDomain Unit :=
  boundedArray (boundedIndex (MvPolynomial.X ())) (MvPolynomial.X ())

noncomputable def quotientStoredInput : EncodedDomain Unit :=
  ((instanceDomain L).prod labelDomain).prod representativeDomain

private def rawValue (sizes : Unit ⊕ Unit → ℕ)
    (value : (instanceDomain L).Carrier (sizes ∘ Sum.inl)) :
    ((instanceDomain L).substitute (fun _ => MvPolynomial.X (.inl ()))).Carrier sizes := by
  exact cast (congrArg (instanceDomain L).Carrier
    (show (sizes ∘ Sum.inl) = SizeSubstitution.assignment (fun _ => MvPolynomial.X (.inl ())) sizes by
      funext name; cases name
      simp only [SizeSubstitution.assignment, MvPolynomial.eval_X, Function.comp_apply])) value

private def labelValue (sizes : Unit ⊕ Unit → ℕ)
    (value : labelDomain.Carrier (sizes ∘ Sum.inl)) :
    ((boundedIndex (MvPolynomial.X (.inl ()))).arrayOfLength (MvPolynomial.X (.inl ()))).Carrier sizes := by
  change Fin (MvPolynomial.eval sizes (MvPolynomial.X (.inl ()))) →
    Fin (MvPolynomial.eval sizes (MvPolynomial.X (.inl ())))
  exact fun index => ⟨(value ⟨index.val, by
    simpa only [MvPolynomial.eval_X, Function.comp_apply] using index.isLt⟩).val, by
      simpa only [MvPolynomial.eval_X, Function.comp_apply] using
        (value ⟨index.val, by simpa only [MvPolynomial.eval_X, Function.comp_apply] using index.isLt⟩).isLt⟩

private def indexValue (sizes : Unit ⊕ Unit → ℕ)
    (value : (boundedIndex (MvPolynomial.X ())).Carrier (sizes ∘ Sum.inl)) :
    (boundedIndex (MvPolynomial.X (.inl ()))).Carrier sizes := by
  change Fin (MvPolynomial.eval sizes (MvPolynomial.X (.inl ())))
  exact ⟨value.val, by simpa only [MvPolynomial.eval_X, Function.comp_apply] using value.isLt⟩

private theorem bitsOfNat_width {first second : ℕ} (same : first = second) (value : ℕ) :
    ArrayEncoding.bits (BitVec.ofNat first value) = ArrayEncoding.bits (BitVec.ofNat second value) := by
  cases same
  rfl

private noncomputable def callee : Computation (Unit ⊕ Unit) Unit where
  inputDomains _ := (quotientStoredInput L).renameParameters Sum.inl
  outputDomain := (instanceDomain L).substitute (fun _ => MvPolynomial.X (.inr ()))
  precondition sizes arguments := (arguments ()).2.1.val = sizes (.inr ())
  compute sizes arguments := by
    classical
    let original : (quotientStoredInput L).Carrier (sizes ∘ Sum.inl) := arguments.val ()
    let values : ∀ name, (quotientInstanceInputs L
        (MvPolynomial.X (.inl ()) : MvPolynomial (Unit ⊕ Unit) ℕ)
        (MvPolynomial.X (.inr ())) name).Carrier sizes := fun name => match name with
      | none => rawValue L sizes original.1.1
      | some false => labelValue sizes original.1.2
      | some true => fun index => indexValue sizes (original.2.2 ⟨index.val, by
          rw [arguments.property]
          simpa only [MvPolynomial.eval_X] using index.isLt⟩)
    change Instance L (MvPolynomial.eval sizes (MvPolynomial.X (.inr ())))
    exact instanceImage (values none) (values (some false)) (values (some true))

private theorem callee_realizable : (callee L).Realizable := by
  let computation := callee L
  let left : MvPolynomial (Unit ⊕ Unit) ℕ := MvPolynomial.X (.inl ())
  let right : MvPolynomial (Unit ⊕ Unit) ℕ := MvPolynomial.X (.inr ())
  have viewed := (renamedPairView_realizable ((instanceDomain L).prod labelDomain)
    representativeDomain (Sum.inl : Unit → Unit ⊕ Unit)).withPrecondition computation.precondition
    (by intros; trivial)
  have first := viewed.fst.followedBy
    (renamedPairView_realizable (instanceDomain L) labelDomain (Sum.inl : Unit → Unit ⊕ Unit))
    rfl (by intros; trivial)
  have raw := first.fst.reinterpretOutput ((instanceDomain L).substitute (fun _ => left))
    (rawValue L) (by
      intro sizes
      simp only [substitute_width, renameParameters_width]
      congr 1
      funext name
      cases name
      exact MvPolynomial.eval_X _) (by
      intro sizes value
      rw [substitute_encode_bits, renameParameters_bits]
      simpa only [rawValue] using encode_bits_cast_sizes (instanceDomain L)
        (show (sizes ∘ Sum.inl) = SizeSubstitution.assignment (fun _ => left) sizes by
          funext name; cases name
          simp only [SizeSubstitution.assignment, left, MvPolynomial.eval_X, Function.comp_apply]) value |>.symm)
  have labels := first.snd.reinterpretOutput ((boundedIndex left).arrayOfLength left)
    labelValue (by
      intro sizes
      simp [EncodedDomain.width, labelDomain, left, boundedIndex, boundedIndexOfWidth]) (by
      intro sizes value
      change (Fin (MvPolynomial.eval (sizes ∘ Sum.inl) (MvPolynomial.X ())) →
        Fin (MvPolynomial.eval (sizes ∘ Sum.inl) (MvPolynomial.X ()))) at value
      rw [renameParameters_bits]
      change ArrayEncoding.bits (((boundedIndex left).arrayOfLength left).encode sizes (labelValue sizes value)) =
        ArrayEncoding.bits (((boundedIndex (MvPolynomial.X ())).arrayOfLength (MvPolynomial.X ())).encode
          (sizes ∘ Sum.inl) value)
      simp only [arrayOfLength_encode_bits, ArrayEncoding.bits_encode, labelValue,
        boundedIndex, boundedIndexOfWidth, BitVec.ofNatLT_eq_ofNat]
      simp only [left, id_eq, Fin.val_mk]
      have same : MvPolynomial.eval sizes (MvPolynomial.X (.inl ()) : MvPolynomial (Unit ⊕ Unit) ℕ) =
          MvPolynomial.eval (sizes ∘ Sum.inl) (MvPolynomial.X ()) := by
        simp only [MvPolynomial.eval_X, Function.comp_apply]
      apply congrArg List.flatten
      calc
        _ = List.ofFn (fun index : Fin (MvPolynomial.eval sizes (MvPolynomial.X (.inl ()))) =>
            ArrayEncoding.bits (BitVec.ofNat (MvPolynomial.eval (sizes ∘ Sum.inl) (MvPolynomial.X ()))
              (value (Fin.cast same index)).val)) := by
          apply congrArg List.ofFn
          funext index
          exact bitsOfNat_width same _
        _ = _ := (List.ofFn_congr same.symm
          (fun index : Fin (MvPolynomial.eval (sizes ∘ Sum.inl) (MvPolynomial.X ())) =>
            ArrayEncoding.bits (BitVec.ofNat (MvPolynomial.eval (sizes ∘ Sum.inl) (MvPolynomial.X ()))
              (value index).val))).symm)
  have representatives := viewed.snd.followedBy
    (boundedArrayAtLength_realizable (boundedIndex (MvPolynomial.X ())) (MvPolynomial.X ())
      Sum.inl right (boundedIndex left) (fun _ => True) (fun sizes _ value => indexValue sizes value)
      (by intro sizes valid value
          change Fin (MvPolynomial.eval (sizes ∘ Sum.inl) (MvPolynomial.X ())) at value
          simp only [indexValue, left, boundedIndex, boundedIndexOfWidth, BitVec.ofNatLT_eq_ofNat,
            id_eq]
          have same : MvPolynomial.eval sizes (MvPolynomial.X (.inl ()) : MvPolynomial (Unit ⊕ Unit) ℕ) =
              MvPolynomial.eval (sizes ∘ Sum.inl) (MvPolynomial.X ()) := by
            simp only [MvPolynomial.eval_X, Function.comp_apply]
          exact bitsOfNat_width same value.val)) rfl
    (by
      intro sizes arguments valid
      change (arguments ()).2.1.val = sizes (.inr ()) at valid
      change (arguments ()).2.1.val = MvPolynomial.eval sizes right ∧ True
      simpa only [right, MvPolynomial.eval_X] using And.intro valid True.intro)
  have complete := (quotientInstanceProgram_realizable L left right).onResults
    computation.inputDomains computation.precondition
    (fun name sizes arguments => match name with
      | none => rawValue L sizes (arguments.val ()).1.1
      | some false => labelValue sizes (arguments.val ()).1.2
      | some true => fun index => indexValue sizes ((arguments.val ()).2.2
          (Fin.cast (arguments.property.trans (MvPolynomial.eval_X _).symm).symm index)))
    (by intros; trivial) (by
      intro name
      cases name with
      | none => exact raw
      | some choice =>
        cases choice
        · exact labels
        · exact representatives)
  apply complete.withSpecification computation.precondition computation.compute (by intros; assumption)
  intro sizes arguments valid
  simp only [onResults, quotientInstanceProgram, instanceTabulate, computation, callee]
  apply (instanceTablesEquiv L (MvPolynomial.eval sizes right)).injective
  simp only [id_eq]
  rw [Equiv.apply_symm_apply, instanceImage_tables]
  simp only [left, right, indexValue, id_eq, SizeSubstitution.assignment, Fin.cast]
  funext symbol tuple
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]

private noncomputable def classBounds : Unit → MvPolynomial Unit ℕ := fun _ => MvPolynomial.X ()

private def counts (sizes : Unit → ℕ) (value : (quotientStoredInput L).Carrier sizes) :
    (computedSizeDomain classBounds).Carrier sizes := fun _ => value.2.1

private theorem count_realizable (name : Unit) :
    (unaryMap (quotientStoredInput L) (boundedUnary (classBounds name)) (fun _ _ => True)
      (fun sizes value => counts L sizes value.val name)).Realizable :=
  (pairProjection_realizable ((instanceDomain L).prod labelDomain) representativeDomain true).followedBy
    (boundedArrayCount_realizable (boundedIndex (MvPolynomial.X ())) (MvPolynomial.X ())) rfl
    (by intros; trivial)

private theorem callee_output : (callee L).outputDomain =
    (instanceDomain L).renameParameters (Sum.inr : Unit → Unit ⊕ Unit) := by
  dsimp only [callee]
  have names : (fun _ : Unit => (MvPolynomial.X (.inr ()) : MvPolynomial (Unit ⊕ Unit) ℕ)) =
      (fun name => MvPolynomial.X (Sum.inr name)) := by
    funext name
    cases name
    rfl
  rw [names, EncodedDomain.substitute_X]

private noncomputable def namedCallee : Computation (Unit ⊕ Unit) Unit :=
  (callee L).followedBy (copy ((instanceDomain L).renameParameters (Sum.inr : Unit → Unit ⊕ Unit)))
    (callee_output L).symm (by intros; trivial)

private theorem namedCallee_realizable : (namedCallee L).Realizable :=
  (callee_realizable L).followedBy
    (copy_realizable ((instanceDomain L).renameParameters (Sum.inr : Unit → Unit ⊕ Unit)))
    (callee_output L).symm (by intros; trivial)

private noncomputable def quotientCall : Computation Unit Unit :=
  ((namedCallee L).atComputedHostInput classBounds (quotientStoredInput L) (counts L) rfl).withPrecondition
    (fun _ _ => True) (by intros; rfl)

private theorem quotientCall_realizable : (quotientCall L).Realizable :=
  ((namedCallee_realizable L).atComputedHostInput classBounds (quotientStoredInput L) (counts L) rfl
    (count_realizable L)).withPrecondition _ (by intros; rfl)

/-- Construct the quotient using the actual representative count, without
requiring a separate class-count argument from the caller. The result retains
only that count and its instance; original working sizes are discarded. -/
noncomputable def quotientAtCount : Computation Unit Unit :=
  (quotientCall L).followedBy (projectComputedFrame classBounds (instanceDomain L))
    rfl (by intros; trivial)

theorem quotientAtCount_realizable : (quotientAtCount L).Realizable :=
  (quotientCall_realizable L).followedBy (projectComputedFrame_realizable classBounds (instanceDomain L))
    rfl (by intros; trivial)

/-- The retained class size is the stored count, rather than its capacity. -/
theorem quotientAtCount_count (sizes : Unit → ℕ)
    (input : (quotientStoredInput L).Carrier sizes) :
    (((quotientAtCount L).compute sizes ⟨fun _ => input, trivial⟩).1 ()).val = input.2.1.val := rfl

/-- Mathematical relation images of the stored data, expressed on ordinary
finite variable sets. Polynomial evaluation casts stay inside this adapter. -/
@[instance_reducible]
noncomputable def storedInstanceImage (sizes : Unit → ℕ)
    (input : (quotientStoredInput L).Carrier sizes) : Instance L input.2.1.val :=
  instanceImage input.1.1
    (fun vertex => ⟨(input.1.2 ⟨vertex.val, by
      simpa only [MvPolynomial.eval_X] using vertex.isLt⟩).val, by
        simpa only [MvPolynomial.eval_X] using
          (input.1.2 ⟨vertex.val, by simpa only [MvPolynomial.eval_X] using vertex.isLt⟩).isLt⟩)
    (fun vertex => ⟨(input.2.2 vertex).val, by
      simpa only [MvPolynomial.eval_X] using (input.2.2 vertex).isLt⟩)

/-- Computed-size preparation and frame projection preserve the mathematical
relation images exactly, including the empty and nullary cases. -/
theorem quotientAtCount_compute (sizes : Unit → ℕ)
    (input : (quotientStoredInput L).Carrier sizes) :
    ((quotientAtCount L).compute sizes ⟨fun _ => input, trivial⟩).2 = storedInstanceImage L sizes input := by
  classical
  obtain ⟨vertices, rfl⟩ : ∃ vertices, sizes = fun _ : Unit => vertices := by
    exact ⟨sizes (), funext (fun name => by cases name; rfl)⟩
  let actual := computedSizeAssignment (extendedSizeBounds classBounds) (fun _ : Unit => vertices)
    (extendedSizeValues classBounds (fun _ : Unit => vertices) (counts L (fun _ => vertices) input))
  dsimp only [quotientAtCount, quotientCall, namedCallee, callee, followedBy, withPrecondition,
    atComputedHostInput, projectComputedFrame, unaryMap, copy, storedInstanceImage]
  apply eq_of_heq
  simp only [eqRec_heq_iff, cast_eq, id_eq]
  apply instanceImage_heq
  · exact MvPolynomial.eval_X (f := actual) (.inl ())
  · exact MvPolynomial.eval_X (f := actual) (.inr ())
  · exact cast_heq _ _
  · intro leftIndex rightIndex same
    change (input.1.2 _).val = (input.1.2 _).val
    apply congrArg (fun index => (input.1.2 index).val)
    exact Fin.ext same
  · intro leftIndex rightIndex same
    change (input.2.2 _).val = (input.2.2 _).val
    apply congrArg (fun index => (input.2.2 index).val)
    exact Fin.ext same

end Polytime2.CSP
