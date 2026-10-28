import Polytime2.Circuit.Construction
import Polytime2.Computation.Branch
import Polytime2.Computation.Constant
import Polytime2.Primitives.FiniteOperations

/-! # Certified dispatch among fixed gate templates

Template choices are specialization-fixed finite data. A runtime tag selects
one template, and runtime coordinates instantiate its wire references. The
dispatch uses existing Boolean branching; its finite control and polynomial
certificate are independent of the coordinate bound.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Circuit

open EncodedDomain Polytime2.Computation

variable {Parameter : Type} [Fintype Parameter]

/-- A template selector is fixed finite data, independent of runtime sizes. -/
noncomputable def templateTagDomain (count : ℕ) : EncodedDomain Parameter :=
  (fixed (Parameter := Empty) (Equiv.refl (Fin count))).constant

private noncomputable def matchesTag {count : ℕ} (candidate : Fin count) : Computation Parameter Unit :=
  by
    classical
    exact unaryMap (templateTagDomain count) booleans (fun _ _ => True) (fun _ tag => decide (tag.val = candidate))

private theorem matchesTag_realizable {count : ℕ} (candidate : Fin count) :
    (matchesTag (Parameter := Parameter) candidate).Realizable := by
  classical
  let domain : EncodedDomain Empty := fixed (Equiv.refl (Fin count))
  have raw := (finitePredicate_realizable domain (fun tag => decide (tag = candidate))).withConstantSizes
    (Parameter := Parameter)
  exact raw.reinterpretOutput booleans (fun _ bit => bit)
    (by intros; simp [withConstantSizes, finitePredicate, finiteOperation, booleans, width])
    (by intros; simp [withConstantSizes, finitePredicate, finiteOperation, constant_encode_bits,
      booleans, fixed_encode_bits])

private def pickTemplate {arity count : ℕ} (templates : Fin count → Bool ⊕ (Fin arity × Fin arity)) :
    List (Fin count) → Fin count → Bool ⊕ (Fin arity × Fin arity)
  | [], _ => .inl false
  | candidate :: rest, selected => if selected = candidate then templates candidate
      else pickTemplate templates rest selected

private noncomputable def emitCandidates (wires : MvPolynomial Parameter ℕ) {arity count : ℕ}
    (templates : Fin count → Bool ⊕ (Fin arity × Fin arity)) (candidates : List (Fin count)) :
    Computation Parameter (Fin arity ⊕ Unit) where
  inputDomains := Sum.elim (fun _ => arrayPosition wires) (fun _ => templateTagDomain count)
  outputDomain := gateDomain wires
  precondition _ _ := True
  compute _ arguments := (pickTemplate templates candidates (arguments.val (.inr ()))).map id
    (fun pair => (arguments.val (.inl pair.1), arguments.val (.inl pair.2)))

private theorem emitCandidates_realizable (wires : MvPolynomial Parameter ℕ) {arity count : ℕ}
    (templates : Fin count → Bool ⊕ (Fin arity × Fin arity)) (candidates : List (Fin count)) :
    (emitCandidates wires templates candidates).Realizable := by
  classical
  let inputs : (Fin arity ⊕ Unit) → EncodedDomain Parameter :=
    Sum.elim (fun _ => arrayPosition wires) (fun _ => templateTagDomain count)
  have emit (template : Bool ⊕ (Fin arity × Fin arity)) :=
    (instantiateGate_realizable wires template).withArguments inputs
      ⟨Sum.inl, Sum.inl_injective⟩ (fun _ => rfl)
  induction candidates with
  | nil =>
    exact (emit (.inl false)).withSpecification (fun _ _ => True) (emitCandidates wires templates []).compute
      (by intros; trivial) (by intros; rfl)
  | cons candidate rest induction =>
    let condition := (matchesTag (Parameter := Parameter) candidate).withArguments inputs
      ⟨(fun _ => .inr ()), by intro a b equal; cases a; cases b; rfl⟩ (fun _ => rfl)
    have conditionReady : condition.Realizable := (matchesTag_realizable candidate).withArguments inputs
      ⟨(fun _ => .inr ()), by intro a b equal; cases a; cases b; rfl⟩ (fun _ => rfl)
    have selected := ((emit (templates candidate)).choose induction (fun _ => rfl) rfl).onResults inputs
      (fun _ _ => True)
      (fun name sizes arguments => match name with
        | .inl original => arguments.val original
        | .inr _ => condition.compute sizes arguments)
      (by intro sizes arguments; cases condition.compute sizes arguments <;> trivial)
      (by
        intro name
        cases name with
        | inl original => exact Realizable.argument inputs original (fun _ _ => True)
        | inr singleton => cases singleton; exact conditionReady)
    apply selected.withSpecification (fun _ _ => True) (emitCandidates wires templates (candidate :: rest)).compute
      (by intros; trivial)
    intro sizes arguments valid
    have conditionValue : condition.compute sizes ⟨arguments, valid⟩ =
        decide ((arguments (.inr ()) : Fin count) = candidate) := by
      apply Bool.eq_iff_iff.mpr
      simp only [condition, Computation.withArguments, matchesTag, Computation.unaryMap, decide_eq_true_eq]
      rfl
    simp only [Computation.onResults, conditionValue]
    dsimp only [Computation.choose, Computation.withArguments, instantiateGate, emitCandidates]
    simp only [Function.Embedding.coeFn_mk]
    by_cases equal : arguments (.inr ()) = candidate
    · rw [show decide (arguments (.inr ()) = candidate) = true from decide_eq_true equal]
      simp only [pickTemplate, ite_eq_left equal]
    · rw [show decide (arguments (.inr ()) = candidate) = false from decide_eq_false equal]
      simp only [pickTemplate, ite_eq_right equal]

/-- Choose and instantiate a gate from a fixed finite template table. -/
noncomputable def instantiateGateChoice (wires : MvPolynomial Parameter ℕ) {arity count : ℕ}
    (templates : Fin count → Bool ⊕ (Fin arity × Fin arity)) : Computation Parameter (Fin arity ⊕ Unit) where
  inputDomains := Sum.elim (fun _ => arrayPosition wires) (fun _ => templateTagDomain count)
  outputDomain := gateDomain wires
  precondition _ _ := True
  compute _ arguments := (templates (arguments.val (.inr ()))).map id
    (fun pair => (arguments.val (.inl pair.1), arguments.val (.inl pair.2)))

theorem instantiateGateChoice_realizable (wires : MvPolynomial Parameter ℕ) {arity count : ℕ}
    (templates : Fin count → Bool ⊕ (Fin arity × Fin arity)) :
    (instantiateGateChoice wires templates).Realizable := by
  have completeFor (candidates : List (Fin count)) (selected : Fin count)
      (member : selected ∈ candidates) : pickTemplate templates candidates selected = templates selected := by
    induction candidates with
    | nil => simp at member
    | cons candidate rest induction =>
      by_cases equal : selected = candidate
      · simp [pickTemplate, equal]
      · simp only [List.mem_cons] at member
        simp [pickTemplate, equal, induction (member.resolve_left equal)]
  have complete (selected : Fin count) : pickTemplate templates (List.finRange count) selected = templates selected :=
    completeFor _ selected (by simp)
  exact (emitCandidates_realizable wires templates (List.finRange count)).withSpecification
    (fun _ _ => True) (instantiateGateChoice wires templates).compute (by intros; trivial) (by
      intro sizes arguments valid
      simp only [emitCandidates, instantiateGateChoice, complete])

/-- Emit a selected fixed program, sharing the runtime tag and coordinate
family across all of its gates. The output is a finite mathematical array. -/
noncomputable def instantiateProgramChoice (wires : MvPolynomial Parameter ℕ) {arity choices count : ℕ}
    (templates : Fin choices → Fin count → Bool ⊕ (Fin arity × Fin arity)) :
    Computation Parameter (Fin arity ⊕ Unit) where
  inputDomains := Sum.elim (fun _ => arrayPosition wires) (fun _ => templateTagDomain choices)
  outputDomain := EncodedDomain.record count (fun _ => gateDomain wires)
  precondition _ _ := True
  compute _ arguments := fun index => (templates (arguments.val (.inr ())) index).map id
    (fun pair => (arguments.val (.inl pair.1), arguments.val (.inl pair.2)))

theorem instantiateProgramChoice_realizable (wires : MvPolynomial Parameter ℕ) {arity choices count : ℕ}
    (templates : Fin choices → Fin count → Bool ⊕ (Fin arity × Fin arity)) :
    (instantiateProgramChoice wires templates).Realizable :=
  Realizable.recordOutputs
    (Sum.elim (fun _ : Fin arity => arrayPosition wires) (fun _ : Unit => templateTagDomain choices))
    count (fun _ => gateDomain wires) (fun _ _ => True)
    (fun index => (instantiateGateChoice wires (fun choice => templates choice index)).compute)
    (fun index => instantiateGateChoice_realizable wires (fun choice => templates choice index))

end Polytime2.Circuit
