import Polytime2.Complexity.CookLevin.WordAlias
import Polytime2.Arrays.Tabulate
import Polytime2.Arrays.FlattenRecords

/-! # Uniform initial-word alias arrays

Tabulation visits every window cell and every one-hot cell bit, then flattens
the rows without changing their canonical words.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Complexity.CookLevin

open Circuit EncodedDomain Polytime2.Computation

variable {Symbol State : Type} [Inhabited Symbol] [Fintype Symbol] [Fintype State]

/-- Number of one-hot inputs to the bounded configuration circuit. -/
noncomputable def wordConfigurationWidth (Symbol State : Type) [Fintype Symbol] [Fintype State] :
    MvPolynomial Bool ℕ := wordPositions * MvPolynomial.C (cellWidth Symbol State)

private noncomputable def cellAliases (entry : State) (letters : Letter ↪ Symbol) : Computation Bool Unit where
  inputDomains _ := arrayPosition wordPositions
  outputDomain := record (cellWidth Symbol State) (fun _ => arrayPosition wordPreparedWires)
  precondition _ _ := True
  compute sizes arguments bit := (wordInitialAlias entry letters bit).compute sizes arguments

private theorem cellAliases_realizable (entry : State) (letters : Letter ↪ Symbol) :
    (cellAliases entry letters).Realizable := by
  apply Realizable.recordOutputs
  intro bit
  exact wordInitialAlias_realizable entry letters bit

private noncomputable def aliasRows (entry : State) (letters : Letter ↪ Symbol) : Computation Bool Empty :=
  arrayTabulate Empty.elim (cellAliases entry letters).outputDomain wordPositions
    (fun sizes _ cell => (cellAliases entry letters).compute sizes ⟨(fun _ => cell), trivial⟩)

private theorem aliasRows_realizable (entry : State) (letters : Letter ↪ Symbol) :
    (aliasRows entry letters).Realizable := by
  apply arrayTabulate_realizable
  let inputs : Empty ⊕ Unit → EncodedDomain Bool :=
    Sum.elim Empty.elim (fun _ => arrayPosition wordPositions)
  have selected := (cellAliases_realizable entry letters).onArguments inputs (fun _ _ => True)
    (fun _ => .inr ()) (by intros; rfl) (by intros; trivial)
  exact selected.withSpecification (fun _ _ => True) _ (by intros; trivial) (by intros; rfl)

/-- All initial configuration inputs, as actual aliases to word bits and
constant gates, in the canonical row-major coordinate order. -/
noncomputable def wordAliases (entry : State) (letters : Letter ↪ Symbol) : Computation Bool Empty :=
  (aliasRows entry letters).followedBy
    (arrayFlattenRecords (arrayPosition wordPreparedWires) (cellWidth Symbol State) wordPositions)
    rfl (by intros; trivial)

theorem wordAliases_realizable (entry : State) (letters : Letter ↪ Symbol) :
    (wordAliases entry letters).Realizable :=
  (aliasRows_realizable entry letters).followedBy
    (arrayFlattenRecords_realizable (arrayPosition wordPreparedWires) (cellWidth Symbol State) wordPositions)
    rfl (by intros; trivial)

/-- The entire flattened alias array has the certified scalar alias formula. -/
theorem wordAliases_value (entry : State) (letters : Letter ↪ Symbol) (sizes : Bool → ℕ)
    (arguments : {arguments : (wordAliases entry letters).Arguments sizes // True})
    (index : Fin (MvPolynomial.eval sizes (wordConfigurationWidth Symbol State))) :
    let coordinate : Fin (MvPolynomial.eval sizes wordPositions) × Fin (cellWidth Symbol State) :=
      finProdFinEquiv.symm (index.cast (by simp [wordConfigurationWidth]))
    ((wordAliases entry letters).compute sizes arguments index).val =
      initialAliasValue entry letters coordinate.2 sizes coordinate.1.val := by
  let coordinate : Fin (MvPolynomial.eval sizes wordPositions) × Fin (cellWidth Symbol State) :=
    finProdFinEquiv.symm (index.cast (by simp [wordConfigurationWidth]))
  change ((wordInitialAlias entry letters coordinate.2).compute sizes
    ⟨(fun _ => coordinate.1), trivial⟩).val = _
  exact wordInitialAlias_value entry letters _ sizes _

theorem wordConfigurationWidth_eval (sizes : Bool → ℕ) :
    MvPolynomial.eval sizes (wordConfigurationWidth Symbol State) =
      (2 * (2 * sizes false) + 1) * cellWidth Symbol State := by
  simp only [wordConfigurationWidth, wordPositions, map_mul, map_add, map_ofNat, map_one,
    MvPolynomial.eval_X, MvPolynomial.eval_C]
  ring

/-- The complete array agrees pointwise with mathematical word-input wiring. -/
theorem wordAliases_correct (entry : State) (letters : Letter ↪ Symbol) (sizes : Bool → ℕ)
    (arguments : {arguments : (wordAliases entry letters).Arguments sizes // True})
    (output : Fin ((2 * (2 * sizes false) + 1) * cellWidth Symbol State)) :
    ((wordAliases entry letters).compute sizes arguments
      (output.cast (wordConfigurationWidth_eval sizes).symm)).val =
      (wiringLayer (sizes true * Fintype.card Letter)
        (initialChoices (2 * sizes false) (sizes true) entry letters)).2 output := by
  rw [wordAliases_value]
  let coordinate : Fin (MvPolynomial.eval sizes wordPositions) × Fin (cellWidth Symbol State) :=
    finProdFinEquiv.symm ((output.cast (wordConfigurationWidth_eval sizes).symm).cast
      (by simp [wordConfigurationWidth]))
  have bitEqual : coordinate.2 = (finProdFinEquiv.symm output).2 := Fin.ext rfl
  change initialAliasValue entry letters coordinate.2 sizes coordinate.1.val = _
  rw [bitEqual]
  change initialAliasValue entry letters (finProdFinEquiv.symm output).2 sizes
    (finProdFinEquiv.symm output).1.val = _
  have correct := initialAliasValue_wiring entry letters (finProdFinEquiv.symm output).2 sizes
    (finProdFinEquiv.symm output).1
  simpa only [Prod.mk.eta, Equiv.apply_symm_apply] using correct

end Polytime2.Complexity.CookLevin
