import Polytime2.Complexity.CookLevin.WordCellChoice
import Polytime2.Computation.Conditional

/-! # Certified initial-word alias wires

Each one-hot configuration bit names an external word bit or one of the two
constant gates. The mathematical sizes are time (false) and word length (true).
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Complexity.CookLevin

open Circuit EncodedDomain Polytime2.Computation

variable {Symbol State : Type} [Inhabited Symbol] [Fintype Symbol] [Fintype State]

private theorem letterChoice_inside (entry : State) (letters : Letter ↪ Symbol)
    (bit : Fin (cellWidth Symbol State)) (inside head : Bool) (letter : Fin (Fintype.card Letter))
    (chosen : initialLetterChoice entry letters bit inside head = .inr letter) : inside = true := by
  cases inside
  · simp [initialLetterChoice] at chosen
  · rfl

/-- Natural wire named by one initial configuration bit. -/
noncomputable def initialAliasValue (entry : State) (letters : Letter ↪ Symbol)
    (bit : Fin (cellWidth Symbol State)) (sizes : Bool → ℕ) (cell : ℕ) : ℕ :=
  match initialLetterChoice entry letters bit
      (decide (2 * sizes false ≤ cell ∧ cell < 2 * sizes false + sizes true))
      (decide (cell = 2 * sizes false)) with
  | .inl value => sizes true * Fintype.card Letter + if value then 1 else 0
  | .inr letter => (cell - 2 * sizes false) * Fintype.card Letter + letter.val

private theorem initialAliasValue_fits (entry : State) (letters : Letter ↪ Symbol)
    (bit : Fin (cellWidth Symbol State)) (sizes : Bool → ℕ)
    (cell : Fin (MvPolynomial.eval sizes wordPositions)) :
    initialAliasValue entry letters bit sizes cell.val < MvPolynomial.eval sizes wordPreparedWires := by
  unfold initialAliasValue
  split
  · rename_i value chosen
    simp only [wordPreparedWires, map_add, map_mul, map_ofNat, MvPolynomial.eval_X, MvPolynomial.eval_C]
    cases value <;> simp <;> omega
  · rename_i letter chosen
    have inside := of_decide_eq_true (letterChoice_inside entry letters bit _ _ letter chosen)
    simpa only [wordLetterWire_value] using
      ((wordLetterWire letter).compute sizes ⟨(fun _ => cell), inside⟩).isLt

/-- The alias formula agrees with the original two-constant input layer. -/
theorem initialAliasValue_wiring (entry : State) (letters : Letter ↪ Symbol)
    (bit : Fin (cellWidth Symbol State)) (sizes : Bool → ℕ)
    (cell : Fin (2 * (2 * sizes false) + 1)) :
    initialAliasValue entry letters bit sizes cell.val =
      (wiringLayer (sizes true * Fintype.card Letter)
        (initialChoices (2 * sizes false) (sizes true) entry letters)).2 (finProdFinEquiv (cell, bit)) := by
  classical
  have insideSame : (0 ≤ (cell.val : ℤ) - 2 * sizes false ∧
      (cell.val : ℤ) - 2 * sizes false < sizes true) ↔
      2 * sizes false ≤ cell.val ∧ cell.val < 2 * sizes false + sizes true := by omega
  have headSame : ((cell.val : ℤ) - 2 * sizes false = 0) ↔ cell.val = 2 * sizes false := by omega
  have positionNat : ((cell.val : ℤ) - 2 * sizes false).toNat = cell.val - 2 * sizes false := by omega
  simp only [initialAliasValue, initialLetterChoice, wiringLayer, initialChoices,
    Equiv.symm_apply_apply, windowPosition, Nat.cast_mul, Nat.cast_ofNat,
    insideSame, headSame, decide_eq_true_eq, positionNat]
  split_ifs <;> simp_all [finProdFinEquiv, Nat.mul_comm, Nat.add_comm]

/-- Initial input preparation returns an actual reference, with no padding or
invalid case exposed to callers. -/
noncomputable def wordInitialAlias (entry : State) (letters : Letter ↪ Symbol)
    (bit : Fin (cellWidth Symbol State)) : Computation Bool Unit :=
  specification (fun _ => arrayPosition wordPositions) (arrayPosition wordPreparedWires) (fun _ _ => True)
    (fun sizes arguments => ⟨initialAliasValue entry letters bit sizes (arguments.val ()).val,
      initialAliasValue_fits entry letters bit sizes (arguments.val ())⟩)

theorem wordInitialAlias_value (entry : State) (letters : Letter ↪ Symbol)
    (bit : Fin (cellWidth Symbol State)) (sizes : Bool → ℕ)
    (arguments : {arguments : (wordInitialAlias entry letters bit).Arguments sizes // True}) :
    ((wordInitialAlias entry letters bit).compute sizes arguments).val =
      initialAliasValue entry letters bit sizes (arguments.val ()).val := by
  simp only [wordInitialAlias, specification_compute]

theorem wordInitialAlias_realizable (entry : State) (letters : Letter ↪ Symbol)
    (bit : Fin (cellWidth Symbol State)) : (wordInitialAlias entry letters bit).Realizable := by
  let computation := wordInitialAlias entry letters bit
  let inside := fun sizes (arguments : computation.Arguments sizes) =>
    decide (2 * sizes false ≤ (arguments ()).val ∧ (arguments ()).val < 2 * sizes false + sizes true)
  let head := fun sizes (arguments : computation.Arguments sizes) => decide ((arguments ()).val = 2 * sizes false)
  have leaves (insideFlag headFlag : Bool) :
      (computation.withPrecondition
        (fun sizes arguments => inside sizes arguments = insideFlag ∧ head sizes arguments = headFlag)
        (by intros; trivial)).Realizable := by
    let allowed := fun sizes (arguments : computation.Arguments sizes) =>
      inside sizes arguments = insideFlag ∧ head sizes arguments = headFlag
    cases chosen : initialLetterChoice entry letters bit insideFlag headFlag with
    | inl value =>
      let coordinate : MvPolynomial Bool ℕ := MvPolynomial.X true * MvPolynomial.C (Fintype.card Letter) +
        MvPolynomial.C (if value then 1 else 0)
      have constant := (wirePolynomial_realizable coordinate wordPreparedWires).onResults
        computation.inputDomains allowed (fun empty => nomatch empty) (by
          intro sizes arguments
          change MvPolynomial.eval sizes coordinate < MvPolynomial.eval sizes wordPreparedWires
          simp only [coordinate, wordPreparedWires, map_add, map_mul, MvPolynomial.eval_X, MvPolynomial.eval_C, map_ofNat]
          cases value <;> simp <;> omega) (fun empty => nomatch empty)
      apply constant.withSpecification _ _ (by intros; assumption)
      intro sizes arguments accepted
      apply Fin.ext
      have choiceEqual : initialLetterChoice entry letters bit (inside sizes arguments) (head sizes arguments) = .inl value := by
        rw [accepted.1, accepted.2, chosen]
      dsimp only [inside, head] at choiceEqual
      simp only [computation, wordInitialAlias, specification_compute, initialAliasValue, choiceEqual]
      change MvPolynomial.eval sizes coordinate = _
      simp only [coordinate, map_add, map_mul, MvPolynomial.eval_X, MvPolynomial.eval_C]
    | inr letter =>
      have insideFlagTrue := letterChoice_inside entry letters bit insideFlag headFlag letter chosen
      have reference := (wordLetterWire_realizable letter).withPrecondition allowed (by
        intro sizes arguments accepted
        change 2 * sizes false ≤ (arguments ()).val ∧ (arguments ()).val < 2 * sizes false + sizes true
        exact of_decide_eq_true (accepted.1.trans insideFlagTrue))
      apply reference.withSpecification _ _ (by intros; assumption)
      intro sizes arguments accepted
      apply Fin.ext
      have choiceEqual : initialLetterChoice entry letters bit (inside sizes arguments) (head sizes arguments) = .inr letter := by
        rw [accepted.1, accepted.2, chosen]
      dsimp only [inside, head] at choiceEqual
      simp only [computation, wordInitialAlias, specification_compute, initialAliasValue, choiceEqual,
        withPrecondition, wordLetterWire_value]
  have byHead (insideFlag : Bool) :
      (computation.withPrecondition
        (fun sizes arguments => computation.precondition sizes arguments ∧ inside sizes arguments = insideFlag)
        (fun _ _ accepted => accepted.1)).Realizable := by
    apply Realizable.ofCases (computation := computation.withPrecondition
      (fun sizes arguments => computation.precondition sizes arguments ∧ inside sizes arguments = insideFlag)
      (fun _ _ accepted => accepted.1)) head
    · exact wordCellFlags_realizable.snd.withPrecondition _ (by intros; trivial)
    · exact (leaves insideFlag true).withSpecification _ _
        (by intro sizes arguments accepted; exact ⟨accepted.1.2, accepted.2⟩) (by intros; rfl)
    · exact (leaves insideFlag false).withSpecification _ _
        (by intro sizes arguments accepted; exact ⟨accepted.1.2, accepted.2⟩) (by intros; rfl)
  apply Realizable.ofCases inside
  · exact wordCellFlags_realizable.fst
  · exact byHead true
  · exact byHead false

end Polytime2.Complexity.CookLevin
