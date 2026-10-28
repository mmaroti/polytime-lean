import Polytime2.Circuit.Observe

/-! # Composing shared-wire circuits

A callee's input wires may refer to any earlier caller wires. Its fresh gates
are relocated after the caller's program, retaining every shared reference.
The gate count is additive. This supplies the input-preparation composition
needed by the bounded-verifier circuit constructor.
-/

namespace Polytime2.Circuit

def Gate.rename (names : ℕ → ℕ) (gate : Gate) : Gate :=
  match gate with
  | .inl value => .inl value
  | .inr (left, right) => .inr (names left, names right)

theorem Gate.rename_eval (names : ℕ → ℕ) (gate : Gate) (values : ℕ → Bool) :
    (gate.rename names).eval values = gate.eval (values ∘ names) := by
  cases gate <;> rfl

theorem Gate.rename_valid {gate : Gate} {source target : ℕ} (valid : gate.Valid source)
    (names : ℕ → ℕ) (bounded : ∀ wire < source, names wire < target) :
    (gate.rename names).Valid target := by
  cases gate with
  | inl value => trivial
  | inr operands => exact ⟨bounded _ valid.1, bounded _ valid.2⟩

/-- Map existing inputs to caller wires and fresh gates to consecutive slots. -/
def spliceNames (source target : ℕ) (inputs : Fin source → ℕ) : ℕ → ℕ :=
  fun wire => if bounded : wire < source then inputs ⟨wire, bounded⟩ else target + (wire - source)

theorem spliceNames_bound {source target : ℕ} (inputs : Fin source → ℕ)
    (bounded : ∀ index, inputs index < target) (count : ℕ) :
    ∀ wire < source + count, spliceNames source target inputs wire < target + count := by
  intro wire bound
  unfold spliceNames
  split
  · have original := bounded ⟨wire, by assumption⟩
    omega
  · omega

theorem spliceNames_fresh (source target : ℕ) (inputs : Fin source → ℕ) (index : ℕ) :
    spliceNames source target inputs (source + index) = target + index := by
  simp [spliceNames]

theorem WellFormed.rename {gates : List Gate} {source target : ℕ}
    (valid : WellFormed source gates) (names : ℕ → ℕ)
    (bounded : ∀ wire < source, names wire < target)
    (fresh : ∀ index, names (source + index) = target + index) :
    WellFormed target (gates.map (Gate.rename names)) := by
  induction gates generalizing source target with
  | nil => trivial
  | cons gate rest induction =>
    refine ⟨gate.rename_valid valid.1 names bounded, induction valid.2 ?_ ?_⟩
    · intro wire bound
      by_cases before : wire < source
      · exact Nat.lt_trans (bounded wire before) (by omega)
      · have equal : wire = source := by omega
        subst wire
        simpa using show names (source + 0) < target + 1 by rw [fresh]; omega
    · intro index
      simpa only [Nat.add_assoc, Nat.add_comm 1] using fresh (index + 1)

/-- Relocation simulates the source on every defined wire. Input aliases are
allowed; only fresh gate slots must be new. -/
theorem run_rename {gates : List Gate} {source target : ℕ}
    (valid : WellFormed source gates) (names : ℕ → ℕ)
    (bounded : ∀ wire < source, names wire < target)
    (fresh : ∀ index, names (source + index) = target + index)
    (sourceValues targetValues : ℕ → Bool)
    (agree : ∀ wire < source, sourceValues wire = targetValues (names wire)) :
    ∀ wire < source + gates.length,
      run source gates sourceValues wire =
        run target (gates.map (Gate.rename names)) targetValues (names wire) := by
  induction gates generalizing source target sourceValues targetValues with
  | nil => exact agree
  | cons gate rest induction =>
    have nextBound : ∀ wire < source + 1, names wire < target + 1 := by
      intro wire bound
      by_cases before : wire < source
      · exact Nat.lt_trans (bounded wire before) (by omega)
      · have equal : wire = source := by omega
        subst wire
        simpa using show names (source + 0) < target + 1 by rw [fresh]; omega
    have nextFresh : ∀ index, names (source + 1 + index) = target + 1 + index := by
      intro index
      simpa only [Nat.add_assoc, Nat.add_comm 1] using fresh (index + 1)
    have gateEqual : gate.eval sourceValues = (gate.rename names).eval targetValues := by
      rw [Gate.rename_eval]
      cases gate with
      | inl value => rfl
      | inr operands =>
        exact congrArg₂ (fun a b => !(a && b)) (agree _ valid.1.1) (agree _ valid.1.2)
    have nextAgree : ∀ wire < source + 1,
        Function.update sourceValues source (gate.eval sourceValues) wire =
          Function.update targetValues target ((gate.rename names).eval targetValues) (names wire) := by
      intro wire bound
      by_cases equal : wire = source
      · subst wire
        have headEqual : names source = target := by simpa using fresh 0
        simp only [headEqual, Function.update_self, gateEqual]
      · have before : wire < source := by omega
        rw [Function.update_of_ne equal,
          Function.update_of_ne (Nat.ne_of_lt (bounded wire before))]
        exact agree wire before
    intro wire bound
    apply induction valid.2 nextBound nextFresh _ _ nextAgree wire
    simp only [List.length_cons] at bound
    omega

/-- Compose a prepared layer with a circuit on its result wires. -/
def composeLayer {width : ℕ} (inputs : ℕ) (prepared : Layer width) (callee : Network) : Network :=
  let names := spliceNames width (inputs + prepared.1.length) prepared.2
  (prepared.1 ++ callee.1.map (Gate.rename names), names callee.2)

theorem composeLayer_length {width : ℕ} (inputs : ℕ) (prepared : Layer width) (callee : Network) :
    (composeLayer inputs prepared callee).1.length = prepared.1.length + callee.1.length := by
  simp [composeLayer]

theorem composeLayer_valid {width inputs : ℕ} {prepared : Layer width} {callee : Network}
    (preparedValid : WellFormed inputs prepared.1)
    (outputsValid : ∀ index, prepared.2 index < inputs + prepared.1.length)
    (calleeValid : Valid width callee) : Valid inputs (composeLayer inputs prepared callee) := by
  have bounded := spliceNames_bound prepared.2 outputsValid
  refine ⟨(wellFormed_append _ _ _).mpr ⟨preparedValid, ?_⟩, ?_⟩
  · exact calleeValid.1.rename _ (by simpa using bounded 0)
      (spliceNames_fresh width (inputs + prepared.1.length) prepared.2)
  · simpa only [composeLayer, List.length_append, List.length_map, Nat.add_assoc] using
      bounded callee.1.length callee.2 calleeValid.2

theorem composeLayer_correct {width inputs : ℕ} (prepared : Layer width) (callee : Network)
    (outputsValid : ∀ index, prepared.2 index < inputs + prepared.1.length)
    (calleeValid : Valid width callee) (assignment : Fin inputs → Bool) :
    evaluate inputs (composeLayer inputs prepared callee) assignment =
      evaluate width callee (fun index => run inputs prepared.1 (inputValues assignment) (prepared.2 index)) := by
  let names := spliceNames width (inputs + prepared.1.length) prepared.2
  have bounded : ∀ wire < width, names wire < inputs + prepared.1.length := by
    simpa using spliceNames_bound prepared.2 outputsValid 0
  have agreement : ∀ wire < width, inputValues
      (fun index => run inputs prepared.1 (inputValues assignment) (prepared.2 index)) wire =
        run inputs prepared.1 (inputValues assignment) (names wire) := by
    intro wire bound
    simp [inputValues, names, spliceNames, bound]
  have simulation := run_rename calleeValid.1 names bounded
    (spliceNames_fresh width (inputs + prepared.1.length) prepared.2) _ _ agreement callee.2 calleeValid.2
  change run inputs (prepared.1 ++ _) (inputValues assignment) (names callee.2) = _
  rw [run_append]
  exact simulation.symm

end Polytime2.Circuit
