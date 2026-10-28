import Polytime2.Complexity.CookLevin.Acceptance
import Polytime2.Circuit.Wiring

/-! # Symbolic word inputs for bounded verifier circuits

An external letter is represented by one bit per possible letter. Every
initial marked-cell bit is an input bit or a constant. The initial layer
therefore needs only two constant gates, independently of the word length
and the simulation window. The choice of a preimage under `letters` is fixed
finite alphabet data, not an input-dependent algorithmic choice.
-/

namespace Polytime2.Complexity.CookLevin

open Turing Circuit

attribute [local instance] Classical.propDecidable

variable {Symbol State : Type} [Inhabited Symbol] [Inhabited State]
variable [Fintype Symbol] [Fintype State]

/-- One-hot external word bits, with ordinary finite word coordinates. -/
noncomputable def encodeWordBits {length : ℕ} (word : Fin length → Letter) :
    Fin (length * Fintype.card Letter) → Bool := by
  classical
  exact fun index => decide (word (finProdFinEquiv.symm index).1 =
    (Fintype.equivFin Letter).symm (finProdFinEquiv.symm index).2)

/-- Equal word lengths change only the proof attached to bit coordinates. -/
theorem encodeWordBits_cast {first second : ℕ} (same : first = second) (word : Fin first → Letter)
    (index : Fin (second * Fintype.card Letter)) :
    encodeWordBits (fun position : Fin second => word (position.cast same.symm)) index =
      encodeWordBits word (index.cast (congrArg (fun length => length * Fintype.card Letter) same.symm)) := by
  cases same
  rfl

/-- The one-hot assignment determines every external letter uniquely. -/
theorem encodeWordBits_injective {length : ℕ} : Function.Injective (@encodeWordBits length) := by
  intro first second equal
  funext position
  have tested := congrFun equal (finProdFinEquiv (position, (Fintype.equivFin Letter) (first position)))
  have same : decide (second position = first position) = true := by
    simpa [encodeWordBits] using tested.symm
  exact (of_decide_eq_true same).symm

/-- The initial word, blank elsewhere, with its sole head at the origin. -/
def initialCells {length : ℕ} (entry : State) (letters : Letter → Symbol)
    (word : Fin length → Letter) (position : ℤ) : Cell Symbol State :=
  (if inside : 0 ≤ position ∧ position < length then letters (word ⟨position.toNat, by omega⟩)
    else default, if position = 0 then some entry else none)

/-- A cell bit in the initial window is a fixed constant or one external
letter bit. Its references are bounded by the mathematical word length. -/
noncomputable def initialChoices (radius length : ℕ) (entry : State) (letters : Letter ↪ Symbol) :
    Fin ((2 * radius + 1) * cellWidth Symbol State) → Bool ⊕ Fin (length * Fintype.card Letter) := by
  classical
  exact fun output =>
    let position := windowPosition radius (finProdFinEquiv.symm output).1
    let cell := (Fintype.equivFin (Cell Symbol State)).symm (finProdFinEquiv.symm output).2
    let marker := if position = 0 then some entry else none
    if inside : 0 ≤ position ∧ position < length then
      if cell.2 = marker then
        if present : ∃ letter, letters letter = cell.1 then
          .inr (finProdFinEquiv (⟨position.toNat, by omega⟩, (Fintype.equivFin Letter) present.choose))
        else .inl false
      else .inl false
    else .inl (decide ((default, marker) = cell))

omit [Inhabited Symbol] [Inhabited State] [Fintype Symbol] [Fintype State] in
theorem letterCell_test (letters : Letter ↪ Symbol) (value : Letter)
    (marker : Option State) (cell : Cell Symbol State) :
    decide ((letters value, marker) = cell) =
      (if cell.2 = marker then
        if present : ∃ letter, letters letter = cell.1 then decide (value = present.choose) else false
      else false) := by
  classical
  by_cases markerEqual : cell.2 = marker
  · by_cases present : ∃ letter, letters letter = cell.1
    · have symbolEqual : letters value = cell.1 ↔ value = present.choose := by
        constructor
        · intro equal
          exact letters.injective (equal.trans present.choose_spec.symm)
        · intro equal
          exact equal ▸ present.choose_spec
      simp [markerEqual, present, Prod.ext_iff, symbolEqual]
    · have different : letters value ≠ cell.1 := fun equal => present ⟨value, equal⟩
      simp [markerEqual, present, Prod.ext_iff, different]
  · simp [markerEqual, Prod.ext_iff, Ne.symm markerEqual]

omit [Inhabited State] in
/-- The symbolic initial wiring produces exactly the one-hot mathematical
initial configuration on every correctly encoded word. -/
theorem initialChoices_correct (radius length : ℕ) (entry : State) (letters : Letter ↪ Symbol)
    (word : Fin length → Letter) (output : Fin ((2 * radius + 1) * cellWidth Symbol State)) :
    (match initialChoices radius length entry letters output with
      | .inl value => value
      | .inr index => encodeWordBits word index) =
      encodeCells (windowArray radius (initialCells entry letters word)) output := by
  classical
  simp only [initialChoices, encodeCells, windowArray, encodeCell, initialCells]
  by_cases inside : 0 ≤ windowPosition radius (finProdFinEquiv.symm output).1 ∧
      windowPosition radius (finProdFinEquiv.symm output).1 < length
  · simp only [dite_eq_left inside]
    rw [letterCell_test]
    by_cases markerEqual : ((Fintype.equivFin (Cell Symbol State)).symm
        (finProdFinEquiv.symm output).2).2 =
        (if windowPosition radius (finProdFinEquiv.symm output).1 = 0 then some entry else none)
    · simp only [ite_eq_left markerEqual]
      by_cases present : ∃ letter, letters letter = ((Fintype.equivFin (Cell Symbol State)).symm
        (finProdFinEquiv.symm output).2).1
      · simp only [dite_eq_left present, encodeWordBits, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      · simp only [dite_eq_right present]
    · simp only [ite_eq_right markerEqual]
  · simp only [dite_eq_right inside]

omit [Inhabited State] [Fintype Symbol] [Fintype State] in
theorem tape_ofFn_nth {length : ℕ} (word : Fin length → Symbol) (position : ℤ) :
    (Tape.mk₁ (List.ofFn word)).nth position =
      if inside : 0 ≤ position ∧ position < length then word ⟨position.toNat, by omega⟩ else default := by
  cases position with
  | ofNat index =>
    rw [Int.ofNat_eq_natCast]
    rw [Tape.mk₁, Tape.mk₂, Tape.mk'_nth_nat (ListBlank.mk []) (ListBlank.mk (List.ofFn word)) index,
      ListBlank.nth_mk]
    by_cases bounded : index < length
    · rw [List.getI_eq_getElem _ (by simpa using bounded)]
      simp [bounded]
    · rw [List.getI_eq_default _ (by simpa using Nat.le_of_not_lt bounded)]
      simp [bounded]
  | negSucc index =>
    simp [Tape.mk₁, Tape.mk₂, Tape.mk', Tape.nth, List.getI]

omit [Inhabited State] [Fintype Symbol] [Fintype State] in
/-- The ordinary array presentation agrees with the actual Mathlib input
tape, including empty words and all negative tape positions. -/
theorem initialCells_eq {length : ℕ} (entry : State) (letters : Letter → Symbol)
    (word : Fin length → Letter) :
    initialCells entry letters word = cells 0 ⟨entry, Tape.mk₁ ((List.ofFn word).map letters)⟩ := by
  have mapped : (List.ofFn word).map letters = List.ofFn (fun index => letters (word index)) := by simp [Function.comp_def]
  funext position
  simp only [initialCells, cells, sub_zero, mapped, tape_ofFn_nth]

/-- A word-input circuit includes the initial wiring and the complete bounded
simulation. Its input bits encode letters, rather than arbitrary tape cells. -/
noncomputable def wordCircuit (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) (steps length : ℕ) : Network :=
  composeLayer (length * Fintype.card Letter)
    (wiringLayer _ (initialChoices (2 * steps) length entry letters))
    (acceptanceCircuit machine (letters (Sum.inl true)) steps)

theorem wordCircuit_valid (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) (steps length : ℕ) :
    Circuit.Valid (length * Fintype.card Letter) (wordCircuit machine entry letters steps length) := by
  have prepared := wiringLayer_valid _ (initialChoices (2 * steps) length entry letters)
  exact composeLayer_valid prepared.1 prepared.2 (acceptanceCircuit_valid machine _ steps)

theorem wordCircuit_bound (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) (steps length : ℕ) :
    (wordCircuit machine entry letters steps length).1.length ≤
      2 + (steps * ((2 * (2 * steps) + 1) * cellWidth Symbol State) *
        (5 * 2 ^ (3 * cellWidth Symbol State)) + (5 * ((2 * (2 * steps) + 1) * cellWidth Symbol State) + 1)) := by
  dsimp only [wordCircuit]
  rw [composeLayer_length]
  exact Nat.add_le_add_left (acceptanceCircuit_bound machine _ steps) 2

/-- Every encoded word is simulated with the exact certified Boolean answer.
No precomputed answer is used by the initial wiring. -/
theorem wordCircuit_runs (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) (steps length : ℕ) (word : Fin length → Letter) (answer : Bool)
    (runs : Internal.Runs machine entry letters (List.ofFn word) [Sum.inl answer] steps) :
    evaluate (length * Fintype.card Letter) (wordCircuit machine entry letters steps length)
      (encodeWordBits word) = answer := by
  dsimp only [wordCircuit]
  rw [composeLayer_correct _ _ (wiringLayer_valid _ _).2 (acceptanceCircuit_valid machine _ steps)]
  have prepared : (fun index => run (length * Fintype.card Letter) (wiringLayer (length * Fintype.card Letter) (initialChoices (2 * steps) length entry letters)).1
      (inputValues (encodeWordBits word)) ((wiringLayer (length * Fintype.card Letter) (initialChoices (2 * steps) length entry letters)).2 index)) =
        encodeCells (windowArray (2 * steps) (initialCells entry letters word)) := by
    funext index
    rw [wiringLayer_correct]
    have correct := initialChoices_correct (2 * steps) length entry letters word index
    cases choice : initialChoices (2 * steps) length entry letters index <;>
      simpa only [choice] using correct
  rw [prepared, initialCells_eq]
  exact acceptanceCircuit_runs machine entry letters (List.ofFn word) answer steps runs

end Polytime2.Complexity.CookLevin
