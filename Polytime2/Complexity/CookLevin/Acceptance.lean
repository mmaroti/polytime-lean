import Polytime2.Complexity.CookLevin.CellObservation
import Polytime2.TM0.FiniteWindow
import Polytime2.Complexity.MachineTrace

/-! # Acceptance circuits for bounded word verifiers

The circuit simulates a fixed finite Mathlib TM0 machine and observes a head
marker carrying the accepting symbol. Only cells within the time allowance
are inspected. Its Boolean inputs are the one-hot initial finite window;
preparing those inputs from a word and serializing the circuit still require
separate polynomial-time certificates.
-/

namespace Polytime2.Complexity.CookLevin

open Turing Circuit

variable {Symbol State : Type} [Inhabited Symbol] [Inhabited State]
variable [Fintype Symbol] [Fintype State]

/-- An accepting head must lie in the possible final head range. -/
def acceptingCell (steps : ℕ) (accepting : Symbol)
    (index : Fin (2 * (2 * steps) + 1)) (cell : Cell Symbol State) : Prop :=
  (-(steps : ℤ) ≤ windowPosition (2 * steps) index ∧ windowPosition (2 * steps) index ≤ steps) ∧
    ∃ state, cell = (accepting, some state)

/-- List every possible accepting marked cell in the reachable head range.
The length is an exact polynomial in the time allowance. -/
noncomputable def acceptingObservations (steps : ℕ) (accepting : Symbol) :
    List (Fin (2 * (2 * steps) + 1) × Cell Symbol State) :=
  (List.ofFn (fun position : Fin (2 * steps + 1) =>
    List.ofFn (fun state : Fin (Fintype.card State) =>
      (⟨position.val + steps, by omega⟩, (accepting, some ((Fintype.equivFin State).symm state)))))).flatten

omit [Inhabited Symbol] [Inhabited State] [Fintype Symbol] in
theorem acceptingObservations_length (steps : ℕ) (accepting : Symbol) :
    (acceptingObservations (State := State) steps accepting).length = (2 * steps + 1) * Fintype.card State := by
  simp only [acceptingObservations, List.length_flatten, List.map_ofFn]
  simp [Nat.add_mul, Nat.add_comm]

private theorem acceptingObservations_bound (steps : ℕ) (accepting : Symbol) :
    (acceptingObservations (State := State) steps accepting).length ≤
      (2 * (2 * steps) + 1) * cellWidth Symbol State := by
  rw [acceptingObservations_length]
  have symbols : 1 ≤ Fintype.card Symbol := Fintype.card_pos
  have scaled := Nat.mul_le_mul_right (Fintype.card State + 1) symbols
  simp only [Nat.one_mul] at scaled
  have cellBound : Fintype.card State ≤ cellWidth Symbol State := by
    simpa only [cellWidth, Cell, Fintype.card_prod, Fintype.card_option] using
      (Nat.le_succ (Fintype.card State)).trans scaled
  exact Nat.mul_le_mul (by omega) cellBound

omit [Inhabited Symbol] [Inhabited State] [Fintype Symbol] in
/-- Explicit observations describe precisely the acceptance predicate. -/
theorem acceptingObservations_correct (steps : ℕ) (accepting : Symbol)
    (contents : Fin (2 * (2 * steps) + 1) → Cell Symbol State) :
    (∃ observation ∈ acceptingObservations steps accepting, contents observation.1 = observation.2) ↔
      ∃ position, acceptingCell steps accepting position (contents position) := by
  constructor
  · rintro ⟨observation, member, equal⟩
    obtain ⟨list, listMember, observationMember⟩ := List.mem_flatten.mp member
    obtain ⟨position, rfl⟩ := List.mem_ofFn.mp listMember
    obtain ⟨state, rfl⟩ := List.mem_ofFn.mp observationMember
    refine ⟨⟨position.val + steps, by omega⟩, ?_, (Fintype.equivFin State).symm state, equal⟩
    dsimp only [windowPosition]
    have bounded := position.isLt
    constructor <;> push_cast <;> omega
  · rintro ⟨position, inside, state, equal⟩
    dsimp only [windowPosition] at inside
    have lower : steps ≤ position.val := by omega
    have upper : position.val ≤ 3 * steps := by omega
    let inner : Fin (2 * steps + 1) := ⟨position.val - steps, by omega⟩
    refine ⟨(position, (accepting, some state)), ?_, equal⟩
    apply List.mem_flatten.mpr
    refine ⟨_, List.mem_ofFn.mpr ⟨inner, rfl⟩, List.mem_ofFn.mpr ⟨(Fintype.equivFin State) state, ?_⟩⟩
    simp only [Equiv.symm_apply_apply, Prod.mk.injEq, and_true]
    apply Fin.ext
    dsimp only [inner]
    omega

/-- The complete bounded computation circuit, including its final acceptance
observer. The machine and accepting symbol are fixed before choosing sizes. -/
noncomputable def acceptanceCircuit (machine : TM0.Machine Symbol State)
    (accepting : Symbol) (steps : ℕ) : Network :=
  cellObservationCircuit (2 * (2 * steps) + 1) steps (windowNeighbors (2 * steps))
    (windowUpdate machine (2 * steps)) (acceptingObservations steps accepting)

theorem acceptanceCircuit_valid (machine : TM0.Machine Symbol State) (accepting : Symbol) (steps : ℕ) :
    Circuit.Valid ((2 * (2 * steps) + 1) * cellWidth Symbol State)
      (acceptanceCircuit machine accepting steps) :=
  (cellObservationCircuit_spec _ steps (windowNeighbors (2 * steps))
    (windowUpdate machine (2 * steps)) (acceptingObservations steps accepting)).1

theorem acceptanceCircuit_bound (machine : TM0.Machine Symbol State) (accepting : Symbol) (steps : ℕ) :
    (acceptanceCircuit machine accepting steps).1.length ≤
      steps * ((2 * (2 * steps) + 1) * cellWidth Symbol State) *
        (5 * 2 ^ (3 * cellWidth Symbol State)) +
          (5 * ((2 * (2 * steps) + 1) * cellWidth Symbol State) + 1) :=
by
  apply (cellObservationCircuit_spec _ steps (windowNeighbors (2 * steps))
    (windowUpdate machine (2 * steps)) (acceptingObservations steps accepting)).2.1.trans
  exact Nat.add_le_add_left (Nat.add_le_add_right
    (Nat.mul_le_mul_left 5 (acceptingObservations_bound steps accepting)) 1) _

/-- Acceptance is precisely an accepting marked cell in the original
infinite local evolution, throughout the possible final head range. -/
theorem acceptanceCircuit_evolve (machine : TM0.Machine Symbol State) (accepting : Symbol) (steps : ℕ)
    (contents : ℤ → Cell Symbol State) :
    evaluate ((2 * (2 * steps) + 1) * cellWidth Symbol State)
      (acceptanceCircuit machine accepting steps) (encodeCells (windowArray (2 * steps) contents)) = true ↔
      ∃ position, (-(steps : ℤ) ≤ position ∧ position ≤ steps) ∧
        ∃ state, (evolve machine)^[steps] contents position = (accepting, some state) := by
  dsimp only [acceptanceCircuit]
  rw [(cellObservationCircuit_spec _ steps (windowNeighbors (2 * steps))
    (windowUpdate machine (2 * steps)) (acceptingObservations steps accepting)).2.2, acceptingObservations_correct, windowArray_iterate]
  constructor
  · rintro ⟨index, inside, state, equal⟩
    refine ⟨windowPosition (2 * steps) index, inside, state, ?_⟩
    change (windowEvolve machine (2 * steps))^[steps] (window (2 * steps) contents)
      (windowPosition (2 * steps) index) = _ at equal
    rwa [windowEvolve_agree_head_range machine steps contents _ inside] at equal
  · rintro ⟨position, inside, state, equal⟩
    obtain ⟨index, positionEqual⟩ := windowPosition_surjective (2 * steps) position
      (by constructor <;> push_cast <;> omega)
    refine ⟨index, ?_, state, ?_⟩
    · simpa [positionEqual] using inside
    · change (windowEvolve machine (2 * steps))^[steps] (window (2 * steps) contents)
        (windowPosition (2 * steps) index) = _
      rw [positionEqual, windowEvolve_agree_head_range machine steps contents position inside]
      exact equal

/-- On the existing canonical Boolean-output word-machine contract, the
acceptance circuit returns exactly the verifier's answer at its full bound. -/
theorem acceptanceCircuit_runs (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) (input : Word) (answer : Bool) (allowance : ℕ)
    (runs : Internal.Runs machine entry letters input [Sum.inl answer] allowance) :
    evaluate ((2 * (2 * allowance) + 1) * cellWidth Symbol State)
      (acceptanceCircuit machine (letters (Sum.inl true)) allowance)
      (encodeCells (windowArray (2 * allowance) (cells 0 ⟨entry, Tape.mk₁ (input.map letters)⟩))) = answer := by
  have equivalence := acceptanceCircuit_evolve machine (letters (Sum.inl true)) allowance
    (cells 0 ⟨entry, Tape.mk₁ (input.map letters)⟩)
  exact Bool.eq_iff_iff.mpr (equivalence.trans (runs_accepting machine entry letters input answer allowance runs))

end Polytime2.Complexity.CookLevin
