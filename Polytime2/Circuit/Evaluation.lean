import Polytime2.Circuit.GateEvaluation
import Polytime2.Arrays.FoldContract

/-! # Certified execution of bounded gate updates

A program pairs each gate with the finite coordinate it defines. The state is
an ordinary Boolean array. Each step evaluates the gate on the old state and
updates that one coordinate, retaining all other wire values.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Circuit

open EncodedDomain Polytime2.Computation
open Polytime2.Computation.Realizable.Internal

variable {Parameter : Type} [Fintype Parameter]

/-- A bounded gate update, with its actual destination wire. -/
noncomputable def gateUpdateDomain (wires : MvPolynomial Parameter ℕ) : EncodedDomain Parameter :=
  (arrayPosition wires).prod (gateDomain wires)

/-- Mathematical execution of one gate update on a Boolean wire array. -/
def applyGateUpdate {wires : ℕ} (values : Fin wires → Bool)
    (update : Fin wires × (Bool ⊕ (Fin wires × Fin wires))) : Fin wires → Bool :=
  Function.update values update.1 (match update.2 with
    | .inl value => value
    | .inr pair => !(values pair.1 && values pair.2))

private theorem updateStep_realizable (wires : MvPolynomial Parameter ℕ) :
    (arrayFoldStep (fun empty : Empty => nomatch empty) (gateUpdateDomain wires)
      (booleans.arrayOfLength wires) (fun _ _ _ _ => True)
      (fun _ _ => applyGateUpdate)).Realizable := by
  let context := (arrayFoldStep (fun empty : Empty => nomatch empty) (gateUpdateDomain wires)
    (booleans.arrayOfLength wires) (fun _ _ _ _ => True) (fun _ _ => applyGateUpdate)).inputDomains
  have token := Realizable.argument context (.inr true) (fun _ _ => True)
  have state := Realizable.argument context (.inr false) (fun _ _ => True)
  have evaluated := (evaluateGate_realizable wires).onResults context (fun _ _ => True)
    (fun name _ arguments => match name with
      | false => (arguments.val (.inr true)).2
      | true => arguments.val (.inr false)) (by intros; trivial) (by
        intro name
        cases name
        · exact token.snd
        · exact state)
  have updated := (arrayUpdateWithIndex_realizable booleans (arrayPosition wires)
    (fun _ index => index.val) (arrayPosition_value wires) wires).onResults context (fun _ _ => True)
    (fun name sizes arguments => match name with
      | 0 => (arguments.val (.inr true)).1
      | 1 => arguments.val (.inr false)
      | 2 => (evaluateGate wires).compute sizes
        ⟨(fun name => match name with
          | false => (arguments.val (.inr true)).2
          | true => arguments.val (.inr false)), trivial⟩)
    (by intro sizes arguments; exact (arguments.val (.inr true)).1.isLt) (by
      intro name
      fin_cases name
      · exact token.fst
      · exact state
      · exact evaluated)
  exact updated.withSpecification (fun _ _ => True) _ (by intros; trivial) (by
    intro sizes arguments accepted
    simp only [onResults, arrayUpdateWithIndex, evaluateGate, applyGateUpdate]
    funext index
    simp only [Function.update_apply, Fin.ext_iff]
    split_ifs <;> cases (arguments (.inr true)).2 <;> simp)

/-- Execute a bounded list of gate updates from the supplied initial values.
False names the initial state and true the update array. -/
noncomputable def evaluateUpdates (wires count : MvPolynomial Parameter ℕ) : Computation Parameter Bool where
  inputDomains name := if name then (gateUpdateDomain wires).arrayOfLength count else booleans.arrayOfLength wires
  outputDomain := booleans.arrayOfLength wires
  precondition _ _ := True
  compute _ arguments := (List.ofFn (arguments.val true)).foldl applyGateUpdate (arguments.val false)

theorem evaluateUpdates_realizable (wires count : MvPolynomial Parameter ℕ) :
    (evaluateUpdates wires count).Realizable := by
  let context := (evaluateUpdates wires count).inputDomains
  have folded := (arrayFold_total_realizable (fun empty : Empty => nomatch empty) (gateUpdateDomain wires)
    (booleans.arrayOfLength wires) count (fun _ _ => applyGateUpdate) (updateStep_realizable wires)).onArguments
      context (fun _ _ => True) (fun name => match name with | .inl empty => nomatch empty | .inr name => name)
      (by intro name; cases name with | inl empty => cases empty | inr name => rfl) (by intros; trivial)
  apply folded.withSpecification (fun _ _ => True) _ (by intros; trivial)
  intro sizes arguments accepted
  simp only [onResults, arrayFold, ArrayFold.prefixValue]
  rw [List.take_of_length_le (by simp)]

/-- The whole certified execution is exactly ordinary left-to-right evaluation
of the supplied gate updates, including an empty program. -/
theorem evaluateUpdates_correct (wires count : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (evaluateUpdates wires count).Arguments sizes) :
    (evaluateUpdates wires count).compute sizes ⟨arguments, trivial⟩ =
      (List.ofFn (arguments true)).foldl applyGateUpdate (arguments false) := by
  rfl

private theorem applyGateUpdate_restrict {wires : ℕ} (values : ℕ → Bool) (destination : Fin wires)
    (gate : Bool ⊕ (Fin wires × Fin wires)) :
    applyGateUpdate (fun index : Fin wires => values index.val) (destination, gate) =
      fun index : Fin wires => Function.update values destination.val ((gateValue gate).eval values) index.val := by
  funext index
  cases gate <;> simp [applyGateUpdate, gateValue, Gate.eval, Function.update_apply, Fin.ext_iff]

/-- Updates at consecutive destinations agree with the existing natural-wire
circuit execution. Initial values on the finite wire set are preserved exactly. -/
theorem fold_gateUpdates {wires : ℕ} (gates : List (Bool ⊕ (Fin wires × Fin wires)))
    (start : ℕ) (bounded : start + gates.length ≤ wires) (values : ℕ → Bool) :
    (List.ofFn (fun index : Fin gates.length =>
      ((⟨start + index.val, by omega⟩ : Fin wires), gates.get index))).foldl
        applyGateUpdate (fun index : Fin wires => values index.val) =
      fun index : Fin wires => run start (gates.map gateValue) values index.val := by
  induction gates generalizing start values with
  | nil => simp [run]
  | cons gate rest induction =>
    simp only [List.length_cons] at bounded
    rw [List.ofFn_succ, List.foldl_cons]
    rw [applyGateUpdate_restrict]
    have shifted : (List.ofFn fun i : Fin rest.length =>
        ((⟨start + i.succ.val, by omega⟩ : Fin wires), (gate :: rest).get i.succ)) =
      List.ofFn (fun i : Fin rest.length =>
        ((⟨start + 1 + i.val, by omega⟩ : Fin wires), rest.get i)) := by
      congr 1
      funext i
      apply Prod.ext
      · apply Fin.ext; simp only [Fin.val_succ]; omega
      · rfl
    rw [shifted]
    simpa [run] using induction (start + 1) (by omega)
      (Function.update values start ((gateValue gate).eval values))

end Polytime2.Circuit
