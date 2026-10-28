import Polytime2.Circuit.Evaluation
import Polytime2.Circuit.WireArithmetic
import Polytime2.Arrays.Tabulate

/-! # Certified circuit evaluation with finite Boolean wire storage

The inputs are a gate array, an actual output wire, and initial wire values.
Destinations are determined by the mathematical input and gate counts. The
result agrees with the shared circuit execution, without a new machine.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Circuit

open EncodedDomain Polytime2.Computation
open Polytime2.Computation.Realizable.Internal

variable {Parameter : Type} [Fintype Parameter]

private noncomputable def networkUpdates (inputs count : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  arrayTabulate (fun _ => (gateDomain (inputs + count)).arrayOfLength count)
    (gateUpdateDomain (inputs + count)) count
    (fun sizes arguments position =>
      ((gateOutputWire inputs count).compute sizes ⟨(fun _ => position), trivial⟩, arguments () position))

private theorem networkUpdates_realizable (inputs count : MvPolynomial Parameter ℕ) :
    (networkUpdates inputs count).Realizable := by
  apply arrayTabulate_realizable
  let context : Unit ⊕ Unit → EncodedDomain Parameter :=
    Sum.elim (fun _ => (gateDomain (inputs + count)).arrayOfLength count) (fun _ => arrayPosition count)
  have gate := (arrayLookupWithIndex_realizable (gateDomain (inputs + count)) (arrayPosition count)
    (fun _ position => position.val) (arrayPosition_value count) count).onArguments context (fun _ _ => True)
      (fun name => if name then .inl () else .inr ()) (by intro name; cases name <;> rfl)
      (by intro sizes arguments; exact (arguments.val (.inr ())).isLt)
  have wire := (gateOutputWire_realizable inputs count).onArguments context (fun _ _ => True)
    (fun _ => .inr ()) (by intros; rfl) (by intros; trivial)
  exact wire.prodMk gate

/-- Evaluate a bounded circuit with the supplied initial values on every wire.
Arguments are gates, selected output wire, and initial values, in that order. -/
noncomputable def evaluateNetwork (inputs count : MvPolynomial Parameter ℕ) : Computation Parameter (Fin 3) where
  inputDomains
    | 0 => (gateDomain (inputs + count)).arrayOfLength count
    | 1 => arrayPosition (inputs + count)
    | 2 => booleans.arrayOfLength (inputs + count)
  outputDomain := booleans
  precondition _ _ := True
  compute sizes arguments :=
    (evaluateUpdates (inputs + count) count).compute sizes
      ⟨(fun name => match name with
        | false => arguments.val 2
        | true => (networkUpdates inputs count).compute sizes ⟨(fun _ => arguments.val 0), trivial⟩), trivial⟩
      (arguments.val 1)

theorem evaluateNetwork_realizable (inputs count : MvPolynomial Parameter ℕ) :
    (evaluateNetwork inputs count).Realizable := by
  let context := (evaluateNetwork inputs count).inputDomains
  have updates := (networkUpdates_realizable inputs count).onArguments context (fun _ _ => True)
    (fun _ => 0) (by intros; rfl) (by intros; trivial)
  have executed := (evaluateUpdates_realizable (inputs + count) count).onResults context (fun _ _ => True)
    (fun name sizes arguments => match name with
      | false => arguments.val 2
      | true => (networkUpdates inputs count).compute sizes ⟨(fun _ => arguments.val 0), trivial⟩)
    (by intros; trivial) (by
      intro name
      cases name
      · exact Realizable.argument context 2 (fun _ _ => True)
      · exact updates)
  have result := (arrayLookupWithIndex_realizable booleans (arrayPosition (inputs + count))
    (fun _ position => position.val) (arrayPosition_value (inputs + count)) (inputs + count)).onResults
    context (fun _ _ => True)
    (fun name sizes arguments => match name with
      | false => arguments.val 1
      | true => (evaluateUpdates (inputs + count) count).compute sizes
        ⟨(fun name => match name with
          | false => arguments.val 2
          | true => (networkUpdates inputs count).compute sizes ⟨(fun _ => arguments.val 0), trivial⟩), trivial⟩)
    (by intro sizes arguments; exact (arguments.val 1).isLt) (by
      intro name
      cases name
      · exact Realizable.argument context 1 (fun _ _ => True)
      · exact executed)
  exact result.withSpecification (fun _ _ => True) _ (by intros; trivial) (by intros; rfl)

/-- The certified evaluator agrees with ordinary circuit execution. Values
outside the actual finite wire set are irrelevant and are initialized false. -/
theorem evaluateNetwork_correct (inputs count : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (evaluateNetwork inputs count).Arguments sizes) :
    (evaluateNetwork inputs count).compute sizes ⟨arguments, trivial⟩ =
      run (MvPolynomial.eval sizes inputs) (List.ofFn (fun index => gateValue (arguments 0 index)))
        (fun wire => if bounded : wire < MvPolynomial.eval sizes (inputs + count) then
          arguments 2 ⟨wire, bounded⟩ else false) (arguments 1).val := by
  let values : ℕ → Bool := fun wire =>
    if bounded : wire < MvPolynomial.eval sizes (inputs + count) then arguments 2 ⟨wire, bounded⟩ else false
  have folded := fold_gateUpdates (List.ofFn (arguments 0)) (MvPolynomial.eval sizes inputs)
    (by simp only [List.length_ofFn, map_add]; omega) values
  have initial : (fun index : Fin (MvPolynomial.eval sizes (inputs + count)) => values index.val) = arguments 2 := by
    funext index
    simp only [values, dite_eq_left index.isLt]
  simp only [List.length_ofFn, List.get_ofFn, List.map_ofFn] at folded
  rw [initial] at folded
  have selected := congrFun folded (arguments 1)
  simpa [evaluateNetwork, evaluateUpdates, networkUpdates, arrayTabulate, gateOutputWire, unaryMap,
    values, Function.comp_def] using selected

end Polytime2.Circuit
