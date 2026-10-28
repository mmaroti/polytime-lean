import Polytime2.Circuit.NetworkEvaluation
import Polytime2.Arrays.Append

/-! # Circuit evaluation on its mathematical input assignment

The caller supplies a bounded network and exactly its input bits. Initial
values for generated wires are prepared internally using existing array
constructors. The returned Boolean is the existing `Circuit.evaluate`.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Circuit

open EncodedDomain Polytime2.Computation

variable {Parameter : Type} [Fintype Parameter]

private noncomputable def zeroWires (count : MvPolynomial Parameter ℕ) : Computation Parameter Empty :=
  arrayTabulate Empty.elim booleans count (fun _ _ _ => false)

private theorem zeroWires_realizable (count : MvPolynomial Parameter ℕ) : (zeroWires count).Realizable := by
  apply arrayTabulate_realizable
  exact (booleanOperation_realizable (Parameter := Parameter) (fun _ : Empty → Bool => false)).onResults
    _ (fun _ _ => True) (fun empty => nomatch empty) (by intros; trivial) (fun empty => nomatch empty)

private noncomputable def initialWires (inputs count : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  (arrayAppend booleans inputs count).onResults (fun _ => booleans.arrayOfLength inputs) (fun _ _ => True)
    (fun _ sizes arguments => (arguments.val (), (zeroWires count).compute sizes ⟨(fun empty => nomatch empty), trivial⟩))
    (by intros; trivial)

private theorem initialWires_realizable (inputs count : MvPolynomial Parameter ℕ) :
    (initialWires inputs count).Realizable := by
  let context : Unit → EncodedDomain Parameter := fun _ => booleans.arrayOfLength inputs
  have zeros := (zeroWires_realizable count).onResults context (fun _ _ => True)
    (fun empty => nomatch empty) (by intros; trivial) (fun empty => nomatch empty)
  apply (arrayAppend_realizable booleans inputs count).onResults
  intro singleton
  cases singleton
  exact (Realizable.argument context () (fun _ _ => True)).prodMk zeros

private theorem initialWires_value (inputs count : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (assignment : Fin (MvPolynomial.eval sizes inputs) → Bool)
    (index : Fin (MvPolynomial.eval sizes (inputs + count))) :
    (initialWires inputs count).compute sizes ⟨(fun _ => assignment), trivial⟩ index =
      if bounded : index.val < MvPolynomial.eval sizes inputs then assignment ⟨index.val, bounded⟩ else false := by
  change Fin.append assignment (fun _ : Fin (MvPolynomial.eval sizes count) => false)
    (index.cast (map_add (MvPolynomial.eval sizes) inputs count)) = _
  simp only [Fin.append, Fin.addCases, Fin.val_cast, eq_rec_constant]
  split_ifs <;> rfl


/-- Evaluate the circuit on exactly its ordinary finite input assignment. -/
noncomputable def evaluateCircuit (inputs count : MvPolynomial Parameter ℕ) : Computation Parameter Bool :=
  specification (fun name => if name then booleans.arrayOfLength inputs else networkDomain inputs count)
    booleans (fun _ _ => True)
    (fun sizes arguments => evaluate (MvPolynomial.eval sizes inputs) (programValue (arguments.val false))
      (arguments.val true))

private noncomputable def evaluateCircuitImplementation (inputs count : MvPolynomial Parameter ℕ) : Computation Parameter Bool :=
  (evaluateNetwork inputs count).onResults (evaluateCircuit inputs count).inputDomains (fun _ _ => True)
    (fun name sizes arguments => match name with
      | 0 => (arguments.val false).1
      | 1 => (arguments.val false).2
      | 2 => (initialWires inputs count).compute sizes ⟨(fun _ => arguments.val true), trivial⟩)
    (by intros; trivial)

private theorem evaluateCircuitImplementation_realizable (inputs count : MvPolynomial Parameter ℕ) :
    (evaluateCircuitImplementation inputs count).Realizable := by
  let context := (evaluateCircuit inputs count).inputDomains
  have source := Realizable.argument context false (fun _ _ => True)
  have prepared := (initialWires_realizable inputs count).onArguments context (fun _ _ => True)
    (fun _ => true) (by intros; rfl) (by intros; trivial)
  apply (evaluateNetwork_realizable inputs count).onResults
  intro name
  fin_cases name
  · exact source.fst
  · exact source.snd
  · exact prepared

private theorem evaluateCircuitImplementation_correct (inputs count : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ) (arguments : (evaluateCircuit inputs count).Arguments sizes) :
    (evaluateCircuitImplementation inputs count).compute sizes ⟨arguments, trivial⟩ =
      evaluate (MvPolynomial.eval sizes inputs) (programValue (arguments false)) (arguments true) := by
  simp only [evaluateCircuitImplementation, onResults]
  rw [evaluateNetwork_correct]
  change run (MvPolynomial.eval sizes inputs) (List.ofFn (fun index => gateValue ((arguments false).1 index)))
      _ (arguments false).2.val = _
  unfold evaluate programValue
  apply congrArg (fun values : ℕ → Bool => run (MvPolynomial.eval sizes inputs)
    (List.ofFn (fun index => gateValue ((arguments false).1 index))) values (arguments false).2.val)
  funext wire
  by_cases inside : wire < MvPolynomial.eval sizes (inputs + count)
  · simp only [dite_eq_left inside]
    exact initialWires_value inputs count sizes (arguments true) ⟨wire, inside⟩
  · have outside : ¬wire < MvPolynomial.eval sizes inputs := by
      simp only [map_add] at inside
      omega
    simp only [dite_eq_right inside, dite_eq_right outside]

theorem evaluateCircuit_realizable (inputs count : MvPolynomial Parameter ℕ) :
    (evaluateCircuit inputs count).Realizable := by
  apply (evaluateCircuitImplementation_realizable inputs count).withSpecification (fun _ _ => True)
    (evaluateCircuit inputs count).compute (by intros; trivial)
  intro sizes arguments accepted
  simpa only [evaluateCircuit, specification_compute] using
    evaluateCircuitImplementation_correct inputs count sizes arguments

/-- The public result is exactly the mathematical circuit evaluator. -/
theorem evaluateCircuit_correct (inputs count : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (evaluateCircuit inputs count).Arguments sizes) :
    (evaluateCircuit inputs count).compute sizes ⟨arguments, trivial⟩ =
      evaluate (MvPolynomial.eval sizes inputs) (programValue (arguments false)) (arguments true) := by
  simp only [evaluateCircuit, specification_compute]

end Polytime2.Circuit
