import Polytime2.Circuit.Unroll
import Polytime2.Circuit.TruthTable

/-! # Observing the result of a shared circuit layer

An observation appends its gates to the existing layer and reads that layer's
result wires. In particular, observing several cells never duplicates the
machine's unrolled computation. Disjunction uses a linear-size expression:
each remaining branch occurs once in the NAND selector.
-/

namespace Polytime2.Circuit

namespace Expression

/-- Disjoin the selected wires, preserving sharing and allowing an empty list. -/
def anyWire : List ℕ → Expression
  | [] => .constant false
  | index :: rest => select (.wire index) (.constant true) (anyWire rest)

theorem anyWire_rename (wires : List ℕ) (names : ℕ → ℕ) :
    (anyWire wires).rename names = anyWire (wires.map names) := by
  induction wires with
  | nil => rfl
  | cons wire rest induction => simp only [anyWire, select, rename, List.map_cons, induction]

theorem anyWire_valid {wires : List ℕ} {available : ℕ}
    (bounded : ∀ wire ∈ wires, wire < available) : (anyWire wires).Valid available := by
  induction wires with
  | nil => trivial
  | cons wire rest induction =>
    exact select_valid (show (Expression.wire wire).Valid available from bounded wire (by simp)) trivial
      (induction (fun index member => bounded index (by simp [member])))

theorem anyWire_gateCount (wires : List ℕ) : (anyWire wires).gateCount = 5 * wires.length + 1 := by
  induction wires with
  | nil => rfl
  | cons wire rest induction => simp [anyWire, select, gateCount, induction]; omega

theorem anyWire_eval (wires : List ℕ) (values : ℕ → Bool) :
    (anyWire wires).eval values = wires.any values := by
  induction wires with
  | nil => rfl
  | cons wire rest induction =>
    simp only [anyWire, select_eval, eval, List.any_cons, induction]
    cases values wire <;> rfl

/-- Conjoin expressions without duplicating the remaining conjunction. Each
individual selector is copied three times, a fixed factor. -/
def allExpressions : List Expression → Expression
  | [] => .constant true
  | expression :: rest => select expression (allExpressions rest) (.constant false)

theorem allExpressions_valid {expressions : List Expression} {available : ℕ}
    (valid : ∀ expression ∈ expressions, expression.Valid available) :
    (allExpressions expressions).Valid available := by
  induction expressions with
  | nil => trivial
  | cons expression rest induction =>
    exact select_valid (valid expression (by simp))
      (induction (fun item member => valid item (by simp [member]))) trivial

theorem allExpressions_gateCount (expressions : List Expression) :
    (allExpressions expressions).gateCount =
      3 * (expressions.map gateCount).sum + 5 * expressions.length + 1 := by
  induction expressions with
  | nil => rfl
  | cons expression rest induction =>
    simp only [allExpressions, select, gateCount, List.map_cons, List.sum_cons, List.length_cons, induction]
    omega

theorem allExpressions_eval (expressions : List Expression) (values : ℕ → Bool) :
    (allExpressions expressions).eval values = expressions.all (fun expression => expression.eval values) := by
  induction expressions with
  | nil => rfl
  | cons expression rest induction =>
    simp only [allExpressions, select_eval, eval, List.all_cons, induction]
    cases expression.eval values <;> rfl

end Expression

/-- Append an observation of a layer's result wires. -/
def observeLayer {width : ℕ} (inputs : ℕ) (layer : Layer width)
    (observation : Expression) : Network :=
  let result := (observation.rename (layerNames layer.2)).compile (inputs + layer.1.length)
  (layer.1 ++ result.1, result.2)

theorem observeLayer_valid {width inputs : ℕ} {layer : Layer width}
    (layerValid : WellFormed inputs layer.1)
    (outputsValid : ∀ index, layer.2 index < inputs + layer.1.length)
    {observation : Expression} (observationValid : observation.Valid width) :
    Valid inputs (observeLayer inputs layer observation) := by
  have renamed : (observation.rename (layerNames layer.2)).Valid (inputs + layer.1.length) := by
    apply Expression.rename_valid observationValid
    intro wire bounded
    simpa [layerNames, bounded] using outputsValid ⟨wire, bounded⟩
  have result := Expression.compile_valid renamed
  exact ⟨(wellFormed_append _ _ _).mpr ⟨layerValid, result.1⟩,
    by simpa only [observeLayer, List.length_append, Nat.add_assoc] using result.2⟩

theorem observeLayer_length {width : ℕ} (inputs : ℕ) (layer : Layer width)
    (observation : Expression) :
    (observeLayer inputs layer observation).1.length = layer.1.length + observation.gateCount := by
  simp only [observeLayer, List.length_append, Expression.compile_length, Expression.rename_gateCount]

/-- A nonempty observer selects the last wire of the combined circuit. -/
theorem observeLayer_output {width : ℕ} (inputs : ℕ) (layer : Layer width)
    (observation : Expression) (positive : 0 < observation.gateCount) :
    (observeLayer inputs layer observation).2 + 1 = inputs + (observeLayer inputs layer observation).1.length := by
  rw [observeLayer_length]
  have output := Expression.compile_output (observation.rename (layerNames layer.2)) (inputs + layer.1.length)
    (by rwa [Expression.rename_gateCount])
  simpa only [observeLayer, Expression.rename_gateCount, Nat.add_assoc] using output

/-- The observation sees exactly the mathematical values on the layer's
output wires, regardless of the layer's private fresh wires. -/
theorem observeLayer_correct {width inputs : ℕ} (layer : Layer width)
    (outputsValid : ∀ index, layer.2 index < inputs + layer.1.length)
    {observation : Expression} (observationValid : observation.Valid width)
    (assignment : Fin inputs → Bool) :
    evaluate inputs (observeLayer inputs layer observation) assignment =
      observation.eval (inputValues (fun index => run inputs layer.1 (inputValues assignment) (layer.2 index))) := by
  have renamed : (observation.rename (layerNames layer.2)).Valid (inputs + layer.1.length) := by
    apply Expression.rename_valid observationValid
    intro wire bounded
    simpa [layerNames, bounded] using outputsValid ⟨wire, bounded⟩
  change run inputs (layer.1 ++ _) (inputValues assignment)
    ((observation.rename (layerNames layer.2)).compile (inputs + layer.1.length)).2 = _
  rw [run_append, Expression.compile_correct renamed, Expression.rename_eval]
  apply Expression.eval_eq_of_agree observationValid
  intro wire bounded
  simp [inputValues, layerNames, bounded]

end Polytime2.Circuit
