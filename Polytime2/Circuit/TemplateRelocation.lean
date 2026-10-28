import Polytime2.Circuit.Compose

/-! # Fixed templates for the expression compiler

Compiling a renamed expression is exactly a relocation of its fixed compiled
template. Runtime construction therefore needs only fixed finite gate data
and arithmetic on wire coordinates; it does not traverse expression trees.
-/

namespace Polytime2.Circuit.Expression

/-- Compose finite wire substitutions without changing expression sharing. -/
theorem rename_layerNames_comp {expression : Expression} {source target : ℕ}
    (valid : expression.Valid source) (first : Fin source → Fin target) (second : Fin target → ℕ) :
    (expression.rename (layerNames (fun index => (first index).val))).rename (layerNames second) =
      expression.rename (layerNames (fun index => second (first index))) := by
  induction expression with
  | wire index => simp [Valid] at valid; simp [rename, layerNames, valid, (first ⟨index, valid⟩).isLt]
  | constant value => rfl
  | nand left right leftInduction rightInduction =>
    simp only [Valid] at valid
    simp only [rename, leftInduction valid.1, rightInduction valid.2]

theorem compile_relocate {expression : Expression} {source : ℕ}
    (valid : expression.Valid source) (target offset : ℕ) (inputs : Fin source → ℕ) :
    (expression.rename (layerNames inputs)).compile (target + offset) =
      (((expression.compile (source + offset)).1.map
        (Gate.rename (spliceNames source target inputs))),
        spliceNames source target inputs (expression.compile (source + offset)).2) := by
  induction expression generalizing offset with
  | wire index =>
    change index < source at valid
    simp [rename, compile, layerNames, spliceNames, valid]
  | constant value => simp [rename, compile, spliceNames_fresh, Gate.rename]
  | nand left right leftInduction rightInduction =>
    simp only [rename, compile, compile_length, rename_gateCount]
    rw [show target + offset + left.gateCount = target + (offset + left.gateCount) by omega,
      show source + offset + left.gateCount = source + (offset + left.gateCount) by omega]
    rw [leftInduction valid.1 offset, rightInduction valid.2 (offset + left.gateCount)]
    simp only [List.map_append, List.map_cons, List.map_nil, Gate.rename]
    congr 2
    simpa only [Nat.add_assoc] using
      (spliceNames_fresh source target inputs (offset + left.gateCount + right.gateCount)).symm

end Polytime2.Circuit.Expression
