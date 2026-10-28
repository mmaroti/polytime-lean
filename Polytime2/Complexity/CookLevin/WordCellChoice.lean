import Polytime2.Complexity.CookLevin.WordCellFlags

/-! # Fixed finite classification of initial cell bits

Once word membership and the head position are known, choosing a constant or
an external letter is fixed finite alphabet data. The word coordinate is
supplied separately by `wordLetterWire`.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Complexity.CookLevin

open Circuit EncodedDomain Polytime2.Computation

variable {Symbol State : Type} [Inhabited Symbol] [Fintype Symbol] [Fintype State]

/-- Fixed alphabet table: a Boolean constant or the one-hot letter to read. -/
noncomputable def initialLetterChoice (entry : State) (letters : Letter ↪ Symbol)
    (bit : Fin (cellWidth Symbol State)) (inside head : Bool) : Bool ⊕ Fin (Fintype.card Letter) := by
  classical
  let cell := (Fintype.equivFin (Cell Symbol State)).symm bit
  let marker := if head then some entry else none
  exact if inside then
    if cell.2 = marker then
      if present : ∃ letter, letters letter = cell.1 then .inr ((Fintype.equivFin Letter) present.choose)
      else .inl false
    else .inl false
  else .inl (decide ((default, marker) = cell))

/-- The fixed table is exactly the constant/letter part of the original
symbolic input wiring, with the word-position component forgotten. -/
theorem initialLetterChoice_correct (radius length : ℕ) (entry : State) (letters : Letter ↪ Symbol)
    (output : Fin ((2 * radius + 1) * cellWidth Symbol State)) :
    (initialChoices radius length entry letters output).map id
      (fun index => (finProdFinEquiv.symm index).2) =
    initialLetterChoice entry letters (finProdFinEquiv.symm output).2
      (decide (0 ≤ windowPosition radius (finProdFinEquiv.symm output).1 ∧
        windowPosition radius (finProdFinEquiv.symm output).1 < length))
      (decide (windowPosition radius (finProdFinEquiv.symm output).1 = 0)) := by
  classical
  simp only [initialChoices, initialLetterChoice, decide_eq_true_eq]
  split_ifs <;> simp_all
  all_goals exact congrArg Prod.snd (finProdFinEquiv.symm_apply_apply _)

end Polytime2.Complexity.CookLevin
