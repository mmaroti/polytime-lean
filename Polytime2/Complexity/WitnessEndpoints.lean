import Polytime2.Arithmetic.NaturalPolynomial
import Polytime2.Arrays.Indices
import Polytime2.Computation.RecordArguments

/-! # Coordinates retained by nested-witness normalization

Given outer-input and inner-witness lengths, produce the outer-prefix end and
the inner-witness interval endpoints. The precondition states precisely that
both nested headers and the witness fit in the original word.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Complexity

open EncodedDomain Polytime2.Computation Polytime2.Computation.Realizable.Internal

/-- Prefix end, witness start, and witness end within the original word. -/
noncomputable def witnessEndpoints (capacity : MvPolynomial Unit ℕ) : Computation Unit Bool where
  inputDomains _ := boundedIndex (capacity + 1)
  outputDomain := record 3 (fun _ => arrayPosition (capacity + 1))
  precondition sizes arguments := 2 * (arguments false).val + 2 * (arguments true).val + 2 ≤ MvPolynomial.eval sizes capacity
  compute sizes arguments index := ⟨match index with
    | 0 => 2 * (arguments.val false).val + 1
    | 1 => 2 * (arguments.val false).val + (arguments.val true).val + 2
    | 2 => 2 * (arguments.val false).val + 2 * (arguments.val true).val + 2, by
      have fits := arguments.property
      simp only [map_add, map_one]
      fin_cases index <;> dsimp <;> omega⟩

theorem witnessEndpoints_realizable (capacity : MvPolynomial Unit ℕ) : (witnessEndpoints capacity).Realizable := by
  let inputs := (witnessEndpoints capacity).inputDomains
  let allowed := (witnessEndpoints capacity).precondition
  let expressions : Fin 3 → MvPolynomial (Unit ⊕ Bool) ℕ :=
    ![MvPolynomial.C 2 * MvPolynomial.X (Sum.inr false) + MvPolynomial.C 1,
      MvPolynomial.C 2 * MvPolynomial.X (Sum.inr false) + MvPolynomial.X (Sum.inr true) + MvPolynomial.C 2,
      MvPolynomial.C 2 * MvPolynomial.X (Sum.inr false) + MvPolynomial.C 2 * MvPolynomial.X (Sum.inr true) + MvPolynomial.C 2]
  have coordinate (name : Bool) := (indexToPosition_realizable (capacity + 1)).onArguments inputs allowed
    (fun _ => name) (by intros; rfl) (by intros; trivial)
  apply Realizable.recordOutputs
  intro index
  have evaluated := (polynomialPosition_realizable (fun _ : Bool => capacity + 1)
    (expressions index) (capacity + 1)).onResults inputs allowed (fun name _ arguments => arguments.val name)
    (by
      intro sizes arguments
      have fits : 2 * (arguments.val false).val + 2 * (arguments.val true).val + 2 ≤
        MvPolynomial.eval sizes capacity := arguments.property
      change MvPolynomial.eval (Sum.elim sizes (fun name => (arguments.val name).val)) (expressions index) < _
      fin_cases index <;> simp only [expressions, Matrix.cons_val_zero', Matrix.cons_val_succ',
        Matrix.cons_val_fin_one, MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_C,
        MvPolynomial.eval_X, Sum.elim_inr, map_one] <;> omega) coordinate
  exact evaluated.withSpecification allowed (fun sizes arguments => (witnessEndpoints capacity).compute sizes arguments index)
    (by intros; assumption) (by
      intro sizes arguments valid
      apply Fin.ext
      change MvPolynomial.eval (Sum.elim sizes (fun name => (arguments name).val)) (expressions index) = _
      fin_cases index <;> simp only [expressions, witnessEndpoints, Matrix.cons_val_zero', Matrix.cons_val_succ',
        Matrix.cons_val_fin_one, MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_C,
        MvPolynomial.eval_X, Sum.elim_inr])

end Polytime2.Complexity
