/-
Copyright (c) 2026 Miklos Maroti <mmaroti@math.u-szeged.hu>
SPDX-License-Identifier: Apache-2.0

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Polytime2.Computation.Layout
import Polytime2.StandardGaussJordanEliminationAlgorithm

/-! # Gauss–Jordan elimination as a mathematical computation

The specialization fixes the finite field enumeration. The three sizes are
binary counter capacity, row count, and column count; the mathematical argument
and result are ordinary matrices of that rectangular shape.
-/

namespace Polytime2.Computation

open MultiTape CallingConvention Realizable StandardMatrixRows

variable {Scalar : Type} [Field Scalar] [DecidableEq Scalar] {cardinality : ℕ}

noncomputable def gaussJordan (enumeration : Scalar ≃ Fin cardinality) : Computation (Fin 3) Unit where
  inputDomains _ := matrixDomain (FieldRow.scalarDomain enumeration)
  outputDomain := matrixDomain (FieldRow.scalarDomain enumeration)
  precondition sizes _ := sizes 1 < 2 ^ sizes 0 ∧ sizes 2 < 2 ^ sizes 0 ∧ sizes 1 * sizes 2 ≤ 2 ^ sizes 0
  compute _ arguments := GaussJordan.eliminate (Scalar := Scalar) (arguments.val ())

namespace Realizable.Internal

private abbrev EliminationTape := StandardGaussJordanElimination.TapeName

/-- Public roles map to the standard interface; all other source tapes remain
private. Extra unused private tapes have no mathematical validity requirement. -/
private noncomputable def eliminationLayoutFunction (enumeration : Scalar ≃ Fin cardinality) :
    EliminationTape → TapeName (gaussJordan enumeration) EliminationTape
  | .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (parameter)))))))))) => .inl parameter
  | .inr 0 => inputTape (gaussJordan enumeration) ()
  | .inl (.inl (.inr 1)) => outputTape (gaussJordan enumeration)
  | name => scratchTape (gaussJordan enumeration) name

private noncomputable def eliminationLayout (enumeration : Scalar ≃ Fin cardinality) :
    EliminationTape ↪ TapeName (gaussJordan enumeration) EliminationTape := by
  refine ⟨eliminationLayoutFunction enumeration, ?_⟩
  let recover : TapeName (gaussJordan enumeration) EliminationTape → EliminationTape
    | .inl parameter => StandardGaussJordanElimination.sizeTape parameter
    | .inr (.inl _) => StandardGaussJordanElimination.inputTape
    | .inr (.inr (.inl _)) => StandardGaussJordanElimination.workingTape
    | .inr (.inr (.inr name)) => name
  have inverse : Function.LeftInverse recover (eliminationLayoutFunction enumeration) := by
    intro name
    fin_cases name <;> rfl
  exact inverse.injective

private noncomputable def eliminationPresentation (enumeration : Scalar ≃ Fin cardinality)
    (name : EliminationTape) : EncodedDomain (Fin 3) :=
  if name = StandardGaussJordanElimination.inputTape ∨ name = StandardGaussJordanElimination.workingTape then
    matrixDomain (FieldRow.scalarDomain enumeration)
  else StandardGaussJordanElimination.domains enumeration name

private theorem eliminationDomains (enumeration : Scalar ≃ Fin cardinality) (name : EliminationTape) :
    domains (gaussJordan enumeration) (StandardGaussJordanElimination.domains enumeration)
      (eliminationLayout enumeration name) = eliminationPresentation enumeration name := by
  fin_cases name <;> rfl

private noncomputable def eliminationPresentationValues (enumeration : Scalar ≃ Fin cardinality)
    (name : EliminationTape) (sizes : Fin 3 → ℕ) :
    (eliminationPresentation enumeration name).Carrier sizes ≃
      (StandardGaussJordanElimination.domains enumeration name).Carrier sizes := by
  classical
  by_cases isInput : name = StandardGaussJordanElimination.inputTape
  · subst name
    exact matrixEquiv sizes
  by_cases isOutput : name = StandardGaussJordanElimination.workingTape
  · subst name
    exact matrixEquiv sizes
  unfold eliminationPresentation
  rw [ite_eq_right (not_or_intro isInput isOutput)]

private noncomputable def eliminationValues (enumeration : Scalar ≃ Fin cardinality)
    (name : EliminationTape) (sizes : Fin 3 → ℕ) :
    (domains (gaussJordan enumeration) (StandardGaussJordanElimination.domains enumeration)
      (eliminationLayout enumeration name)).Carrier sizes ≃
      (StandardGaussJordanElimination.domains enumeration name).Carrier sizes :=
  (Equiv.cast (congrArg (fun domain => domain.Carrier sizes) (eliminationDomains enumeration name))).trans
    (eliminationPresentationValues enumeration name sizes)

end Realizable.Internal

open Realizable.Internal in
/-- The public certificate contains neither workspace names nor runtime bounds. -/
theorem gaussJordan_realizable (enumeration : Scalar ≃ Fin cardinality) :
    (gaussJordan enumeration).Realizable := by
  classical
  refine ofLayout (gaussJordan enumeration) (StandardGaussJordanElimination.domains enumeration)
    (StandardGaussJordanElimination.domains enumeration) StandardGaussJordanElimination.readOnly
    StandardGaussJordanElimination.sizeTapes StandardGaussJordanElimination.outputTapes
    (StandardGaussJordanElimination.algorithm enumeration)
    (StandardGaussJordanElimination.entry (StandardGaussJordanClear.zeroBits enumeration).length
      (StandardPivotSearch.defaultBits (FieldRow.scalarDomain enumeration) (0 : Scalar)).length
      ((FieldRow.scalarDomain enumeration).width Empty.elim))
    (StandardGaussJordanElimination.exit (StandardGaussJordanClear.zeroBits enumeration).length
      (StandardPivotSearch.defaultBits (FieldRow.scalarDomain enumeration) (0 : Scalar)).length
      ((FieldRow.scalarDomain enumeration).width Empty.elim))
    _ _ (StandardGaussJordanElimination.contract enumeration) (eliminationLayout enumeration)
    (eliminationValues enumeration) ?_ ?_ ?_ (by intro parameter; rfl) () rfl
    (by intro sizes input valid; exact valid) ?_
  · intro name sizes
    fin_cases name <;> rfl
  · intro name sizes value
    fin_cases name <;> rfl
  · intro name
    fin_cases name <;> rfl
  · intro sizes input valid output correct
    change (matrixEquiv (Carrier := Scalar) sizes).symm (output ()) =
      GaussJordan.eliminate (Scalar := Scalar)
        ((matrixEquiv (Carrier := Scalar) sizes).symm
          (matrixEquiv sizes (arguments (gaussJordan enumeration)
            (StandardGaussJordanElimination.domains enumeration) sizes input ()))) at correct
    have roundtrip := (matrixEquiv (Carrier := Scalar) sizes).symm_apply_apply
      (arguments (gaussJordan enumeration) (StandardGaussJordanElimination.domains enumeration) sizes input ())
    have mathematical := correct.trans (congrArg (GaussJordan.eliminate (Scalar := Scalar)) roundtrip)
    have equality := ((matrixEquiv (Carrier := Scalar) sizes).apply_symm_apply (output ())).symm.trans
      (congrArg (matrixEquiv (Carrier := Scalar) sizes) mathematical)
    exact congrArg (encoded _ sizes) equality

/-- Elimination preserves the row space and returns reduced row-echelon form. -/
theorem gaussJordan_correct (enumeration : Scalar ≃ Fin cardinality) (sizes : Fin 3 → ℕ)
    (arguments : (gaussJordan enumeration).Arguments sizes)
    (valid : (gaussJordan enumeration).precondition sizes arguments) :
    Matrix.RowEquivalent (R := Scalar) (arguments () : Matrix (Fin (sizes 1)) (Fin (sizes 2)) Scalar)
      ((gaussJordan enumeration).compute sizes ⟨arguments, valid⟩) ∧
      Matrix.IsReducedRowEchelon (R := Scalar)
        ((gaussJordan enumeration).compute sizes ⟨arguments, valid⟩ : Matrix (Fin (sizes 1)) (Fin (sizes 2)) Scalar) :=
  ⟨GaussJordan.rowEquivalent (Scalar := Scalar) _, GaussJordan.reducedRowEchelon (Scalar := Scalar) _⟩

end Polytime2.Computation
