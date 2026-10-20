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
import Polytime2.Computation.InternalSize
import Polytime2.GaussJordan.EliminationAlgorithm

/-! # Gauss–Jordan elimination as a mathematical computation

The specialization fixes the finite field enumeration. The only public sizes
are row and column counts; the mathematical argument and result are ordinary
matrices of that shape. Counter capacity and its unary header are private.
-/

namespace Polytime2.Computation

open MultiTape CallingConvention Realizable StandardMatrixRows

variable {Scalar : Type} [Field Scalar] [DecidableEq Scalar] {cardinality : ℕ}

private noncomputable def gaussJordanWithCapacity (enumeration : Scalar ≃ Fin cardinality) : Computation (Fin 3) Unit where
  inputDomains _ := matrixDomain (FieldRow.scalarDomain enumeration)
  outputDomain := matrixDomain (FieldRow.scalarDomain enumeration)
  precondition sizes _ := sizes 1 < 2 ^ sizes 0 ∧ sizes 2 < 2 ^ sizes 0 ∧ sizes 1 * sizes 2 ≤ 2 ^ sizes 0
  compute _ arguments := GaussJordan.eliminate (Scalar := Scalar) (arguments.val ())

namespace Realizable.Internal

private abbrev EliminationTape := StandardGaussJordanElimination.TapeName

private def eliminationPlacement : PublicTape (Fin 3) Unit ↪ EliminationTape :=
  ⟨(fun role => match role with
    | .inl parameter => StandardGaussJordanElimination.sizeTape parameter
    | .inr (.inl _) => StandardGaussJordanElimination.inputTape
    | .inr (.inr _) => StandardGaussJordanElimination.workingTape), by
    intro first second equal
    fin_cases first <;> fin_cases second <;> first | rfl | exact absurd equal (by decide)⟩

private noncomputable def eliminationPresentation (enumeration : Scalar ≃ Fin cardinality)
    (name : EliminationTape) : EncodedDomain (Fin 3) :=
  if name = StandardGaussJordanElimination.inputTape ∨ name = StandardGaussJordanElimination.workingTape then
    matrixDomain (FieldRow.scalarDomain enumeration)
  else StandardGaussJordanElimination.domains enumeration name

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

/-- Expose ordinary matrices through the source controller's existing codec. -/
private theorem eliminationPresentation_contract (enumeration : Scalar ≃ Fin cardinality) :
    CallingConvention.Realizes (eliminationPresentation enumeration) StandardGaussJordanElimination.readOnly
      StandardGaussJordanElimination.sizeTapes StandardGaussJordanElimination.outputTapes
      (StandardGaussJordanElimination.algorithm enumeration)
      (StandardGaussJordanElimination.entry ((FieldRow.scalarDomain enumeration).width Empty.elim))
      (StandardGaussJordanElimination.exit ((FieldRow.scalarDomain enumeration).width Empty.elim))
      (fun sizes _ => sizes 1 < 2 ^ sizes 0 ∧ sizes 2 < 2 ^ sizes 0 ∧ sizes 1 * sizes 2 ≤ 2 ^ sizes 0)
      (fun sizes input output => output () = GaussJordan.eliminate (Scalar := Scalar)
        (input ⟨StandardGaussJordanElimination.inputTape, rfl⟩)) := by
  classical
  refine CallingConvention.realizes_reindex (eliminationPresentationValues enumeration)
    (by intro name sizes; fin_cases name <;> rfl)
    (by intro name sizes value; fin_cases name <;> rfl)
    StandardGaussJordanElimination.readOnly StandardGaussJordanElimination.sizeTapes
    StandardGaussJordanElimination.outputTapes (StandardGaussJordanElimination.algorithm enumeration)
    (StandardGaussJordanElimination.entry ((FieldRow.scalarDomain enumeration).width Empty.elim))
    (StandardGaussJordanElimination.exit ((FieldRow.scalarDomain enumeration).width Empty.elim))
    _ _ _ _ (by intro sizes input valid; exact valid) ?_
    (StandardGaussJordanElimination.contract enumeration)
  intro sizes input output correct
  change (matrixEquiv (Carrier := Scalar) sizes).symm (output ()) =
    GaussJordan.eliminate (Scalar := Scalar) ((matrixEquiv (Carrier := Scalar) sizes).symm
      (matrixEquiv sizes (input ⟨StandardGaussJordanElimination.inputTape, rfl⟩))) at correct
  change (matrixEquiv (Carrier := Scalar) sizes).symm (output ()) =
    GaussJordan.eliminate (Scalar := Scalar) (input ⟨StandardGaussJordanElimination.inputTape, rfl⟩)
  exact correct.trans (congrArg (GaussJordan.eliminate (Scalar := Scalar))
    ((matrixEquiv (Carrier := Scalar) sizes).symm_apply_apply _))

end Realizable.Internal

open Realizable.Internal in
/-- The public certificate contains neither workspace names nor runtime bounds. -/
private theorem gaussJordanWithCapacity_realizable (enumeration : Scalar ≃ Fin cardinality) :
    (gaussJordanWithCapacity enumeration).Realizable := by
  refine ofNamedLayout (gaussJordanWithCapacity enumeration) (eliminationPresentation enumeration)
    StandardGaussJordanElimination.readOnly StandardGaussJordanElimination.sizeTapes
    StandardGaussJordanElimination.outputTapes (StandardGaussJordanElimination.algorithm enumeration)
    (StandardGaussJordanElimination.entry ((FieldRow.scalarDomain enumeration).width Empty.elim))
    (StandardGaussJordanElimination.exit ((FieldRow.scalarDomain enumeration).width Empty.elim))
    _ _ (eliminationPresentation_contract enumeration) eliminationPlacement
    (by intro role; fin_cases role <;> rfl) (by intro role; fin_cases role <;> rfl)
    (by intro name outside; fin_cases name <;> first
      | rfl
      | exact False.elim (outside ⟨.inl 0, rfl⟩)
      | exact False.elim (outside ⟨.inl 1, rfl⟩)
      | exact False.elim (outside ⟨.inl 2, rfl⟩)
      | exact False.elim (outside ⟨.inr (.inl ()), rfl⟩))
    (by intro parameter; rfl) () rfl (by intro sizes input valid; exact valid) ?_
  intro sizes input valid output correct
  exact congrArg (encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes) correct

/-- Finite-field elimination has just two public sizes, rows and columns.
Counter capacity is constructed privately; every rectangular matrix is admissible. -/
noncomputable def gaussJordan (enumeration : Scalar ≃ Fin cardinality) : Computation (Fin 2) Unit :=
  ((gaussJordanWithCapacity enumeration).withInternalSize).withPrecondition
    (fun _ _ => True) (fun sizes _ _ => Realizable.Internal.internalCapacity_fits sizes)

/-- One finite algorithm works for every pair of dimensions. Its private size
header, scratch tapes, controllers, and polynomial bound remain existential. -/
theorem gaussJordan_realizable (enumeration : Scalar ≃ Fin cardinality) :
    (gaussJordan enumeration).Realizable :=
  ((gaussJordanWithCapacity_realizable enumeration).withInternalSize).withPrecondition
    (fun _ _ => True) (fun sizes _ _ => Realizable.Internal.internalCapacity_fits sizes)

/-- Elimination preserves the row space and returns reduced row-echelon form. -/
theorem gaussJordan_correct (enumeration : Scalar ≃ Fin cardinality) (sizes : Fin 2 → ℕ)
    (arguments : (gaussJordan enumeration).Arguments sizes)
    (valid : (gaussJordan enumeration).precondition sizes arguments) :
    Matrix.RowEquivalent (R := Scalar) (arguments () : Matrix (Fin (sizes 0)) (Fin (sizes 1)) Scalar)
      ((gaussJordan enumeration).compute sizes ⟨arguments, valid⟩) ∧
      Matrix.IsReducedRowEchelon (R := Scalar)
        ((gaussJordan enumeration).compute sizes ⟨arguments, valid⟩ : Matrix (Fin (sizes 0)) (Fin (sizes 1)) Scalar) :=
  ⟨GaussJordan.rowEquivalent (Scalar := Scalar) _, GaussJordan.reducedRowEchelon (Scalar := Scalar) _⟩

end Polytime2.Computation
