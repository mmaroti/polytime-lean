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

import Polytime2.Arithmetic.Operations
import Polytime2.Computation.Substitution
import Polytime2.Computation.Constant
import Polytime2.Computation.Conditional
import Polytime2.Primitives.FiniteOperations
import Polytime2.Arrays.PackingTransport
import Polytime2.Encoding.ParameterRename

/-! # Comparison of words with polynomial bit widths -/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter Argument : Type} [Fintype Parameter] [Fintype Argument]

/-- A fixed Boolean operation uses the same ordinary Boolean domain at every
size assignment. -/
noncomputable def booleanOperation (operation : (Argument → Bool) → Bool) :
    Computation Parameter Argument where
  inputDomains _ := booleans
  outputDomain := booleans
  precondition _ _ := True
  compute _ arguments := operation arguments.val

theorem booleanOperation_realizable (operation : (Argument → Bool) → Bool) :
    (booleanOperation (Parameter := Parameter) operation).Realizable := by
  have table := (finiteOperation_realizable (fun _ : Argument => (booleans : EncodedDomain Empty))
    booleans (fun _ arguments => operation arguments)).withConstantSizes (Parameter := Parameter)
  exact table.reindexDomains (fun _ => booleans) booleans (fun _ _ => Equiv.refl Bool)
    (fun _ => Equiv.refl Bool)
    (by intros; simp [withConstantSizes, finiteOperation, EncodedDomain.constant, booleans, fixed, ofCodec])
    (by intros; simp [withConstantSizes, finiteOperation, EncodedDomain.constant, booleans, fixed, ofCodec])
    (by
      intros
      apply ArrayPacking.bits_injective
      simp only [withConstantSizes, finiteOperation, EncodedDomain.constant, booleans, fixed, ofCodec]
      simp only [ArrayEncoding.bits_cast, Equiv.refl_apply])
    (by
      intros
      apply ArrayPacking.bits_injective
      simp only [withConstantSizes, finiteOperation, EncodedDomain.constant, booleans, fixed, ofCodec]
      simp only [ArrayEncoding.bits_cast, Equiv.refl_apply])

/-- Unsigned comparison at an exact polynomial width. -/
noncomputable def bitsLess (width : MvPolynomial Parameter ℕ) : Computation Parameter Bool where
  inputDomains _ := bitVectors width
  outputDomain := booleans
  precondition _ _ := True
  compute _ arguments := decide ((arguments.val false).toNat < (arguments.val true).toNat)

theorem bitsLess_realizable (width : MvPolynomial Parameter ℕ) : (bitsLess width).Realizable := by
  let computation := bitsLess width
  have compared := binaryLess_realizable.substitute (fun _ : Unit => width)
  let valueEquiv sizes : BitVec (MvPolynomial.eval sizes width) ≃ Fin (2 ^ MvPolynomial.eval sizes width) :=
    ⟨BitVec.toFin, BitVec.ofFin, (by intro value; rfl), (by intro value; rfl)⟩
  exact compared.reindexDomains computation.inputDomains computation.outputDomain
    (fun _ sizes => valueEquiv sizes) (fun _ => Equiv.refl Bool)
    (by intros; simp [computation, bitsLess, binaryLess, Computation.substitute, EncodedDomain.substitute, binaryNaturals,
      bitVectors, ofCodec, SizeSubstitution.polynomial, SizeSubstitution.assignment])
    (by intros; simp [computation, bitsLess, binaryLess, Computation.substitute, EncodedDomain.substitute,
      booleans, fixed, ofCodec, SizeSubstitution.polynomial])
    (by
      intros
      apply ArrayPacking.bits_injective
      simp only [computation, bitsLess, binaryLess, Computation.substitute, EncodedDomain.substitute,
        binaryNaturals, bitVectors, ofCodec, valueEquiv, ArrayEncoding.bits_cast]
      rfl)
    (by
      intros
      apply ArrayPacking.bits_injective
      simp only [computation, bitsLess, binaryLess, Computation.substitute, EncodedDomain.substitute,
        booleans, fixed, ofCodec]
      simp only [ArrayEncoding.bits_cast, Equiv.refl_apply])

/-- Equality of source-coordinate labels needs no extra capacity parameter. -/
noncomputable def bitsEqual (width : MvPolynomial Parameter ℕ) : Computation Parameter Bool where
  inputDomains _ := bitVectors width
  outputDomain := booleans
  precondition _ _ := True
  compute _ arguments := decide (arguments.val false = arguments.val true)

theorem bitsEqual_realizable (width : MvPolynomial Parameter ℕ) : (bitsEqual width).Realizable := by
  let computation := bitsEqual width
  have forward := bitsLess_realizable width
  have backward := forward.onResults computation.inputDomains computation.precondition
    (fun choice _ arguments => arguments.val (!choice)) (by intros; trivial)
    (fun choice => Realizable.argument computation.inputDomains (!choice) computation.precondition)
  have combined := (booleanOperation_realizable (Parameter := Parameter)
    (fun flags : Bool → Bool => !(flags false) && !(flags true))).onResults
      computation.inputDomains computation.precondition
      (fun choice sizes arguments => if choice then
        decide ((arguments.val true).toNat < (arguments.val false).toNat) else
        decide ((arguments.val false).toNat < (arguments.val true).toNat))
      (by intros; trivial) (by intro choice; cases choice; exact forward; exact backward)
  exact combined.withSpecification computation.precondition computation.compute (by intros; trivial) (by
    intro sizes arguments valid
    dsimp [Computation.onResults, booleanOperation, computation, bitsEqual]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
      decide_eq_true_eq, not_lt, ← Nat.le_antisymm_iff, BitVec.toNat_inj]
    exact eq_comm)

/-- Compare words retaining their original-size interpretation inside a larger
parameter family. This is a codec transport of the same comparison. -/
noncomputable def bitsEqualAtNames {HostParameter : Type} [Fintype HostParameter]
    (width : MvPolynomial HostParameter ℕ) (names : HostParameter → Parameter) : Computation Parameter Bool where
  inputDomains _ := (bitVectors width).renameParameters names
  outputDomain := booleans
  precondition _ _ := True
  compute sizes arguments := @decide (arguments.val false = arguments.val true)
    ((inferInstance : DecidableEq (BitVec (MvPolynomial.eval (sizes ∘ names) width)))
      (arguments.val false) (arguments.val true))

theorem bitsEqualAtNames_realizable {HostParameter : Type} [Fintype HostParameter]
    (width : MvPolynomial HostParameter ℕ) (names : HostParameter → Parameter) :
    (bitsEqualAtNames width names).Realizable := by
  let computation := bitsEqualAtNames width names
  let equivalence sizes : BitVec (MvPolynomial.eval (sizes ∘ names) width) ≃
      BitVec (MvPolynomial.eval sizes (MvPolynomial.rename names width)) :=
    { toFun := fun value => value.cast (MvPolynomial.eval_rename names sizes width).symm
      invFun := fun value => value.cast (MvPolynomial.eval_rename names sizes width)
      left_inv := by intro value; simp
      right_inv := by intro value; simp }
  have transported := (bitsEqual_realizable (MvPolynomial.rename names width)).reindexDomains
    computation.inputDomains computation.outputDomain (fun _ sizes => equivalence sizes) (fun _ => Equiv.refl Bool)
    (by intros; rfl) (by intros; rfl) (by intros; rfl) (by intros; rfl)
  exact transported.withSpecification computation.precondition computation.compute (by intros; trivial) (by
    intro sizes arguments valid
    apply Bool.eq_iff_iff.mpr
    dsimp [reindexDomains, computation, bitsEqualAtNames, bitsEqual]
    simp only [decide_eq_true_eq]
    change decide (equivalence sizes (arguments false) = equivalence sizes (arguments true)) = true ↔
      arguments false = arguments true
    rw [decide_eq_true_eq]
    exact (equivalence sizes).injective.eq_iff)

end Polytime2.Computation
