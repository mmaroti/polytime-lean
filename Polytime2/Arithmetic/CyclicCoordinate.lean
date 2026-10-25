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

import Polytime2.Computation.Specification
import Polytime2.Encoding.Cyclic
import Polytime2.Arithmetic.SignedQuotient
import Polytime2.Arithmetic.SignedWidth

/-! # Certified cyclic and free quotient coordinates

Input a bounded natural modulus and an independently bounded integer. Return
the actual ZMod coordinate, retaining the modulus. A zero modulus preserves
the original signed integer. All operand preparation and canonical remainder
construction are certified; capacities are derived from the two input widths.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain Realizable.Internal

variable {Parameter : Type} [Fintype Parameter]

private noncomputable def inputs (modulusWidth valueWidth : MvPolynomial Parameter ℕ) : Bool → EncodedDomain Parameter :=
  fun choice => if choice then binaryIntegers valueWidth else binaryNaturalsOfWidth modulusWidth

private noncomputable def divisor (modulusWidth valueWidth : MvPolynomial Parameter ℕ) :=
  ((integerOfMagnitude modulusWidth).withArguments (inputs modulusWidth valueWidth) (MultiTape.oneTape false) (by intros; rfl)).followedBy
    (integerWidenTo modulusWidth valueWidth (modulusWidth + valueWidth) rfl) rfl (by intros; trivial)

private noncomputable def dividend (modulusWidth valueWidth : MvPolynomial Parameter ℕ) :=
  (integerWidenTo valueWidth modulusWidth (modulusWidth + valueWidth) (by ring)).withArguments
    (inputs modulusWidth valueWidth) (MultiTape.oneTape true) (by intros; rfl)

private noncomputable def remainder (modulusWidth valueWidth : MvPolynomial Parameter ℕ) :=
  (integerTotalRemainder (modulusWidth + valueWidth)).onResults (inputs modulusWidth valueWidth) (fun _ _ => True)
    (fun choice sizes arguments => match choice with
      | false => (dividend modulusWidth valueWidth).compute sizes arguments
      | true => (divisor modulusWidth valueWidth).compute sizes arguments) (by intros; trivial)

private theorem remainder_realizable (modulusWidth valueWidth : MvPolynomial Parameter ℕ) :
    (remainder modulusWidth valueWidth).Realizable := by
  have numerator := (integerWidenTo_realizable valueWidth modulusWidth (modulusWidth + valueWidth) (by ring)).withArguments
    (inputs modulusWidth valueWidth) (MultiTape.oneTape true) (by intros; rfl)
  have denominator := ((integerOfMagnitude_realizable modulusWidth).withArguments
    (inputs modulusWidth valueWidth) (MultiTape.oneTape false) (by intros; rfl)).followedBy
      (integerWidenTo_realizable modulusWidth valueWidth (modulusWidth + valueWidth) rfl) rfl (by intros; trivial)
  apply (integerTotalRemainder_realizable (modulusWidth + valueWidth)).onResults
    (inputs modulusWidth valueWidth) (fun _ _ => True) _ (by intros; trivial)
  intro choice
  cases choice
  · exact numerator
  · exact denominator

private theorem remainder_canonical (modulusWidth valueWidth : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (remainder modulusWidth valueWidth).Arguments sizes) :
    cyclicRepresentativeCanonical (arguments false).val
      ((remainder modulusWidth valueWidth).compute sizes ⟨arguments, trivial⟩).val := by
  change cyclicRepresentativeCanonical (arguments false).val ((arguments true).val % ((arguments false).val : ℤ))
  by_cases zero : (arguments false).val = 0
  · exact Or.inl zero
  · have positive : (0 : ℤ) < (arguments false).val := by exact_mod_cast Nat.pos_of_ne_zero zero
    exact Or.inr ⟨Int.emod_nonneg _ (ne_of_gt positive), Int.emod_lt_of_pos _ positive⟩

/-- Reduce an integer to an actual cyclic coordinate, or retain its free integer coordinate. -/
private noncomputable def implementation (modulusWidth valueWidth : MvPolynomial Parameter ℕ) : Computation Parameter Bool where
  inputDomains := inputs modulusWidth valueWidth
  outputDomain := boundedCyclic modulusWidth (modulusWidth + valueWidth)
  precondition _ _ := True
  compute sizes arguments := boundedCyclicOfRepresentative modulusWidth (modulusWidth + valueWidth) sizes
    (arguments.val false) ((remainder modulusWidth valueWidth).compute sizes arguments)
    (remainder_canonical modulusWidth valueWidth sizes arguments.val)

/-- Unsigned-to-signed conversion, total remainder, and the canonical codec view are realized. -/
private theorem implementation_realizable (modulusWidth valueWidth : MvPolynomial Parameter ℕ) :
    (implementation modulusWidth valueWidth).Realizable := by
  let computation := implementation modulusWidth valueWidth
  have paired := (Realizable.argument computation.inputDomains false computation.precondition).prodMk (remainder_realizable modulusWidth valueWidth)
  apply paired.withEncodedOutput computation.outputDomain computation.compute (by intros; rfl)
  intro sizes arguments
  apply congrArg CallingConvention.tape
  exact boundedCyclicOfRepresentative_encode_bits modulusWidth (modulusWidth + valueWidth) sizes
    (arguments.val false) ((remainder modulusWidth valueWidth).compute sizes arguments)
    (remainder_canonical modulusWidth valueWidth sizes arguments.val)

/-- The coordinate is the integer's ordinary image in ZMod, also at modulus zero. -/
private theorem implementation_correct (modulusWidth valueWidth : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (implementation modulusWidth valueWidth).Arguments sizes) :
    let result := (implementation modulusWidth valueWidth).compute sizes ⟨arguments, trivial⟩
    result.2.val = ((arguments true).val : ZMod result.1.val) := by
  change (((arguments true).val % ((arguments false).val : ℤ) : ℤ) : ZMod (arguments false).val) = _
  exact ZMod.intCast_mod _ _

/-- The ordinary image of the integer in the supplied cyclic or free group.
The canonical representative and its storage bound stay inside the codec. -/
noncomputable def integerCyclicCoordinate (modulusWidth valueWidth : MvPolynomial Parameter ℕ) :
    Computation Parameter Bool :=
  specificationBy (inputs modulusWidth valueWidth)
    (boundedCyclic modulusWidth (modulusWidth + valueWidth)) (fun _ _ => True)
    (fun _ result => (⟨result.1.val, result.2.val⟩ : (modulus : ℕ) × ZMod modulus))
    (fun _ arguments => (⟨(arguments.val false).val,
      ((arguments.val true).val : ZMod (arguments.val false).val)⟩ : (modulus : ℕ) × ZMod modulus))
    (fun sizes arguments => ⟨(implementation modulusWidth valueWidth).compute sizes arguments,
      congrArg (Sigma.mk (arguments.val false).val)
        (implementation_correct modulusWidth valueWidth sizes arguments.val)⟩)

theorem integerCyclicCoordinate_realizable (modulusWidth valueWidth : MvPolynomial Parameter ℕ) :
    (integerCyclicCoordinate modulusWidth valueWidth).Realizable := by
  apply (implementation_realizable modulusWidth valueWidth).specificationBy
  · intro sizes
    exact Fin.val_injective.sigma_map (fun _ => Subtype.val_injective)
  · intro sizes arguments valid
    exact congrArg (Sigma.mk (arguments false).val)
      (implementation_correct modulusWidth valueWidth sizes arguments)

/-- Observe the modulus and actual group element without canonicalization details. -/
theorem integerCyclicCoordinate_observe (modulusWidth valueWidth : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ) (arguments : (integerCyclicCoordinate modulusWidth valueWidth).Arguments sizes) :
    let result := (integerCyclicCoordinate modulusWidth valueWidth).compute sizes ⟨arguments, trivial⟩
    (⟨result.1.val, result.2.val⟩ : (modulus : ℕ) × ZMod modulus) =
      ⟨(arguments false).val, ((arguments true).val : ZMod (arguments false).val)⟩ := by
  exact specificationBy_correct _ (integerCyclicCoordinate modulusWidth valueWidth).outputDomain _
    (fun _ result => (⟨result.1.val, result.2.val⟩ : (modulus : ℕ) × ZMod modulus)) _ _ sizes ⟨arguments, trivial⟩

/-- The reported modulus is exactly the supplied mathematical modulus. -/
theorem integerCyclicCoordinate_modulus (modulusWidth valueWidth : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (integerCyclicCoordinate modulusWidth valueWidth).Arguments sizes) :
    ((integerCyclicCoordinate modulusWidth valueWidth).compute sizes ⟨arguments, trivial⟩).1 = arguments false := by
  apply Fin.ext
  exact congrArg Sigma.fst (integerCyclicCoordinate_observe modulusWidth valueWidth sizes arguments)

/-- The coordinate is the integer's ordinary image in ZMod, also at modulus zero. -/
theorem integerCyclicCoordinate_correct (modulusWidth valueWidth : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (integerCyclicCoordinate modulusWidth valueWidth).Arguments sizes) :
    let result := (integerCyclicCoordinate modulusWidth valueWidth).compute sizes ⟨arguments, trivial⟩
    result.2.val = ((arguments true).val : ZMod result.1.val) := by
  have observed := integerCyclicCoordinate_observe modulusWidth valueWidth sizes arguments
  exact (congrArg (fun pair : (modulus : ℕ) × ZMod modulus =>
    pair.2 = ((arguments true).val : ZMod pair.1)) observed).mpr rfl

end Polytime2.Computation
