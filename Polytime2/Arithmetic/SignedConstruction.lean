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

import Polytime2.Arithmetic.SignedOperations
import Polytime2.Arithmetic.CounterOperations
import Polytime2.Computation.Reindex
import Polytime2.Computation.Substitution
import Polytime2.Arithmetic.WidthOperations
import Polytime2.Arithmetic.BitComparison

/-! # Constructing integers from certified canonical sign/magnitude results

Arithmetic constructs a sign/magnitude pair through ordinary certified product
operations. The sole admissibility condition excludes negative zero. This rule
then reuses the same word as an ordinary bounded integer, without a new machine.
-/

namespace Polytime2.Computation.Realizable.Internal

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

noncomputable def integerOfParts (width : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  unaryMap (booleans.prod (binaryNaturalsOfWidth width)) (binaryIntegers width)
    (fun _ parts => parts.1 = true → parts.2.val ≠ 0)
    (fun sizes value => (SignedEncoding.representationEquiv (MvPolynomial.eval sizes width)).symm
      ⟨value.val, value.property⟩)

theorem integerOfParts_realizable (width : MvPolynomial Parameter ℕ) :
    (integerOfParts width).Realizable := by
  have copied := (copy_realizable (booleans.prod (binaryNaturalsOfWidth width))).withPrecondition
    (integerOfParts width).precondition (by intros; trivial)
  have refined := copied.refineOutput
    (fun _ parts => parts.1 = true → parts.2.val ≠ 0)
    (fun _ arguments => arguments.property)
  exact refined.reinterpretOutput (binaryIntegers width)
    (fun sizes => (SignedEncoding.representationEquiv (MvPolynomial.eval sizes width)).symm)
    (by intros; rfl)
    (fun sizes parts => congrArg ArrayEncoding.bits (binaryIntegers_encode_parts width sizes parts))

/-- Interpret an ordinary magnitude as a nonnegative signed integer. -/
noncomputable def integerOfMagnitude (width : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  encodingMap (binaryNaturalsOfWidth width) (binaryIntegers width)
    (fun _ value => ⟨(value.val : ℤ), by simpa using value.isLt⟩)

theorem integerOfMagnitude_realizable (width : MvPolynomial Parameter ℕ) :
    (integerOfMagnitude width).Realizable := by
  let inputs := (integerOfMagnitude width).inputDomains
  have sign := (booleanOperation_realizable (Parameter := Parameter) (Argument := Empty) (fun _ => false)).onResults
    inputs (fun _ _ => True) (fun impossible => impossible.elim) (by intros; trivial)
    (fun impossible => impossible.elim)
  have parts := Realizable.pairOutputs inputs booleans (binaryNaturalsOfWidth width)
    (fun _ _ => True) _ _ sign (copy_realizable (binaryNaturalsOfWidth width))
  have constructed := parts.followedBy (integerOfParts_realizable width) rfl (by
    intro sizes arguments valid
    change false = true → _
    simp)
  exact constructed.withSpecification (fun _ _ => True) (integerOfMagnitude width).compute
    (by intros; trivial) (by intros; rfl)

/-- A Boolean table may return any of the three one-bit-magnitude integers. -/
noncomputable def integerBooleanOperation {Argument : Type} [Fintype Argument]
    (operation : (Argument → Bool) → {value : ℤ // value.natAbs < 2}) : Computation Parameter Argument where
  inputDomains _ := booleans
  outputDomain := binaryIntegers 1
  precondition _ _ := True
  compute _ arguments := ⟨(operation arguments.val).val, by simpa using (operation arguments.val).property⟩

theorem integerBooleanOperation_realizable {Argument : Type} [Fintype Argument]
    (operation : (Argument → Bool) → {value : ℤ // value.natAbs < 2}) :
    (integerBooleanOperation (Parameter := Parameter) operation).Realizable := by
  have words (sizes : Parameter → ℕ) (value : {value : ℤ // value.natAbs < 2}) :
      ArrayEncoding.bits ((binaryIntegers 1).encode sizes ⟨value.val, by simpa using value.property⟩) =
        ArrayEncoding.bits (((binaryIntegers (Parameter := Empty) 1).constant).encode sizes
          ⟨value.val, by simpa using value.property⟩) := by
    let targetValue : (binaryIntegers 1).Carrier sizes := ⟨value.val, by simpa using value.property⟩
    let sourceValue : (binaryIntegers (Parameter := Empty) 1).Carrier Empty.elim :=
      ⟨value.val, by simpa using value.property⟩
    exact (binaryIntegers_fixed_encode_bits 1 sizes targetValue).trans
      ((binaryIntegers_fixed_encode_bits 1 Empty.elim sourceValue).symm.trans
        (constant_encode_bits (binaryIntegers (Parameter := Empty) 1) sizes sourceValue).symm)
  have table := (finiteOperation_realizable (fun _ : Argument => (booleans : EncodedDomain Empty))
    (binaryIntegers 1) (fun flags => ⟨(operation flags).val, by simpa using (operation flags).property⟩)).withConstantSizes
      (Parameter := Parameter)
  have inputs := table.reinterpretInputs (fun _ => booleans) (fun _ _ value => value)
    (by intros; simp [Computation.withConstantSizes, finiteOperation, booleans,
      EncodedDomain.width, EncodedDomain.constant, fixed, ofCodec])
    (fun _ sizes value => (fixed_encode_bits finTwoEquiv.symm sizes value).trans
      ((fixed_encode_bits finTwoEquiv.symm Empty.elim value).symm.trans
        (constant_encode_bits (booleans : EncodedDomain Empty) sizes value).symm))
    (fun _ _ => True) (by intros; trivial)
  exact inputs.reinterpretOutput (binaryIntegers 1)
    (fun sizes value => ⟨value.val, by simpa using value.property⟩)
    (by intros; simp [Computation.withConstantSizes, finiteOperation,
      Computation.reinterpretInputs, EncodedDomain.constant, ofCodec])
    (fun sizes value => words sizes ⟨value.val, by simpa using value.property⟩)

/-- Reuse the unsigned nonzero scan at an exact polynomial magnitude width. -/
noncomputable def naturalNonzero (width : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  unaryMap (binaryNaturalsOfWidth width) booleans (fun _ _ => True)
    (fun _ value => decide (0 < value.val.val))

theorem naturalNonzero_realizable (width : MvPolynomial Parameter ℕ) :
    (naturalNonzero width).Realizable := by
  have source := (counterNonzero_realizable.substitute (fun _ : Unit => width)).reinterpretInputs
    (fun _ => binaryNaturalsOfWidth width) (fun _ _ value => value)
    (by
      intro name sizes
      change (binaryNaturalsOfWidth width).width sizes =
        ((binaryNaturals ()).substitute (fun _ : Unit => width)).width sizes
      simp [SizeSubstitution.assignment])
    (fun _ sizes value => binaryNaturals_substitute_bits (fun _ : Unit => width) () sizes value)
    (fun _ _ => True) (by intros; trivial)
  exact source.reinterpretOutput booleans (fun _ value => value)
    (by
      intro sizes
      change booleans.width sizes = (booleans.substitute (fun _ : Unit => width)).width sizes
      simp [booleans, fixed, ofCodec])
    (fun sizes value => (fixed_encode_bits finTwoEquiv.symm sizes value).trans
      ((fixed_encode_bits finTwoEquiv.symm (SizeSubstitution.assignment (fun _ : Unit => width) sizes) value).symm.trans
        (substitute_encode_bits (booleans : EncodedDomain Unit) (fun _ : Unit => width) sizes value).symm))

end Polytime2.Computation.Realizable.Internal
