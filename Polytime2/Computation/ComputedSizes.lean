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

import Polytime2.Computation.Dependent
import Polytime2.Encoding.BoundedUnary
import Polytime2.Encoding.SizeSubstitution
import Polytime2.Arrays.FirstFalse
import Polytime2.Arithmetic.CounterOperations

/-! # Mathematical interfaces for calls at computed size assignments

Computed sizes are bounded unary data. A call frame is an ordinary dependent
pair of these sizes and the callee's exact mathematical arguments or result.
The payload is zero padded privately to the polynomial majorant's width.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

variable {Parameter NewParameter InputName : Type}
variable [Fintype Parameter] [Fintype NewParameter] [Fintype InputName]

/-- One bounded unary value per callee parameter, in a fixed finite record. -/
noncomputable def computedSizeDomain (bounds : NewParameter → MvPolynomial Parameter ℕ) :
    EncodedDomain Parameter :=
  EncodedDomain.namedRecord (fun parameter => EncodedDomain.boundedUnary (bounds parameter))

/-- Runtime counts determine the callee assignment; bounds are not substituted
for the actual counts. -/
def computedSizeAssignment (bounds : NewParameter → MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ) (values : (computedSizeDomain bounds).Carrier sizes) : NewParameter → ℕ :=
  fun parameter => (values parameter).val

/-- Computed size bounds majorize every dependent payload width. -/
theorem computedSizeWidth_bound (bounds : NewParameter → MvPolynomial Parameter ℕ)
    (payload : EncodedDomain NewParameter) (sizes : Parameter → ℕ)
    (values : (computedSizeDomain bounds).Carrier sizes) :
    payload.width (computedSizeAssignment bounds sizes values) ≤
      MvPolynomial.eval sizes (SizeSubstitution.polynomial bounds payload.widthPolynomial) :=
  SizeSubstitution.eval_le bounds payload.widthPolynomial sizes
    (computedSizeAssignment bounds sizes values) (fun parameter => by
      change (values parameter).val ≤ MvPolynomial.eval sizes (bounds parameter)
      exact Nat.le_of_lt_succ (values parameter).isLt)

/-- A dependent payload has a polynomial capacity at every computed assignment.
-/
noncomputable def atComputedSizeDomain (bounds : NewParameter → MvPolynomial Parameter ℕ)
    (payload : EncodedDomain NewParameter) : EncodedDomain Parameter :=
  EncodedDomain.boundedSigma (computedSizeDomain bounds) (computedSizeAssignment bounds)
    payload (SizeSubstitution.polynomial bounds payload.widthPolynomial)
    (computedSizeWidth_bound bounds payload)

/-- Observe the actual mathematical size assignment together with its payload,
forgetting the bounded count representation and private padding. -/
def atComputedSizeValue (bounds : NewParameter → MvPolynomial Parameter ℕ)
    (payload : EncodedDomain NewParameter) (sizes : Parameter → ℕ)
    (value : (atComputedSizeDomain bounds payload).Carrier sizes) :
    (assignment : NewParameter → ℕ) × payload.Carrier assignment :=
  ⟨computedSizeAssignment bounds sizes value.1, value.2⟩

/-- Extract one actual size as proper unary data before preparing its raw
header. -/
noncomputable def readComputedSize (bounds : NewParameter → MvPolynomial Parameter ℕ)
    (payload : EncodedDomain NewParameter) (parameter : NewParameter) : Computation Parameter Unit :=
  (boundedSigmaIndex (computedSizeDomain bounds) (computedSizeAssignment bounds) payload
    (SizeSubstitution.polynomial bounds payload.widthPolynomial) (computedSizeWidth_bound bounds payload)).followedBy
    (namedRecordProjection (fun parameter => EncodedDomain.boundedUnary (bounds parameter)) parameter)
    rfl (by intros; trivial)

theorem readComputedSize_realizable (bounds : NewParameter → MvPolynomial Parameter ℕ)
    (payload : EncodedDomain NewParameter) (parameter : NewParameter) :
    (readComputedSize bounds payload parameter).Realizable :=
  (boundedSigmaIndex_realizable _ _ _ _ _).followedBy
    (namedRecordProjection_realizable _ _) rfl (by intros; trivial)

/-- A call accepts a size assignment and the corresponding mathematical input.
Its result retains that assignment for subsequent dependent consumers. -/
noncomputable def atComputedSizes (computation : Computation NewParameter InputName)
    (bounds : NewParameter → MvPolynomial Parameter ℕ) : Computation Parameter Unit where
  inputDomains _ := atComputedSizeDomain bounds (EncodedDomain.namedRecord computation.inputDomains)
  outputDomain := atComputedSizeDomain bounds computation.outputDomain
  precondition sizes arguments := computation.precondition
    (computedSizeAssignment bounds sizes (arguments ()).1) (arguments ()).2
  compute sizes arguments := ⟨(arguments.val ()).1,
    computation.compute (computedSizeAssignment bounds sizes (arguments.val ()).1)
      ⟨(arguments.val ()).2, arguments.property⟩⟩

/-- Invoke a unary computation on a value at its stored size assignment. The
result retains those sizes, and callers supply no singleton argument record. -/
noncomputable def atComputedUnarySizes (computation : Computation NewParameter Unit)
    (bounds : NewParameter → MvPolynomial Parameter ℕ) : Computation Parameter Unit where
  inputDomains _ := atComputedSizeDomain bounds (computation.inputDomains ())
  outputDomain := atComputedSizeDomain bounds computation.outputDomain
  precondition sizes arguments := computation.precondition
    (computedSizeAssignment bounds sizes (arguments ()).1) (fun _ => (arguments ()).2)
  compute sizes arguments := ⟨(arguments.val ()).1,
    computation.compute (computedSizeAssignment bounds sizes (arguments.val ()).1)
      ⟨(fun _ => (arguments.val ()).2), arguments.property⟩⟩

/-- Exact polynomial sizes are the maximal values of their bounded unary
domains. -/
noncomputable def polynomialUnarySize (capacity : MvPolynomial Parameter ℕ) : Computation Parameter Empty where
  inputDomains := Empty.elim
  outputDomain := EncodedDomain.boundedUnary capacity
  precondition _ _ := True
  compute sizes _ := Fin.last (MvPolynomial.eval sizes capacity)

/-- Fixed polynomial size preparation reuses the existing private width
evaluator. -/
theorem polynomialUnarySize_realizable (capacity : MvPolynomial Parameter ℕ) :
    (polynomialUnarySize capacity).Realizable := by
  apply Realizable.withComputedWidth (polynomialUnarySize capacity) capacity
  have copied := (copy_realizable (EncodedDomain.unaryOfLength capacity)).withArguments
    ((polynomialUnarySize capacity).withUnaryWidth capacity).inputDomains
    ⟨Sum.inr, Sum.inr_injective⟩ (by intro name; cases name; rfl)
  apply copied.withEncodedOutput (EncodedDomain.boundedUnary capacity)
    ((polynomialUnarySize capacity).withUnaryWidth capacity).compute (fun _ => rfl)
  intro sizes arguments
  change CallingConvention.encoded (EncodedDomain.boundedUnary capacity) sizes (Fin.last _) =
    CallingConvention.encoded (EncodedDomain.unaryOfLength capacity) sizes (arguments.val (.inr ()))
  rw [show (arguments.val (.inr ()) : PUnit.{1}) = PUnit.unit from @Subsingleton.elim PUnit.{1} inferInstance _ _,
    EncodedDomain.encoded_unaryOfLength]
  change CallingConvention.tape (EncodedDomain.ArrayEncoding.bits (BoundedUnary.encode _ _)) = _
  rw [BoundedUnary.encode_bits]
  simp [BoundedUnary.bits, CallingConvention.unary, EncodedDomain.boundedUnary]

namespace FirstFalse

/-- Leading flags form a canonical unary word, including the all-true sentinel.
-/
theorem mask_unary (flags : List Bool) :
    mask flags = BoundedUnary.bits flags.length (flags.findIdx (! ·)) := by
  induction flags with
  | nil => rfl
  | cons bit flags hypothesis =>
    cases bit <;> simp [mask, BoundedUnary.bits, List.findIdx_cons, hypothesis, List.replicate_succ]

end FirstFalse

/-- A certified unary size depending on the input flags, not just their length.
-/
noncomputable def leadingUnarySize (capacity : MvPolynomial Parameter ℕ) : Computation Parameter Unit where
  inputDomains _ := EncodedDomain.booleans.arrayOfLength capacity
  outputDomain := EncodedDomain.boundedUnary capacity
  precondition _ _ := True
  compute sizes arguments := ⟨(List.ofFn (arguments.val ())).findIdx (! ·), by
    have bounded := List.findIdx_le_length (p := (! ·)) (xs := List.ofFn (arguments.val ()))
    simpa only [List.length_ofFn] using Nat.lt_succ_of_le bounded⟩

/-- Reinterpret the existing finite-memory scan; no counting machine is needed.
-/
theorem leadingUnarySize_realizable (capacity : MvPolynomial Parameter ℕ) :
    (leadingUnarySize capacity).Realizable := by
  apply (leadingFlags_realizable capacity).withEncodedOutput
    (EncodedDomain.boundedUnary capacity) (leadingUnarySize capacity).compute (by
      intro sizes
      simp [leadingFlags, encodingMap, unaryMap, EncodedDomain.boundedUnary,
        EncodedDomain.arrayOfLength, EncodedDomain.booleans, EncodedDomain.fixed, EncodedDomain.ofCodec,
        show Nat.clog 2 2 = 1 by decide])
  intro sizes arguments
  apply congrArg CallingConvention.tape
  change EncodedDomain.ArrayEncoding.bits (BoundedUnary.encode _ _) =
    EncodedDomain.ArrayEncoding.bits ((EncodedDomain.booleans.arrayOfLength capacity).encode sizes
      (FirstFalse.masked (arguments.val ())))
  rw [BoundedUnary.encode_bits, FirstFalse.boolean_bits, FirstFalse.ofFn_masked, FirstFalse.mask_unary]
  simp only [leadingUnarySize, List.length_ofFn, EncodedDomain.boundedUnary]

end Polytime2.Computation
