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

import Polytime2.Arrays.PackingRaw
import Polytime2.Arrays.PackingTransport
import Polytime2.Arrays.FirstFalse
import Polytime2.Arrays.Transform

/-! # Raw-block packing with private polynomial counter capacity -/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain ArrayPacking

variable {Parameter : Type} [Fintype Parameter]

/-- Both dimensions are arbitrary caller polynomials; no counter-capacity size
is externally visible. This intermediate result still contains raw padding. -/
noncomputable def arrayPackBits (width length : MvPolynomial Parameter ℕ) : Computation Parameter Bool where
  inputDomains choice := if choice then (bitVectors width).arrayOfLength length
    else booleans.arrayOfLength length
  outputDomain := (bitVectors width).arrayOfLength length
  precondition _ _ := True
  compute _ arguments := rawPack id (arguments.val false) (arguments.val true)

theorem arrayPackBits_realizable (width length : MvPolynomial Parameter ℕ) :
    (arrayPackBits width length).Realizable := by
  classical
  let element : EncodedDomain (Fin 3) := bitVectors (MvPolynomial.X 0)
  let kernel := arrayPackRawSized element 2 (MvPolynomial.X 1)
  let polynomials : Fin 3 → MvPolynomial Parameter ℕ := ![width, length, length + 1]
  let specialized := kernel.substitute polynomials
  let target := arrayPackBits width length
  let actual := SizeSubstitution.assignment polynomials
  have lengthEq sizes : MvPolynomial.eval (actual sizes) (MvPolynomial.X 1) = MvPolynomial.eval sizes length := by
    simp [actual, SizeSubstitution.assignment, polynomials]
  have widthEq sizes : MvPolynomial.eval (actual sizes) (MvPolynomial.X 0) = MvPolynomial.eval sizes width := by
    simp [actual, SizeSubstitution.assignment, polynomials]
  let inputs (choice : Bool) sizes : (target.inputDomains choice).Carrier sizes ≃
      (specialized.inputDomains choice).Carrier sizes :=
    match choice with
    | false => (arrayCast (lengthEq sizes) (Equiv.refl Bool)).symm
    | true => (bitArrayCast (lengthEq sizes) (widthEq sizes)).symm
  let output sizes : target.outputDomain.Carrier sizes ≃ specialized.outputDomain.Carrier sizes :=
    (bitArrayCast (lengthEq sizes) (widthEq sizes)).symm
  have inputWidths choice sizes : (target.inputDomains choice).width sizes = (specialized.inputDomains choice).width sizes := by
    cases choice <;>
      simp [target, arrayPackBits, specialized, Computation.substitute, kernel, arrayPackRawSized,
        EncodedDomain.substitute, arrayOfLength, booleans, fixed, ofCodec,
        element, bitVectors, actual, SizeSubstitution.polynomial_eval, SizeSubstitution.assignment,
        polynomials, show Nat.clog 2 2 = 1 by decide]
  have outputWidths sizes : target.outputDomain.width sizes = specialized.outputDomain.width sizes :=
    inputWidths true sizes
  have inputEncodings choice sizes value :
      ArrayEncoding.bits ((target.inputDomains choice).encode sizes value) =
        ArrayEncoding.bits ((specialized.inputDomains choice).encode sizes (inputs choice sizes value)) := by
    cases choice
    · change ArrayEncoding.bits ((booleans.arrayOfLength length).encode sizes value) =
        ArrayEncoding.bits (((booleans.arrayOfLength (MvPolynomial.X (1 : Fin 3))).substitute polynomials).encode sizes
          ((arrayCast (lengthEq sizes) (Equiv.refl Bool)).symm value))
      rw [substitute_encode_bits, FirstFalse.boolean_bits, FirstFalse.boolean_bits]
      exact (arrayCast_ofFn (lengthEq sizes) value).symm
    · change ArrayEncoding.bits (((bitVectors width).arrayOfLength length).encode sizes value) =
        ArrayEncoding.bits ((((bitVectors (MvPolynomial.X (0 : Fin 3))).arrayOfLength
          (MvPolynomial.X 1)).substitute polynomials).encode sizes
          ((bitArrayCast (lengthEq sizes) (widthEq sizes)).symm value))
      rw [substitute_encode_bits]
      simp only [arrayOfLength, ofCodec, ArrayEncoding.bits_cast]
      exact (bitArrayCast_bits (lengthEq sizes) (widthEq sizes) value).symm
  have outputEncodings sizes value :
      ArrayEncoding.bits (target.outputDomain.encode sizes value) =
        ArrayEncoding.bits (specialized.outputDomain.encode sizes (output sizes value)) := inputEncodings true sizes value
  have normalized := (arrayPackRawSized_realizable element 2 (MvPolynomial.X 1)).substitute polynomials |>.reindexDomains
    target.inputDomains target.outputDomain inputs output inputWidths outputWidths inputEncodings outputEncodings
  have compatible sizes (arguments : target.Arguments sizes) (_valid : target.precondition sizes arguments) :
      (specialized.reindexDomains target.inputDomains target.outputDomain inputs output).precondition sizes arguments := by
    change MvPolynomial.eval (actual sizes) (MvPolynomial.X 1) < 2 ^ actual sizes 2
    simp only [lengthEq]
    have fits := Nat.lt_two_pow_self (n := MvPolynomial.eval sizes length + 1)
    simpa [actual, SizeSubstitution.assignment, polynomials] using
      (lt_trans (Nat.lt_succ_self _) fits)
  exact normalized.withSpecification target.precondition target.compute compatible (by
    intro sizes arguments valid
    exact rawPack_bitArrayCast (lengthEq sizes) (widthEq sizes) (arguments false) (arguments true))

/-- Generic element packing uses its existing canonical encoding. Padding is
raw storage and imposes no default-value or constant-width requirement. -/
noncomputable def arrayPackRaw (element : EncodedDomain Parameter)
    (length : MvPolynomial Parameter ℕ) : Computation Parameter Bool where
  inputDomains choice := if choice then element.arrayOfLength length
    else booleans.arrayOfLength length
  outputDomain := (bitVectors element.widthPolynomial).arrayOfLength length
  precondition _ _ := True
  compute sizes arguments := rawPack (element.encode sizes) (arguments.val false) (arguments.val true)

theorem arrayPackRaw_realizable (element : EncodedDomain Parameter)
    (length : MvPolynomial Parameter ℕ) : (arrayPackRaw element length).Realizable := by
  let target := arrayPackRaw element length
  let raw := bitVectors element.widthPolynomial
  let values (choice : Bool) sizes (arguments : {arguments : target.Arguments sizes // target.precondition sizes arguments}) :
      ((arrayPackBits element.widthPolynomial length).inputDomains choice).Carrier sizes :=
    match choice with
    | false => arguments.val false
    | true => fun index => element.encode sizes (arguments.val true index)
  have producers choice : (Computation.mk target.inputDomains
      ((arrayPackBits element.widthPolynomial length).inputDomains choice) target.precondition (values choice)).Realizable := by
    cases choice
    · exact Realizable.argument target.inputDomains false target.precondition
    · have encoded := mapArray_realizable element raw length element.encode (encode_realizable element)
      exact encoded.onResults target.inputDomains target.precondition
        (fun _ sizes arguments => arguments.val true) (by intros; trivial)
        (fun _ => Realizable.argument target.inputDomains true target.precondition)
  exact (arrayPackBits_realizable element.widthPolynomial length).onResults target.inputDomains target.precondition
    values (by intros; trivial) producers

end Polytime2.Computation

