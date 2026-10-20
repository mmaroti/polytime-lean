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

import Polytime2.Computation.ComputedCall
import Polytime2.Computation.ComputedSizeRun
import Polytime2.Primitives.UnaryHeader
import Polytime2.TM0.Computation
import Polytime2.Computation.Substitution

/-! # Value-dependent unary sizes and dependent call frames

The callee's width is selected by input data. Exact mathematical values remain
in the dependent pair while only their encodings receive capacity padding.
The public composition rule hides all preparation and execution witnesses.
-/

namespace Polytime2.Examples.ComputedSizes

open _root_.Polytime2.Computation

/-- Leading-prefix lengths are input-dependent and have certified unary
evaluation, including width zero. -/
example (capacity : MvPolynomial Unit ℕ) : (leadingUnarySize capacity).TM0Realizable :=
  (leadingUnarySize_realizable capacity).tm0

example (capacity : MvPolynomial Unit ℕ) : (polynomialUnarySize capacity).TM0Realizable :=
  (polynomialUnarySize_realizable capacity).tm0

example (capacity : MvPolynomial Unit ℕ) (sizes : Unit → ℕ)
    (flags : Fin (MvPolynomial.eval sizes capacity) → Bool) :
    ((leadingUnarySize capacity).compute sizes ⟨(fun _ => flags), trivial⟩).val =
      (List.ofFn flags).findIdx (! ·) := rfl

example : FirstFalse.mask [true, false, true] = BoundedUnary.bits 3 1 := by decide
example : BoundedUnary.decode 0 0 = some (0 : Fin 1) := by decide

/-- An interrupted prefix is not another encoding of the same unary count. -/
example : BoundedUnary.decode 3 (5#3) = none := by decide

private noncomputable def wordDomain : EncodedDomain Unit := EncodedDomain.bitVectors (MvPolynomial.X ())
private noncomputable def bounds : Unit → MvPolynomial Unit ℕ := fun _ => MvPolynomial.X ()

/-- Actual size values can be extracted and exported without exposing machines. -/
example : (readComputedSize bounds wordDomain ()).TM0Realizable :=
  (readComputedSize_realizable bounds wordDomain ()).tm0

/-- Fixed polynomial size assignments use the public composition rule. -/
example : ((copy wordDomain).substitute
    (fun _ : Unit => (MvPolynomial.X ()) ^ 2)).TM0Realizable :=
  ((copy_realizable wordDomain).substitute _).tm0

/-- A unary dependent call needs no singleton argument record and exports to TM0. -/
example : ((copy wordDomain).atComputedUnarySizes bounds).TM0Realizable :=
  ((copy_realizable wordDomain).atComputedUnarySizes bounds).tm0

/-- Empty parameter and argument families need no special operational case. -/
example : ((polynomialUnarySize (Parameter := Empty) 0).atComputedSizes
    (fun parameter : Empty => parameter.elim : Empty → MvPolynomial Unit ℕ)).TM0Realizable :=
  ((polynomialUnarySize_realizable (Parameter := Empty) 0).atComputedSizes _).tm0

/-- The callee sees the chosen count, never the upper capacity in its place. -/
example (sizes : Unit → ℕ)
    (input : ((copy wordDomain).atComputedUnarySizes bounds).inputDomains () |>.Carrier sizes) :
    (((copy wordDomain).atComputedUnarySizes bounds).compute sizes ⟨(fun _ => input), trivial⟩).2 = input.2 := rfl

/-- Call-frame round trips preserve actual dependent mathematical arguments. -/
example (sizes : Unit → ℕ)
    (input : ((copy wordDomain).atComputedUnarySizes bounds).inputDomains () |>.Carrier sizes) :
    (((copy wordDomain).atComputedUnarySizes bounds).inputDomains ()).decode sizes
      ((((copy wordDomain).atComputedUnarySizes bounds).inputDomains ()).encode sizes input) = some input :=
  (((copy wordDomain).atComputedUnarySizes bounds).inputDomains ()).decode_encode sizes input

/-- A bound on a computed count majorizes every callee polynomial, not only
linear storage sizes. -/
example (size actual : ℕ) (bounded : actual ≤ size) :
    MvPolynomial.eval (fun _ : Unit => actual) ((MvPolynomial.X ()) ^ 2 + 3 * MvPolynomial.X () + 4) ≤
      MvPolynomial.eval (fun _ : Unit => size) ((MvPolynomial.X ()) ^ 2 + 3 * MvPolynomial.X () + 4) :=
  SizeSubstitution.eval_mono _ (fun _ => bounded)

/-- Exact polynomial substitution is the corresponding domain view. -/
example (sizes : Unit → ℕ) :
    (wordDomain.substitute (fun _ : Unit => (MvPolynomial.X ()) ^ 2)).width sizes = sizes () ^ 2 := by
  simp [EncodedDomain.substitute, wordDomain, EncodedDomain.bitVectors, SizeSubstitution.assignment]

end Polytime2.Examples.ComputedSizes
