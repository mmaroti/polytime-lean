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

import Polytime2.Examples.SMP.DenseConversion
import Mathlib.ModelTheory.Algebra.Ring.Basic
import Mathlib.Data.ZMod.Basic

/-! # A concrete SMP preparation over the four-element ring

The specialization uses the mathematical ring language and carrier directly.
All coordinate-image and monolith preparation data are supplied by the generic
construction; no decomposition or graph certificates are assumed as input.
-/

namespace Polytime2.SMP.RingExample

open FirstOrder FirstOrder.Language

local instance : FirstOrder.Ring.CompatibleRing (ZMod 4) :=
  FirstOrder.Ring.compatibleRingOfRing (ZMod 4)

/-- Two independent public dimensions: coordinates and generators. -/
noncomputable def preparation : Computation (Fin 2) Unit :=
  denseConversion (L := Language.ring) (Carrier := ZMod 4) (MvPolynomial.X 0) (MvPolynomial.X 1)

theorem preparation_realizable : preparation.Realizable := denseConversion_realizable _ _

theorem preparation_tm0 : preparation.TM0Realizable := denseConversion_tm0

theorem preparation_correct (sizes : Fin 2 → ℕ) (arguments : preparation.Arguments sizes) :
    DenseOutputCorrect (L := Language.ring) (Carrier := ZMod 4)
      (MvPolynomial.X 0) (MvPolynomial.X 1) sizes arguments
      (preparation.compute sizes ⟨arguments, trivial⟩) :=
  denseConversion_correct _ _ _ _

/-- Empty-coordinate instances return the accepted sentinel, with no hidden
positive-dimension or nonempty-generator requirement. -/
theorem empty_coordinates (sizes : Fin 2 → ℕ) (zero : sizes 0 = 0)
    (arguments : preparation.Arguments sizes) :
    (preparation.compute sizes ⟨arguments, trivial⟩).1.2.toNat = 0 := by
  change ((denseConversion (L := Language.ring) (Carrier := ZMod 4)
    (MvPolynomial.X 0) (MvPolynomial.X 1)).compute sizes ⟨arguments, trivial⟩).1.2.toNat = 0
  have core := denseConversion_core (L := Language.ring) (Carrier := ZMod 4)
    (MvPolynomial.X (0 : Fin 2)) (MvPolynomial.X 1) sizes arguments
  have marker := congrArg (fun result => result.2.toNat) core
  have computed := conversionResult_compute (L := Language.ring) (Carrier := ZMod 4)
    (MvPolynomial.X (0 : Fin 2)) (MvPolynomial.X 1) sizes arguments
  have resultMarker := congrArg (fun result => result.2.toNat) computed
  refine marker.trans (resultMarker.trans ?_)
  have bounded := rejectionCoordinate_bound (L := Language.ring) (Carrier := ZMod 4)
    (MvPolynomial.X 0) (MvPolynomial.X 1) sizes arguments
  simpa only [MvPolynomial.eval_X, zero, Nat.le_zero] using bounded

end Polytime2.SMP.RingExample
