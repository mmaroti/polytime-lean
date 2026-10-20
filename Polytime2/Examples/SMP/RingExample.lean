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

import Polytime2.Examples.SMP.PreparedConsumer
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
  Prepared.prepare (L := Language.ring) (Carrier := ZMod 4) (MvPolynomial.X 0) (MvPolynomial.X 1)

theorem preparation_realizable : preparation.Realizable := Prepared.prepare_realizable _ _

theorem preparation_tm0 : preparation.TM0Realizable := Prepared.prepare_tm0

theorem preparation_correct (sizes : Fin 2 → ℕ) (arguments : preparation.Arguments sizes) :
    Prepared.OutcomeCorrect (L := Language.ring) (Carrier := ZMod 4)
      (MvPolynomial.X 0) (MvPolynomial.X 1) sizes arguments
      (preparation.compute sizes ⟨arguments, trivial⟩) :=
  Prepared.prepare_specification _ _ _ _

/-- Empty-coordinate instances are accepted, including with zero generators. -/
theorem empty_coordinates (sizes : Fin 2 → ℕ) (zero : sizes 0 = 0)
    (arguments : preparation.Arguments sizes) :
    (preparation.compute sizes ⟨arguments, trivial⟩).isRight = true := by
  rcases preparation_correct sizes arguments with rejected | accepted
  · obtain ⟨coordinate, _, _, _⟩ := rejected
    have impossible : coordinate.val < 0 := by
      simpa only [MvPolynomial.eval_X, zero] using coordinate.isLt
    omega
  · obtain ⟨frame, equal, _, _, _⟩ := accepted
    simpa using congrArg Sum.isRight equal

/-- A prepared consumer sees the ordinary exact tuple domain, with no knowledge
of original coordinates, packed fields, or conversion capacities. -/
noncomputable def targetAfterPreparation : Computation (Fin 2) Unit :=
  Prepared.prepareAndConsume
    (Multisorted.tupleDomain (Prepared.enumeration (L := Language.ring) (Carrier := ZMod 4)))
    (fun _ _ => True) (fun _ value => value.val.1.2) (by intros; trivial)
    (MvPolynomial.X 0) (MvPolynomial.X 1)

theorem targetAfterPreparation_realizable : targetAfterPreparation.Realizable := by
  let enumeration := Prepared.enumeration (L := Language.ring) (Carrier := ZMod 4)
  have consumerReady := (Multisorted.readPreparedTarget_realizable enumeration).withSpecification
    (fun _ _ => True) (fun _ value => (value.val ()).1.2) (by intros; trivial) (by intros; rfl)
  exact Prepared.prepareAndConsume_realizable _ _ _ _ consumerReady _ _

theorem targetAfterPreparation_tm0 : targetAfterPreparation.TM0Realizable :=
  targetAfterPreparation_realizable.tm0

end Polytime2.SMP.RingExample
