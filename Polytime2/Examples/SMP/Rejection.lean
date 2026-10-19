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

import Polytime2.Examples.SMP.OrderedConversion
import Polytime2.Arrays.FirstFalse

/-! # Selecting an explicit rejected coordinate from the converted instance -/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.SMP

open FirstOrder FirstOrder.Language
open Polytime2.Computation

variable {L : Language.{0, 0}} [L.IsAlgebraic] {Carrier Parameter : Type}
variable [L.Structure Carrier] [Finite Carrier] [Fintype Parameter]

/-- Normalize the fixed Boolean codec without changing any input bits. -/
noncomputable def acceptanceFlags (coordinates generators : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  let converted := orderedConversion (L := L) (Carrier := Carrier) coordinates generators
  unaryMap converted.outputDomain (EncodedDomain.booleans.arrayOfLength coordinates)
    (fun _ _ => True) (fun _ value => value.val.1)

theorem acceptanceFlags_realizable (coordinates generators : MvPolynomial Parameter ℕ) :
    (acceptanceFlags (L := L) (Carrier := Carrier) coordinates generators).Realizable := by
  let flags : EncodedDomain Parameter := EncodedDomain.booleans.constant.arrayOfLength coordinates
  let data := (orderedCoordinates (L := L) (Carrier := Carrier) coordinates generators).outputDomain.prod
    (convertedCounts (L := L) (Carrier := Carrier) coordinates generators).outputDomain
  have normalized := encodingMap_realizable flags (EncodedDomain.booleans.arrayOfLength coordinates)
    (fun _ value => value) (by
      intros
      simp [flags, EncodedDomain.arrayOfLength, EncodedDomain.constant, EncodedDomain.booleans,
        EncodedDomain.fixed, EncodedDomain.ofCodec]) (by
      intros
      simp [flags, EncodedDomain.arrayOfLength, EncodedDomain.constant, EncodedDomain.booleans,
        EncodedDomain.fixed, EncodedDomain.ofCodec, EncodedDomain.ArrayEncoding.bits_cast,
        EncodedDomain.ArrayEncoding.bits_encode])
  exact (pairProjection_realizable flags data false).followedBy normalized rfl (by intros; trivial)

/-- Select from already organized data, so preparation is performed only once. -/
noncomputable def selectRejection (coordinates generators : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  (acceptanceFlags (L := L) (Carrier := Carrier) coordinates generators).followedBy
    (firstFalse coordinates) rfl (by intros; trivial)

theorem selectRejection_realizable (coordinates generators : MvPolynomial Parameter ℕ) :
    (selectRejection (L := L) (Carrier := Carrier) coordinates generators).Realizable :=
  (acceptanceFlags_realizable coordinates generators).followedBy (firstFalse_realizable coordinates)
    rfl (by intros; trivial)

/-- A failed coordinate, or the coordinate-count sentinel when all are accepted. -/
noncomputable def rejectionCoordinate (coordinates generators : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  (orderedConversion (L := L) (Carrier := Carrier) coordinates generators).followedBy
    (selectRejection coordinates generators) rfl (by intros; trivial)

theorem rejectionCoordinate_realizable (coordinates generators : MvPolynomial Parameter ℕ) :
    (rejectionCoordinate (L := L) (Carrier := Carrier) coordinates generators).Realizable :=
  (orderedConversion_realizable coordinates generators).followedBy
    (selectRejection_realizable coordinates generators) rfl (by intros; trivial)

@[simp] theorem rejectionCoordinate_compute (coordinates generators : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (rejectionCoordinate (L := L) (Carrier := Carrier) coordinates generators).Arguments sizes) :
    (rejectionCoordinate (L := L) (Carrier := Carrier) coordinates generators).compute sizes ⟨arguments, trivial⟩ =
      (firstFalse coordinates).compute sizes ⟨(fun _ coordinate =>
        ((orderedConversion (L := L) (Carrier := Carrier) coordinates generators).compute sizes
          ⟨arguments, trivial⟩).1 coordinate), trivial⟩ := by
  unfold rejectionCoordinate selectRejection Computation.followedBy acceptanceFlags unaryMap
  congr 1

/-- The selected coordinate is bounded by the original coordinate count. -/
theorem rejectionCoordinate_bound (coordinates generators : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (rejectionCoordinate (L := L) (Carrier := Carrier) coordinates generators).Arguments sizes) :
    ((rejectionCoordinate (L := L) (Carrier := Carrier) coordinates generators).compute sizes ⟨arguments, trivial⟩).toNat ≤
      MvPolynomial.eval sizes coordinates :=
  by rw [rejectionCoordinate_compute]; exact firstFalse_bound _ _ _

/-- The returned in-range number names a coordinate outside its generated image. -/
theorem rejectionCoordinate_witness (coordinates generators : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (rejectionCoordinate (L := L) (Carrier := Carrier) coordinates generators).Arguments sizes)
    (before : ((rejectionCoordinate (L := L) (Carrier := Carrier) coordinates generators).compute sizes
      ⟨arguments, trivial⟩).toNat < MvPolynomial.eval sizes coordinates) :
    ∃ coordinate : Fin (MvPolynomial.eval sizes coordinates), coordinate.val =
        ((rejectionCoordinate (L := L) (Carrier := Carrier) coordinates generators).compute sizes ⟨arguments, trivial⟩).toNat ∧
      conversionTarget coordinates generators sizes arguments coordinate ∉
        CoordinateReduction.images (L := L) (conversionGenerators coordinates generators sizes arguments) coordinate := by
  let flags := fun coordinate => ((orderedConversion (L := L) (Carrier := Carrier) coordinates generators).compute sizes
    ⟨arguments, trivial⟩).1 coordinate
  have bound : ((firstFalse coordinates).compute sizes ⟨(fun _ => flags), trivial⟩).toNat <
      MvPolynomial.eval sizes coordinates := by simpa only [rejectionCoordinate_compute] using before
  let coordinate : Fin (MvPolynomial.eval sizes coordinates) :=
    ⟨((firstFalse coordinates).compute sizes ⟨(fun _ => flags), trivial⟩).toNat, bound⟩
  refine ⟨coordinate, (congrArg BitVec.toNat (rejectionCoordinate_compute coordinates generators sizes arguments)).symm, ?_⟩
  intro member
  have accepted := (orderedConversion_accepted coordinates generators sizes arguments coordinate).mpr member
  have failed := firstFalse_found coordinates sizes flags bound
  change flags coordinate = true at accepted
  rw [show flags coordinate = false from failed] at accepted
  contradiction

/-- A nonsentinel result explicitly certifies original SMP nonmembership. -/
theorem rejectionCoordinate_found (coordinates generators : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (rejectionCoordinate (L := L) (Carrier := Carrier) coordinates generators).Arguments sizes)
    (before : ((rejectionCoordinate (L := L) (Carrier := Carrier) coordinates generators).compute sizes
      ⟨arguments, trivial⟩).toNat < MvPolynomial.eval sizes coordinates) :
    conversionTarget coordinates generators sizes arguments ∉
      Substructure.closure (M := Fin (MvPolynomial.eval sizes coordinates) → Carrier) L
        (Set.range (conversionGenerators coordinates generators sizes arguments)) := by
  obtain ⟨coordinate, _, outside⟩ := rejectionCoordinate_witness coordinates generators sizes arguments before
  exact coordinate_obstruction _ _ coordinate outside

/-- The sentinel certifies every coordinate-image condition needed by preparation. -/
theorem rejectionCoordinate_sentinel (coordinates generators : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (rejectionCoordinate (L := L) (Carrier := Carrier) coordinates generators).Arguments sizes) :
    ((rejectionCoordinate (L := L) (Carrier := Carrier) coordinates generators).compute sizes
      ⟨arguments, trivial⟩).toNat = MvPolynomial.eval sizes coordinates ↔
      ∀ coordinate, conversionTarget coordinates generators sizes arguments coordinate ∈
        CoordinateReduction.images (L := L) (conversionGenerators coordinates generators sizes arguments) coordinate := by
  have sentinel := firstFalse_sentinel coordinates sizes
    (fun coordinate => ((orderedConversion (L := L) (Carrier := Carrier) coordinates generators).compute sizes
      ⟨arguments, trivial⟩).1 coordinate)
  rw [rejectionCoordinate_compute]
  exact sentinel.trans (forall_congr' (fun coordinate => orderedConversion_accepted coordinates generators sizes arguments coordinate))

/-- Preserve organized data alongside its explicit rejection index or sentinel. -/
noncomputable def collectRejection (coordinates generators : MvPolynomial Parameter ℕ) : Computation Parameter Unit where
  inputDomains _ := (orderedConversion (L := L) (Carrier := Carrier) coordinates generators).outputDomain
  outputDomain := (orderedConversion (L := L) (Carrier := Carrier) coordinates generators).outputDomain.prod
    (EncodedDomain.bitVectors (coordinates + 1))
  precondition _ _ := True
  compute sizes arguments := (arguments.val (),
    (selectRejection coordinates generators).compute sizes ⟨arguments.val, trivial⟩)

theorem collectRejection_realizable (coordinates generators : MvPolynomial Parameter ℕ) :
    (collectRejection (L := L) (Carrier := Carrier) coordinates generators).Realizable := by
  let source := (orderedConversion (L := L) (Carrier := Carrier) coordinates generators).outputDomain
  have retained := encodingMap_realizable source source (fun _ value => value) (by intros; rfl) (by intros; rfl)
  exact Realizable.pairOutputs (fun _ : Unit => source) source
    (EncodedDomain.bitVectors (coordinates + 1)) (fun _ _ => True) (fun _ arguments => arguments.val ())
    (fun sizes arguments => (selectRejection coordinates generators).compute sizes ⟨arguments.val, trivial⟩)
    retained (selectRejection_realizable coordinates generators)

noncomputable def conversionResult (coordinates generators : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  (orderedConversion (L := L) (Carrier := Carrier) coordinates generators).followedBy
    (collectRejection coordinates generators) rfl (by intros; trivial)

theorem conversionResult_realizable (coordinates generators : MvPolynomial Parameter ℕ) :
    (conversionResult (L := L) (Carrier := Carrier) coordinates generators).Realizable :=
  (orderedConversion_realizable coordinates generators).followedBy
    (collectRejection_realizable coordinates generators) rfl (by intros; trivial)

/-- The public result pairs the ordered instance with exactly the proved selector. -/
theorem conversionResult_compute (coordinates generators : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (conversionResult (L := L) (Carrier := Carrier) coordinates generators).Arguments sizes) :
    (conversionResult (L := L) (Carrier := Carrier) coordinates generators).compute sizes ⟨arguments, trivial⟩ =
      ((orderedConversion (L := L) (Carrier := Carrier) coordinates generators).compute sizes ⟨arguments, trivial⟩,
        (rejectionCoordinate (L := L) (Carrier := Carrier) coordinates generators).compute sizes ⟨arguments, trivial⟩) := by
  unfold conversionResult collectRejection rejectionCoordinate Computation.followedBy
  congr 1

theorem conversionResult_tm0 :
    (conversionResult (L := L) (Carrier := Carrier)
      (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℕ) (MvPolynomial.X 1)).TM0Realizable :=
  (conversionResult_realizable _ _).tm0

end Polytime2.SMP
