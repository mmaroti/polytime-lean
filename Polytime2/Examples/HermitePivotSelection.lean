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

import Polytime2.Matrices.HermitePivotUpdate
import Polytime2.Matrices.HermitePivotRead
import Polytime2.TM0.Computation

/-! # Dynamic Hermite metadata without default coordinates

Rank-zero initialization works when either coordinate type is empty. The
rank reader also accepts an ordinary nonzero-rank pair of embeddings.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Examples.HermitePivotSelection

open Polytime2.Computation Polytime2.EncodedDomain

example {Parameter : Type} [Fintype Parameter] (rows columns : MvPolynomial Parameter ℕ) :
    (hermitePivotSelectionEmpty rows columns).TM0Realizable :=
  (hermitePivotSelectionEmpty_realizable rows columns).tm0

example {Parameter : Type} [Fintype Parameter] (rows columns : MvPolynomial Parameter ℕ) :
    (hermitePivotSelectionRank rows columns).TM0Realizable :=
  (hermitePivotSelectionRank_realizable rows columns).tm0

example : (boundedArrayEmpty (boundedIndex (0 : MvPolynomial Empty ℕ)) 5).TM0Realizable :=
  (boundedArrayEmpty_realizable _ _).tm0

example : ((hermitePivotSelectionEmpty (Parameter := Empty) 0 7).compute Empty.elim
    ⟨(fun impossible => impossible.elim), trivial⟩).1 = 0 := rfl

example : ((hermitePivotSelectionEmpty (Parameter := Empty) 7 0).compute Empty.elim
    ⟨(fun impossible => impossible.elim), trivial⟩).1 = 0 := rfl

private noncomputable def selection : (hermitePivotSelection (Parameter := Empty) 3 2).Carrier Empty.elim :=
  ⟨2, Fin.castLEEmb (by norm_num), Fin.castLEEmb (by norm_num)⟩

example : ((hermitePivotSelectionRank (Parameter := Empty) 3 2).compute Empty.elim
    ⟨(fun _ => selection), trivial⟩).val = 2 := rfl

example : (hermitePivotSelection (Parameter := Empty) 3 2).width Empty.elim = 18 := by
  unfold Polytime2.EncodedDomain.width
  rw [hermitePivotSelection_width]
  norm_num

example {Parameter : Type} [Fintype Parameter] (rows columns : MvPolynomial Parameter ℕ) :
    (hermitePivotSelectionSnoc rows columns).TM0Realizable :=
  (hermitePivotSelectionSnoc_realizable rows columns).tm0

private noncomputable def appendArguments
    (_name : Unit) : ((hermitePivotSelectionSnoc (Parameter := Empty) 3 3).inputDomains ()).Carrier Empty.elim :=
  (⟨1, Fin.castLEEmb (by norm_num), Fin.castLEEmb (by norm_num)⟩, (⟨2, by norm_num⟩, ⟨1, by norm_num⟩))

private theorem appendValid :
    (hermitePivotSelectionSnoc (Parameter := Empty) 3 3).precondition Empty.elim appendArguments := by
  constructor
  · rintro ⟨index, equality⟩
    have bound : index.val < 1 := index.isLt
    have values : index.val = 2 := congrArg Fin.val equality
    omega
  · rintro ⟨index, equality⟩
    have bound : index.val < 1 := index.isLt
    have values : index.val = 1 := congrArg Fin.val equality
    omega

private noncomputable def appended :=
  (hermitePivotSelectionSnoc (Parameter := Empty) 3 3).compute Empty.elim ⟨appendArguments, appendValid⟩

example : appended.1 = 2 := rfl
example : (appended.2.1 ⟨0, by change 0 < 2; decide⟩).val = 0 := rfl
example : (appended.2.1 ⟨1, by change 1 < 2; decide⟩).val = 2 := rfl
example : (appended.2.2 ⟨1, by change 1 < 2; decide⟩).val = 1 := rfl

example : ¬ (hermitePivotSelectionSnoc (Parameter := Empty) 3 2).precondition Empty.elim
    (fun _ => (selection, (⟨2, by norm_num⟩, ⟨0, by norm_num⟩))) := by
  intro valid
  exact valid.2 ⟨⟨0, by change 0 < 2; decide⟩, rfl⟩

private noncomputable def firstArguments
    (_name : Unit) : ((hermitePivotSelectionSnoc (Parameter := Empty) 1 1).inputDomains ()).Carrier Empty.elim :=
  (⟨0, ⟨Fin.elim0, by intro index; exact index.elim0⟩,
    ⟨Fin.elim0, by intro index; exact index.elim0⟩⟩,
    (⟨0, by norm_num⟩, ⟨0, by norm_num⟩))

private theorem firstValid :
    (hermitePivotSelectionSnoc (Parameter := Empty) 1 1).precondition Empty.elim firstArguments := by
  constructor <;> rintro ⟨index, _⟩ <;> exact index.elim0

example : ((hermitePivotSelectionSnoc (Parameter := Empty) 1 1).compute Empty.elim
    ⟨firstArguments, firstValid⟩).1 = 1 := rfl

example {HostParameter Parameter : Type} [Fintype HostParameter] [Fintype Parameter]
    (rows columns : MvPolynomial HostParameter ℕ) (hostNames : HostParameter → Parameter)
    (rankName : Parameter) :
    (hermitePivotSelectionAtSize rows columns hostNames rankName).TM0Realizable :=
  (hermitePivotSelectionAtSize_realizable rows columns hostNames rankName).tm0

example {HostParameter Parameter : Type} [Fintype HostParameter] [Fintype Parameter]
    (rows columns : MvPolynomial HostParameter ℕ) (hostNames : HostParameter → Parameter)
    (rankName : Parameter) :
    (hermitePivotIncomingAtSize rows columns hostNames rankName).TM0Realizable :=
  (hermitePivotIncomingAtSize_realizable rows columns hostNames rankName).tm0

private noncomputable def readArguments (_name : Unit) :
    ((hermitePivotIncomingAtSize (3 : MvPolynomial Empty ℕ) 2 Empty.elim ()).inputDomains ()).Carrier (fun _ => 1) :=
  (⟨1, Fin.castLEEmb (by norm_num), Fin.castLEEmb (by norm_num)⟩, ⟨2, by norm_num⟩)

private theorem readValid :
    (hermitePivotIncomingAtSize (3 : MvPolynomial Empty ℕ) 2 Empty.elim ()).precondition
      (fun _ => 1) readArguments := rfl

private noncomputable def incomingCoordinates :=
  (hermitePivotIncomingAtSize (3 : MvPolynomial Empty ℕ) 2 Empty.elim ()).compute
    (fun _ => 1) ⟨readArguments, readValid⟩

example : (successorValues (MvPolynomial.X ()) (fun _ => 1) incomingCoordinates.1
    (Fin.last (MvPolynomial.eval (fun _ => 1) (MvPolynomial.X ())))).val = 2 := by
  simp only [incomingCoordinates, hermitePivotIncomingAtSize, snocValues, successorValues,
    Fin.cast]
  rw [Fin.snoc_last]
  rfl

example : (successorValues (MvPolynomial.X ()) (fun _ => 1) incomingCoordinates.1
    (Fin.castSucc ⟨0, by simp⟩)).val = 0 := by
  dsimp only [incomingCoordinates, hermitePivotIncomingAtSize, snocValues, successorValues, Fin.cast]
  rw [Fin.snoc_castSucc]
  rfl

example : (incomingCoordinates.2 (0 : Fin 1)).val = 0 := rfl

example {Parameter : Type} [Fintype Parameter] (rows columns : MvPolynomial Parameter ℕ) :
    (hermitePivotSelectionUpdate rows columns).TM0Realizable :=
  (hermitePivotSelectionUpdate_realizable rows columns).tm0

private noncomputable def updateArguments (grow : Bool) (_name : Unit) :
    ((hermitePivotSelectionUpdate (Parameter := Empty) 3 3).inputDomains ()).Carrier Empty.elim :=
  (((appendArguments ()).1, (appendArguments ()).2.1),
    (if grow then some (appendArguments ()).2.2 else none))

private theorem updateValid (grow : Bool) :
    (hermitePivotSelectionUpdate (Parameter := Empty) 3 3).precondition Empty.elim (updateArguments grow) := by
  refine ⟨appendValid.1, ?_⟩
  intro column found
  cases grow
  · contradiction
  · have same : (appendArguments ()).2.2 = column := Option.some.inj found
    exact same ▸ appendValid.2

example (grow : Bool) : ((hermitePivotSelectionUpdate (Parameter := Empty) 3 3).compute Empty.elim
    ⟨updateArguments grow, updateValid grow⟩).1 = (if grow then 2 else 1) := by cases grow <;> rfl

end Polytime2.Examples.HermitePivotSelection
