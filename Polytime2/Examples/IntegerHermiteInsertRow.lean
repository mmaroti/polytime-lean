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

import Polytime2.Matrices.IntegerHermiteAdvance
import Polytime2.TM0.Computation

/-! # Complete runtime row insertion

The first incoming row has no old pivots. Its zero outcome is dependent; a
negative nonzero entry creates a positive pivot. Both retain the actual basis.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Examples.IntegerHermiteInsertRow

open Polytime2.Computation Polytime2.Computation.Realizable.Internal

example {Parameter : Type} [Fintype Parameter]
    (rows columns width pivots : MvPolynomial Parameter ℕ) :
    (integerHermiteInsertRow rows columns width pivots).TM0Realizable :=
  (integerHermiteInsertRow_realizable rows columns width pivots).tm0

private noncomputable def arguments (nonzero : Bool) :
    (integerHermiteInsertRow (Parameter := Empty) 1 1 2 0).Arguments Empty.elim
  | 0 => fun index => ⟨index.val, by simpa using index.isLt⟩
  | 1 => fun index => ⟨index.val, by have impossible := index.isLt; norm_num at impossible⟩
  | 2 => ⟨fun _ _ => if nonzero then -3 else 0, by intro row column; dsimp only; split_ifs <;> norm_num⟩
  | 3 => ⟨1, by intro row column; simp only [Matrix.one_apply]; split_ifs <;> norm_num⟩

private theorem valid (nonzero : Bool) :
    (integerHermiteInsertRow (Parameter := Empty) 1 1 2 0).precondition Empty.elim (arguments nonzero) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro first second same
    have values := congrArg Fin.val same
    exact Fin.ext values
  · intro first second same
    have impossible := first.isLt
    norm_num at impossible
  · intro index
    have impossible := index.isLt
    norm_num at impossible
  · intro row column before
    have impossible := row.isLt
    norm_num at impossible

example (nonzero : Bool) :
    let result := (integerHermiteInsertRow (Parameter := Empty) 1 1 2 0).compute Empty.elim
      ⟨arguments nonzero, valid nonzero⟩
    result.1.2.val * (arguments nonzero 2).val = result.1.1.val ∧ IsUnit result.1.2.val.det := by
  have preserved := integerHermiteInsertRow_preserves 1 1 2 0 Empty.elim
    ⟨arguments nonzero, valid nonzero⟩ (arguments nonzero 2).val 1
    (by simp [arguments]) (by simp [arguments])
  simpa only [Matrix.mul_one] using preserved

example : ((integerHermiteInsertRow (Parameter := Empty) 1 1 2 0).compute Empty.elim
    ⟨arguments false, valid false⟩).2 = none := by
  have actual := congrArg Prod.snd (integerHermiteInsertRow_correct 1 1 2 0 Empty.elim
    ⟨arguments false, valid false⟩)
  dsimp only [IntegerMatrix.hermiteInsertRow] at actual
  norm_num [IntegerMatrix.hermiteIncomingPrefix, arguments, successorValues, Fin.last,
    IntegerMatrix.hermiteResidualPivot, ArraySearch.firstFalse, List.ofFn] at actual
  exact actual

example : ((integerHermiteInsertRow (Parameter := Empty) 1 1 2 0).compute Empty.elim
    ⟨arguments true, valid true⟩).2 = some ⟨0, by norm_num⟩ := by
  have actual := congrArg Prod.snd (integerHermiteInsertRow_correct 1 1 2 0 Empty.elim
    ⟨arguments true, valid true⟩)
  dsimp only [IntegerMatrix.hermiteInsertRow] at actual
  norm_num [IntegerMatrix.hermiteIncomingPrefix, arguments, successorValues, Fin.last,
    IntegerMatrix.hermiteResidualPivot, ArraySearch.firstFalse, List.ofFn] at actual
  exact actual

private noncomputable def oldPivotArguments (independent : Bool) :
    (integerHermiteInsertRow (Parameter := Empty) 2 2 3 1).Arguments Empty.elim
  | 0 => fun index => ⟨index.val, by simpa using index.isLt⟩
  | 1 => fun _ => ⟨0, by norm_num⟩
  | 2 => ⟨fun row column => if row.val = 0 then (if column.val = 0 then 6 else 3)
      else if column.val = 0 then 2 else if independent then 2 else 1, by
        intro row column; dsimp only; split_ifs <;> norm_num⟩
  | 3 => ⟨1, by intro row column; simp only [Matrix.one_apply]; split_ifs <;> norm_num⟩

private theorem oldPivotValid (independent : Bool) :
    (integerHermiteInsertRow (Parameter := Empty) 2 2 3 1).precondition Empty.elim (oldPivotArguments independent) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro first second same
    have values := congrArg Fin.val same
    exact Fin.ext values
  · intro first second same
    have firstBound := first.isLt
    have secondBound := second.isLt
    norm_num at firstBound secondBound
    exact Fin.ext (by omega)
  · intro index
    norm_num [oldPivotArguments, successorValues]
    split_ifs <;> norm_num
  · intro row column before
    have rowBound := row.isLt
    have columnBound := column.isLt
    norm_num at rowBound columnBound
    exact False.elim (by omega)

private theorem oldPivotSearch (independent : Bool) :
    ((integerHermiteInsertRow (Parameter := Empty) 2 2 3 1).compute Empty.elim
      ⟨oldPivotArguments independent, oldPivotValid independent⟩).2 =
      IntegerMatrix.hermiteResidualPivot
        (successorValues 1 Empty.elim (oldPivotArguments independent 0)
          (Fin.last (MvPolynomial.eval Empty.elim (1 : MvPolynomial Empty ℕ))))
        (IntegerMatrix.hermiteIncomingPrefix
          (Row := Fin (MvPolynomial.eval Empty.elim (2 : MvPolynomial Empty ℕ)))
          (Column := Fin (MvPolynomial.eval Empty.elim (2 : MvPolynomial Empty ℕ)))
          ⟨successorValues 1 Empty.elim (oldPivotArguments independent 0), (oldPivotValid independent).1⟩
          (oldPivotArguments independent 1) (MvPolynomial.eval Empty.elim (1 : MvPolynomial Empty ℕ))
          (oldPivotArguments independent 2).val (oldPivotArguments independent 3).val).1 := by
  exact (congrArg Prod.snd (integerHermiteInsertRow_correct 2 2 3 1 Empty.elim
    ⟨oldPivotArguments independent, oldPivotValid independent⟩)).trans
    (IntegerMatrix.hermiteInsertRow_pivot _ _ _ _)

private theorem oldPivotStage (independent : Bool) :
    IntegerMatrix.hermiteIncomingPrefix
      (Row := Fin (MvPolynomial.eval Empty.elim (2 : MvPolynomial Empty ℕ)))
      (Column := Fin (MvPolynomial.eval Empty.elim (2 : MvPolynomial Empty ℕ)))
      ⟨successorValues 1 Empty.elim (oldPivotArguments independent 0), (oldPivotValid independent).1⟩
      (oldPivotArguments independent 1) (MvPolynomial.eval Empty.elim (1 : MvPolynomial Empty ℕ))
      (oldPivotArguments independent 2).val (oldPivotArguments independent 3).val =
    IntegerMatrix.hermiteRowStage
      (Row := Fin (MvPolynomial.eval Empty.elim (2 : MvPolynomial Empty ℕ)))
      (Column := Fin (MvPolynomial.eval Empty.elim (2 : MvPolynomial Empty ℕ)))
      ⟨0, by norm_num⟩ ⟨1, by norm_num⟩ ⟨0, by norm_num⟩ []
      (oldPivotArguments independent 2).val (oldPivotArguments independent 3).val := by
  have step := IntegerMatrix.hermiteIncomingPrefix_succ_forward
    (Row := Fin (MvPolynomial.eval Empty.elim (2 : MvPolynomial Empty ℕ)))
    (Column := Fin (MvPolynomial.eval Empty.elim (2 : MvPolynomial Empty ℕ)))
    ⟨successorValues 1 Empty.elim (oldPivotArguments independent 0), (oldPivotValid independent).1⟩
    (oldPivotArguments independent 1) (⟨0, by norm_num⟩ : Fin (MvPolynomial.eval Empty.elim (1 : MvPolynomial Empty ℕ)))
    (oldPivotArguments independent 2).val (oldPivotArguments independent 3).val
  norm_num only [map_one] at step ⊢
  convert step using 1
  norm_num [oldPivotArguments, successorValues, Fin.last, IntegerMatrix.hermiteIncomingPrefix]

example : ((integerHermiteInsertRow (Parameter := Empty) 2 2 3 1).compute Empty.elim
    ⟨oldPivotArguments false, oldPivotValid false⟩).2 = none := by
  have actual := (oldPivotSearch false).trans (congrArg (fun pair => IntegerMatrix.hermiteResidualPivot
    (successorValues 1 Empty.elim (oldPivotArguments false 0)
      (Fin.last (MvPolynomial.eval Empty.elim (1 : MvPolynomial Empty ℕ)))) pair.1) (oldPivotStage false))
  norm_num [IntegerMatrix.hermiteIncomingPrefix, oldPivotArguments, successorValues, Fin.last,
    IntegerMatrix.hermiteResidualPivot, ArraySearch.firstFalse, List.ofFn] at actual
  exact actual.trans (by
    change (_ : Option (Fin (MvPolynomial.eval Empty.elim (2 : MvPolynomial Empty ℕ)))) = _
    decide +kernel)

example : ((integerHermiteInsertRow (Parameter := Empty) 2 2 3 1).compute Empty.elim
    ⟨oldPivotArguments true, oldPivotValid true⟩).2 = some ⟨1, by norm_num⟩ := by
  have actual := (oldPivotSearch true).trans (congrArg (fun pair => IntegerMatrix.hermiteResidualPivot
    (successorValues 1 Empty.elim (oldPivotArguments true 0)
      (Fin.last (MvPolynomial.eval Empty.elim (1 : MvPolynomial Empty ℕ)))) pair.1) (oldPivotStage true))
  norm_num [IntegerMatrix.hermiteIncomingPrefix, oldPivotArguments, successorValues, Fin.last,
    IntegerMatrix.hermiteResidualPivot, ArraySearch.firstFalse, List.ofFn] at actual
  exact actual.trans (by
    change (_ : Option (Fin (MvPolynomial.eval Empty.elim (2 : MvPolynomial Empty ℕ)))) = _
    decide +kernel)

example {HostParameter Parameter : Type} [Fintype HostParameter] [Fintype Parameter]
    (rows columns width : MvPolynomial HostParameter ℕ) (names : HostParameter → Parameter)
    (rankName : Parameter) :
    (integerHermiteInsertAtSize rows columns width names rankName).TM0Realizable :=
  (integerHermiteInsertAtSize_realizable rows columns width names rankName).tm0

private noncomputable def storedArguments :
    (integerHermiteInsertHost (1 : MvPolynomial Empty ℕ) 1 2).Arguments Empty.elim :=
  fun _ name => match name with
    | 0 => (⟨0, ⟨Fin.elim0, by intro index; exact index.elim0⟩,
        ⟨Fin.elim0, by intro index; exact index.elim0⟩⟩, ⟨0, by norm_num⟩)
    | 1 => ⟨fun _ _ => -3, by intro row column; norm_num⟩
    | 2 => ⟨1, by intro row column; simp only [Matrix.one_apply]; split_ifs <;> norm_num⟩

private theorem storedValid :
    (integerHermiteInsertHost (1 : MvPolynomial Empty ℕ) 1 2).precondition Empty.elim storedArguments := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨index, _⟩
    exact index.elim0
  · intro index
    exact index.elim0
  · intro row column before
    exact row.elim0

example :
    let result := (integerHermiteInsertHost (1 : MvPolynomial Empty ℕ) 1 2).compute Empty.elim
      ⟨storedArguments, storedValid⟩
    result.1.2.val * (storedArguments () 1).val = result.1.1.val := by
  have preserved := integerHermiteInsertHost_preserves 1 1 2 Empty.elim
    ⟨storedArguments, storedValid⟩ (storedArguments () 1).val 1
    (by simp [storedArguments]) (by simp [storedArguments])
  simpa only [Matrix.mul_one] using preserved.1

private noncomputable def oldStoredArguments :
    (integerHermiteInsertHost (2 : MvPolynomial Empty ℕ) 2 3).Arguments Empty.elim :=
  fun _ name => match name with
    | 0 => (⟨1, Fin.castLEEmb (by norm_num), Fin.castLEEmb (by norm_num)⟩, ⟨1, by norm_num⟩)
    | 1 => oldPivotArguments true 2
    | 2 => oldPivotArguments true 3

private theorem oldStoredValid :
    (integerHermiteInsertHost (2 : MvPolynomial Empty ℕ) 2 3).precondition Empty.elim oldStoredArguments := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨index, equal⟩
    have bound : index.val < 1 := index.isLt
    have values : index.val = 1 := congrArg Fin.val equal
    omega
  · intro index
    norm_num [oldStoredArguments, oldPivotArguments]
    split_ifs <;> norm_num
  · intro row column before
    have rowBound : row.val < 1 := row.isLt
    have columnBound : column.val < 1 := column.isLt
    have order : column.val < row.val := before
    omega

example :
    let result := (integerHermiteInsertHost (2 : MvPolynomial Empty ℕ) 2 3).compute Empty.elim
      ⟨oldStoredArguments, oldStoredValid⟩
    result.1.2.val * (oldStoredArguments () 1).val = result.1.1.val ∧ IsUnit result.1.2.val.det := by
  have preserved := integerHermiteInsertHost_preserves 2 2 3 Empty.elim
    ⟨oldStoredArguments, oldStoredValid⟩ (oldStoredArguments () 1).val 1
    (by simp [oldStoredArguments, oldPivotArguments]) (by simp [oldStoredArguments, oldPivotArguments])
  simpa only [Matrix.mul_one] using preserved

private noncomputable def namedFirstArguments :
    (integerHermiteInsertAtSize (1 : MvPolynomial Empty ℕ) 1 2 Empty.elim ()).Arguments (fun _ => 0)
  | 0 => (⟨0, ⟨Fin.elim0, by intro index; exact index.elim0⟩,
      ⟨Fin.elim0, by intro index; exact index.elim0⟩⟩, ⟨0, by norm_num⟩)
  | 1 => ⟨fun _ _ => -3, by intro row column; norm_num⟩
  | 2 => ⟨1, by intro row column; simp only [Matrix.one_apply]; split_ifs <;> norm_num⟩

private theorem namedFirstValid :
    (integerHermiteInsertAtSize (1 : MvPolynomial Empty ℕ) 1 2 Empty.elim ()).precondition
      (fun _ => 0) namedFirstArguments :=
  integerHermiteInsertAtSize_permitted 1 1 2 Empty.elim () (fun _ => 0) namedFirstArguments rfl
    (by rintro ⟨index, _⟩; exact index.elim0)
    (by intro index; exact index.elim0)
    (by intro row column before; exact row.elim0)

private noncomputable def namedFirstRows :
    Fin (MvPolynomial.eval (fun _ : Unit => 0) (MvPolynomial.X ()) + 1) ↪
      Fin (MvPolynomial.eval (fun _ : Unit => 0) (MvPolynomial.rename Empty.elim (1 : MvPolynomial Empty ℕ))) :=
  Fin.castLEEmb (by simp)

private noncomputable def namedFirstColumns :
    Fin (MvPolynomial.eval (fun _ : Unit => 0) (MvPolynomial.X ())) →
      Fin (MvPolynomial.eval (fun _ : Unit => 0) (MvPolynomial.rename Empty.elim (1 : MvPolynomial Empty ℕ))) :=
  fun index => False.elim (by have impossible := index.isLt; simp at impossible)

example : (((integerHermiteInsertAtSize (1 : MvPolynomial Empty ℕ) 1 2 Empty.elim ()).compute
    (fun _ => 0) ⟨namedFirstArguments, namedFirstValid⟩).2).isSome = true := by
  have actual := congrArg (fun result => result.2.isSome)
    (integerHermiteInsertAtSize_correct 1 1 2 Empty.elim () (fun _ => 0)
      ⟨namedFirstArguments, namedFirstValid⟩ rfl namedFirstRows namedFirstColumns
      (by intro index; have impossible := index.isLt; norm_num at impossible)
      (by simp [namedFirstRows, namedFirstArguments])
      (by intro index; have impossible := index.isLt; norm_num at impossible))
  norm_num [IntegerMatrix.hermiteInsertRow, IntegerMatrix.hermiteIncomingPrefix,
    namedFirstRows, namedFirstColumns, namedFirstArguments, Polytime2.EncodedDomain.integerMatricesRenameValues,
    IntegerMatrix.hermiteResidualPivot, ArraySearch.firstFalse, List.ofFn] at actual
  exact actual

private theorem storedPivotPresent : (((integerHermiteInsertHost (1 : MvPolynomial Empty ℕ) 1 2).compute Empty.elim
    ⟨storedArguments, storedValid⟩).2).isSome = true := by
  have actual := congrArg (fun result => result.2.isSome)
    (integerHermiteInsertHost_correct 1 1 2 Empty.elim ⟨storedArguments, storedValid⟩)
  norm_num [IntegerMatrix.hermiteInsertRow, IntegerMatrix.hermiteIncomingPrefix,
    storedArguments, Fin.Embedding.snoc, IntegerMatrix.hermiteResidualPivot,
    ArraySearch.firstFalse, List.ofFn] at actual
  have flags : Fin.foldr 1 (fun (_ : Fin 1) (entries : List Bool) => false :: entries) [] = [false] := rfl
  simp only [flags] at actual
  norm_num at actual
  exact actual

example :
    let result := (integerHermiteAdvance (1 : MvPolynomial Empty ℕ) 1 2).compute Empty.elim
      ⟨storedArguments, storedValid⟩
    result.1.2.val * (storedArguments () 1).val = result.1.1.val ∧ IsUnit result.1.2.val.det := by
  have preserved := integerHermiteAdvance_preserves 1 1 2 Empty.elim
    ⟨storedArguments, storedValid⟩ (storedArguments () 1).val 1
    (by simp [storedArguments]) (by simp [storedArguments])
  simpa only [Matrix.mul_one] using preserved

example {Parameter : Type} [Fintype Parameter] (rows columns width : MvPolynomial Parameter ℕ) :
    (integerHermiteInsertHost rows columns width).TM0Realizable :=
  (integerHermiteInsertHost_realizable rows columns width).tm0

example {HostParameter Parameter : Type} [Fintype HostParameter] [Fintype Parameter]
    (rows columns width : MvPolynomial HostParameter ℕ) (names : HostParameter → Parameter)
    (rankName : Parameter) :
    (integerHermiteInsertAtSizeBounded rows columns width names rankName).TM0Realizable :=
  (integerHermiteInsertAtSizeBounded_realizable rows columns width names rankName).tm0

example {HostParameter Parameter : Type} [Fintype HostParameter] [Fintype Parameter]
    (rows columns width : MvPolynomial HostParameter ℕ) (names : HostParameter → Parameter)
    (rankName : Parameter) :
    (integerHermiteInsertAtSizeOriginal rows columns width names rankName).TM0Realizable :=
  (integerHermiteInsertAtSizeOriginal_realizable rows columns width names rankName).tm0

example {Parameter : Type} [Fintype Parameter] (rows columns width : MvPolynomial Parameter ℕ) :
    (integerHermiteAdvance rows columns width).TM0Realizable :=
  (integerHermiteAdvance_realizable rows columns width).tm0

example : (((integerHermiteAdvance (1 : MvPolynomial Empty ℕ) 1 2).compute Empty.elim
    ⟨storedArguments, storedValid⟩).2).1 = 1 := by
  rw [integerHermiteAdvance_compute]
  change ((integerHermiteInsertSelection 1 1 2).compute Empty.elim ⟨storedArguments, storedValid⟩).1 = 1
  cases found : ((integerHermiteInsertHost (1 : MvPolynomial Empty ℕ) 1 2).compute Empty.elim
      ⟨storedArguments, storedValid⟩).2 with
  | none => have impossible := storedPivotPresent; simp only [found, Option.isSome_none, Bool.false_eq_true] at impossible
  | some column =>
    rw [integerHermiteInsertSelection_some 1 1 2 Empty.elim ⟨storedArguments, storedValid⟩ column found]
    rfl

end Polytime2.Examples.IntegerHermiteInsertRow
