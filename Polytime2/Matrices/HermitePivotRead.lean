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

import Polytime2.Matrices.HermitePivotSelection
import Polytime2.Arrays.PackingRead
import Polytime2.Arrays.NamedTransform
import Polytime2.Arrays.Snoc
import Polytime2.Computation.ComputedFrame

/-! # Reading Hermite pivot embeddings at the stored rank

Within a computed-size call, extract the live paired coordinates, then project
rows and columns through certified array maps. The result contains precisely
the selected embeddings, with no capacity padding or default coordinates.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain

variable {HostParameter Parameter : Type} [Fintype HostParameter] [Fintype Parameter]

/-- Read both pivot embeddings as arrays at a named runtime rank. -/
noncomputable def hermitePivotSelectionAtSize
    (rows columns : MvPolynomial HostParameter ℕ) (hostNames : HostParameter → Parameter)
    (rankName : Parameter) : Computation Parameter Unit where
  inputDomains _ := (hermitePivotSelection rows columns).renameParameters hostNames
  outputDomain := (((boundedIndex rows).renameParameters hostNames).array rankName).prod
    (((boundedIndex columns).renameParameters hostNames).array rankName)
  precondition sizes arguments := (arguments ()).1 = sizes rankName
  compute _ arguments :=
    (fun index => (arguments.val ()).2.1 (Fin.cast arguments.property.symm index),
      fun index => (arguments.val ()).2.2 (Fin.cast arguments.property.symm index))

/-- Read one shared live array and project its two coordinates by composition. -/
theorem hermitePivotSelectionAtSize_realizable
    (rows columns : MvPolynomial HostParameter ℕ) (hostNames : HostParameter → Parameter)
    (rankName : Parameter) :
    (hermitePivotSelectionAtSize rows columns hostNames rankName).Realizable := by
  let computation := hermitePivotSelectionAtSize rows columns hostNames rankName
  let element := (boundedIndex rows).prod (boundedIndex columns)
  let renamed := element.renameParameters hostNames
  let row := (boundedIndex rows).renameParameters hostNames
  let column := (boundedIndex columns).renameParameters hostNames
  let convert (_name : Unit) sizes (value : (computation.inputDomains ()).Carrier sizes) :
      ((boundedArray element rows).renameParameters hostNames).Carrier sizes :=
    ⟨⟨value.1, Nat.lt_succ_of_le (by
      simpa using Fintype.card_le_of_injective value.2.1 value.2.1.injective)⟩,
      fun index => (value.2.1 index, value.2.2 index)⟩
  have live := (boundedArrayAtSize_realizable element rows hostNames rankName renamed
    (fun _ => True) (fun _ _ value => value)
    (by intro sizes valid value; exact renameParameters_bits element hostNames sizes value)).reinterpretInputs
    computation.inputDomains convert (by intros; rfl) (by intros; rfl)
    computation.precondition (by intro sizes arguments valid; exact ⟨valid, trivial⟩)
  have first := (renamedPairView_realizable (boundedIndex rows) (boundedIndex columns) hostNames).fst
  have second := (renamedPairView_realizable (boundedIndex rows) (boundedIndex columns) hostNames).snd
  have firstMap := mapArrayAtParameter_realizable renamed row rankName (fun _ value => value.1)
    (first.withSpecification (fun _ _ => True) (fun _ value => (value.val ()).1) (by intros; trivial) (by intros; rfl))
  have secondMap := mapArrayAtParameter_realizable renamed column rankName (fun _ value => value.2)
    (second.withSpecification (fun _ _ => True) (fun _ value => (value.val ()).2) (by intros; trivial) (by intros; rfl))
  have firstReady := live.followedBy firstMap rfl (by intros; trivial)
  have secondReady := live.followedBy secondMap rfl (by intros; trivial)
  exact firstReady.prodMk secondReady

/-- Prepare the selected rows followed by the incoming row, and the old pivot columns. -/
noncomputable def hermitePivotIncomingAtSize
    (rows columns : MvPolynomial HostParameter ℕ) (hostNames : HostParameter → Parameter)
    (rankName : Parameter) : Computation Parameter Unit where
  inputDomains _ := ((hermitePivotSelection rows columns).prod (boundedIndex rows)).renameParameters hostNames
  outputDomain := (((boundedIndex rows).renameParameters hostNames).arrayOfLength
    (MvPolynomial.X rankName + 1)).prod
    (((boundedIndex columns).renameParameters hostNames).array rankName)
  precondition sizes arguments := (arguments ()).1.1 = sizes rankName
  compute sizes arguments :=
    (snocValues (MvPolynomial.X rankName) sizes
      (arrayParameterEquiv ((boundedIndex rows).renameParameters hostNames) rankName sizes
        (fun index => (arguments.val ()).1.2.1 (Fin.cast arguments.property.symm index)))
      (arguments.val ()).2,
      fun index => (arguments.val ()).1.2.2 (Fin.cast arguments.property.symm index))

/-- Coordinate preparation composes rank reading, pair projections, and array snoc. -/
theorem hermitePivotIncomingAtSize_realizable
    (rows columns : MvPolynomial HostParameter ℕ) (hostNames : HostParameter → Parameter)
    (rankName : Parameter) :
    (hermitePivotIncomingAtSize rows columns hostNames rankName).Realizable := by
  let computation := hermitePivotIncomingAtSize rows columns hostNames rankName
  let row := (boundedIndex rows).renameParameters hostNames
  have viewed := (renamedPairView_realizable (hermitePivotSelection rows columns) (boundedIndex rows) hostNames).withPrecondition computation.precondition (by intros; trivial)
  have read := viewed.fst.followedBy (hermitePivotSelectionAtSize_realizable rows columns hostNames rankName)
    rfl (by intro sizes arguments valid; exact valid)
  have polynomial := read.fst.reinterpretOutput (row.arrayOfLength (MvPolynomial.X rankName))
    (fun sizes => arrayParameterEquiv row rankName sizes) (by intros; rfl)
    (by intro sizes values; exact (array_X_encode_bits row rankName sizes values).symm)
  have appended := (arraySnoc_realizable row (MvPolynomial.X rankName)).onResults
    computation.inputDomains computation.precondition
    (fun choice sizes arguments => match choice with
      | false => arrayParameterEquiv row rankName sizes
          (fun index => (arguments.val ()).1.2.1 (Fin.cast arguments.property.symm index))
      | true => (arguments.val ()).2) (by intros; trivial) (by
        intro choice
        cases choice
        · exact polynomial
        · exact viewed.snd)
  exact appended.prodMk read.snd

/-- An excluded incoming row gives distinct selected rows; old pivot columns remain distinct. -/
theorem hermitePivotIncomingAtSize_injective
    (rows columns : MvPolynomial HostParameter ℕ) (hostNames : HostParameter → Parameter)
    (rankName : Parameter) (sizes : Parameter → ℕ)
    (arguments : {arguments : (hermitePivotIncomingAtSize rows columns hostNames rankName).Arguments sizes //
      (hermitePivotIncomingAtSize rows columns hostNames rankName).precondition sizes arguments})
    (excluded : (arguments.val ()).2 ∉ Set.range (arguments.val ()).1.2.1) :
    let result := (hermitePivotIncomingAtSize rows columns hostNames rankName).compute sizes arguments
    Function.Injective (successorValues (MvPolynomial.X rankName) sizes result.1) ∧
      Function.Injective result.2 := by
  dsimp only [hermitePivotIncomingAtSize, successorValues, snocValues, Fin.cast]
  constructor
  · apply Fin.snoc_injective_iff.mpr
    constructor
    · intro first second equal
      have old := (arguments.val ()).1.2.1.injective equal
      have values := congrArg Fin.val old
      exact Fin.ext values
    · rintro ⟨index, equal⟩
      exact excluded ⟨_, equal⟩
  · intro first second equal
    have old := (arguments.val ()).1.2.2.injective equal
    have values := congrArg Fin.val old
    exact Fin.ext values

/-- Supply insertion's exact polynomial array domains at the named stored rank. -/
noncomputable def hermitePivotInsertionCoordinates
    (rows columns : MvPolynomial HostParameter ℕ) (hostNames : HostParameter → Parameter)
    (rankName : Parameter) : Computation Parameter Unit where
  inputDomains := (hermitePivotIncomingAtSize rows columns hostNames rankName).inputDomains
  outputDomain := ((boundedIndex (MvPolynomial.rename hostNames rows)).arrayOfLength
    (MvPolynomial.X rankName + 1)).prod
    ((boundedIndex (MvPolynomial.rename hostNames columns)).arrayOfLength (MvPolynomial.X rankName))
  precondition := (hermitePivotIncomingAtSize rows columns hostNames rankName).precondition
  compute sizes arguments :=
    let ready := (hermitePivotIncomingAtSize rows columns hostNames rankName).compute sizes arguments
    (fun index => Fin.cast (MvPolynomial.eval_rename hostNames sizes rows).symm (ready.1 index),
      arrayParameterEquiv (boundedIndex (MvPolynomial.rename hostNames columns)) rankName sizes
        (fun index => Fin.cast (MvPolynomial.eval_rename hostNames sizes columns).symm (ready.2 index)))

/-- Convert coordinate meanings by bit-preserving maps, retaining canonical array storage. -/
theorem hermitePivotInsertionCoordinates_realizable
    (rows columns : MvPolynomial HostParameter ℕ) (hostNames : HostParameter → Parameter)
    (rankName : Parameter) :
    (hermitePivotInsertionCoordinates rows columns hostNames rankName).Realizable := by
  let row := (boundedIndex rows).renameParameters hostNames
  let column := (boundedIndex columns).renameParameters hostNames
  let targetRow := boundedIndex (MvPolynomial.rename hostNames rows)
  let targetColumn := boundedIndex (MvPolynomial.rename hostNames columns)
  let length : MvPolynomial Parameter ℕ := MvPolynomial.X rankName
  have ready := hermitePivotIncomingAtSize_realizable rows columns hostNames rankName
  have rowMap := mapArray_realizable row targetRow (length + 1)
    (fun sizes index => Fin.cast (MvPolynomial.eval_rename hostNames sizes rows).symm index)
    (renamedIndexView_realizable rows hostNames)
  have columnMap := mapArrayAtParameter_realizable column targetColumn rankName
    (fun sizes index => Fin.cast (MvPolynomial.eval_rename hostNames sizes columns).symm index)
    (renamedIndexView_realizable columns hostNames)
  have rowsReady := ready.fst.followedBy rowMap rfl (by intros; trivial)
  have columnsReady := (ready.snd.followedBy columnMap rfl (by intros; trivial)).reinterpretOutput
    (targetColumn.arrayOfLength length) (fun sizes => arrayParameterEquiv targetColumn rankName sizes)
    (by intros; rfl) (by intro sizes values; exact (array_X_encode_bits targetColumn rankName sizes values).symm)
  exact rowsReady.prodMk columnsReady

/-- Renaming coordinate domains preserves distinctness for the insertion inputs. -/
theorem hermitePivotInsertionCoordinates_injective
    (rows columns : MvPolynomial HostParameter ℕ) (names : HostParameter → Parameter)
    (rankName : Parameter) (sizes : Parameter → ℕ)
    (arguments : {arguments : (hermitePivotInsertionCoordinates rows columns names rankName).Arguments sizes //
      (hermitePivotInsertionCoordinates rows columns names rankName).precondition sizes arguments})
    (excluded : (arguments.val ()).2 ∉ Set.range (arguments.val ()).1.2.1) :
    let result := (hermitePivotInsertionCoordinates rows columns names rankName).compute sizes arguments
    Function.Injective (successorValues (MvPolynomial.X rankName) sizes result.1) ∧ Function.Injective result.2 := by
  have base := hermitePivotIncomingAtSize_injective rows columns names rankName sizes arguments excluded
  constructor
  · intro first second equal
    apply base.1
    have values := congrArg Fin.val equal
    exact Fin.ext values
  · intro first second equal
    have values := congrArg Fin.val equal
    have old : ((hermitePivotIncomingAtSize rows columns names rankName).compute sizes arguments).2
        (Fin.cast (MvPolynomial.eval_X rankName) first) =
      ((hermitePivotIncomingAtSize rows columns names rankName).compute sizes arguments).2
        (Fin.cast (MvPolynomial.eval_X rankName) second) := Fin.ext values
    have indices := base.2 old
    have indexValues := congrArg Fin.val indices
    exact Fin.ext indexValues

/-- Read the two pivot arrays in native polynomial domains at the named rank. -/
noncomputable def hermitePivotCoordinatesAtSize
    (rows columns : MvPolynomial HostParameter ℕ) (hostNames : HostParameter → Parameter)
    (rankName : Parameter) : Computation Parameter Unit where
  inputDomains := (hermitePivotSelectionAtSize rows columns hostNames rankName).inputDomains
  outputDomain := ((boundedIndex (MvPolynomial.rename hostNames rows)).arrayOfLength
    (MvPolynomial.X rankName)).prod
    ((boundedIndex (MvPolynomial.rename hostNames columns)).arrayOfLength (MvPolynomial.X rankName))
  precondition := (hermitePivotSelectionAtSize rows columns hostNames rankName).precondition
  compute sizes arguments :=
    let ready := (hermitePivotSelectionAtSize rows columns hostNames rankName).compute sizes arguments
    (arrayParameterEquiv (boundedIndex (MvPolynomial.rename hostNames rows)) rankName sizes
      (fun index => Fin.cast (MvPolynomial.eval_rename hostNames sizes rows).symm (ready.1 index)),
    arrayParameterEquiv (boundedIndex (MvPolynomial.rename hostNames columns)) rankName sizes
      (fun index => Fin.cast (MvPolynomial.eval_rename hostNames sizes columns).symm (ready.2 index)))

/-- Canonical coordinate views and array maps prepare both compaction inputs. -/
theorem hermitePivotCoordinatesAtSize_realizable
    (rows columns : MvPolynomial HostParameter ℕ) (hostNames : HostParameter → Parameter)
    (rankName : Parameter) :
    (hermitePivotCoordinatesAtSize rows columns hostNames rankName).Realizable := by
  let computation := hermitePivotCoordinatesAtSize rows columns hostNames rankName
  let row := (boundedIndex rows).renameParameters hostNames
  let column := (boundedIndex columns).renameParameters hostNames
  have ready := hermitePivotSelectionAtSize_realizable rows columns hostNames rankName
  have first : (Computation.mk computation.inputDomains
      ((boundedIndex (MvPolynomial.rename hostNames rows)).arrayOfLength (MvPolynomial.X rankName))
      computation.precondition (fun sizes arguments => (computation.compute sizes arguments).1)).Realizable := by
    have projected := ready.fst
    have mapped := projected.followedBy
      (mapArrayAtParameter_realizable row (boundedIndex (MvPolynomial.rename hostNames rows)) rankName
        (fun sizes index => Fin.cast (MvPolynomial.eval_rename hostNames sizes rows).symm index)
        (renamedIndexView_realizable rows hostNames)) rfl (by intros; trivial)
    exact mapped.reinterpretOutput _
      (fun sizes => arrayParameterEquiv (boundedIndex (MvPolynomial.rename hostNames rows)) rankName sizes)
      (by intros; rfl) (by intro sizes values; exact (array_X_encode_bits _ rankName sizes values).symm)
  have second : (Computation.mk computation.inputDomains
      ((boundedIndex (MvPolynomial.rename hostNames columns)).arrayOfLength (MvPolynomial.X rankName))
      computation.precondition (fun sizes arguments => (computation.compute sizes arguments).2)).Realizable := by
    have projected := ready.snd
    have mapped := projected.followedBy
      (mapArrayAtParameter_realizable column (boundedIndex (MvPolynomial.rename hostNames columns)) rankName
        (fun sizes index => Fin.cast (MvPolynomial.eval_rename hostNames sizes columns).symm index)
        (renamedIndexView_realizable columns hostNames)) rfl (by intros; trivial)
    exact mapped.reinterpretOutput _
      (fun sizes => arrayParameterEquiv (boundedIndex (MvPolynomial.rename hostNames columns)) rankName sizes)
      (by intros; rfl) (by intro sizes values; exact (array_X_encode_bits _ rankName sizes values).symm)
  exact first.prodMk second

/-- Reading and renaming the two embeddings preserves injectivity. -/
theorem hermitePivotCoordinatesAtSize_injective
    (rows columns : MvPolynomial HostParameter ℕ) (names : HostParameter → Parameter)
    (rankName : Parameter) (sizes : Parameter → ℕ)
    (arguments : {arguments : (hermitePivotCoordinatesAtSize rows columns names rankName).Arguments sizes //
      (hermitePivotCoordinatesAtSize rows columns names rankName).precondition sizes arguments}) :
    let result := (hermitePivotCoordinatesAtSize rows columns names rankName).compute sizes arguments
    Function.Injective result.1 ∧ Function.Injective result.2 := by
  constructor
  · intro first second equal
    have values := congrArg Fin.val equal
    have old : (arguments.val ()).2.1
        (Fin.cast arguments.property.symm (Fin.cast (MvPolynomial.eval_X rankName) first)) =
      (arguments.val ()).2.1
        (Fin.cast arguments.property.symm (Fin.cast (MvPolynomial.eval_X rankName) second)) := Fin.ext values
    have indices := (arguments.val ()).2.1.injective old
    have indexValues := congrArg Fin.val indices
    exact Fin.ext indexValues
  · intro first second equal
    have values := congrArg Fin.val equal
    have old : (arguments.val ()).2.2
        (Fin.cast arguments.property.symm (Fin.cast (MvPolynomial.eval_X rankName) first)) =
      (arguments.val ()).2.2
        (Fin.cast arguments.property.symm (Fin.cast (MvPolynomial.eval_X rankName) second)) := Fin.ext values
    have indices := (arguments.val ()).2.2.injective old
    have indexValues := congrArg Fin.val indices
    exact Fin.ext indexValues

end Polytime2.Computation
