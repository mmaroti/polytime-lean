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

import Polytime2.Arrays.FindFalse
import Polytime2.Arithmetic.NaturalArithmetic
import Polytime2.Computation.Fields
import Polytime2.Computation.Records
import Polytime2.Encoding.Dependent
import Polytime2.Encoding.ParameterRename

/-! # Coordinates recovered from successful array searches

A successful optional search result supplies its actual coordinate. An index
with a successor inside the array supplies that successor. Both operations use
ordinary finite coordinates; the search sentinel and differing binary widths
stay inside the realizations.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

/-- Extract the coordinate of a successful search. -/
noncomputable def arraySearchFound (length : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  unaryMap (arraySearchResult length) (boundedIndex length)
    (fun _ value => value.isSome) (fun _ value => value.val.get value.property)

theorem arraySearchFound_realizable (length : MvPolynomial Parameter ℕ) :
    (arraySearchFound length).Realizable := by
  apply Realizable.Internal.fieldProjection (arraySearchResult length) (boundedIndex length) 0
  intro sizes value
  let index := value.val.get value.property
  have someIndex : value.val = some index := (Option.some_get value.property).symm
  have below : Fin.castSucc index < Fin.last (MvPolynomial.eval sizes length) := by simp
  have capacity : index.val < 2 ^ MvPolynomial.eval sizes (length + 1) := by
    simp only [map_add, map_one]
    exact index.isLt.trans_le ((Nat.le_succ _).trans Nat.lt_two_pow_self.le)
  have encoded : (arraySearchResult length).encode sizes value.val =
      (BitVec.ofNatLT index.val capacity : BitVec (MvPolynomial.eval sizes (length + 1))) := by
    dsimp only [arraySearchResult, reindex, boundedIndexOfWidth]
    rw [someIndex, finSuccEquiv'_symm_some_below below]
    rfl
  let source := ArrayEncoding.bits ((arraySearchResult length).encode sizes value.val)
  let target := ArrayEncoding.bits ((boundedIndex length).encode sizes index)
  have initialBits : target = source.take (MvPolynomial.eval sizes length) := by
    dsimp only [source, target]
    rw [encoded]
    exact bits_ofFin_narrow
      (⟨index.val, capacity⟩ : Fin (2 ^ MvPolynomial.eval sizes (length + 1)))
      (⟨index.val, index.isLt.trans_le Nat.lt_two_pow_self.le⟩ : Fin (2 ^ MvPolynomial.eval sizes length))
      rfl (by simp only [map_add, map_one]; omega)
  refine ⟨[], source.drop (MvPolynomial.eval sizes length), ?_, by simp⟩
  change source = [] ++ target ++ source.drop (MvPolynomial.eval sizes length)
  rw [initialBits]
  simpa only [List.nil_append] using (List.take_append_drop (MvPolynomial.eval sizes length) source).symm

/-- Construct the actual successor, provided it remains inside the array. -/
noncomputable def arrayIndexSuccessor (length : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  unaryMap (boundedIndex length) (boundedIndex length)
    (fun sizes value => value.val + 1 < MvPolynomial.eval sizes length)
    (fun _ value => ⟨value.val.val + 1, value.property⟩)

theorem arrayIndexSuccessor_realizable (length : MvPolynomial Parameter ℕ) :
    (arrayIndexSuccessor length).Realizable := by
  let computation := arrayIndexSuccessor length
  have incremented := (Realizable.Internal.naturalIncrement_realizable length).reinterpretInputs
    (fun _ : Unit => boundedIndex length)
    (fun _ _ value => ⟨value.val, value.isLt.trans_le Nat.lt_two_pow_self.le⟩)
    (by intros; rfl) (by intros; rfl) computation.precondition (by intros; trivial)
  have refined := incremented.refineOutput
    (fun sizes value => value.val < MvPolynomial.eval sizes length) (by
      intro sizes arguments
      change ((arguments.val ()).val + 1) % 2 ^ MvPolynomial.eval sizes length < _
      rw [Nat.mod_eq_of_lt (arguments.property.trans_le Nat.lt_two_pow_self.le)]
      exact arguments.property)
  have converted := refined.reinterpretOutput (boundedIndex length)
    (fun _ value => ⟨value.val.val, value.property⟩) (by intros; rfl) (by intros; rfl)
  apply converted.withSpecification computation.precondition computation.compute (by intros; assumption)
  intro sizes arguments valid
  apply Fin.ext
  change ((arguments ()).val + 1) % 2 ^ MvPolynomial.eval sizes length = (arguments ()).val + 1
  exact Nat.mod_eq_of_lt (valid.trans_le Nat.lt_two_pow_self.le)

/-- Extract a successful coordinate together with its adjacent successor. -/
noncomputable def arraySearchAdjacentPair (length : MvPolynomial Parameter ℕ) : Computation Parameter Unit where
  inputDomains _ := arraySearchResult length
  outputDomain := (boundedIndex length).prod (boundedIndex length)
  precondition sizes arguments := (arguments ()).isSome ∧
    ∀ first, arguments () = some first → first.val + 1 < MvPolynomial.eval sizes length
  compute _ arguments :=
    let first := (arguments.val ()).get arguments.property.1
    (first, ⟨first.val + 1, arguments.property.2 first (Option.some_get arguments.property.1).symm⟩)

theorem arraySearchAdjacentPair_realizable (length : MvPolynomial Parameter ℕ) :
    (arraySearchAdjacentPair length).Realizable := by
  let computation := arraySearchAdjacentPair length
  have first := (arraySearchFound_realizable length).withPrecondition computation.precondition
    (by intro sizes arguments valid; exact valid.1)
  have second := first.followedBy (arrayIndexSuccessor_realizable length) rfl (by
    intro sizes arguments valid
    exact valid.2 _ (Option.some_get valid.1).symm)
  exact (first.prodMk second).withSpecification computation.precondition computation.compute
    (by intros; assumption) (by intros; rfl)

/-- The extracted pair contains the returned coordinate and its actual successor. -/
theorem arraySearchAdjacentPair_values (length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (arraySearchAdjacentPair length).Arguments sizes //
      (arraySearchAdjacentPair length).precondition sizes arguments}) :
    let pair := (arraySearchAdjacentPair length).compute sizes arguments
    arguments.val () = some pair.1 ∧ pair.2.val = pair.1.val + 1 ∧ pair.1 ≠ pair.2 := by
  refine ⟨(Option.some_get arguments.property.1).symm, rfl, ?_⟩
  intro same
  have values := congrArg Fin.val same
  dsimp [arraySearchAdjacentPair] at values
  omega

/-- None and actual coordinates retain the same canonical optional-index word. -/
theorem arraySearchResult_original_bits {HostParameter : Type} [Fintype HostParameter]
    (length : MvPolynomial HostParameter ℕ) (names : HostParameter → Parameter) (sizes : Parameter → ℕ)
    (value : (EncodedDomain.arraySearchResult (MvPolynomial.rename names length)).Carrier sizes) :
    EncodedDomain.ArrayEncoding.bits ((EncodedDomain.arraySearchResult (MvPolynomial.rename names length)).encode sizes value) =
      EncodedDomain.ArrayEncoding.bits (((EncodedDomain.arraySearchResult length).renameParameters names).encode sizes
        (value.map (Fin.cast (MvPolynomial.eval_rename names sizes length)))) := by
  rw [EncodedDomain.renameParameters_bits]
  cases value with
  | none =>
    simp only [Option.map_none, EncodedDomain.arraySearchResult, EncodedDomain.reindex,
      EncodedDomain.boundedIndexOfWidth, finSuccEquiv'_symm_none, BitVec.ofNatLT_eq_ofNat,
      EncodedDomain.ArrayEncoding.bits, BitVec.getLsbD_ofNat, Fin.val_last,
      map_add, map_one, MvPolynomial.eval_rename]
    simp only [Fin.val_cast]
  | some index =>
    have sourceCode := finSuccEquiv'_symm_some_below
      (i := Fin.last (MvPolynomial.eval sizes (MvPolynomial.rename names length))) (m := index) index.isLt
    have targetCode := finSuccEquiv'_symm_some_below
      (i := Fin.last (MvPolynomial.eval (sizes ∘ names) length))
      (m := Fin.cast (MvPolynomial.eval_rename names sizes length) index)
      (by simpa only [Fin.lt_def, Fin.val_castSucc, Fin.val_cast, Fin.val_last, MvPolynomial.eval_rename] using index.isLt)
    simp only [Option.map_some, EncodedDomain.arraySearchResult, EncodedDomain.reindex,
      EncodedDomain.boundedIndexOfWidth, sourceCode, targetCode, BitVec.ofNatLT_eq_ofNat,
      EncodedDomain.ArrayEncoding.bits, BitVec.getLsbD_ofNat, Fin.val_castSucc, Fin.val_cast,
      map_add, map_one, MvPolynomial.eval_rename]


end Polytime2.Computation
