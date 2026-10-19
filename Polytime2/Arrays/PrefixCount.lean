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

import Polytime2.Arrays.Count
import Polytime2.Arrays.Scan

/-! # Certified dense positions as strict Boolean prefix counts -/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

variable {Parameter : Type} [Fintype Parameter]

/-- Every position stores the number of true flags strictly before it. -/
private noncomputable def prefixCountsImplementation (length : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  let state := EncodedDomain.bitVectors (length + 1)
  let seed := (zeroBitArray (length + 1) (length + 1)).withArguments
    (fun _ : Unit => EncodedDomain.booleans.arrayOfLength length)
    ⟨Empty.elim, by intro impossible; exact impossible.elim⟩ (by intro impossible; exact impossible.elim)
  let domains := Sum.elim seed.inputDomains (fun _ : Unit => state.arrayOfLength (length + 1))
  let scan := (arrayScan EncodedDomain.booleans state length (fun _ current flag => addFlag current flag)).withArguments
    domains ⟨(fun choice => if choice then (Sum.inl () : Unit ⊕ Unit) else .inr ()), by
      intro first second equal; cases first <;> cases second <;> simp_all⟩
    (by intro choice; cases choice <;> rfl)
  (seed.letThen scan (fun _ => rfl) rfl (by intros; trivial)).followedBy
    (arrayInit state length) rfl (by intros; trivial)

private theorem prefixCountsImplementation_realizable (length : MvPolynomial Parameter ℕ) : (prefixCountsImplementation length).Realizable := by
  let state := EncodedDomain.bitVectors (length + 1)
  have seed := (zeroBitArray_realizable (length + 1) (length + 1)).withArguments
    (fun _ : Unit => EncodedDomain.booleans.arrayOfLength length)
    ⟨Empty.elim, by intro impossible; exact impossible.elim⟩ (by intro impossible; exact impossible.elim)
  let domains := Sum.elim (fun _ : Unit => EncodedDomain.booleans.arrayOfLength length)
    (fun _ : Unit => state.arrayOfLength (length + 1))
  have scan := (arrayScan_realizable EncodedDomain.booleans state length
    (fun _ current flag => addFlag current flag) (countFlagStep_realizable (length + 1))).withArguments domains
    ⟨(fun choice => if choice then (Sum.inl () : Unit ⊕ Unit) else .inr ()), by
      intro first second equal; cases first <;> cases second <;> simp_all⟩
    (by intro choice; cases choice <;> rfl)
  exact (seed.letThen scan (fun _ => rfl) rfl (by intros; trivial)).followedBy
    (arrayInit_realizable state length) rfl (by intros; trivial)

omit [Fintype Parameter] in
private theorem prefix_capacity (length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (flags : Fin (MvPolynomial.eval sizes length) → Bool) (index : Fin (MvPolynomial.eval sizes length)) :
    ((List.ofFn flags).take index.val).count true < 2 ^ MvPolynomial.eval sizes (length + 1) := by
  have bounded := List.count_le_length (a := true) (l := (List.ofFn flags).take index.val)
  have lengthBound : ((List.ofFn flags).take index.val).length ≤ MvPolynomial.eval sizes length := by simp
  have capacity := lt_trans (Nat.lt_succ_self _) (Nat.lt_two_pow_self (n := MvPolynomial.eval sizes length + 1))
  exact lt_of_le_of_lt (bounded.trans lengthBound) (by simpa only [map_add, map_one] using capacity)

/-- Prefix counters are exact, including zero length and inactive positions. -/
private theorem prefixCountsImplementation_correct (length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (flags : Fin (MvPolynomial.eval sizes length) → Bool) (index : Fin (MvPolynomial.eval sizes length)) :
    (((prefixCountsImplementation length).compute sizes ⟨(fun _ => flags), trivial⟩) index).toNat =
      ((List.ofFn flags).take index.val).count true := by
  let state := EncodedDomain.bitVectors (length + 1)
  let initial : (state.arrayOfLength (length + 1)).Carrier sizes := fun _ =>
    BitVec.ofNat (MvPolynomial.eval sizes (length + 1)) 0
  let result : Fin (MvPolynomial.eval sizes (length + 1)) → BitVec (MvPolynomial.eval sizes (length + 1)) := (arrayScan EncodedDomain.booleans state length (fun _ current flag => addFlag current flag)).compute sizes
    ⟨(fun | false => initial | true => flags), trivial⟩
  have trace := arrayScan_correct EncodedDomain.booleans state length
    (fun _ current flag => addFlag current flag) sizes initial flags
  have entry := congrArg (fun values : List (BitVec (MvPolynomial.eval sizes (length + 1))) => values[index.val]?) trace
  have before : index.val < MvPolynomial.eval sizes length + 1 := by omega
  have bounded : index.val ≤ MvPolynomial.eval sizes length := by omega
  simp only [List.getElem?_ofFn, before, dite_true, List.getElem?_scanl, List.length_ofFn,
    bounded, ite_true] at entry
  have value := Option.some.inj entry
  change (successorValues (Element := BitVec (MvPolynomial.eval sizes (length + 1))) length sizes result ⟨index.val, before⟩).toNat = _
  change successorValues (Element := BitVec (MvPolynomial.eval sizes (length + 1))) length sizes result ⟨index.val, before⟩ = _ at value
  rw [value, countFlag_fold]
  simp only [initial, successorValues, BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_add]
  apply Nat.mod_eq_of_lt
  exact prefix_capacity length sizes flags index


/-- Store exact strict prefix counts with a compact mathematical specification. -/
noncomputable def prefixCounts (length : MvPolynomial Parameter ℕ) : Computation Parameter Unit where
  inputDomains _ := EncodedDomain.booleans.arrayOfLength length
  outputDomain := (EncodedDomain.bitVectors (length + 1)).arrayOfLength length
  precondition _ _ := True
  compute sizes arguments := fun index => BitVec.ofNat (MvPolynomial.eval sizes (length + 1))
    (((List.ofFn (arguments.val ())).take index.val).count true)

theorem prefixCounts_realizable (length : MvPolynomial Parameter ℕ) : (prefixCounts length).Realizable := by
  exact (prefixCountsImplementation_realizable length).withSpecification (prefixCounts length).precondition
    (prefixCounts length).compute (by intros; trivial) (by
      intro sizes arguments valid
      funext index
      apply BitVec.eq_of_toNat_eq
      have normalized : arguments = (fun _ => arguments ()) := by funext name; cases name; rfl
      have correct := prefixCountsImplementation_correct length sizes (arguments ()) index
      rw [← normalized] at correct
      rw [correct]
      exact (Nat.mod_eq_of_lt (prefix_capacity length sizes (arguments ()) index)).symm)

theorem prefixCounts_correct (length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (flags : Fin (MvPolynomial.eval sizes length) → Bool) (index : Fin (MvPolynomial.eval sizes length)) :
    (((prefixCounts length).compute sizes ⟨(fun _ => flags), trivial⟩) index).toNat =
      ((List.ofFn flags).take index.val).count true :=
  Nat.mod_eq_of_lt (prefix_capacity length sizes flags index)

omit [Fintype Parameter] in
/-- A finite order index is the cardinality of its strict initial segment. -/
theorem orderIndex_card {Ordered : Type} [LinearOrder Ordered] {count : ℕ}
    (ordering : Ordered ≃o Fin count) (value : Ordered) :
    Nat.card {other : Ordered // other < value} = (ordering value).val := by
  let equivalence : {other : Ordered // other < value} ≃ Fin (ordering value).val :=
    { toFun := fun other => ⟨(ordering other.val).val, ordering.strictMono other.property⟩
      invFun := fun position =>
        ⟨ordering.symm ⟨position.val, lt_trans position.isLt (ordering value).isLt⟩, by
          apply (ordering.lt_iff_lt).mp
          rw [ordering.apply_symm_apply]
          exact position.isLt⟩
      left_inv := by
        intro other
        apply Subtype.ext
        apply ordering.injective
        simp
      right_inv := by intro position; apply Fin.ext; simp }
  exact (Nat.card_congr equivalence).trans (Nat.card_fin _)

omit [Fintype Parameter] in
/-- Strict Boolean prefix counts are the dense order indices of active positions. -/
theorem prefix_count_orderIndex {length count : ℕ} (flags : Fin length → Bool)
    (active : {index : Fin length // flags index = true})
    (ordering : {index : Fin length // flags index = true} ≃o Fin count) :
    ((List.ofFn flags).take active.val.val).count true = (ordering active).val := by
  let restricted : Fin active.val.val → Bool := fun index =>
    flags ⟨index.val, lt_trans index.isLt active.val.isLt⟩
  have taken : (List.ofFn flags).take active.val.val = List.ofFn restricted := by
    apply List.ext_getElem
    · simp
    · intro index firstBound secondBound
      simp [restricted]
  rw [taken, count_flags_card]
  let equivalence : {index : Fin active.val.val // restricted index = true} ≃
      {other : {index : Fin length // flags index = true} // other < active} :=
    { toFun := fun index => ⟨⟨⟨index.val.val, lt_trans index.val.isLt active.val.isLt⟩, index.property⟩, index.val.isLt⟩
      invFun := fun other => ⟨⟨other.val.val.val, other.property⟩, other.val.property⟩
      left_inv := by intro index; apply Subtype.ext; rfl
      right_inv := by intro other; apply Subtype.ext; apply Subtype.ext; rfl }
  rw [Nat.card_congr equivalence]
  exact orderIndex_card ordering active

end Polytime2.Computation
