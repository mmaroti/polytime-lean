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

import Polytime2.Computation.Specification
import Polytime2.Arrays.Count

/-! # Finding the first false flag through a finite-memory prefix scan -/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

variable {Parameter : Type} [Fintype Parameter]

namespace FirstFalse

/-- Once a false flag is read, every subsequent output flag is false. -/
def update (active bit : Bool) : Bool × Bool := (active && bit, active && bit)

def mask : List Bool → List Bool
  | [] => []
  | true :: rest => true :: mask rest
  | false :: rest => List.replicate (rest.length + 1) false

@[simp] theorem mask_length (flags : List Bool) : (mask flags).length = flags.length := by
  induction flags with
  | nil => rfl
  | cons flag rest hypothesis => cases flag <;> simp [mask, hypothesis]

theorem scan_false (flags : List Bool) : (BinaryScan.run update false flags).2 = List.replicate flags.length false := by
  induction flags with
  | nil => rfl
  | cons flag rest hypothesis => simp [BinaryScan.run, update, hypothesis, List.replicate_succ]

theorem scan_true (flags : List Bool) : (BinaryScan.run update true flags).2 = mask flags := by
  induction flags with
  | nil => rfl
  | cons flag rest hypothesis => cases flag <;> simp [BinaryScan.run, update, mask, hypothesis, scan_false, List.replicate_succ]

theorem mask_count (flags : List Bool) : (mask flags).count true = flags.findIdx (! ·) := by
  induction flags with
  | nil => rfl
  | cons flag rest hypothesis => cases flag <;> simp [mask, List.findIdx_cons, hypothesis, List.count_replicate]

/-- Boolean domain arrays are exactly their sequence of canonical Boolean bits. -/
theorem boolean_bits (length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (flags : Fin (MvPolynomial.eval sizes length) → Bool) :
    EncodedDomain.ArrayEncoding.bits ((EncodedDomain.booleans.arrayOfLength length).encode sizes flags) = List.ofFn flags := by
  rw [EncodedDomain.arrayOfLength_encode_bits, EncodedDomain.ArrayEncoding.bits_encode]
  have scalar (value : Bool) : EncodedDomain.ArrayEncoding.bits (EncodedDomain.booleans.encode sizes value) = [value] := by
    cases value <;> simp [EncodedDomain.booleans, EncodedDomain.fixed, EncodedDomain.ofCodec,
      EncodedDomain.ArrayEncoding.bits, List.ofFn_succ] <;> decide
  simp only [scalar]
  change (List.ofFn ((fun value : Bool => [value]) ∘ flags)).flatten = _
  rw [← List.map_ofFn]
  exact List.flatMap_singleton' _

/-- Restore the indexed array carrier after a length-preserving list scan. -/
def masked {length : ℕ} (flags : Fin length → Bool) : Fin length → Bool := fun index =>
  (mask (List.ofFn flags)).get ⟨index.val, by simp only [mask_length, List.length_ofFn]; exact index.isLt⟩

theorem ofFn_masked {length : ℕ} (flags : Fin length → Bool) :
    List.ofFn (masked flags) = mask (List.ofFn flags) := by
  rw [List.ofFn_congr (show length = (mask (List.ofFn flags)).length by simp)]
  exact List.ofFn_get _

end FirstFalse

noncomputable def leadingFlags (length : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  encodingMap (EncodedDomain.booleans.arrayOfLength length) (EncodedDomain.booleans.arrayOfLength length)
    (fun _ flags => FirstFalse.masked flags)

theorem leadingFlags_realizable (length : MvPolynomial Parameter ℕ) : (leadingFlags length).Realizable := by
  apply bitTransducer_realizable FirstFalse.update true _ _ _ (by intros; rfl)
  intro sizes flags
  rw [FirstFalse.boolean_bits, FirstFalse.boolean_bits, FirstFalse.ofFn_masked, FirstFalse.scan_true]

/-- The array length is the all-true sentinel, including the empty array. -/
private noncomputable def implementation (length : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  (leadingFlags length).followedBy (countFlags length) rfl (by intros; trivial)

private theorem implementation_realizable (length : MvPolynomial Parameter ℕ) : (implementation length).Realizable :=
  (leadingFlags_realizable length).followedBy (countFlags_realizable length) rfl (by intros; trivial)

private theorem implementation_correct (length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (flags : Fin (MvPolynomial.eval sizes length) → Bool) :
    ((implementation length).compute sizes ⟨(fun _ => flags), trivial⟩).toNat = (List.ofFn flags).findIdx (! ·) := by
  change ((countFlags length).compute sizes ⟨(fun _ => FirstFalse.masked flags), trivial⟩).toNat = _
  rw [countFlags_correct, FirstFalse.ofFn_masked, FirstFalse.mask_count]

/-- Specify the first false position, or the array length if none exists mathematically.
The finite-memory traversal and counter implementation stay private. -/
noncomputable def firstFalse (length : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  specificationBy (fun _ => EncodedDomain.booleans.arrayOfLength length)
    (EncodedDomain.bitVectors (length + 1)) (fun _ _ => True) (fun _ => BitVec.toNat)
    (fun _sizes arguments => (List.ofFn (arguments.val ())).findIdx (! ·))
    (fun sizes arguments => ⟨(implementation length).compute sizes arguments,
      implementation_correct length sizes (arguments.val ())⟩)

theorem firstFalse_realizable (length : MvPolynomial Parameter ℕ) : (firstFalse length).Realizable := by
  apply (implementation_realizable length).specificationBy
  · intro sizes first second same
    exact BitVec.eq_of_toNat_eq same
  · intro sizes arguments valid
    exact implementation_correct length sizes (arguments ())

/-- Evaluate the mathematical observation without unfolding the traversal. -/
theorem firstFalse_correct (length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (flags : Fin (MvPolynomial.eval sizes length) → Bool) :
    ((firstFalse length).compute sizes ⟨(fun _ => flags), trivial⟩).toNat = (List.ofFn flags).findIdx (! ·) := by
  simp only [firstFalse, specificationBy_correct]

theorem firstFalse_bound (length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (flags : Fin (MvPolynomial.eval sizes length) → Bool) :
    ((firstFalse length).compute sizes ⟨(fun _ => flags), trivial⟩).toNat ≤ MvPolynomial.eval sizes length := by
  rw [firstFalse_correct]
  simpa only [List.length_ofFn] using (List.findIdx_le_length (p := (! ·)) (xs := List.ofFn flags))

/-- A nonsentinel result is an actual false input flag. -/
theorem firstFalse_found (length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (flags : Fin (MvPolynomial.eval sizes length) → Bool)
    (before : ((firstFalse length).compute sizes ⟨(fun _ => flags), trivial⟩).toNat < MvPolynomial.eval sizes length) :
    flags ⟨((firstFalse length).compute sizes ⟨(fun _ => flags), trivial⟩).toNat, before⟩ = false := by
  have bounded : (List.ofFn flags).findIdx (! ·) < MvPolynomial.eval sizes length := by
    rw [← firstFalse_correct length sizes flags]
    exact before
  have indices : (⟨((firstFalse length).compute sizes ⟨(fun _ => flags), trivial⟩).toNat, before⟩ : Fin _) =
      ⟨(List.ofFn flags).findIdx (! ·), bounded⟩ := Fin.ext (firstFalse_correct _ _ _)
  rw [indices]
  have found := List.findIdx_getElem (p := (! ·)) (xs := List.ofFn flags) (w := by simpa using bounded)
  simpa using found

/-- The sentinel is returned exactly when every flag is true. -/
theorem firstFalse_sentinel (length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (flags : Fin (MvPolynomial.eval sizes length) → Bool) :
    ((firstFalse length).compute sizes ⟨(fun _ => flags), trivial⟩).toNat = MvPolynomial.eval sizes length ↔
      ∀ index, flags index = true := by
  rw [firstFalse_correct]
  simpa using (List.findIdx_eq_length (p := (! ·)) (xs := List.ofFn flags))

end Polytime2.Computation
