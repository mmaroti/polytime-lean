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

import Polytime2.Arrays.PackingStep
import Polytime2.Arrays.FoldContract

/-! # A certified traversal for stable array packing

The source cursor visits every input element once. The dense cursor advances
only for selected entries; the accumulator keeps all capacity storage private.
-/

namespace Polytime2.Computation

variable {Parameter : Type} [Fintype Parameter]

/-- Run the packing update from zero cursors and caller-supplied raw storage.
The public packing algorithm will allocate zero storage and hide the capacity. -/
noncomputable def packingPass (element : EncodedDomain Parameter) (capacity : Parameter)
    (length : MvPolynomial Parameter ℕ) : Computation Parameter (Unit ⊕ Bool) :=
  arrayFold (fun _ : Unit => EncodedDomain.booleans.arrayOfLength length)
    element (packingState element capacity length) length
    (fun sizes _ _ initial => initial.1.val = 0 ∧ initial.2.1.val = 0 ∧
      MvPolynomial.eval sizes length < 2 ^ sizes capacity)
    (fun sizes flags current value => packingAdvance element capacity length sizes (flags ()) current value)

theorem packingPass_realizable (element : EncodedDomain Parameter) (capacity : Parameter)
    (length : MvPolynomial Parameter ℕ) : (packingPass element capacity length).Realizable := by
  refine arrayFold_realizable (fun _ : Unit => EncodedDomain.booleans.arrayOfLength length)
    element (packingState element capacity length) length _ _
    (fun sizes _ current _ => current.1.val < MvPolynomial.eval sizes length ∧ current.2.1.val ≤ current.1.val)
    (packingAdvance_realizable element capacity length)
    (fun _ _ _ _ processed current => current.1.val = processed ∧ current.2.1.val ≤ processed) ?_ ?_ ?_
  · intro sizes flags array initial valid
    exact ⟨valid.1, by omega⟩
  · intro sizes flags array initial valid index current invariant
    constructor
    · rw [invariant.1]; exact index.isLt
    · rw [invariant.1]; exact invariant.2
  · intro sizes flags array initial valid index current invariant
    exact packingAdvance_cursors element capacity length sizes (flags ()) current (array index)
      index.val invariant.1 invariant.2 index.isLt valid.2.2

/-- Canonical private initial state, without a default value of the element
carrier. Zero blocks are raw bits and need not decode as elements. -/
noncomputable def packingZero (element : EncodedDomain Parameter) (capacity : Parameter)
    (length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ) :
    (packingState element capacity length).Carrier sizes :=
  (⟨0, by positivity⟩, (⟨0, by positivity⟩, fun _ => 0))

private theorem packingSeed_realizable (element : EncodedDomain Parameter) (capacity : Parameter)
    (length : MvPolynomial Parameter ℕ) :
    (Computation.mk (Empty.elim : Empty → EncodedDomain Parameter) (packingState element capacity length)
      (fun _ _ => True) (fun sizes _ => packingZero element capacity length sizes)).Realizable := by
  let counter := EncodedDomain.binaryNaturals capacity
  let raw := EncodedDomain.bitVectors element.widthPolynomial
  let array := raw.arrayOfLength length
  have zeroCounter : (Computation.mk (Empty.elim : Empty → EncodedDomain Parameter) counter
      (fun _ _ => True) (fun sizes _ => (⟨0, by positivity⟩ : Fin (2 ^ sizes capacity)))).Realizable := by
    apply (zeroBits_realizable (MvPolynomial.X capacity)).withEncodedOutput counter
      (fun sizes _ => (⟨0, by positivity⟩ : Fin (2 ^ sizes capacity)))
      (by intro sizes; simp [counter, zeroBits, EncodedDomain.binaryNaturals, EncodedDomain.ofCodec])
    intro sizes arguments
    simp [CallingConvention.encoded, counter, EncodedDomain.binaryNaturals, EncodedDomain.ofCodec,
      EncodedDomain.ArrayEncoding.bits_cast, EncodedDomain.ArrayEncoding.bits, zeroBits, BitVec.getLsbD, BitVec.toNat_zero]
    have zero : BitVec.toNat (0 : (EncodedDomain.bitVectors (MvPolynomial.X capacity)).Carrier sizes) = 0 := rfl
    simp only [zero, Nat.zero_testBit, List.ofFn_const]
  have zeroArray : (Computation.mk (Empty.elim : Empty → EncodedDomain Parameter) array
      (fun _ _ => True) (fun _ _ => fun _ => 0)).Realizable :=
    zeroBitArray_realizable element.widthPolynomial length
  exact zeroCounter.prodMk (zeroCounter.prodMk zeroArray)

/-- The mask and values are the only mathematical inputs. Initialization of
both counters and all capacity blocks is charged to the algorithm. -/
noncomputable def packingInitialized (element : EncodedDomain Parameter) (capacity : Parameter)
    (length : MvPolynomial Parameter ℕ) : Computation Parameter Bool where
  inputDomains choice := if choice then element.arrayOfLength length
    else EncodedDomain.booleans.arrayOfLength length
  outputDomain := packingState element capacity length
  precondition sizes _ := MvPolynomial.eval sizes length < 2 ^ sizes capacity
  compute sizes arguments := ArrayFold.prefixValue
    (packingAdvance element capacity length sizes (arguments.val false)) (arguments.val true)
    (packingZero element capacity length sizes) (MvPolynomial.eval sizes length)

theorem packingInitialized_realizable (element : EncodedDomain Parameter) (capacity : Parameter)
    (length : MvPolynomial Parameter ℕ) : (packingInitialized element capacity length).Realizable := by
  let computation := packingInitialized element capacity length
  let inputs := computation.inputDomains
  let allowed := computation.precondition
  let Arguments sizes := {arguments : ∀ name, (inputs name).Carrier sizes // allowed sizes arguments}
  let values (name : Unit ⊕ Bool) sizes (arguments : Arguments sizes) :
      ((packingPass element capacity length).inputDomains name).Carrier sizes :=
    match name with
    | .inl _ => arguments.val false
    | .inr false => packingZero element capacity length sizes
    | .inr true => arguments.val true
  have valid sizes (arguments : Arguments sizes) : (packingPass element capacity length).precondition sizes
      (fun name => values name sizes arguments) := ⟨rfl, rfl, arguments.property⟩
  have seedReady : (Computation.mk inputs (packingState element capacity length) allowed
      (fun sizes _ => packingZero element capacity length sizes)).Realizable :=
    (packingSeed_realizable element capacity length).onResults inputs allowed
      (fun impossible => impossible.elim) (by intros; trivial) (fun impossible => impossible.elim)
  have producers name : (Computation.mk inputs ((packingPass element capacity length).inputDomains name)
      allowed (values name)).Realizable := by
    rcases name with singleton | choice
    · cases singleton; exact Realizable.argument inputs false allowed
    · cases choice
      · exact seedReady
      · exact Realizable.argument inputs true allowed
  exact (packingPass_realizable element capacity length).onResults inputs allowed values valid producers

end Polytime2.Computation
