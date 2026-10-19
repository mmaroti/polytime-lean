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

import Polytime2.Arithmetic.BoundedTraversal

/-! # Bounded binary loops with mathematical invariants -/

namespace Polytime2.BinaryTraversal

open MultiTape CallingConvention

variable {Parameter TapeName Body : Type} [Fintype Parameter]

/-- Shared traversal proof. The caller describes its live mathematical values
and one body step; the library maintains guard scratch, size headers, regions,
counter capacity, and the polynomial bound for an arbitrary bounded interval. -/
theorem range_runs (capacity : Parameter) (sizes : Parameter → ℕ)
    (width : TapeName → ℕ) (readOnly : TapeName → Bool)
    (wiring : Unit ⊕ Fin 4 ↪ TapeName)
    (guardBound bodyBound length : MvPolynomial Parameter ℕ)
    (compare : ∀ (initial : Tapes (Alphabet TapeName)) (counter limit : Fin (2 ^ sizes capacity)),
      initial (wiring (.inl ())) = unary (sizes capacity) →
      initial (wiring (.inr 0)) = encoded (EncodedDomain.binaryNaturals capacity) sizes counter →
      initial (wiring (.inr 1)) = encoded (EncodedDomain.binaryNaturals capacity) sizes limit →
      Region (sizes capacity) 0 (initial (wiring (.inr 2))) → Region 1 0 (initial (wiring (.inr 3))) →
      ∃ ticks final, ticks ≤ MvPolynomial.eval sizes guardBound ∧
        Runs width readOnly (wire (Alphabet := Alphabet TapeName) wiring BinarySubtraction.algorithm) ticks
          BinarySubtraction.entry (fun _ => 0) initial BinarySubtraction.exit (fun _ => 0) final ∧
        final (wiring (.inr 3)) = encoded EncodedDomain.booleans sizes (decide (counter.val < limit.val)) ∧
        (∀ name, name ≠ wiring (.inr 2) → name ≠ wiring (.inr 3) → final name = initial name))
    (differenceWidth : width (wiring (.inr 2)) = sizes capacity)
    (flagWidth : width (wiring (.inr 3)) = 1)
    (sizeTape : Parameter → TapeName) (capacityTape : sizeTape capacity = wiring (.inl ()))
    (sizeReadonly : ∀ parameter, readOnly (sizeTape parameter) = true)
    (body : Machine (Alphabet TapeName) Body) (bodyEntry bodyExit : Body)
    (bodyHalt : ∀ symbols, body bodyExit symbols = none)
    (invariant : ℕ → Tapes (Alphabet TapeName) → Prop)
    (stable : ∀ count tapes final,
      (∀ name, name ≠ wiring (.inr 2) → name ≠ wiring (.inr 3) → final name = tapes name) →
      invariant count tapes → invariant count final)
    (start limit : Fin (2 ^ sizes capacity)) (within : start.val ≤ limit.val)
    (limitBound : limit.val ≤ MvPolynomial.eval sizes length)
    (bodyRuns : ∀ (count : ℕ) (counterFits : count < 2 ^ sizes capacity), start.val ≤ count →
      count < limit.val → ∀ (nextFits : count + 1 < 2 ^ sizes capacity),
      StandardBinaryIncrement.next capacity sizes ⟨count, counterFits⟩ = ⟨count + 1, nextFits⟩ →
      ∀ initial, invariant count initial →
      initial (wiring (.inr 0)) = encoded (EncodedDomain.binaryNaturals capacity) sizes ⟨count, counterFits⟩ →
      initial (wiring (.inr 1)) = encoded (EncodedDomain.binaryNaturals capacity) sizes limit →
      (∀ parameter, initial (sizeTape parameter) = unary (sizes parameter)) →
      (∀ name, Region (width name) 0 (initial name)) →
      ∃ ticks final, ticks ≤ MvPolynomial.eval sizes bodyBound ∧
        Runs width readOnly body ticks bodyEntry (fun _ => 0) initial bodyExit (fun _ => 0) final ∧
        invariant (count + 1) final ∧
        final (wiring (.inr 0)) = encoded (EncodedDomain.binaryNaturals capacity) sizes ⟨count + 1, nextFits⟩ ∧
        final (wiring (.inr 1)) = initial (wiring (.inr 1)))
    (initial : Tapes (Alphabet TapeName))
    (liveInitial : invariant start.val initial)
    (counterInitial : initial (wiring (.inr 0)) = encoded (EncodedDomain.binaryNaturals capacity) sizes start)
    (limitInitial : initial (wiring (.inr 1)) = encoded (EncodedDomain.binaryNaturals capacity) sizes limit)
    (headers : ∀ parameter, initial (sizeTape parameter) = unary (sizes parameter))
    (regions : ∀ name, Region (width name) 0 (initial name)) :
    ∃ ticks final, ticks ≤ MvPolynomial.eval sizes ((length + 1) * (guardBound + bodyBound + 2) + 1) ∧
      Runs width readOnly
        (withExit (whileMachine (wire (Alphabet := Alphabet TapeName) wiring BinarySubtraction.algorithm) body BinarySubtraction.entry bodyEntry
          (fun symbols => decide (symbols (wiring (.inr 3)) = Binary.data true)))) ticks
        (.inl (.inl BinarySubtraction.entry)) (fun _ => 0) initial (.inr ()) (fun _ => 0) final ∧
      invariant limit.val final ∧
      final (wiring (.inr 0)) = encoded (EncodedDomain.binaryNaturals capacity) sizes limit := by
  let representation (count : ℕ) (tapes : Tapes (Alphabet TapeName)) : Prop :=
    ∃ fits : count < 2 ^ sizes capacity,
      invariant count tapes ∧
      tapes (wiring (.inr 0)) = encoded (EncodedDomain.binaryNaturals capacity) sizes ⟨count, fits⟩ ∧
      tapes (wiring (.inr 1)) = encoded (EncodedDomain.binaryNaturals capacity) sizes limit ∧
      (∀ parameter, tapes (sizeTape parameter) = unary (sizes parameter)) ∧
      (∀ name, Region (width name) 0 (tapes name))
  let result := fun symbols : Symbols (Alphabet TapeName) => decide (symbols (wiring (.inr 3)) = Binary.data true)
  have guardHalt : ∀ symbols, (wire (Alphabet := Alphabet TapeName) wiring BinarySubtraction.algorithm) BinarySubtraction.exit symbols = none := by
    intro symbols
    simp [wire, BinarySubtraction.algorithm, BinarySubtraction.exit,
      StandardBinaryArithmetic.algorithm, StandardBinaryArithmetic.exit, withExit]
  have guarded : ∀ count, start.val ≤ count → count ≤ limit.val → ∀ tapes,
      representation count tapes → ∃ ticks final, ticks ≤ MvPolynomial.eval sizes guardBound ∧
        Runs width readOnly (wire (Alphabet := Alphabet TapeName) wiring BinarySubtraction.algorithm) ticks BinarySubtraction.entry (fun _ => 0)
          tapes BinarySubtraction.exit (fun _ => 0) final ∧
        (representation count final ∧ result (MultiTape.read final) = decide (count < limit.val)) := by
    intro count lower upper tapes valid
    obtain ⟨fits, live, counterEq, limitEq, headers, regions⟩ := valid
    obtain ⟨ticks, final, cost, trace, flag, outside⟩ :=
      compare tapes ⟨count, fits⟩ limit (by rw [← capacityTape]; exact headers capacity) counterEq limitEq
        (by simpa only [differenceWidth] using regions (wiring (.inr 2)))
        (by simpa only [flagWidth] using regions (wiring (.inr 3)))
    refine ⟨ticks, final, cost, trace, ⟨fits, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · exact stable count tapes final outside live
    · exact (outside _ (by exact wiring.injective.ne (by decide)) (by exact wiring.injective.ne (by decide))).trans counterEq
    · exact (outside _ (by exact wiring.injective.ne (by decide)) (by exact wiring.injective.ne (by decide))).trans limitEq
    · intro parameter; exact (trace.readOnly_tape _ (sizeReadonly parameter)).trans (headers parameter)
    · intro name; exact trace.region name (regions name)
    · simp only [result, MultiTape.read, flag, encoded_booleans]
      cases decide (count < limit.val) <;> rfl
  have advanced : ∀ count, start.val ≤ count → count < limit.val → ∀ tapes,
      representation count tapes → ∃ ticks final, ticks ≤ MvPolynomial.eval sizes bodyBound ∧
        Runs width readOnly body ticks bodyEntry (fun _ => 0) tapes bodyExit (fun _ => 0) final ∧
        representation (count + 1) final := by
    intro count lower before tapes valid
    obtain ⟨fits, live, counterEq, limitEq, headers, regions⟩ := valid
    have nextFits : count + 1 < 2 ^ sizes capacity := lt_of_le_of_lt (Nat.succ_le_of_lt before) limit.isLt
    have nextValue : StandardBinaryIncrement.next capacity sizes ⟨count, fits⟩ = ⟨count + 1, nextFits⟩ :=
      Fin.ext (Nat.mod_eq_of_lt nextFits)
    obtain ⟨ticks, final, cost, trace, nextLive, nextCounter, sameLimit⟩ :=
      bodyRuns count fits lower before nextFits nextValue tapes live counterEq limitEq headers regions
    exact ⟨ticks, final, cost, trace, nextFits, nextLive, nextCounter, sameLimit.trans limitEq,
      (fun parameter => (trace.readOnly_tape _ (sizeReadonly parameter)).trans (headers parameter)),
      (fun name => trace.region name (regions name))⟩
  obtain ⟨ticks, final, cost, trace, represented, stopped⟩ :=
    Runs.whileRange width readOnly (wire (Alphabet := Alphabet TapeName) wiring BinarySubtraction.algorithm) body
      BinarySubtraction.entry BinarySubtraction.exit bodyEntry bodyExit result representation
      (fun count tapes => representation count tapes ∧ result (MultiTape.read tapes) = decide (count < limit.val))
      start.val limit.val (MvPolynomial.eval sizes guardBound) (MvPolynomial.eval sizes bodyBound)
      within guardHalt bodyHalt guarded
      (fun count lower before tapes valid => advanced count lower before tapes valid.1)
      (fun _ _ _ _ valid => valid.2) initial
      ⟨start.isLt, liveInitial, counterInitial, limitInitial, headers, regions⟩
  obtain ⟨fits, live, counterEq, remaining⟩ := represented
  refine ⟨ticks, final, ?_, trace, live, counterEq⟩
  have intervalBound : limit.val - start.val + 1 ≤ MvPolynomial.eval sizes length + 1 := by omega
  have total := cost.trans (Nat.add_le_add_right
    (Nat.mul_le_mul_right (MvPolynomial.eval sizes guardBound + MvPolynomial.eval sizes bodyBound + 2) intervalBound) 1)
  simpa only [map_add, map_mul, map_one, map_ofNat] using total

end Polytime2.BinaryTraversal
