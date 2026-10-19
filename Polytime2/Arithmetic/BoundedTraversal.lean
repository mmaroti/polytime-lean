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

import Polytime2.Arithmetic.BinarySubtraction
import Polytime2.Arithmetic.BinaryIncrement
import Polytime2.Machine.CallingConventionRegions
import Polytime2.Machine.CallingConventionWhile

/-! # Shared binary guards and bounded traversal contracts -/

namespace Polytime2.BinaryTraversal

open MultiTape CallingConvention

variable {Parameter TapeName : Type} [Fintype Parameter]

/-- Place the same restoring comparison in any traversal workspace. Only its
binary difference and Boolean flag may change; every other tape is preserved. -/
theorem comparison_runs (capacity : Parameter)
    (width : (Parameter → ℕ) → TapeName → ℕ) (readOnly : TapeName → Bool)
    (wiring : Unit ⊕ Fin 4 ↪ TapeName)
    (widths : ∀ sizes name, width sizes (wiring name) =
      (BinarySubtraction.domains name).width (fun _ => sizes capacity))
    (immutable : ∀ name, readOnly (wiring name) = true → BinarySubtraction.argumentReadOnly name = true) :
    ∃ bound : MvPolynomial Parameter ℕ, ∀ (sizes : Parameter → ℕ)
      (initial : Tapes (Alphabet TapeName)) (counter limit : Fin (2 ^ sizes capacity)),
      initial (wiring (.inl ())) = unary (sizes capacity) →
      initial (wiring (.inr 0)) = encoded (EncodedDomain.binaryNaturals capacity) sizes counter →
      initial (wiring (.inr 1)) = encoded (EncodedDomain.binaryNaturals capacity) sizes limit →
      Region (sizes capacity) 0 (initial (wiring (.inr 2))) →
      Region 1 0 (initial (wiring (.inr 3))) →
      ∃ ticks final, ticks ≤ MvPolynomial.eval sizes bound ∧
        Runs (width sizes) readOnly (wire wiring BinarySubtraction.algorithm) ticks
          BinarySubtraction.entry (fun _ => 0) initial BinarySubtraction.exit (fun _ => 0) final ∧
        final (wiring (.inr 3)) = encoded EncodedDomain.booleans sizes (decide (counter.val < limit.val)) ∧
        (∀ name, name ≠ wiring (.inr 2) → name ≠ wiring (.inr 3) → final name = initial name) := by
  obtain ⟨bound, execute⟩ := BinarySubtraction.comparison_contract.wired_runs wiring
  refine ⟨MvPolynomial.rename (fun _ : Unit => capacity) bound, ?_⟩
  intro sizes initial counter limit header counterEq limitEq differenceRegion guardRegion
  let localSizes : Unit → ℕ := fun _ => sizes capacity
  let input : Inputs BinarySubtraction.domains BinarySubtraction.argumentReadOnly localSizes := fun name => by
    rcases name with ⟨name, readonly⟩
    cases name with
    | inl parameter => exact PUnit.unit
    | inr name =>
      by_cases first : name = 0
      · subst name; exact counter
      · by_cases second : name = 1
        · subst name; exact limit
        · have writable : BinarySubtraction.argumentReadOnly (.inr name) = false := by
            fin_cases name <;> first | rfl | contradiction
          rw [writable] at readonly
          contradiction
  obtain ⟨ticks, output, final, cost, trace, correct, canonical, outside, unchanged⟩ :=
    execute localSizes input (width sizes) readOnly initial (widths sizes) immutable trivial
      (by
        intro name readonly
        fin_cases name
        · change initial (wiring (.inl ())) = encoded (EncodedDomain.unary ()) localSizes PUnit.unit
          rw [encoded_unary]; exact header
        · change initial (wiring (.inr 0)) = encoded (EncodedDomain.binaryNaturals ()) localSizes counter
          simpa only [encoded, EncodedDomain.binaryNaturals, EncodedDomain.ofCodec,
            EncodedDomain.ArrayEncoding.bits_cast, localSizes] using counterEq
        · change initial (wiring (.inr 1)) = encoded (EncodedDomain.binaryNaturals ()) localSizes limit
          simpa only [encoded, EncodedDomain.binaryNaturals, EncodedDomain.ofCodec,
            EncodedDomain.ArrayEncoding.bits_cast, localSizes] using limitEq
        · contradiction
        · contradiction)
      (by
        intro name writable
        fin_cases name
        · contradiction
        · contradiction
        · contradiction
        · rw [widths]
          simpa [BinarySubtraction.domains, StandardBinaryArithmetic.domains,
            EncodedDomain.binaryNaturals_width] using differenceRegion
        · rw [widths]
          simpa [BinarySubtraction.domains, StandardBinaryArithmetic.domains, EncodedDomain.booleans, EncodedDomain.fixed, EncodedDomain.ofCodec,
            show Nat.clog 2 2 = 1 from by decide] using guardRegion)
      (by intro parameter; cases parameter; exact header)
  refine ⟨ticks, final, ?_, trace, ?_, ?_⟩
  · simpa only [MvPolynomial.eval_rename, localSizes, Function.comp_def] using cost
  · have flag := canonical true
    change final (wiring (.inr 3)) = encoded EncodedDomain.booleans localSizes (output true) at flag
    change output true = decide (counter.val < limit.val) at correct
    rw [correct] at flag
    simpa only [encoded, EncodedDomain.booleans, EncodedDomain.fixed, EncodedDomain.ofCodec,
      EncodedDomain.ArrayEncoding.bits_cast] using flag
  · intro name notDifference notGuard
    apply preserved_of_wiring wiring BinarySubtraction.argumentReadOnly initial final outside unchanged
    intro localName equal
    fin_cases localName
    · rfl
    · rfl
    · rfl
    · exact False.elim (notDifference equal.symm)
    · exact False.elim (notGuard equal.symm)

end Polytime2.BinaryTraversal
