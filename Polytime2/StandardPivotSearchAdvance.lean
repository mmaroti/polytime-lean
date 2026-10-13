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

import Polytime2.StandardPivotSearchCalls

/-! # Advancing the fixed-width pivot candidate -/

namespace Polytime2.StandardPivotSearch

open MultiTape CallingConvention

/-- Increment a candidate into a separate tape, then commit it by copying the
result back. The capacity hypothesis rules out modular overflow. -/
theorem advance_runs (scalar : EncodedDomain.{0, 0} Empty) :
    ∃ bound : MvPolynomial (Fin 3) ℕ, ∀ (sizes : Fin 3 → ℕ) (initial : Tapes Alphabet)
      (candidate : Fin (2 ^ sizes 0)),
      (candidateValue : candidate.val + 1 < 2 ^ sizes 0) →
      initial (counterTape 1) = encoded (EncodedDomain.binaryNaturals 0) sizes candidate →
      (∀ parameter, initial (sizeTape parameter) = unary (sizes parameter)) →
      (∀ name, Region ((domains scalar name).width sizes) 0 (initial name)) →
      (∀ name, readOnly name = false →
        ∃ value : (domains scalar name).Carrier sizes,
          initial name = encoded (domains scalar name) sizes value) →
      ∃ ticks final,
        ticks ≤ MvPolynomial.eval sizes bound ∧
        Runs (fun name => (domains scalar name).width sizes) readOnly advance ticks
          advanceEntry (fun _ => 0) initial advanceExit (fun _ => 0) final ∧
        final (counterTape 1) = encoded (EncodedDomain.binaryNaturals 0) sizes
          ⟨candidate.val + 1, candidateValue⟩ ∧
        (∀ name, readOnly name = false →
          ∃ value : (domains scalar name).Carrier sizes,
            final name = encoded (domains scalar name) sizes value) ∧
        (∀ name, name ≠ counterTape 1 → name ≠ nextTape → final name = initial name) := by
  classical
  obtain ⟨incrementBound, executeIncrement⟩ :=
    (StandardBinaryIncrement.contract (0 : Fin 3)).wired_runs incrementWiring
  refine ⟨incrementBound +
    (MvPolynomial.C (2 : ℕ) * MvPolynomial.X 0 + MvPolynomial.C (3 : ℕ)), ?_⟩
  intro sizes initial candidate candidateValue candidateEq headers regions canonical
  let localInput : Inputs
      (StandardBinaryScan.domains (EncodedDomain.binaryNaturals (0 : Fin 3))
        (EncodedDomain.binaryNaturals 0)) StandardTerminatedCopy.readOnly sizes :=
    fun name => by
      rcases name with ⟨name, readonly⟩
      cases name with
      | inl parameter => exact PUnit.unit
      | inr name => cases name with
        | false => exact candidate
        | true => contradiction
  obtain ⟨incrementTicks, incrementOutput, incremented, incrementCost,
      incrementTrace, incrementCorrect, incrementCanonical, incrementOutside,
      incrementImmutable⟩ :=
    executeIncrement sizes localInput
      (fun name => (domains scalar name).width sizes) readOnly initial
      (by
        intro name
        cases name with
        | inl parameter => rfl
        | inr name => cases name <;> rfl)
      (by
        intro name premise
        cases name with
        | inl parameter => rfl
        | inr name => cases name with
          | false => cases premise
          | true => cases premise)
      trivial
      (by
        intro name readonly
        cases name with
        | inl parameter =>
          change initial (sizeTape parameter) =
            encoded (EncodedDomain.unary parameter) sizes PUnit.unit
          rw [encoded_unary]
          exact headers parameter
        | inr name => cases name with
          | false => exact candidateEq
          | true => contradiction)
      (by
        intro name writable
        cases name with
        | inl parameter => cases writable
        | inr name => cases name with
          | false => cases writable
          | true => exact regions nextTape)
      headers
  have incrementValue : StandardBinaryIncrement.next 0 sizes candidate =
      (⟨candidate.val + 1, candidateValue⟩ : Fin (2 ^ sizes 0)) := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt candidateValue
  have resultEq : incremented nextTape =
      encoded (EncodedDomain.binaryNaturals 0) sizes
        (⟨candidate.val + 1, candidateValue⟩ : Fin (2 ^ sizes 0)) := by
    have valid := incrementCanonical (.inr true) rfl
    change incrementOutput ⟨.inr true, rfl⟩ =
      StandardBinaryIncrement.next 0 sizes candidate at incrementCorrect
    rw [incrementCorrect, incrementValue] at valid
    exact valid
  have copyTrace := StandardTapeCommands.copy_encoded_runs
    (EncodedDomain.binaryNaturals 0) sizes
    (⟨candidate.val + 1, candidateValue⟩ : Fin (2 ^ sizes 0))
    nextTape (counterTape 1) (by decide)
    (fun name => (domains scalar name).width sizes) readOnly
    (by rfl) (by rfl) (by rfl) incremented resultEq
    (incrementTrace.region (counterTape 1) (regions (counterTape 1)))
  let finalTapes := Function.update incremented (counterTape 1)
    (encoded (EncodedDomain.binaryNaturals 0) sizes
      (⟨candidate.val + 1, candidateValue⟩ : Fin (2 ^ sizes 0)))
  have incrementPreserves : ∀ name, name ≠ nextTape → incremented name = initial name := by
    intro name notNext
    apply preserved_of_wiring incrementWiring StandardTerminatedCopy.readOnly
      initial incremented incrementOutside incrementImmutable name
    intro localName equal
    cases localName with
    | inl parameter => rfl
    | inr localName => cases localName with
      | false => rfl
      | true => exact False.elim (notNext (by simpa [incrementWiring, nextTape] using equal.symm))
  refine ⟨incrementTicks + (2 * sizes 0 + 2) + 1, finalTapes, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [map_add, map_mul, map_ofNat, MvPolynomial.eval_C, MvPolynomial.eval_X]
    omega
  · have joined := incrementTrace.sequence
      (StandardTapeCommands.copy nextTape (counterTape 1) (by decide)) 0
      (by intro symbols; rfl) copyTrace
    simpa [advance, increment, copyNext, advanceEntry, advanceExit, finalTapes,
      EncodedDomain.binaryNaturals] using joined
  · change finalTapes (counterTape 1) = _
    simp [finalTapes, Function.update_self]
  · intro name writable
    by_cases isCandidate : name = counterTape 1
    · subst name
      exact ⟨⟨candidate.val + 1, candidateValue⟩, by
        simp [domains, counterTape, StandardMatrixEntry.domains,
          StandardMatrixAddress.domains, finalTapes]⟩
    · by_cases isNext : name = nextTape
      · subst name
        have finalNext : finalTapes nextTape = incremented nextTape := by
          simp [finalTapes, nextTape, counterTape]
        exact ⟨⟨candidate.val + 1, candidateValue⟩, by
          simpa [domains, nextTape] using finalNext.trans resultEq⟩
      · obtain ⟨value, valid⟩ := canonical name writable
        have afterCopy : finalTapes name = incremented name := by
          simp [finalTapes, Function.update_of_ne isCandidate]
        exact ⟨value, afterCopy.trans ((incrementPreserves name isNext).trans valid)⟩
  · intro name notCandidate notNext
    have afterCopy : finalTapes name = incremented name := by
      simp [finalTapes, Function.update_of_ne notCandidate]
    exact afterCopy.trans (incrementPreserves name notNext)

end Polytime2.StandardPivotSearch
