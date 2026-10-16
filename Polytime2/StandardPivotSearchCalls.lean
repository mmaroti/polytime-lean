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

import Polytime2.StandardPivotSearch

/-! # Certified bound and scalar tests in the pivot-search workspace -/

namespace Polytime2.StandardPivotSearch

open MultiTape CallingConvention

/-- The immutable unary row count formats its private binary limit and scratch.
No execution-time width computation or prefilled output word is required. -/
theorem readLimit_runs (scalar : EncodedDomain.{0, 0} Empty) :
    ∃ bound : MvPolynomial (Fin 3) ℕ, ∀ (sizes : Fin 3 → ℕ) (initial : Tapes Alphabet)
      (fits : sizes 1 < 2 ^ sizes 0),
      (∀ parameter, initial (sizeTape parameter) = unary (sizes parameter)) →
      Region (sizes 0) 0 (initial rowLimitTape) → Region (sizes 0) 0 (initial (counterTape 2)) →
      ∃ ticks final, ticks ≤ MvPolynomial.eval sizes bound ∧
        Runs (fun name => (domains scalar name).width sizes) readOnly readLimit ticks
          StandardSizeRead.entry (fun _ => 0) initial StandardSizeRead.exit (fun _ => 0) final ∧
        final rowLimitTape = encoded (EncodedDomain.binaryNaturals 0) sizes ⟨sizes 1, fits⟩ ∧
        (∃ value : Fin (2 ^ sizes 0), final (counterTape 2) = encoded (EncodedDomain.binaryNaturals 0) sizes value) ∧
        (∀ name, name ≠ rowLimitTape → name ≠ counterTape 2 → final name = initial name) := by
  refine ⟨4 * MvPolynomial.X 0 + MvPolynomial.X 1 * (4 * MvPolynomial.X 0 + 8) + 11, ?_⟩
  intro sizes initial fits headers limitRegion scratchRegion
  let localSizes : Bool → ℕ := fun name => if name then sizes 0 else sizes 1
  obtain ⟨scratch, scratchLength, final, trace, resultEq, scratchEq, outside, immutable⟩ :=
    StandardSizeRead.Internal.runs_wired limitWiring localSizes
      (fun name => (domains scalar name).width sizes) readOnly initial
      (by intro name; fin_cases name <;> rfl)
      (by intro name premise; fin_cases name <;> first | rfl | contradiction)
      (by intro name; cases name <;> exact headers _) limitRegion scratchRegion
  let resultBits := StandardSizeRead.advanceBits (sizes 1) (List.replicate (sizes 0) false)
  have resultLength : resultBits.length = sizes 0 := by simp [resultBits]
  have resultValue : Binary.value resultBits = sizes 1 := by
    simp [resultBits, StandardSizeRead.advanceBits_value, Nat.mod_eq_of_lt fits]
  have resultEncoding := encoded_binaryNaturals (0 : Fin 3) sizes resultBits resultLength
  have naturalEq : (⟨Binary.value resultBits, by
      simpa only [resultLength] using Binary.value_lt_pow_length resultBits⟩ : Fin (2 ^ sizes 0)) =
      ⟨sizes 1, fits⟩ := Fin.ext resultValue
  rw [naturalEq] at resultEncoding
  let scratchValue : Fin (2 ^ sizes 0) := ⟨Binary.value scratch, by
    simpa only [show scratch.length = sizes 0 from scratchLength] using Binary.value_lt_pow_length scratch⟩
  refine ⟨_, final, ?_, trace, resultEq.trans resultEncoding.symm,
    ⟨scratchValue, scratchEq.trans (encoded_binaryNaturals 0 sizes scratch scratchLength).symm⟩, ?_⟩
  · simp [localSizes]
  · intro name notLimit notScratch
    apply preserved_of_wiring limitWiring StandardSizeRead.argumentReadOnly initial final outside immutable
    intro localName equal
    cases localName with
    | inl parameter => rfl
    | inr name => cases name with
      | false => exact False.elim (notLimit equal.symm)
      | true => exact False.elim (notScratch equal.symm)

theorem compare_runs (scalar : EncodedDomain.{0, 0} Empty) :
    ∃ bound : MvPolynomial (Fin 3) ℕ, ∀ (sizes : Fin 3 → ℕ) (initial : Tapes Alphabet)
      (candidate limit : Fin (2 ^ sizes 0)),
      initial (sizeTape 0) = unary (sizes 0) →
      initial (counterTape 1) = encoded (EncodedDomain.binaryNaturals 0) sizes candidate →
      initial rowLimitTape = encoded (EncodedDomain.binaryNaturals 0) sizes limit →
      Region (sizes 0) 0 (initial differenceTape) → Region 1 0 (initial foundTape) →
      ∃ ticks final, ticks ≤ MvPolynomial.eval sizes bound ∧
        Runs (fun name => (domains scalar name).width sizes) readOnly compare ticks
          BinarySubtraction.entry (fun _ => 0) initial BinarySubtraction.exit (fun _ => 0) final ∧
        final foundTape = encoded EncodedDomain.booleans sizes (decide (candidate.val < limit.val)) ∧
        (∃ value : Fin (2 ^ sizes 0), final differenceTape = encoded (EncodedDomain.binaryNaturals 0) sizes value) ∧
        (∀ name, name ≠ differenceTape → name ≠ foundTape → final name = initial name) := by
  obtain ⟨bound, execute⟩ := BinarySubtraction.comparison_contract.wired_runs comparisonWiring
  refine ⟨MvPolynomial.rename (fun _ : Unit => (0 : Fin 3)) bound, ?_⟩
  intro sizes initial candidate limit header candidateEq limitEq differenceRegion foundRegion
  let localSizes : Unit → ℕ := fun _ => sizes 0
  let input : Inputs BinarySubtraction.domains BinarySubtraction.argumentReadOnly localSizes := fun name => by
    rcases name with ⟨name, readonly⟩
    cases name with
    | inl parameter => exact PUnit.unit
    | inr name =>
      by_cases first : name = 0
      · subst name; exact candidate
      · by_cases second : name = 1
        · subst name; exact limit
        · have writable : BinarySubtraction.argumentReadOnly (.inr name) = false := by
            fin_cases name <;> first | rfl | contradiction
          rw [writable] at readonly
          contradiction
  obtain ⟨ticks, output, final, cost, trace, correct, canonical, outside, immutable⟩ :=
    execute localSizes input (fun name => (domains scalar name).width sizes) readOnly initial
      (by intro name; fin_cases name <;> rfl)
      (by intro name premise; fin_cases name <;> first | rfl | contradiction)
      trivial
      (by
        intro name readonly
        fin_cases name
        · change initial (sizeTape 0) = encoded (EncodedDomain.unary ()) localSizes PUnit.unit
          rw [encoded_unary]
          exact header
        · exact candidateEq
        · exact limitEq
        · contradiction
        · contradiction)
      (by intro name writable; fin_cases name <;> first | contradiction | exact differenceRegion | exact foundRegion)
      (by intro parameter; cases parameter; exact header)
  refine ⟨ticks, final, ?_, trace, ?_, ⟨output false, canonical false⟩, ?_⟩
  · simpa only [MvPolynomial.eval_rename, localSizes, Function.comp_def] using cost
  · have flag := canonical true
    change output true = decide (candidate.val < limit.val) at correct
    rw [correct] at flag
    exact flag
  · intro name notDifference notFound
    apply preserved_of_wiring comparisonWiring BinarySubtraction.argumentReadOnly initial final outside immutable
    intro localName equal
    fin_cases localName
    · rfl
    · rfl
    · rfl
    · exact False.elim (notDifference equal.symm)
    · exact False.elim (notFound equal.symm)

/-- The finite scalar test changes only the continue bit. Its private singleton
tape remains blank and valid, and the scalar argument is preserved throughout. -/
theorem zeroTest_runs (scalar : EncodedDomain.{0, 0} Empty)
    (isZero : ∀ assignment, scalar.Carrier assignment → Bool) :
    ∃ bound : ℕ, ∀ (sizes : Fin 3 → ℕ) (initial : Tapes Alphabet)
      (value : scalar.Carrier Empty.elim),
      initial elementTape = encoded scalar Empty.elim value →
      Region 0 0 (initial unitTape) → Region 1 0 (initial continueTape) →
      ∃ ticks final, ticks ≤ bound ∧
        Runs (fun name => (domains scalar name).width sizes) readOnly (zeroTest scalar isZero) ticks
          StandardFiniteTable.entry (fun _ => 0) initial StandardFiniteTable.exit (fun _ => 0) final ∧
        final continueTape = encoded EncodedDomain.booleans sizes (isZero Empty.elim value) ∧
        (∀ name, name ≠ continueTape → final name = initial name) := by
  obtain ⟨bound, execute⟩ := (StandardFinitePredicate.contract scalar isZero).wired_runs testWiring
  refine ⟨MvPolynomial.eval Empty.elim bound, ?_⟩
  intro sizes initial value scalarEq unitRegion continueRegion
  obtain ⟨oldUnit, unitLength, unitEq⟩ := unitRegion.exists_buffer
  have empty : oldUnit = [] := List.eq_nil_of_length_eq_zero unitLength
  subst oldUnit
  let input : Inputs (StandardFinitePredicate.domains scalar) StandardFinitePredicate.readOnly Empty.elim := fun name => by
    rcases name with ⟨name, readonly⟩
    have argument : name = 0 := of_decide_eq_true readonly
    subst name
    exact value
  obtain ⟨ticks, output, final, cost, trace, correct, canonical, outside, immutable⟩ :=
    execute Empty.elim input (fun name => (domains scalar name).width sizes) readOnly initial
      (by intro name; fin_cases name <;> rfl)
      (by intro name premise; fin_cases name <;> contradiction)
      trivial
      (by intro name readonly; fin_cases name <;> first | exact scalarEq | contradiction)
      (by intro name writable; fin_cases name <;> first | contradiction | exact unitRegion | exact continueRegion)
      (by intro parameter; cases parameter)
  have unitFinal : final unitTape = initial unitTape := by
    obtain ⟨contents, length, finalEq⟩ := (trace.region unitTape unitRegion).exists_buffer
    have empty : contents = [] := List.eq_nil_of_length_eq_zero length
    subst contents
    exact finalEq.trans unitEq.symm
  refine ⟨ticks, final, cost, trace, ?_, ?_⟩
  · have result := canonical ()
    change output () = isZero Empty.elim value at correct
    exact result.trans (congrArg (encoded EncodedDomain.booleans Empty.elim) correct)
  · intro name notContinue
    by_cases isUnit : name = unitTape
    · subst name
      exact unitFinal
    · apply preserved_of_wiring testWiring StandardFinitePredicate.readOnly initial final outside immutable
      intro localName equal
      fin_cases localName
      · rfl
      · exact False.elim (isUnit equal.symm)
      · exact False.elim (notContinue equal.symm)

/-- Lookup preserves the candidate and all comparison tapes. Its scalar output
and every arithmetic scratch word are canonical before the finite zero test. -/
theorem readEntry_runs (scalar : EncodedDomain.{0, 0} Empty) :
    ∃ bound : MvPolynomial (Fin 3) ℕ, ∀ (sizes : Fin 3 → ℕ) (initial : Tapes Alphabet)
      (candidate column : Fin (2 ^ sizes 0))
      (array : (scalar.constant.arrayOfLength StandardMatrixEntry.length).Carrier sizes)
      (within : candidate.val * sizes 2 + column.val < MvPolynomial.eval sizes StandardMatrixEntry.length),
      sizes 2 < 2 ^ sizes 0 → candidate.val < sizes 1 → column.val < sizes 2 → sizes 1 * sizes 2 ≤ 2 ^ sizes 0 →
      initial (counterTape 1) = encoded (EncodedDomain.binaryNaturals 0) sizes candidate →
      initial (counterTape 6) = encoded (EncodedDomain.binaryNaturals 0) sizes column →
      initial matrixTape = encoded (scalar.constant.arrayOfLength StandardMatrixEntry.length) sizes array →
      (∀ parameter, initial (sizeTape parameter) = unary (sizes parameter)) →
      (∀ name, Region ((domains scalar name).width sizes) 0 (initial name)) →
      ∃ ticks final, ticks ≤ MvPolynomial.eval sizes bound ∧
        Runs (fun name => (domains scalar name).width sizes) readOnly (readEntry (scalar.width Empty.elim)) ticks
          (StandardMatrixEntry.entry (scalar.width Empty.elim)) (fun _ => 0) initial
          (StandardMatrixEntry.exit (scalar.width Empty.elim)) (fun _ => 0) final ∧
        final elementTape = encoded scalar Empty.elim (array ⟨candidate.val * sizes 2 + column.val, within⟩) ∧
        final (counterTape 1) = encoded (EncodedDomain.binaryNaturals 0) sizes candidate ∧
        (∀ name, StandardMatrixEntry.readOnly name = false → ∃ value : (domains scalar (.inl name)).Carrier sizes,
          final (.inl name) = encoded (domains scalar (.inl name)) sizes value) ∧
        (∀ name : Fin 7, final (.inr name) = initial (.inr name)) := by
  obtain ⟨bound, execute⟩ := StandardMatrixEntry.Internal.wired_runs scalar.constant (scalar.width Empty.elim) (fun _ => rfl)
    (Function.Embedding.inl (α := StandardMatrixEntry.TapeName) (β := Fin 7))
  refine ⟨bound, ?_⟩
  intro sizes initial candidate column array within columnsFit candidateValid columnValid capacity candidateEq columnEq arrayEq headers regions
  let input := StandardMatrixEntry.inputValues scalar.constant sizes candidate column array
  obtain ⟨ticks, output, final, cost, trace, correct, canonical, privateFrame, outside, immutable⟩ :=
    execute sizes input (fun name => (domains scalar name).width sizes) readOnly initial
      (fun _ => rfl)
      (by intro name premise; fin_cases name <;> first | rfl | contradiction)
      ⟨columnsFit, candidateValid, columnValid, capacity⟩
      (by
        intro name readonly
        cases name with
        | inl name => cases name with
          | inl parameter =>
            change initial (sizeTape parameter) = encoded (EncodedDomain.unary parameter) sizes PUnit.unit
            rw [encoded_unary]
            exact headers parameter
          | inr name =>
            by_cases isCandidate : name = 1
            · subst name; exact candidateEq
            · by_cases isColumn : name = 6
              · subst name; exact columnEq
              · have impossible : StandardMatrixEntry.readOnly (.inl (.inr name)) = false := by
                  simp [StandardMatrixEntry.readOnly, StandardMatrixAddress.readOnly, isCandidate, isColumn]
                rw [impossible] at readonly
                contradiction
        | inr name => cases name with
          | false => exact arrayEq
          | true => contradiction)
      (by intro name writable; exact regions (.inl name)) headers
  obtain ⟨otherWithin, valueEq⟩ := correct
  change output () = array ⟨candidate.val * sizes 2 + column.val, otherWithin⟩ at valueEq
  refine ⟨ticks, final, cost, trace, ?_, (immutable (.inl (.inr 1)) rfl).trans candidateEq, ?_, ?_⟩
  · have result := canonical ()
    rw [valueEq] at result
    exact result
  · intro name writable
    exact privateFrame name writable
  · intro name
    apply outside (.inr name)
    rintro ⟨localName, equal⟩
    cases equal

end Polytime2.StandardPivotSearch
