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

import Polytime2.StandardSizeRead

/-! # Encoded-domain contract for unary size reading -/

namespace Polytime2.StandardSizeRead

open MultiTape CallingConvention
open Binary (word)

noncomputable def domains : Sum Bool Bool → EncodedDomain Bool
  | .inl parameter => EncodedDomain.unary parameter
  | .inr _ => EncodedDomain.binaryNaturals true

def argumentReadOnly : Sum Bool Bool → Bool
  | .inl _ => true
  | .inr _ => false

def sizeTapes : Bool ↪ Sum Bool Bool :=
  ⟨Sum.inl, by intro first second equal; cases equal; rfl⟩

def wiring : Fin 4 ↪ Sum Bool Bool :=
  ⟨(fun name => match name.val with
    | 0 => .inl false | 1 => .inl true | 2 => .inr false | _ => .inr true), by
    intro first second equal
    fin_cases first <;> fin_cases second <;> simp_all⟩

noncomputable def algorithm : Machine (CallingConvention.Alphabet (Sum Bool Bool)) State :=
  MultiTape.wire wiring machine

/-- Concrete execution evidence for internal controller proofs. The physical
scratch word is recorded here; it is not a public output or validity obligation. -/
theorem Internal.runs_wired {TargetTape : Type} [Fintype TargetTape]
    (targetWiring : Sum Bool Bool ↪ TargetTape) (assignment : Bool → ℕ)
    (width : TargetTape → ℕ) (targetReadOnly : TargetTape → Bool)
    (initial : Tapes (CallingConvention.Alphabet TargetTape))
    (widthsMatch : ∀ name, width (targetWiring name) = (domains name).width assignment)
    (readOnlyMatch : ∀ name, targetReadOnly (targetWiring name) = true → argumentReadOnly name = true)
    (headers : ∀ parameter, initial (targetWiring (.inl parameter)) = unary (assignment parameter))
    (resultRegion : Region (assignment true) 0 (initial (targetWiring (.inr false))))
    (scratchRegion : Region (assignment true) 0 (initial (targetWiring (.inr true)))) :
    ∃ scratch : List Bool, scratch.length = assignment true ∧ ∃ final,
      Runs width targetReadOnly (MultiTape.wire targetWiring algorithm)
        (4 * assignment true + assignment false * (4 * assignment true + 8) + 11)
        entry (fun _ => 0) initial exit (fun _ => 0) final ∧
      final (targetWiring (.inr false)) = buffer
        (word (advanceBits (assignment false) (List.replicate (assignment true) false))) ∧
      final (targetWiring (.inr true)) = buffer (word scratch) ∧
      (∀ name, name ∉ Set.range targetWiring → final name = initial name) ∧
      (∀ name, argumentReadOnly name = true →
        final (targetWiring name) = initial (targetWiring name)) := by
  obtain ⟨oldResult, resultLength, resultEq⟩ := resultRegion.exists_buffer
  obtain ⟨oldScratch, scratchLength, scratchEq⟩ := scratchRegion.exists_buffer
  obtain ⟨scratch, scratchLength, rawTrace⟩ := runs (assignment false) (assignment true)
    oldResult oldScratch resultLength scratchLength
  let localInitial := fun name => initial (targetWiring name)
  have trace := rawTrace.wire wiring (fun name => (domains name).width assignment)
    argumentReadOnly (by
      intro name
      fin_cases name
      · change (domains (.inl false)).width assignment = _
        simp [domains, widths, EncodedDomain.unary, EncodedDomain.ofCodec]
      · change (domains (.inl true)).width assignment = _
        simp [domains, widths, EncodedDomain.unary, EncodedDomain.ofCodec]
      · change (domains (.inr false)).width assignment = _
        simp [domains, widths, EncodedDomain.binaryNaturals, EncodedDomain.ofCodec]
      · change (domains (.inr true)).width assignment = _
        simp [domains, widths, EncodedDomain.binaryNaturals, EncodedDomain.ofCodec])
    (by intro name premise; fin_cases name <;> exact premise) localInitial (fun _ => 0)
  have initialMatches : (fun name => localInitial (wiring name)) =
      entryFrame (assignment false) (assignment true) oldResult oldScratch := by
    funext name
    fin_cases name
    · exact headers false
    · exact headers true
    · exact resultEq
    · exact scratchEq
  have start : install wiring (entryFrame (assignment false) (assignment true) oldResult oldScratch)
      localInitial = localInitial := by rw [← initialMatches, install_self]
  have positions : install wiring (fun _ : Fin 4 => (0 : ℤ))
      (fun _ : Sum Bool Bool => (0 : ℤ)) = fun _ => 0 := install_self _ _
  rw [start, positions] at trace
  have complete := trace.wire targetWiring width targetReadOnly widthsMatch readOnlyMatch initial (fun _ => 0)
  rw [show install targetWiring localInitial initial = initial from install_self _ _,
    show install targetWiring (fun _ => (0 : ℤ)) (fun _ => (0 : ℤ)) = fun _ => 0 from install_self _ _] at complete
  refine ⟨scratch, scratchLength, _, complete, ?_, ?_, ?_, ?_⟩
  · rw [install_at]
    change install wiring _ localInitial (wiring 2) = _
    rw [install_at]
    rfl
  · rw [install_at]
    change install wiring _ localInitial (wiring 3) = _
    rw [install_at]
    rfl
  · intro name outside
    exact install_outside _ _ _ _ outside
  · intro name immutable
    rw [install_at]
    exact trace.readOnly_tape name immutable

def outputTapes : Unit ↪ Sum Bool Bool := oneTape (.inr false)

/-- A size can be read as an ordinary natural whenever it fits the declared
binary capacity. Both unary sizes remain unchanged; only the result is exposed. -/
theorem contract : CallingConvention.Realizes domains argumentReadOnly sizeTapes outputTapes algorithm entry exit
    (fun assignment _ => assignment false < 2 ^ assignment true)
    (fun assignment _ output => (output ()).val = assignment false) := by
  refine ⟨(by intro parameter; rfl), (by intro name; rfl), (by intro symbols; simp [algorithm, MultiTape.wire]),
    4 * MvPolynomial.X true + MvPolynomial.X false * (4 * MvPolynomial.X true + 8) + 11, ?_⟩
  intro assignment input initial valid represented sizes
  obtain ⟨oldResult, resultLength, resultEq⟩ := represented.2 (.inr false) rfl
  obtain ⟨oldScratch, scratchLength, scratchEq⟩ := represented.2 (.inr true) rfl
  simp [domains, EncodedDomain.binaryNaturals, EncodedDomain.ofCodec] at resultLength scratchLength
  obtain ⟨finalScratch, finalLength, localTrace⟩ := runs (assignment false) (assignment true)
    oldResult oldScratch resultLength scratchLength
  let result := advanceBits (assignment false) (List.replicate (assignment true) false)
  have resultLength : result.length = assignment true := by simp [result]
  have resultValue : Binary.value result = assignment false := by
    simp [result, advanceBits_value, Nat.mod_eq_of_lt valid]
  have resultBound : Binary.value result < 2 ^ assignment true :=
    resultValue.symm ▸ valid
  let resultNatural : Fin (2 ^ assignment true) := ⟨Binary.value result, resultBound⟩
  let localFinal := entryFrame (assignment false) (assignment true) (word result) (word finalScratch)
  have trace := localTrace.wire wiring
    (fun name => (domains name).width assignment) argumentReadOnly
    (by
      intro name
      fin_cases name
      · change (domains (.inl false)).width assignment = _
        simp [domains, widths, EncodedDomain.unary, EncodedDomain.ofCodec]
      · change (domains (.inl true)).width assignment = _
        simp [domains, widths, EncodedDomain.unary, EncodedDomain.ofCodec]
      · change (domains (.inr false)).width assignment = _
        simp [domains, widths, EncodedDomain.binaryNaturals, EncodedDomain.ofCodec]
      · change (domains (.inr true)).width assignment = _
        simp [domains, widths, EncodedDomain.binaryNaturals, EncodedDomain.ofCodec])
    (by intro name premise; fin_cases name <;> exact premise) initial (fun _ => 0)
  have initialMatches : (fun name => initial (wiring name)) =
      entryFrame (assignment false) (assignment true) oldResult oldScratch := by
    funext name
    fin_cases name
    · exact sizes false
    · exact sizes true
    · exact resultEq
    · exact scratchEq
  have start : install wiring (entryFrame (assignment false) (assignment true) oldResult oldScratch) initial = initial := by
    rw [← initialMatches, install_self]
  have positions : install wiring (fun _ : Fin 4 => (0 : ℤ)) (fun _ : Sum Bool Bool => (0 : ℤ)) =
      fun _ => 0 := install_self _ _
  rw [start, positions] at trace
  let output : Outputs domains outputTapes assignment := fun _ => resultNatural
  refine ⟨_, output, _, ?_, trace, resultValue, ?_⟩
  · simp
  · intro name
    cases name
    change install wiring _ initial (wiring 2) = _
    rw [install_at]
    exact (encoded_binaryNaturals true assignment result resultLength).symm

end Polytime2.StandardSizeRead
