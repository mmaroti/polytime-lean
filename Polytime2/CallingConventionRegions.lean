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

import Polytime2.CallingConvention

/-! # Arbitrary writable regions at internal call boundaries

Fixed-region preservation supplies the writable-buffer entry condition for
matrix row subroutine calls, independently of previous scratch contents.
-/

namespace Polytime2.CallingConvention

open MultiTape
open Binary (Symbol word)

private theorem tape_eq_of_nth (first second : Turing.Tape Symbol)
    (agreement : ∀ index : ℤ, first.nth index = second.nth index) : first = second := by
  cases first with
  | mk firstHead firstLeft firstRight =>
    cases second with
    | mk secondHead secondLeft secondRight =>
      have headEq : firstHead = secondHead := agreement 0
      have leftEq : firstLeft = secondLeft := Turing.ListBlank.ext (fun index => agreement (.negSucc index))
      have rightEq : firstRight = secondRight := Turing.ListBlank.ext (fun index => agreement (index + 1 : ℕ))
      cases headEq
      cases leftEq
      cases rightEq
      rfl

/-- An arbitrary buffer has blank surroundings, even with interior blanks. -/
theorem buffer_region (contents : List Symbol) : Region contents.length 0 (buffer contents) := by
  intro index outside
  rw [sub_zero]
  cases index with
  | ofNat index =>
    simp only [Int.ofNat_eq_natCast] at outside
    simp only [Int.ofNat_eq_natCast, buffer, Turing.Tape.mk₁, Turing.Tape.mk₂, Turing.Tape.mk'_nth_nat,
      Turing.ListBlank.nth_mk]
    exact List.getI_eq_default contents (by omega)
  | negSucc index =>
    rfl

/-- A head at the start of any fixed blank-surrounded region is an admissible
arbitrary writable buffer. Its interior need not encode a valid value yet. -/
theorem Region.exists_buffer {width : ℕ} {tape : Turing.Tape Symbol}
    (region : Region width 0 tape) :
    ∃ contents : List Symbol, contents.length = width ∧ tape = buffer contents := by
  let contents := List.ofFn (fun index : Fin width => tape.nth index.val)
  refine ⟨contents, List.length_ofFn, ?_⟩
  apply tape_eq_of_nth
  intro index
  cases index with
  | ofNat index =>
    change tape.nth (index : ℤ) = (Turing.Tape.mk₁ contents).nth (index : ℤ)
    simp only [Turing.Tape.mk₁, Turing.Tape.mk₂, Turing.Tape.mk'_nth_nat,
      Turing.ListBlank.nth_mk]
    by_cases inside : index < width
    · have length : index < contents.length := by simpa only [contents, List.length_ofFn] using inside
      rw [List.getI_eq_getElem contents length]
      simp [contents]
    · rw [List.getI_eq_default contents (by simpa only [contents, List.length_ofFn] using Nat.le_of_not_gt inside)]
      change tape.nth (index : ℤ) = 0
      simpa only [sub_zero] using region (index : ℤ) (Or.inr (by omega))
  | negSucc index =>
    have outside := region (.negSucc index) (Or.inl (by omega))
    change tape.nth (.negSucc index) = 0
    simpa only [sub_zero] using outside

-- parameterLevel: size names; carrierLevel: mathematical argument values;
-- tapeLevel: the finite catalogue of argument and scratch tapes.
universe parameterLevel carrierLevel tapeLevel
variable {Parameter : Type parameterLevel} [Fintype Parameter] {TapeName : Type tapeLevel}

/-- Every canonical value has exactly the declared blank-surrounded region. -/
theorem encoded_region (domain : EncodedDomain.{parameterLevel, carrierLevel} Parameter)
    (sizes : Parameter → ℕ) (value : domain.Carrier sizes) :
    Region (domain.width sizes) 0 (encoded domain sizes value) := by
  change Region _ 0 (buffer (word (List.ofFn (fun index : Fin (domain.width sizes) =>
    (domain.encode sizes value).getLsbD index.val))))
  convert buffer_region _ using 1 <;> simp [word]

/-- Every public entry supplies the fixed blank surroundings needed by all
subsequent internal writable calls. -/
theorem Entry.region {domains : TapeName → EncodedDomain.{parameterLevel, carrierLevel} Parameter}
    {readOnly : TapeName → Bool} {sizes : Parameter → ℕ}
    {input : Inputs domains readOnly sizes} {tapes : Tapes (Alphabet TapeName)}
    (entry : Entry domains readOnly sizes input tapes) (name : TapeName) :
    Region ((domains name).width sizes) 0 (tapes name) := by
  cases selected : readOnly name with
  | false =>
    obtain ⟨contents, length, sameTape⟩ := entry.2 name selected
    rw [sameTape, ← length]
    exact buffer_region contents
  | true =>
    rw [entry.1 name selected]
    exact encoded_region _ _ _

-- localTapeLevel: a subroutine's tapes; stateLevel: its finite controller.
universe localTapeLevel stateLevel
variable {LocalTape : Type localTapeLevel} [Fintype LocalTape]
variable {State : Type stateLevel} [Fintype State]

/-- A caller's tape is preserved when every local role that can name it is
read-only. This also covers tapes absent from the subroutine's wiring. -/
theorem preserved_of_wiring (wiring : LocalTape ↪ TapeName) (readOnly : LocalTape → Bool)
    (initial final : Tapes (Alphabet TapeName))
    (outside : ∀ name, name ∉ Set.range wiring → final name = initial name)
    (immutable : ∀ name, readOnly name = true → final (wiring name) = initial (wiring name))
    (name : TapeName) (unchanged : ∀ localName, wiring localName = name → readOnly localName = true) :
    final name = initial name := by
  classical
  by_cases located : name ∈ Set.range wiring
  · obtain ⟨localName, rfl⟩ := located
    exact immutable localName (unchanged localName rfl)
  · exact outside name located

/-- Call a certified routine inside a larger tape collection. Read-only inputs
must already be encoded; writable entry buffers follow from fixed-region
preservation, so callers need not track their previous contents. -/
theorem Realizes.wired_runs
    {domains : LocalTape → EncodedDomain.{parameterLevel, carrierLevel} Parameter}
    {localReadOnly : LocalTape → Bool} {sizeTapes : Parameter ↪ LocalTape}
    {machine : Machine (Alphabet LocalTape) State} {entry exit : State}
    {hypothesis : ∀ sizes, Inputs domains localReadOnly sizes → Prop}
    {postcondition : ∀ sizes, Inputs domains localReadOnly sizes → Outputs domains localReadOnly sizes → Prop}
    (realizes : Realizes domains localReadOnly sizeTapes machine entry exit hypothesis postcondition)
    (wiring : LocalTape ↪ TapeName) :
    ∃ bound : MvPolynomial Parameter ℕ,
      ∀ (sizes : Parameter → ℕ) (input : Inputs domains localReadOnly sizes)
        (width : TapeName → ℕ) (readOnly : TapeName → Bool) (initial : Tapes (Alphabet TapeName)),
        (∀ name, width (wiring name) = (domains name).width sizes) →
        (∀ name, readOnly (wiring name) = true → localReadOnly name = true) →
        hypothesis sizes input →
        (∀ name (readonly : localReadOnly name = true),
          initial (wiring name) = encoded (domains name) sizes (input ⟨name, readonly⟩)) →
        (∀ name, localReadOnly name = false → Region (width (wiring name)) 0 (initial (wiring name))) →
        (∀ parameter, initial (wiring (sizeTapes parameter)) = unary (sizes parameter)) →
        ∃ ticks output final,
          ticks ≤ MvPolynomial.eval sizes bound ∧
          Runs width readOnly (MultiTape.wire wiring machine) ticks entry (fun _ => 0) initial exit (fun _ => 0) final ∧
          postcondition sizes input output ∧
          (∀ name (writable : localReadOnly name = false),
            final (wiring name) = encoded (domains name) sizes (output ⟨name, writable⟩)) ∧
          (∀ name, name ∉ Set.range wiring → final name = initial name) ∧
          (∀ name, localReadOnly name = true → final (wiring name) = initial (wiring name)) := by
  obtain ⟨sizeReadOnly, halts, bound, execute⟩ := realizes
  refine ⟨bound, ?_⟩
  intro sizes input width readOnly initial widthMatches readOnlyMatches valid encodedInputs regions sizeHeaders
  let localInitial : Tapes (Alphabet LocalTape) := fun name => initial (wiring name)
  have localEntry : Entry domains localReadOnly sizes input localInitial := by
    refine ⟨encodedInputs, ?_⟩
    intro name writable
    obtain ⟨contents, length, sameTape⟩ := (regions name writable).exists_buffer
    exact ⟨contents, length.trans (widthMatches name), sameTape⟩
  obtain ⟨ticks, output, localFinal, cost, localTrace, correct, localExit⟩ :=
    execute sizes input localInitial valid localEntry sizeHeaders
  have trace := localTrace.wire wiring width readOnly widthMatches readOnlyMatches initial (fun _ => 0)
  have initialEq : install wiring localInitial initial = initial := install_self wiring initial
  have positions : install wiring (fun _ : LocalTape => (0 : ℤ)) (fun _ : TapeName => (0 : ℤ)) =
      fun _ => 0 := install_self wiring _
  rw [initialEq, positions] at trace
  refine ⟨ticks, output, install wiring localFinal initial, cost, trace, correct, ?_, ?_, ?_⟩
  · intro name writable
    rw [install_at]
    exact localExit name writable
  · intro name outside
    exact install_outside wiring localFinal initial name outside
  · intro name immutable
    rw [install_at]
    exact localTrace.readOnly_tape name immutable

end Polytime2.CallingConvention
