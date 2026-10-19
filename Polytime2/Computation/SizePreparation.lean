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

import Polytime2.Computation.UnaryPreparation
import Polytime2.Machine.Pipeline

/-! # Preparing an arbitrary finite family of computed size tapes

Each size is produced by a certified computation on shared immutable arguments.
A fixed pipeline prepares all raw headers inside a polynomial private capacity.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation.Realizable.Internal

open MultiTape CallingConvention

variable {Parameter InputName NewParameter : Type}
variable [Fintype Parameter] [Fintype InputName] [Fintype NewParameter]

abbrev SizePreparationTape (Parameter InputName NewParameter : Type) (Scratch : NewParameter → Type) :=
  Parameter ⊕ (InputName ⊕ (Σ parameter, Unit ⊕ Scratch parameter))

/-- Shared arguments keep their canonical widths; each private block has the
same larger capacity. -/
noncomputable def sizePreparationWidths (inputs : InputName → EncodedDomain Parameter)
    (Scratch : NewParameter → Type) (sizes : Parameter → ℕ) (capacity : ℕ) :
    SizePreparationTape Parameter InputName NewParameter Scratch → ℕ
  | .inl parameter => sizes parameter
  | .inr (.inl name) => (inputs name).width sizes
  | .inr (.inr _) => capacity

def sizePreparationReadOnly (Scratch : NewParameter → Type) :
    SizePreparationTape Parameter InputName NewParameter Scratch → Bool
  | .inl _ => true
  | .inr (.inl _) => true
  | .inr (.inr _) => false

/-- An arbitrary specialization-fixed number of value-dependent sizes can be
prepared without changing the caller's size assignment or immutable arguments. -/
theorem preparesSizes (inputs : InputName → EncodedDomain Parameter)
    (allowed : ∀ sizes, (∀ name, (inputs name).Carrier sizes) → Prop)
    (bounds : NewParameter → MvPolynomial Parameter ℕ)
    (values : ∀ parameter sizes, {arguments : ∀ name, (inputs name).Carrier sizes // allowed sizes arguments} →
      Fin (MvPolynomial.eval sizes (bounds parameter) + 1))
    (realizable : ∀ parameter,
      (Computation.mk inputs (EncodedDomain.boundedUnary (bounds parameter)) allowed (values parameter)).Realizable) :
    ∃ (Scratch : NewParameter → Type) (_finiteScratch : ∀ parameter, Fintype (Scratch parameter))
      (State : Type) (_finiteState : Fintype State)
      (machine : Machine (Alphabet (SizePreparationTape Parameter InputName NewParameter Scratch)) State)
      (entry exit : State) (capacityBound runtimeBound : MvPolynomial Parameter ℕ),
      (∀ symbols, machine exit symbols = none) ∧
      ∀ (sizes : Parameter → ℕ) (arguments : ∀ name, (inputs name).Carrier sizes)
        (valid : allowed sizes arguments) (capacity : ℕ)
        (_fits : MvPolynomial.eval sizes capacityBound ≤ capacity)
        (initial : Tapes (Alphabet (SizePreparationTape Parameter InputName NewParameter Scratch))),
        (∀ parameter, initial (.inl parameter) = unary (sizes parameter)) →
        (∀ name, initial (.inr (.inl name)) = encoded (inputs name) sizes (arguments name)) →
        (∀ parameter block, initial (.inr (.inr ⟨parameter, block⟩)) = buffer []) →
        (∀ name, Region (sizePreparationWidths inputs Scratch sizes capacity name) 0 (initial name)) →
        ∃ ticks final, ticks ≤ MvPolynomial.eval sizes runtimeBound ∧
          Runs (sizePreparationWidths inputs Scratch sizes capacity) (sizePreparationReadOnly Scratch)
            machine ticks entry (fun _ => 0) initial exit (fun _ => 0) final ∧
          ∀ parameter, final (.inr (.inr ⟨parameter, .inl ()⟩)) =
            unary (values parameter sizes ⟨arguments, valid⟩).val := by
  classical
  let maker (parameter : NewParameter) : Computation Parameter InputName :=
    ⟨inputs, EncodedDomain.boundedUnary (bounds parameter), allowed, values parameter⟩
  choose Scratch scratchFinite State stateFinite component componentEntry componentExit capacityBound runtimeBound contract using
    (fun parameter => preparesUnary (maker parameter) (bounds parameter) rfl (realizable parameter))
  let _ : ∀ parameter, Fintype (Scratch parameter) := scratchFinite
  let _ : ∀ parameter, Fintype (State parameter) := stateFinite
  let Tape := SizePreparationTape Parameter InputName NewParameter Scratch
  let wiring (parameter : NewParameter) : TapeName (maker parameter) (Scratch parameter) ↪ Tape :=
    ⟨(fun role => match role with
      | .inl original => .inl original
      | .inr (.inl argument) => .inr (.inl argument)
      | .inr (.inr (.inl output)) => .inr (.inr ⟨parameter, .inl output⟩)
      | .inr (.inr (.inr temporary)) => .inr (.inr ⟨parameter, .inr temporary⟩)), by
      intro first second equal
      rcases first with original | argument | output | temporary <;>
        rcases second with original' | argument' | output' | temporary'
      all_goals first
        | (cases output; cases output'; rfl)
        | (cases equal <;> rfl)⟩
  let enumeration := Fintype.equivFin NewParameter
  let components : ∀ index : Fin (Fintype.card NewParameter), Machine (Alphabet Tape) (State (enumeration.symm index)) :=
    fun index => MultiTape.wire (wiring (enumeration.symm index)) (component (enumeration.symm index))
  let entries (index : Fin (Fintype.card NewParameter)) := componentEntry (enumeration.symm index)
  let exits (index : Fin (Fintype.card NewParameter)) := componentExit (enumeration.symm index)
  refine ⟨Scratch, scratchFinite, _, inferInstance, Pipeline.machine components entries,
    Pipeline.position entries 0, none, ∑ parameter, capacityBound parameter,
    Fintype.card NewParameter * ((∑ parameter, runtimeBound parameter) + 1), ?_, ?_⟩
  · intro symbols; rfl
  intro sizes arguments valid capacity fits initial headers inputValues blank regions
  let width := sizePreparationWidths inputs Scratch sizes capacity
  let readonly := sizePreparationReadOnly (Parameter := Parameter) (InputName := InputName) Scratch
  let representation (stage : Fin (Fintype.card NewParameter + 1)) (tapes : Tapes (Alphabet Tape)) : Prop :=
    (∀ name, readonly name = true → tapes name = initial name) ∧
    (∀ name, Region (width name) 0 (tapes name)) ∧
    (∀ parameter, stage.val ≤ (enumeration parameter).val → ∀ block,
      tapes (.inr (.inr ⟨parameter, block⟩)) = buffer []) ∧
    ∀ parameter, (enumeration parameter).val < stage.val →
      tapes (.inr (.inr ⟨parameter, .inl ()⟩)) = unary (values parameter sizes ⟨arguments, valid⟩).val
  have ready : representation 0 initial :=
    ⟨(by intros; rfl), regions, (by intro parameter before; exact blank parameter),
      (by intro parameter before; exact False.elim (Nat.not_lt_zero _ before))⟩
  obtain ⟨ticks, final, cost, trace, prepared⟩ := Pipeline.runs width readonly components entries exits representation
    (MvPolynomial.eval sizes (∑ parameter, runtimeBound parameter))
    (by intro index symbols; simp [components, exits, MultiTape.wire, (contract _).1])
    (by
      intro index tapes good
      let parameter := enumeration.symm index
      obtain ⟨immutable, currentRegions, future, previous⟩ := good
      have currentBlank (block : Unit ⊕ Scratch parameter) :
          tapes (.inr (.inr ⟨parameter, block⟩)) = buffer [] :=
        future parameter (by simp [parameter]) block
      have capacityFits : MvPolynomial.eval sizes (capacityBound parameter) ≤ capacity := by
        apply le_trans _ fits
        rw [map_sum]
        exact Finset.single_le_sum (fun other _ => Nat.zero_le (MvPolynomial.eval sizes (capacityBound other))) (Finset.mem_univ parameter)
      obtain ⟨localTicks, localFinal, localCost, localTrace, result⟩ := (contract parameter).2 sizes arguments valid
        capacity capacityFits (fun name => tapes (wiring parameter name))
        (fun original => (immutable (.inl original) rfl).trans (headers original))
        (fun argument => (immutable (.inr (.inl argument)) rfl).trans (inputValues argument))
        (by
          rintro (original | argument | output | temporary) writable
          · contradiction
          · contradiction
          · exact currentBlank (.inl output)
          · exact currentBlank (.inr temporary))
        (by
          rintro (original | argument | output | temporary)
          · exact currentRegions (.inl original)
          · exact currentRegions (.inr (.inl argument))
          · exact currentRegions (.inr (.inr ⟨parameter, .inl output⟩))
          · exact currentRegions (.inr (.inr ⟨parameter, .inr temporary⟩)))
      obtain ⟨following, lifted, located, outside, preserved⟩ := localTrace.wire_restoring
        (wiring parameter) width readonly (by rintro (original | argument | output | temporary) <;> rfl)
        (by rintro (original | argument | output | temporary) premise <;> first | rfl | contradiction)
        tapes (fun _ => rfl)
      have untouched (other : NewParameter) (different : other ≠ parameter) (block : Unit ⊕ Scratch other) :
          following (.inr (.inr ⟨other, block⟩)) = tapes (.inr (.inr ⟨other, block⟩)) := by
        apply outside
        rintro ⟨role, equal⟩
        let label : Tape → Option NewParameter
          | .inr (.inr ⟨name, _⟩) => some name
          | _ => none
        have selected := congrArg label equal
        rcases role with original | argument | output | temporary
        · change (none : Option NewParameter) = some other at selected; contradiction
        · change (none : Option NewParameter) = some other at selected; contradiction
        · change some parameter = some other at selected
          exact different (Option.some.inj selected).symm
        · change some parameter = some other at selected
          exact different (Option.some.inj selected).symm
      refine ⟨localTicks, following, ?_, lifted, ?_⟩
      · simpa only [map_sum] using localCost.trans
          (Finset.single_le_sum (fun other _ => Nat.zero_le (MvPolynomial.eval sizes (runtimeBound other)))
            (Finset.mem_univ parameter))
      · refine ⟨?_, (fun name => lifted.region name (currentRegions name)), ?_, ?_⟩
        · intro name immutableName
          exact (lifted.readOnly_tape name immutableName).trans (immutable name immutableName)
        · intro other later block
          have different : other ≠ parameter := by
            intro equal; subst other; simp [parameter] at later
          exact (untouched other different block).trans (future other (by
            change index.val + 1 ≤ (enumeration other).val at later
            change index.val ≤ (enumeration other).val
            omega) block)
        · intro other before
          by_cases equal : other = parameter
          · subst other
            exact (located (outputTape (maker parameter))).trans result
          · have earlier : (enumeration other).val < index.val := by
              have different : (enumeration other).val ≠ index.val := by
                intro same
                exact equal (enumeration.injective (Fin.ext (by simpa [parameter] using same)))
              change (enumeration other).val < index.val + 1 at before
              omega
            exact (untouched other equal (.inl ())).trans (previous other earlier))
    initial ready
  refine ⟨ticks, final, ?_, trace, ?_⟩
  · simpa only [map_mul, map_add, map_one, map_natCast, Nat.cast_id] using cost
  · intro parameter
    exact prepared.2.2.2 parameter (enumeration parameter).isLt

end Polytime2.Computation.Realizable.Internal
