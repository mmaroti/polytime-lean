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

import Polytime2.Primitives.TapeCommands
import Polytime2.Primitives.SizeReadContract
import Polytime2.Machine.Pipeline

/-! # Initialization plans for live workspace variables

Commands overwrite their destinations from canonical sources or fixed words.
Unmentioned scratch tapes need only their bounded regions, even for empty loops.
-/

namespace Polytime2.MultiTape.Initialization

open CallingConvention

universe tapeLevel
variable {TapeName : Type tapeLevel} [DecidableEq TapeName]

/-- Commands whose only effect is to replace one destination word. -/
inductive Command (TapeName : Type tapeLevel) where
  | copy (source target : TapeName) (distinct : source ≠ target)
  | clear (source target : TapeName) (distinct : source ≠ target)
  | constant (target : TapeName) (bits : List Bool)

namespace Command

def target : Command TapeName → TapeName
  | .copy _ target _ | .clear _ target _ | .constant target _ => target

def source : Command TapeName → Option TapeName
  | .copy source _ _ | .clear source _ _ => some source
  | .constant _ _ => none

def word (words : TapeName → List Bool) : Command TapeName → List Bool
  | .copy source _ _ => words source
  | .clear source _ _ => List.replicate (words source).length false
  | .constant _ bits => bits

def cost (words : TapeName → List Bool) (command : Command TapeName) : ℕ :=
  match command with
  | .constant _ bits => 2 * bits.length + 1
  | _ => 2 * (command.word words).length + 2

abbrev State : Command TapeName → Type
  | .copy _ _ _ => Fin 3
  | .clear _ _ _ => StandardBinaryScan.State Unit
  | .constant _ bits => Copy.State bits.length

instance stateFinite (command : Command TapeName) : Fintype command.State := by
  cases command <;> dsimp [State] <;> infer_instance

noncomputable def machine (command : Command TapeName) :
    Machine (CallingConvention.Alphabet TapeName) command.State :=
  match command with
  | .copy source target distinct => StandardTapeCommands.copy source target distinct
  | .clear source target distinct => StandardTapeCommands.clear source target distinct
  | .constant target bits => StandardTapeCommands.setConstant target bits

def entry (command : Command TapeName) : command.State :=
  match command with
  | .copy _ _ _ => 0
  | .clear _ _ _ => .inl ()
  | .constant _ bits => (false, Fin.last bits.length)

def exit (command : Command TapeName) : command.State :=
  match command with
  | .copy _ _ _ => 2
  | .clear _ _ _ => .inr ((), true)
  | .constant _ _ => (true, 0)

omit [DecidableEq TapeName] in
@[simp] theorem halt (command : Command TapeName)
    (symbols : Symbols (CallingConvention.Alphabet TapeName)) :
    command.machine command.exit symbols = none := by
  cases command <;> rfl

/-- Each command accepts arbitrary destination contents and restores all heads.
Only its source, when present, must already contain a valid binary word. -/
theorem runs (command : Command TapeName) (words : TapeName → List Bool)
    (width : TapeName → ℕ) (readOnly : TapeName → Bool)
    (writable : readOnly command.target = false)
    (sourceWidth : ∀ name, command.source = some name → width name = (words name).length)
    (targetWidth : width command.target = (command.word words).length)
    (initial : Tapes (CallingConvention.Alphabet TapeName))
    (sourceEq : ∀ name, command.source = some name → initial name = buffer (Binary.word (words name)))
    (region : Region (width command.target) 0 (initial command.target)) :
    ∃ ticks, ticks ≤ command.cost words ∧
      Runs width readOnly command.machine ticks command.entry (fun _ => 0) initial
        command.exit (fun _ => 0)
        (Function.update initial command.target (buffer (Binary.word (command.word words)))) := by
  obtain ⟨old, oldLength, oldEq⟩ := region.exists_buffer
  cases command with
  | copy source target distinct =>
    exact ⟨_, le_rfl, StandardTapeCommands.copy_runs source target distinct width readOnly
      writable (words source) old (sourceWidth source rfl) targetWidth
      (oldLength.trans targetWidth) initial (sourceEq source rfl) oldEq⟩
  | clear source target distinct =>
    have targetLength : width target = (words source).length := by simpa [word, Command.target] using targetWidth
    exact ⟨_, by simp [word, cost], StandardTapeCommands.clear_runs source target distinct width readOnly
      writable (words source) old (sourceWidth source rfl) targetLength
      (oldLength.trans targetLength) initial (sourceEq source rfl) oldEq⟩
  | constant target bits =>
    exact ⟨_, le_rfl, StandardTapeCommands.setConstant_runs target bits
      width readOnly writable targetWidth initial old (oldLength.trans targetWidth) oldEq⟩

end Command

variable {count : ℕ}

/-- Compile a fixed finite list of initialization commands. -/
noncomputable def machine (commands : Fin count → Command TapeName) :=
  Pipeline.machine (fun stage => (commands stage).machine) (fun stage => (commands stage).entry)

/-- Initialize just the selected live variables. Sources are immutable, and
scratch outside the plan has no encoding requirement. -/
theorem runs (commands : Fin count → Command TapeName) (words : TapeName → List Bool)
    (width : TapeName → ℕ) (readOnly : TapeName → Bool) (allowance : ℕ)
    (distinct : Function.Injective (fun stage => (commands stage).target))
    (writable : ∀ stage, readOnly (commands stage).target = false)
    (immutable : ∀ stage name, (commands stage).source = some name → readOnly name = true)
    (sourceWidth : ∀ stage name, (commands stage).source = some name → width name = (words name).length)
    (targetWidth : ∀ stage, width (commands stage).target = ((commands stage).word words).length)
    (bounded : ∀ stage, (commands stage).cost words ≤ allowance)
    (initial : Tapes (CallingConvention.Alphabet TapeName))
    (sourceEq : ∀ stage name, (commands stage).source = some name →
      initial name = buffer (Binary.word (words name)))
    (regions : ∀ name, Region (width name) 0 (initial name)) :
    ∃ ticks final, ticks ≤ count * (allowance + 1) ∧
      Runs width readOnly (machine commands) ticks
        (Pipeline.position (fun stage => (commands stage).entry) 0) (fun _ => 0) initial
        none (fun _ => 0) final ∧
      ∀ stage, final (commands stage).target = buffer (Binary.word ((commands stage).word words)) := by
  apply Pipeline.updates_runs width readOnly (fun stage => (commands stage).machine)
    (fun stage => (commands stage).entry) (fun stage => (commands stage).exit)
    (fun stage => (commands stage).target) distinct
    (fun stage => buffer (Binary.word ((commands stage).word words))) allowance
    (fun stage => (commands stage).halt) initial regions
  intro stage tapes preserved currentRegions
  obtain ⟨ticks, cost, trace⟩ := (commands stage).runs words width readOnly (writable stage)
    (sourceWidth stage) (targetWidth stage) tapes
    (fun name source => (preserved name (immutable stage name source)).trans (sourceEq stage name source))
    (currentRegions _)
  exact ⟨ticks, cost.trans (bounded stage), trace⟩

/-- Read an immutable unary size into a binary live variable. The second
writable word is private scratch and requires only its bounded region. -/
theorem readSize_runs {Parameter TargetTape : Type} [Fintype Parameter] [Fintype TargetTape]
    (wiring : Sum Bool Bool ↪ TargetTape) (parameter capacity : Parameter)
    (sizes : Parameter → ℕ) (width : TargetTape → ℕ) (readOnly : TargetTape → Bool)
    (initial : Tapes (CallingConvention.Alphabet TargetTape))
    (widthsMatch : ∀ name, width (wiring name) = (StandardSizeRead.domains name).width
      (fun name => if name then sizes capacity else sizes parameter))
    (readOnlyMatch : ∀ name, readOnly (wiring name) = true → StandardSizeRead.argumentReadOnly name = true)
    (headers : ∀ name, initial (wiring (.inl name)) = unary (if name then sizes capacity else sizes parameter))
    (fits : sizes parameter < 2 ^ sizes capacity)
    (resultRegion : Region (sizes capacity) 0 (initial (wiring (.inr false))))
    (scratchRegion : Region (sizes capacity) 0 (initial (wiring (.inr true)))) :
    ∃ final, Runs width readOnly (MultiTape.wire wiring StandardSizeRead.algorithm)
        (4 * sizes capacity + sizes parameter * (4 * sizes capacity + 8) + 11)
        StandardSizeRead.entry (fun _ => 0) initial StandardSizeRead.exit (fun _ => 0) final ∧
      final (wiring (.inr false)) = encoded (EncodedDomain.binaryNaturals capacity) sizes
        ⟨sizes parameter, fits⟩ ∧
      (∃ value : Fin (2 ^ sizes capacity), final (wiring (.inr true)) =
        encoded (EncodedDomain.binaryNaturals capacity) sizes value) ∧
      (∀ name, name ≠ wiring (.inr false) → name ≠ wiring (.inr true) → final name = initial name) := by
  obtain ⟨scratch, scratchLength, final, trace, resultEq, scratchEq, outside, immutable⟩ :=
    StandardSizeRead.Internal.runs_wired wiring
      (fun name => if name then sizes capacity else sizes parameter)
      width readOnly initial widthsMatch readOnlyMatch headers resultRegion scratchRegion
  let bits := StandardSizeRead.advanceBits (sizes parameter) (List.replicate (sizes capacity) false)
  have length : bits.length = sizes capacity := by simp [bits]
  have value : Binary.value bits = sizes parameter := by
    simp [bits, StandardSizeRead.advanceBits_value, Nat.mod_eq_of_lt fits]
  have resultEncoding := encoded_binaryNaturals capacity sizes bits length
  have sameValue : (⟨Binary.value bits, by
      simpa only [length] using Binary.value_lt_pow_length bits⟩ : Fin (2 ^ sizes capacity)) =
      ⟨sizes parameter, fits⟩ := Fin.ext value
  rw [sameValue] at resultEncoding
  refine ⟨final, trace, resultEq.trans resultEncoding.symm, ?_, ?_⟩
  · exact ⟨⟨Binary.value scratch, by
      simpa only [scratchLength, ite_true] using Binary.value_lt_pow_length scratch⟩,
      scratchEq.trans (encoded_binaryNaturals capacity sizes scratch scratchLength).symm⟩
  · intro name notResult notScratch
    apply preserved_of_wiring wiring StandardSizeRead.argumentReadOnly initial final outside immutable
    intro localName equal
    cases localName with
    | inl parameter => rfl
    | inr name => cases name with
      | false => exact False.elim (notResult equal.symm)
      | true => exact False.elim (notScratch equal.symm)

end Polytime2.MultiTape.Initialization
