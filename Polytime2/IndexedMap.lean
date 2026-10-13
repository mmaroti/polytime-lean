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

import Polytime2.StandardFiniteTable
import Polytime2.StandardArrayLookupSizedContract
import Polytime2.StandardArrayUpdate

/-! # Applying a fixed finite operation at an indexed array coordinate

The index, scalar parameter, and source array are immutable. Lookup, a binary
finite table, and update share private scalar tapes; the changed array goes to
a distinct output tape. Every domain has the caller's explicit size assignment.
-/

namespace Polytime2.IndexedMap

open MultiTape CallingConvention

-- parameterLevel: names of the caller's unary size parameters.
universe parameterLevel
variable {Parameter : Type parameterLevel} [Fintype Parameter]

abbrev Alphabet := CallingConvention.Alphabet (Sum Parameter (Fin 12))
abbrev State (parameterWidth elementWidth : ℕ) :=
  Sum (StandardArrayLookup.State elementWidth)
    (Sum (StandardFiniteTable.State parameterWidth elementWidth elementWidth)
      (StandardArrayUpdate.State elementWidth))

def lookupData (name : Fin 6) : Fin 12 :=
  ⟨match name.val with
    | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 6 | 4 => 7 | _ => 8,
    by fin_cases name <;> decide⟩

def updateData (name : Fin 7) : Fin 12 :=
  ⟨match name.val with
    | 0 => 0 | 1 => 1 | 2 => 5 | 3 => 3 | 4 => 9 | 5 => 10 | _ => 11,
    by fin_cases name <;> decide⟩

private theorem lookupData_injective : Function.Injective lookupData := by
  intro first second equal
  fin_cases first <;> fin_cases second <;> simp [lookupData] at equal ⊢

private theorem updateData_injective : Function.Injective updateData := by
  intro first second equal
  fin_cases first <;> fin_cases second <;> simp [updateData] at equal ⊢

def lookupWiring : Sum Parameter (Fin 6) ↪ Sum Parameter (Fin 12) :=
  (Function.Embedding.refl Parameter).sumMap ⟨lookupData, lookupData_injective⟩

def updateWiring : Sum Parameter (Fin 7) ↪ Sum Parameter (Fin 12) :=
  (Function.Embedding.refl Parameter).sumMap ⟨updateData, updateData_injective⟩

def tableWiring : Fin 3 ↪ Sum Parameter (Fin 12) :=
  ⟨(fun name => Sum.inr (match name.val with | 0 => 2 | 1 => 4 | _ => 5)), by
    intro first second equal
    fin_cases first <;> fin_cases second <;> simp at equal ⊢⟩

noncomputable def domains (parameterDomain elementDomain : EncodedDomain Empty)
    (indexCapacity : Parameter) (length : MvPolynomial Parameter ℕ) :
    Sum Parameter (Fin 12) → EncodedDomain Parameter
  | .inl parameter => EncodedDomain.unary parameter
  | .inr 0 => EncodedDomain.binaryNaturals indexCapacity
  | .inr 1 | .inr 3 => elementDomain.constant.arrayOfLength length
  | .inr 2 => parameterDomain.constant
  | .inr 4 | .inr 5 => elementDomain.constant
  | .inr 6 | .inr 7 | .inr 9 | .inr 10 => EncodedDomain.binaryNaturals indexCapacity
  | .inr 8 | .inr 11 => EncodedDomain.booleans

def argumentReadOnly : Sum Parameter (Fin 12) → Bool
  | .inl _ => true
  | .inr name => decide (name.val < 3)

def sizeTapes : Parameter ↪ Sum Parameter (Fin 12) :=
  ⟨Sum.inl, by intro first second equal; cases equal; rfl⟩

noncomputable def algorithm (parameterDomain elementDomain : EncodedDomain Empty)
    (operation : ∀ assignment, parameterDomain.Carrier assignment →
      elementDomain.Carrier assignment → elementDomain.Carrier assignment) :
    Machine (Alphabet (Parameter := Parameter))
      (State (parameterDomain.width Empty.elim) (elementDomain.width Empty.elim)) :=
  MultiTape.sequence
    (MultiTape.wire lookupWiring
      (StandardArrayLookupSized.algorithmSized (elementDomain.width Empty.elim)))
    (MultiTape.sequence
      (MultiTape.wire tableWiring
        (StandardFiniteTable.algorithm parameterDomain elementDomain elementDomain operation))
      (MultiTape.wire updateWiring
        (StandardArrayUpdate.algorithmSized (elementDomain.width Empty.elim)))
      (StandardArrayUpdate.entry (elementDomain.width Empty.elim)))
    (.inl StandardFiniteTable.entry)

def entry (parameterWidth elementWidth : ℕ) : State parameterWidth elementWidth :=
  .inl (StandardArrayLookup.entry elementWidth)

def exit (parameterWidth elementWidth : ℕ) : State parameterWidth elementWidth :=
  .inr (.inr (StandardArrayUpdate.exit elementWidth))

omit [Fintype Parameter] in
@[simp] theorem halt (parameterDomain elementDomain : EncodedDomain Empty)
    (operation : ∀ assignment, parameterDomain.Carrier assignment →
      elementDomain.Carrier assignment → elementDomain.Carrier assignment)
    (symbols : Symbols (Alphabet (Parameter := Parameter))) :
    algorithm parameterDomain elementDomain operation
      (exit (parameterDomain.width Empty.elim) (elementDomain.width Empty.elim)) symbols = none := by
  simp [algorithm, exit, MultiTape.sequence, MultiTape.wire,
    StandardArrayUpdate.algorithmSized, StandardArrayUpdate.machine,
    StandardArrayUpdate.exit, StandardArrayUpdate.restore, StandardHead.BlankReturn.machine]

omit [Fintype Parameter] in
/-- The three components share one frame, with two stationary handovers. -/
theorem sequence_runs (parameterDomain elementDomain : EncodedDomain Empty)
    (operation : ∀ assignment, parameterDomain.Carrier assignment →
      elementDomain.Carrier assignment → elementDomain.Carrier assignment)
    (width : Sum Parameter (Fin 12) → ℕ) (readOnly : Sum Parameter (Fin 12) → Bool)
    {lookupTicks tableTicks updateTicks : ℕ}
    {initialPosition lookupPosition tablePosition finalPosition : Sum Parameter (Fin 12) → ℤ}
    {initial afterLookup afterTable final : Tapes (Alphabet (Parameter := Parameter))}
    (lookupTrace : Runs width readOnly
      (MultiTape.wire lookupWiring
        (StandardArrayLookupSized.algorithmSized (elementDomain.width Empty.elim)))
      lookupTicks (StandardArrayLookup.entry (elementDomain.width Empty.elim)) initialPosition initial
      (StandardArrayLookup.exit (elementDomain.width Empty.elim)) lookupPosition afterLookup)
    (tableTrace : Runs width readOnly
      (MultiTape.wire tableWiring
        (StandardFiniteTable.algorithm parameterDomain elementDomain elementDomain operation))
      tableTicks StandardFiniteTable.entry lookupPosition afterLookup
      StandardFiniteTable.exit tablePosition afterTable)
    (updateTrace : Runs width readOnly
      (MultiTape.wire updateWiring
        (StandardArrayUpdate.algorithmSized (elementDomain.width Empty.elim)))
      updateTicks (StandardArrayUpdate.entry (elementDomain.width Empty.elim)) tablePosition afterTable
      (StandardArrayUpdate.exit (elementDomain.width Empty.elim)) finalPosition final) :
    Runs width readOnly (algorithm parameterDomain elementDomain operation)
      (lookupTicks + tableTicks + updateTicks + 2)
      (entry (parameterDomain.width Empty.elim) (elementDomain.width Empty.elim)) initialPosition initial
      (exit (parameterDomain.width Empty.elim) (elementDomain.width Empty.elim)) finalPosition final := by
  have tail := tableTrace.sequence
    (MultiTape.wire updateWiring (StandardArrayUpdate.algorithmSized (elementDomain.width Empty.elim)))
    (StandardArrayUpdate.entry (elementDomain.width Empty.elim))
    (by intro symbols; simp [MultiTape.wire, StandardFiniteTable.algorithm,
      StandardFiniteTable.machine, StandardFiniteTable.exit]) updateTrace
  have complete := lookupTrace.sequence
    (MultiTape.sequence
      (MultiTape.wire tableWiring
        (StandardFiniteTable.algorithm parameterDomain elementDomain elementDomain operation))
      (MultiTape.wire updateWiring
        (StandardArrayUpdate.algorithmSized (elementDomain.width Empty.elim)))
      (StandardArrayUpdate.entry (elementDomain.width Empty.elim)))
    (.inl StandardFiniteTable.entry)
    (by intro symbols; simp [MultiTape.wire, StandardArrayLookupSized.algorithmSized,
      StandardArrayLookup.halt]) tail
  convert complete using 1 <;> first | rfl | omega

end Polytime2.IndexedMap
