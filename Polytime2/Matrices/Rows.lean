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

import Polytime2.Matrices.RowStep
import Polytime2.Arithmetic.BinarySubtraction
import Polytime2.Primitives.SizeReadContract
import Polytime2.Machine.Pipeline

/-! # A fixed-width workspace for complete matrix row operations

The original matrix is immutable. The column step uses private working tapes;
the additional tapes hold the binary column limit, difference, and guard bit.
-/

namespace Polytime2.StandardMatrixRows

open MultiTape CallingConvention

abbrev TapeName := Sum StandardMatrixRowStep.TapeName (Fin 4)
abbrev Alphabet := CallingConvention.Alphabet TapeName

def dataTape (name : Fin 18) : TapeName := .inl (.inl (.inr name))
def sizeTape (parameter : Fin 3) : TapeName := .inl (.inl (.inl parameter))
def nextTape : TapeName := .inl (.inr ())
def limitTape : TapeName := .inr 0
def differenceTape : TapeName := .inr 1
def guardTape : TapeName := .inr 2
def inputTape : TapeName := .inr 3

noncomputable def domains (scalar : EncodedDomain.{0, 0} Empty) :
    TapeName → EncodedDomain.{0, 0} (Fin 3)
  | .inl name => StandardMatrixRowStep.domains scalar name
  | .inr name => if name = 3 then scalar.constant.arrayOfLength StandardMatrixEntry.length
      else if name = 2 then EncodedDomain.booleans else EncodedDomain.binaryNaturals 0

def readOnly : TapeName → Bool
  | .inl name => StandardMatrixRowStep.readOnly name
  | .inr name => decide (name = 3)

def sizeTapes : Fin 3 ↪ TapeName :=
  ⟨sizeTape, by intro first second equal; cases equal; rfl⟩

def stepWiring : StandardMatrixRowStep.TapeName ↪ TapeName :=
  ⟨Sum.inl, by intro first second equal; cases equal; rfl⟩

@[simp] theorem stepWiring_apply (name : StandardMatrixRowStep.TapeName) : stepWiring name = .inl name := rfl

def guardWiring : Sum Unit (Fin 4) ↪ TapeName :=
  ⟨(fun name => match name with
    | .inl _ => sizeTape 0
    | .inr name => match name.val with
      | 0 => dataTape 2 | 1 => limitTape | 2 => differenceTape | _ => guardTape), by
    intro first second equal
    fin_cases first <;> fin_cases second <;>
      simp_all [dataTape, sizeTape, limitTape, differenceTape, guardTape]⟩

@[simp] theorem guardWiring_apply (name : Sum Unit (Fin 4)) : guardWiring name =
    (match name with
    | .inl _ => sizeTape 0
    | .inr name => match name.val with
      | 0 => dataTape 2 | 1 => limitTape | 2 => differenceTape | _ => guardTape) := rfl

noncomputable def guard : Machine Alphabet (Sum StandardBinaryArithmetic.State Unit) :=
  MultiTape.wire guardWiring BinarySubtraction.algorithm

noncomputable def body (writeSource : Bool) (scalar : EncodedDomain.{0, 0} Empty)
    (operation : ∀ assignment, scalar.Carrier assignment → scalar.Carrier assignment →
      scalar.Carrier assignment → scalar.Carrier assignment × scalar.Carrier assignment) :
    Machine Alphabet (StandardMatrixRowStep.State (scalar.width Empty.elim)) :=
  MultiTape.wire stepWiring (StandardMatrixRowStep.machine writeSource scalar operation)

def result (symbols : Symbols Alphabet) : Bool := decide (symbols guardTape = Binary.data true)

@[simp] theorem guard_halt (symbols : Symbols Alphabet) : guard BinarySubtraction.exit symbols = none := by
  simp [guard, MultiTape.wire, BinarySubtraction.algorithm, BinarySubtraction.exit,
    StandardBinaryArithmetic.algorithm, StandardBinaryArithmetic.exit, MultiTape.withExit]

/-- The guard compares bounded binary values and canonicalizes both outputs.
Every tape except its difference and Boolean result stays unchanged. -/
theorem guard_runs (scalar : EncodedDomain.{0, 0} Empty) :
    ∃ bound : MvPolynomial (Fin 3) ℕ, ∀ (sizes : Fin 3 → ℕ) (initial : Tapes Alphabet)
      (column limit : Fin (2 ^ sizes 0)),
      initial (sizeTape 0) = unary (sizes 0) →
      initial (dataTape 2) = encoded (EncodedDomain.binaryNaturals 0) sizes column →
      initial limitTape = encoded (EncodedDomain.binaryNaturals 0) sizes limit →
      Region (sizes 0) 0 (initial differenceTape) → Region 1 0 (initial guardTape) →
      ∃ ticks final, ticks ≤ MvPolynomial.eval sizes bound ∧
        Runs (fun name => (domains scalar name).width sizes) readOnly guard ticks
          BinarySubtraction.entry (fun _ => 0) initial BinarySubtraction.exit (fun _ => 0) final ∧
        final guardTape = encoded EncodedDomain.booleans sizes (decide (column.val < limit.val)) ∧
        (∃ value : Fin (2 ^ sizes 0), final differenceTape = encoded (EncodedDomain.binaryNaturals 0) sizes value) ∧
        (∀ name, name ≠ differenceTape → name ≠ guardTape → final name = initial name) := by
  obtain ⟨bound, execute⟩ := BinarySubtraction.comparison_contract.wired_runs guardWiring
  refine ⟨MvPolynomial.rename (fun _ : Unit => (0 : Fin 3)) bound, ?_⟩
  intro sizes initial column limit header columnEq limitEq differenceRegion guardRegion
  let localSizes : Unit → ℕ := fun _ => sizes 0
  let input : Inputs BinarySubtraction.domains BinarySubtraction.argumentReadOnly localSizes := fun name => by
    rcases name with ⟨name, readonly⟩
    cases name with
    | inl parameter => exact PUnit.unit
    | inr name =>
      by_cases first : name = 0
      · subst name; exact column
      · by_cases second : name = 1
        · subst name; exact limit
        · have writable : BinarySubtraction.argumentReadOnly (.inr name) = false := by
            fin_cases name <;> first | rfl | contradiction
          rw [writable] at readonly
          contradiction
  obtain ⟨ticks, output, final, cost, trace, correct, canonical, outside, immutable⟩ :=
    execute localSizes input (fun name => (domains scalar name).width sizes) readOnly initial
      (by intro name; fin_cases name <;>
        simp [domains, StandardMatrixRowStep.domains, StandardMatrixRowEntry.domains,
          BinarySubtraction.domains, StandardBinaryArithmetic.domains, EncodedDomain.unary,
          EncodedDomain.binaryNaturals, EncodedDomain.booleans, EncodedDomain.fixed,
          EncodedDomain.ofCodec, sizeTape, dataTape, limitTape, differenceTape, guardTape, localSizes])
      (by intro name premise; fin_cases name <;> first | rfl | contradiction)
      trivial
      (by
        intro name readonly
        fin_cases name
        · change initial (sizeTape 0) = encoded (EncodedDomain.unary ()) localSizes PUnit.unit
          rw [encoded_unary]
          exact header
        · change initial (dataTape 2) = encoded (EncodedDomain.binaryNaturals ()) localSizes column
          simpa only [encoded, EncodedDomain.binaryNaturals, EncodedDomain.ofCodec,
            EncodedDomain.ArrayEncoding.bits_cast, localSizes] using columnEq
        · change initial (limitTape) = encoded (EncodedDomain.binaryNaturals ()) localSizes limit
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
        · convert differenceRegion using 1 <;>
            norm_num [domains, differenceTape, EncodedDomain.binaryNaturals, EncodedDomain.ofCodec] <;> rfl
        · convert guardRegion using 1 <;>
            norm_num [domains, guardTape, EncodedDomain.booleans, EncodedDomain.fixed, EncodedDomain.ofCodec] <;> rfl)
      (by intro parameter; cases parameter; exact header)
  refine ⟨ticks, final, ?_, trace, ?_, ?_, ?_⟩
  · simpa only [MvPolynomial.eval_rename, localSizes, Function.comp_def] using cost
  · have flag := canonical true
    change final guardTape = encoded EncodedDomain.booleans localSizes (output true) at flag
    change output true = decide (column.val < limit.val) at correct
    rw [correct] at flag
    simpa only [encoded, EncodedDomain.booleans, EncodedDomain.fixed, EncodedDomain.ofCodec,
      EncodedDomain.ArrayEncoding.bits_cast] using flag
  · have result := canonical false
    change final differenceTape = encoded (EncodedDomain.binaryNaturals ()) localSizes (output false) at result
    refine ⟨output false, ?_⟩
    simpa only [encoded, EncodedDomain.binaryNaturals, EncodedDomain.ofCodec,
      EncodedDomain.ArrayEncoding.bits_cast, localSizes] using result
  · intro name notDifference notGuard
    apply preserved_of_wiring guardWiring BinarySubtraction.argumentReadOnly initial final outside immutable
    intro localName equal
    fin_cases localName
    · rfl
    · rfl
    · rfl
    · exact False.elim (notDifference equal.symm)
    · exact False.elim (notGuard equal.symm)

end Polytime2.StandardMatrixRows
