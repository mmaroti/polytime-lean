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

import Polytime2.StandardMatrixEntryContract
import Polytime2.StandardMatrixReplaceContract
import Polytime2.StandardRowCombine
import Polytime2.CallingConventionRegions

/-! # One column of a matrix row operation

Separate source and target indices select entries of an immutable matrix.
Scalar combination and two separate-output replacements use private tapes.
All matrix-access calls share the same arithmetic scratch and flags.
-/

namespace Polytime2.StandardMatrixRowEntry

open MultiTape CallingConvention

abbrev TapeName := Sum (Fin 3) (Fin 18)
abbrev Alphabet := CallingConvention.Alphabet TapeName
abbrev State (width : ℕ) := Sum (StandardMatrixEntry.State width)
  (Sum (StandardMatrixEntry.State width)
    (Sum (StandardRowCombine.State width)
      (Sum (StandardMatrixReplace.State width) (StandardMatrixReplace.State width))))

instance statesFinite (width : ℕ) : Fintype (State width) := by
  letI : Fintype (StandardMatrixEntry.State width) := inferInstance
  letI : Fintype (StandardRowCombine.State width) := inferInstance
  letI : Fintype (StandardMatrixReplace.State width) := inferInstance
  dsimp only [State]
  infer_instance

/-- Slots 0/1/2 hold source row, target row, and column. Slot 3 is the
coefficient; 4/5/6 are source, result, and intermediate matrices. Slots 7–10
hold scalar scratch, 11–15 binary arithmetic words, and 16/17 flags. -/
noncomputable def domains (scalar : EncodedDomain.{0, 0} Empty) : TapeName → EncodedDomain.{0, 0} (Fin 3)
  | .inl parameter => EncodedDomain.unary parameter
  | .inr name => if name = 3 ∨ (7 ≤ name.val ∧ name.val ≤ 10) then scalar.constant
      else if 4 ≤ name.val ∧ name.val ≤ 6 then scalar.constant.arrayOfLength StandardMatrixEntry.length
      else if 16 ≤ name.val then EncodedDomain.booleans else EncodedDomain.binaryNaturals 0

def readOnly : TapeName → Bool
  | .inl _ => true
  | .inr name => decide (name.val < 5)

def sizeTapes : Fin 3 ↪ TapeName := ⟨Sum.inl, by intro first second equal; cases equal; rfl⟩

def addressSlot (target : Bool) (name : Fin 9) : Fin 18 :=
  match name.val with
  | 0 => 11 | 1 => if target then 1 else 0 | 2 => 12 | 3 => 13 | 4 => 16
  | 5 => 14 | 6 => 2 | 7 => 15 | _ => 17

def accessWiring (target : Bool) : StandardMatrixEntry.TapeName ↪ TapeName :=
  ⟨(fun name => match name with
    | .inl (.inl parameter) => .inl parameter
    | .inl (.inr name) => .inr (addressSlot target name)
    | .inr false => .inr 4 | .inr true => .inr (if target then 8 else 7)), by
    intro first second equal
    cases target <;> fin_cases first <;> fin_cases second <;> simp_all [addressSlot]⟩

@[simp] theorem accessWiring_apply (target : Bool) (name : StandardMatrixEntry.TapeName) :
    accessWiring target name = (match name with
    | .inl (.inl parameter) => .inl parameter
    | .inl (.inr name) => .inr (addressSlot target name)
    | .inr false => .inr 4 | .inr true => .inr (if target then 8 else 7)) := rfl

def replaceWiring (source : Bool) : StandardMatrixReplace.TapeName ↪ TapeName :=
  ⟨(fun name => match name with
    | .inl (.inl parameter) => .inl parameter
    | .inl (.inr name) => .inr (addressSlot (!source) name)
    | .inr name => .inr (if name = 0 then (if source then 4 else 6)
        else if name = 1 then (if source then 9 else 10) else (if source then 6 else 5))), by
    intro first second equal
    cases source <;> fin_cases first <;> fin_cases second <;> simp_all [addressSlot]⟩

@[simp] theorem replaceWiring_apply (source : Bool) (name : StandardMatrixReplace.TapeName) :
    replaceWiring source name = (match name with
    | .inl (.inl parameter) => .inl parameter
    | .inl (.inr name) => .inr (addressSlot (!source) name)
    | .inr name => .inr (if name = 0 then (if source then 4 else 6)
        else if name = 1 then (if source then 9 else 10) else (if source then 6 else 5))) := rfl

def combineWiring : (Fin 3 ⊕ Fin 2) ↪ TapeName :=
  ⟨(fun name => .inr (match name with
    | .inl name => match name.val with | 0 => 3 | 1 => 7 | _ => 8
    | .inr name => if name = 0 then 9 else 10)), by
    intro first second equal
    fin_cases first <;> fin_cases second <;> simp_all⟩

@[simp] theorem combineWiring_apply (name : Fin 3 ⊕ Fin 2) : combineWiring name =
    .inr (match name with
    | .inl name => match name.val with | 0 => 3 | 1 => 7 | _ => 8
    | .inr name => if name = 0 then 9 else 10) := rfl

def effectiveOperation (writeSource : Bool) (scalar : EncodedDomain.{0, 0} Empty)
    (operation : ∀ assignment, scalar.Carrier assignment → scalar.Carrier assignment → scalar.Carrier assignment →
      scalar.Carrier assignment × scalar.Carrier assignment)
    (assignment : Empty → ℕ) (coefficient source target : scalar.Carrier assignment) :
      scalar.Carrier assignment × scalar.Carrier assignment :=
  (if writeSource then (operation assignment coefficient source target).1 else source,
    (operation assignment coefficient source target).2)

noncomputable def access (target : Bool) (width : ℕ) : Machine Alphabet (StandardMatrixEntry.State width) :=
  MultiTape.wire (accessWiring target) (StandardMatrixEntry.machine width)

noncomputable def replace (source : Bool) (width : ℕ) : Machine Alphabet (StandardMatrixReplace.State width) :=
  MultiTape.wire (replaceWiring source) (StandardMatrixReplace.machine width)

noncomputable def combine (writeSource : Bool) (scalar : EncodedDomain.{0, 0} Empty)
    (operation : ∀ assignment, scalar.Carrier assignment → scalar.Carrier assignment → scalar.Carrier assignment →
      scalar.Carrier assignment × scalar.Carrier assignment) : Machine Alphabet (StandardRowCombine.State (scalar.width Empty.elim)) :=
  MultiTape.wire combineWiring (StandardRowCombine.algorithm scalar
    (effectiveOperation writeSource scalar operation))

noncomputable def machine (writeSource : Bool) (scalar : EncodedDomain.{0, 0} Empty)
    (operation : ∀ assignment, scalar.Carrier assignment → scalar.Carrier assignment → scalar.Carrier assignment →
      scalar.Carrier assignment × scalar.Carrier assignment) : Machine Alphabet (State (scalar.width Empty.elim)) :=
  let width := scalar.width Empty.elim
  MultiTape.sequence (access false width)
    (MultiTape.sequence (access true width)
      (MultiTape.sequence (combine writeSource scalar operation)
        (MultiTape.sequence (replace true width) (replace false width) (StandardMatrixReplace.entry width))
        (.inl (StandardMatrixReplace.entry width)))
      (.inl StandardRowCombine.entry))
    (.inl (StandardMatrixEntry.entry width))

def entry (width : ℕ) : State width := .inl (StandardMatrixEntry.entry width)
def exit (width : ℕ) : State width := .inr (.inr (.inr (.inr (StandardMatrixReplace.exit width))))

@[simp] theorem halt (writeSource : Bool) (scalar : EncodedDomain.{0, 0} Empty)
    (operation : ∀ assignment, scalar.Carrier assignment → scalar.Carrier assignment → scalar.Carrier assignment →
      scalar.Carrier assignment × scalar.Carrier assignment) (symbols : Symbols Alphabet) :
    machine writeSource scalar operation (exit (scalar.width Empty.elim)) symbols = none := by
  simp [machine, exit, MultiTape.sequence, replace, MultiTape.wire]

/-- Scalar calls consume valid entries from the matrix-read results. Arbitrary
output scratch is admitted using its preserved region, rather than old values. -/
theorem combine_runs (writeSource : Bool) (scalar : EncodedDomain.{0, 0} Empty)
    (operation : ∀ assignment, scalar.Carrier assignment → scalar.Carrier assignment → scalar.Carrier assignment →
      scalar.Carrier assignment × scalar.Carrier assignment) :
    ∃ bound : ℕ, ∀ (sizes : Fin 3 → ℕ) (initial : Tapes Alphabet)
      (coefficient source target : scalar.Carrier Empty.elim),
      initial (.inr 3) = encoded scalar Empty.elim coefficient →
      initial (.inr 7) = encoded scalar Empty.elim source →
      initial (.inr 8) = encoded scalar Empty.elim target →
      (∀ name, Region ((domains scalar name).width sizes) 0 (initial name)) →
      ∃ ticks final, ticks ≤ bound ∧
        Runs (fun name => (domains scalar name).width sizes) readOnly (combine writeSource scalar operation) ticks
          StandardRowCombine.entry (fun _ => 0) initial StandardRowCombine.exit (fun _ => 0) final ∧
        final (.inr 9) = encoded scalar Empty.elim (effectiveOperation writeSource scalar operation Empty.elim coefficient source target).1 ∧
        final (.inr 10) = encoded scalar Empty.elim (effectiveOperation writeSource scalar operation Empty.elim coefficient source target).2 ∧
        (∀ name, name ∉ Set.range combineWiring → final name = initial name) ∧
        (∀ name, StandardRowCombine.readOnly name = true → final (combineWiring name) = initial (combineWiring name)) := by
  obtain ⟨bound, execute⟩ := (StandardRowCombine.contract scalar
    (effectiveOperation writeSource scalar operation)).wired_runs combineWiring
  refine ⟨MvPolynomial.eval Empty.elim bound, ?_⟩
  intro sizes initial coefficient source target coefficientEq sourceEq targetEq regions
  let input : Inputs (StandardRowCombine.domains scalar) StandardRowCombine.readOnly Empty.elim := fun name =>
    match name with
    | ⟨.inl name, _⟩ => if name = 0 then coefficient else if name = 1 then source else target
    | ⟨.inr _, impossible⟩ => nomatch impossible
  obtain ⟨ticks, output, final, cost, trace, correct, canonical, outside, immutable⟩ :=
    execute Empty.elim input (fun name => (domains scalar name).width sizes) readOnly initial
      (by intro name; fin_cases name <;>
        simp [domains, StandardRowCombine.domains, FiniteTable.domains, EncodedDomain.constant, EncodedDomain.ofCodec])
      (by
        intro name premise
        simp only [combineWiring_apply] at premise
        fin_cases name <;> norm_num [readOnly, StandardRowCombine.readOnly] at *)
      trivial
      (by
        intro name readonly
        fin_cases name
        · exact coefficientEq
        · exact sourceEq
        · exact targetEq
        · contradiction
        · contradiction)
      (by intro name writable; exact regions (combineWiring name))
      (by intro parameter; cases parameter)
  have firstOutput := congrArg Prod.fst correct
  have secondOutput := congrArg Prod.snd correct
  change output 0 =
    (effectiveOperation writeSource scalar operation Empty.elim coefficient source target).1 at firstOutput
  change output 1 =
    (effectiveOperation writeSource scalar operation Empty.elim coefficient source target).2 at secondOutput
  refine ⟨ticks, final, cost, trace, ?_, ?_, outside, immutable⟩
  · have result := canonical 0
    rw [firstOutput] at result
    exact result
  · have result := canonical 1
    rw [secondOutput] at result
    exact result

end Polytime2.StandardMatrixRowEntry
