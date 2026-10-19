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

import Polytime2.Primitives.FixedRead
import Polytime2.Primitives.Constant
import Mathlib.Algebra.BigOperators.Fin

/-! # Finite tables with heterogeneous argument and result families

All widths, arities, and registers belong to the specialization. Reading every
argument precedes writing any result. No extra tape representation is used.
-/

namespace Polytime2.FiniteTable

open MultiTape CallingConvention
open Binary (Symbol word)

variable {inputCount outputCount : ℕ}

abbrev Registers (widths : Fin inputCount → ℕ) := ∀ name, StandardFixedRead.Memory (widths name)

def WriteActive : {count : ℕ} → (Fin count → ℕ) → Type
  | 0, _ => Empty
  | _ + 1, widths => Copy.State (widths 0) ⊕ WriteActive (fun name => widths name.succ)

def Active : {count : ℕ} → (Fin count → ℕ) → (Fin outputCount → ℕ) → Type
  | 0, _, outputs => WriteActive outputs
  | _ + 1, inputs, outputs => StandardFixedRead.State (inputs 0) ⊕
      (StandardFixedRead.Memory (inputs 0) × Active (fun name => inputs name.succ) outputs)

abbrev WriteState (widths : Fin outputCount → ℕ) := Option (WriteActive widths)
abbrev State (inputs : Fin inputCount → ℕ) (outputs : Fin outputCount → ℕ) := Option (Active inputs outputs)

instance writeActive_fintype (widths : Fin outputCount → ℕ) : Fintype (WriteActive widths) := by
  induction outputCount with
  | zero => dsimp [WriteActive]; infer_instance
  | succ count hypothesis => dsimp [WriteActive]; infer_instance

instance active_fintype (inputs : Fin inputCount → ℕ) (outputs : Fin outputCount → ℕ) :
    Fintype (Active inputs outputs) := by
  induction inputCount with
  | zero => dsimp [Active]; infer_instance
  | succ count hypothesis => dsimp [Active]; infer_instance

def cost (widths : Fin inputCount → ℕ) : ℕ := ∑ name, (2 * widths name + 2)

def writeEntry : {count : ℕ} → (widths : Fin count → ℕ) → WriteState widths
  | 0, _ => none
  | _ + 1, widths => some (.inl (false, Fin.last (widths 0)))

def entry : {count : ℕ} → (inputs : Fin count → ℕ) → (outputs : Fin outputCount → ℕ) → State inputs outputs
  | 0, _, outputs => writeEntry outputs
  | _ + 1, inputs, _ => some (.inl ((false, Fin.last (inputs 0)), fun _ => false))

-- tapeLevel: names in the enclosing machine.
universe tapeLevel
variable {TapeName : Type tapeLevel}

noncomputable def writer : {count : ℕ} → (widths : Fin count → ℕ) →
    (Fin count ↪ TapeName) → (∀ name, BitVec (widths name)) →
    Machine (CallingConvention.Alphabet TapeName) (WriteState widths)
  | 0, _, _, _ => fun _ _ => none
  | _ + 1, widths, tapes, values => fun state symbols => match state with
    | none => none
    | some (.inl localState) =>
      match MultiTape.wire (oneTape (tapes 0)) (StandardConstant.ofBitVec (values 0)) localState symbols with
      | some (next, actions) => some (some (.inl next), actions)
      | none => some ((writeEntry (fun name => widths name.succ)).map Sum.inr, stationary symbols)
    | some (.inr localState) =>
      (writer (fun name => widths name.succ) ((Fin.succEmb _).trans tapes)
        (fun name => values name.succ) (some localState) symbols).map
          (fun command => (command.1.map Sum.inr, command.2))

noncomputable def machine : {count : ℕ} → (inputs : Fin count → ℕ) →
    (outputs : Fin outputCount → ℕ) → (Fin count ↪ TapeName) → (Fin outputCount ↪ TapeName) →
    (Registers inputs → ∀ name, BitVec (outputs name)) →
    Machine (CallingConvention.Alphabet TapeName) (State inputs outputs)
  | 0, _, outputs, _, outputTapes, table => writer outputs outputTapes (table (fun name => Fin.elim0 name))
  | _ + 1, inputs, outputs, inputTapes, outputTapes, table => fun state symbols => match state with
    | none => none
    | some (.inl localState) =>
      match MultiTape.wire (oneTape (inputTapes 0)) (StandardFixedRead.machine (inputs 0)) localState symbols with
      | some (next, actions) => some (some (.inl next), actions)
      | none => some ((entry (fun name => inputs name.succ) outputs).map (fun tail => .inr (localState.2, tail)),
          stationary symbols)
    | some (.inr (value, localState)) =>
      (machine (fun name => inputs name.succ) outputs ((Fin.succEmb _).trans inputTapes) outputTapes
        (fun values => table (Fin.cons value values)) (some localState) symbols).map
          (fun command => (command.1.map (fun tail => .inr (value, tail)), command.2))

/-- Neighboring symbols are retained when a table acts on an array block. -/
def block (contents left right : List Symbol) : Turing.Tape Symbol :=
  Turing.Tape.mk' (Turing.ListBlank.mk left) (Turing.ListBlank.mk (contents ++ right))

@[simp] theorem writer_halt (widths : Fin outputCount → ℕ) (tapes : Fin outputCount ↪ TapeName)
    (values : ∀ name, BitVec (widths name)) (symbols : Symbols (CallingConvention.Alphabet TapeName)) :
    writer widths tapes values none symbols = none := by cases outputCount <;> rfl

@[simp] theorem halt (inputs : Fin inputCount → ℕ) (outputs : Fin outputCount → ℕ)
    (inputTapes : Fin inputCount ↪ TapeName) (outputTapes : Fin outputCount ↪ TapeName)
    (table : Registers inputs → ∀ name, BitVec (outputs name))
    (symbols : Symbols (CallingConvention.Alphabet TapeName)) :
    machine inputs outputs inputTapes outputTapes table none symbols = none := by
  cases inputCount with
  | zero => exact writer_halt outputs outputTapes _ symbols
  | succ count => rfl

private theorem stationary_runs {Controller : Type}
    (program : Machine (CallingConvention.Alphabet TapeName) Controller)
    (width : TapeName → ℕ) (readOnly : TapeName → Bool)
    (initial : Tapes (CallingConvention.Alphabet TapeName)) (state next : Controller)
    (instruction : program state (MultiTape.read initial) = some (next, stationary (MultiTape.read initial))) :
    Runs width readOnly program 1 state (fun _ => 0) initial next (fun _ => 0) initial := by
  apply Runs.next instruction (by intro name premise; rfl)
  simpa only [stationary, displacement, add_zero, act_stationary] using
    Runs.zero (machine := program) next (fun _ => 0) initial

/-- Each output is written once, with arbitrary old contents and unchanged neighbors. -/
theorem writer_runs (outputs : Fin outputCount → ℕ) (tapes : Fin outputCount ↪ TapeName)
    (values : ∀ name, BitVec (outputs name)) (old : Fin outputCount → List Symbol)
    (oldLength : ∀ name, (old name).length = outputs name)
    (width : TapeName → ℕ) (readOnly : TapeName → Bool)
    (widthMatches : ∀ name, width (tapes name) = outputs name)
    (writable : ∀ name, readOnly (tapes name) = false)
    (left right : TapeName → List Symbol) (initial : Tapes (CallingConvention.Alphabet TapeName))
    (represented : ∀ name, initial (tapes name) = block (old name) (left (tapes name)) (right (tapes name))) :
    ∃ final, Runs width readOnly (writer outputs tapes values) (cost outputs)
      (writeEntry outputs) (fun _ => 0) initial none (fun _ => 0) final ∧
      (∀ name, final (tapes name) = block (word (List.ofFn (fun index : Fin (outputs name) => (values name).getLsbD index.val)))
        (left (tapes name)) (right (tapes name))) ∧
      (∀ name, name ∉ Set.range tapes → final name = initial name) := by
  classical
  induction outputCount generalizing initial with
  | zero =>
    refine ⟨initial, ?_, (by intro name; exact Fin.elim0 name), (by intro name outside; rfl)⟩
    simpa [writer, cost, writeEntry] using Runs.zero (machine := writer outputs tapes values) none (fun _ => 0) initial
  | succ count hypothesis =>
    let expected := block (word (List.ofFn (fun index : Fin (outputs 0) => (values 0).getLsbD index.val)))
      (left (tapes 0)) (right (tapes 0))
    let middle := Function.update initial (tapes 0) expected
    have written := (StandardConstant.ofBitVec_runsWithContext (values 0) (old 0) (oldLength 0)
      (left (tapes 0)) (right (tapes 0))).wire_of_eq (oneTape (tapes 0)) width readOnly
      (by intro name; exact widthMatches 0)
      (by intro name premise; change readOnly (tapes 0) = true at premise; rw [writable 0] at premise; contradiction)
      initial middle (by intro name; exact represented 0) (by intro name; exact Function.update_self _ _ _)
      (by intro name outside; apply Function.update_of_ne; intro equal; exact outside ⟨(), equal.symm⟩)
    have lifted := written.rename (fun state => some (Sum.inl state)) (target := writer outputs tapes values)
      (by intro state symbols next actions instruction; simp [writer, instruction])
    have handover := stationary_runs (writer outputs tapes values) width readOnly middle
      (some (.inl (true, 0))) ((writeEntry (fun name => outputs name.succ)).map Sum.inr)
      (by simp [writer, MultiTape.wire, StandardConstant.ofBitVec, StandardConstant.machineSized])
    obtain ⟨final, tailTrace, tailResults, tailOutside⟩ := hypothesis (fun name => outputs name.succ)
      ((Fin.succEmb count).trans tapes) (fun name => values name.succ) (fun name => old name.succ)
      (fun name => oldLength name.succ) (fun name => widthMatches name.succ) (fun name => writable name.succ)
      middle (by
        intro name
        dsimp only [middle, Function.Embedding.trans_apply, Fin.succEmb]
        rw [Function.update_of_ne (by intro equal; have same := tapes.injective equal; exact Fin.succ_ne_zero _ same)]
        exact represented name.succ)
    have tailLifted := tailTrace.rename (Option.map Sum.inr) (target := writer outputs tapes values) (by
      intro state symbols next actions instruction
      cases state with
      | none => simp at instruction
      | some state => change (writer _ _ _ (some state) symbols).map _ = _; rw [instruction]; rfl)
    refine ⟨final, ?_, ?_, ?_⟩
    · have complete := lifted.trans (handover.trans tailLifted)
      convert complete using 1 <;> first | rfl | (simp only [cost, Fin.sum_univ_succ]; omega)
    · intro name
      refine Fin.cases ?_ (fun name => tailResults name) name
      exact (tailOutside (tapes 0) (by
        rintro ⟨name, equal⟩
        exact Fin.succ_ne_zero name (tapes.injective equal))).trans (Function.update_self _ _ _)
    · intro name outside
      rw [tailOutside name (by rintro ⟨localName, equal⟩; exact outside ⟨localName.succ, equal⟩)]
      apply Function.update_of_ne
      intro equal
      exact outside ⟨0, equal.symm⟩

/-- A finite family is read completely before any output is overwritten.
The cost includes all controller handovers, even for zero-width words. -/
theorem runsWithContext (inputs : Fin inputCount → ℕ) (outputs : Fin outputCount → ℕ)
    (inputTapes : Fin inputCount ↪ TapeName) (outputTapes : Fin outputCount ↪ TapeName)
    (table : Registers inputs → ∀ name, BitVec (outputs name))
    (bits : Fin inputCount → List Bool) (bitsLength : ∀ name, (bits name).length = inputs name)
    (old : Fin outputCount → List Symbol) (oldLength : ∀ name, (old name).length = outputs name)
    (width : TapeName → ℕ) (readOnly : TapeName → Bool)
    (inputWidths : ∀ name, width (inputTapes name) = inputs name)
    (outputWidths : ∀ name, width (outputTapes name) = outputs name)
    (writable : ∀ name, readOnly (outputTapes name) = false)
    (left right : TapeName → List Symbol) (initial : Tapes (CallingConvention.Alphabet TapeName))
    (inputMatches : ∀ name, initial (inputTapes name) = block (word (bits name))
      (left (inputTapes name)) (right (inputTapes name)))
    (outputMatches : ∀ name, initial (outputTapes name) = block (old name)
      (left (outputTapes name)) (right (outputTapes name))) :
    let registers : Registers inputs := fun name index => ((bits name)[index.val]?).getD false
    ∃ final, Runs width readOnly (machine inputs outputs inputTapes outputTapes table)
      (cost inputs + cost outputs) (entry inputs outputs) (fun _ => 0) initial none (fun _ => 0) final ∧
      (∀ name, final (outputTapes name) = block
        (word (List.ofFn (fun index : Fin (outputs name) => (table registers name).getLsbD index.val)))
        (left (outputTapes name)) (right (outputTapes name))) ∧
      (∀ name, name ∉ Set.range outputTapes → final name = initial name) := by
  intro registers
  induction inputCount with
  | zero =>
    have registerEq : registers = fun name => Fin.elim0 name := by funext name; exact Fin.elim0 name
    rw [registerEq]
    convert writer_runs outputs outputTapes (table (fun name => Fin.elim0 name)) old oldLength width readOnly
      outputWidths writable left right initial outputMatches using 1
    first | rfl | (simp [cost, machine, entry]; rfl)
  | succ count hypothesis =>
    let head : StandardFixedRead.Memory (inputs 0) := fun index => ((bits 0)[index.val]?).getD false
    have readHead := (StandardFixedRead.runsWithContext (inputs 0) (bits 0) (bitsLength 0)
      (fun _ => false) (left (inputTapes 0)) (right (inputTapes 0))).wire_of_eq
      (oneTape (inputTapes 0)) width readOnly (by intro name; exact inputWidths 0)
      (by intro name premise; rfl) initial initial
      (by intro name; exact inputMatches 0) (by intro name; exact inputMatches 0)
      (by intro name outside; rfl)
    have lifted := readHead.rename (fun state => some (Sum.inl state))
      (target := machine inputs outputs inputTapes outputTapes table)
      (by intro state symbols next actions instruction; simp [machine, instruction])
    let embed : State (fun name => inputs name.succ) outputs → State inputs outputs := Option.map (fun tail : Active (fun name => inputs name.succ) outputs => Sum.inr (head, tail))
    have handover := stationary_runs (machine inputs outputs inputTapes outputTapes table) width readOnly initial
      (some (.inl ((true, 0), head))) (embed (entry (fun name => inputs name.succ) outputs))
      (by simp [machine, MultiTape.wire, StandardFixedRead.machine, embed])
    obtain ⟨final, tailTrace, results, outside⟩ := hypothesis (fun name => inputs name.succ)
      ((Fin.succEmb count).trans inputTapes) (fun values => table (Fin.cons head values))
      (fun name => bits name.succ) (fun name => bitsLength name.succ) (fun name => inputWidths name.succ)
      (fun name => inputMatches name.succ)
    have tailLifted := tailTrace.rename embed (target := machine inputs outputs inputTapes outputTapes table) (by
      intro state symbols next actions instruction
      cases state with
      | none => simp at instruction
      | some state => change (machine _ _ _ _ _ (some state) symbols).map _ = _; rw [instruction]; rfl)
    have registerEq : Fin.cons head (fun name index => ((bits name.succ)[index.val]?).getD false) = registers := by
      funext name
      refine Fin.cases rfl (fun name => rfl) name
    refine ⟨final, ?_, ?_, outside⟩
    · have complete := lifted.trans (handover.trans tailLifted)
      convert complete using 1 <;> first | rfl | (simp only [cost, Fin.sum_univ_succ]; omega)
    · simpa only [registerEq] using results

-- carrierLevel: mathematical carriers of the specialization-fixed domains.
universe carrierLevel

/-- Decode all input registers, then apply the mathematical family operation.
Unused binary labels have arbitrary output words. -/
noncomputable def encodedTable (inputs : Fin inputCount → EncodedDomain.{0, carrierLevel} Empty)
    (outputs : Fin outputCount → EncodedDomain.{0, carrierLevel} Empty)
    (operation : ∀ sizes, (∀ name, (inputs name).Carrier sizes) → ∀ name, (outputs name).Carrier sizes) :
    Registers (fun name => (inputs name).width Empty.elim) → ∀ name, BitVec ((outputs name).width Empty.elim) := by
  classical
  exact fun registers => if decoded : ∀ name, ∃ value, (inputs name).decode Empty.elim
      (BitVec.ofNat _ (Binary.value (List.ofFn (registers name)))) = some value then
    fun name => (outputs name).encode Empty.elim
      (operation Empty.elim (fun name => Classical.choose (decoded name)) name)
  else fun _ => 0

/-- Canonical encodings select the intended mathematical table entry. -/
theorem encodedTable_encode (inputs : Fin inputCount → EncodedDomain.{0, carrierLevel} Empty)
    (outputs : Fin outputCount → EncodedDomain.{0, carrierLevel} Empty)
    (operation : ∀ sizes, (∀ name, (inputs name).Carrier sizes) → ∀ name, (outputs name).Carrier sizes)
    (values : ∀ name, (inputs name).Carrier Empty.elim) :
    encodedTable inputs outputs operation
      (fun name index => ((inputs name).encode Empty.elim (values name)).getLsbD index.val) =
      fun name => (outputs name).encode Empty.elim (operation Empty.elim values name) := by
  classical
  have roundtrip (name : Fin inputCount) : (inputs name).decode Empty.elim
      (BitVec.ofNat _ (Binary.value (List.ofFn
        (fun index : Fin ((inputs name).width Empty.elim) =>
          ((inputs name).encode Empty.elim (values name)).getLsbD index.val)))) = some (values name) := by
    simp only [Binary.value_bits, BitVec.ofNat_toNat, BitVec.setWidth_eq, EncodedDomain.decode_encode]
  rw [encodedTable, dite_eq_left (fun name => ⟨values name, roundtrip name⟩)]
  have selected : (fun name => Classical.choose (show ∃ value, (inputs name).decode Empty.elim
      (BitVec.ofNat _ (Binary.value (List.ofFn
        (fun index : Fin ((inputs name).width Empty.elim) =>
          ((inputs name).encode Empty.elim (values name)).getLsbD index.val)))) = some value from
      ⟨values name, roundtrip name⟩)) = values := by
    funext name
    apply Option.some.inj
    exact (Classical.choose_spec (show ∃ value, _ = some value from
      ⟨values name, roundtrip name⟩)).symm.trans (roundtrip name)
  rw [selected]

def domains (inputs : Fin inputCount → EncodedDomain.{0, carrierLevel} Empty)
    (outputs : Fin outputCount → EncodedDomain.{0, carrierLevel} Empty) :
    Fin inputCount ⊕ Fin outputCount → EncodedDomain Empty := Sum.elim inputs outputs

abbrev readOnly : Fin inputCount ⊕ Fin outputCount → Bool
  | .inl _ => true
  | .inr _ => false

def sizeTapes : Empty ↪ (Fin inputCount ⊕ Fin outputCount) := ⟨Empty.elim, by intro parameter; cases parameter⟩
def outputTapes : Fin outputCount ↪ (Fin inputCount ⊕ Fin outputCount) := Function.Embedding.inr

noncomputable def algorithm (inputs : Fin inputCount → EncodedDomain.{0, carrierLevel} Empty)
    (outputs : Fin outputCount → EncodedDomain.{0, carrierLevel} Empty)
    (operation : ∀ sizes, (∀ name, (inputs name).Carrier sizes) → ∀ name, (outputs name).Carrier sizes) :=
  machine (fun name => (inputs name).width Empty.elim) (fun name => (outputs name).width Empty.elim)
    Function.Embedding.inl Function.Embedding.inr (encodedTable inputs outputs operation)

/-- Every operation on fixed encoded families has a finite table realization.
There are exactly the declared argument and result tapes, with no scratch. -/
theorem contract (inputs : Fin inputCount → EncodedDomain.{0, carrierLevel} Empty)
    (outputs : Fin outputCount → EncodedDomain.{0, carrierLevel} Empty)
    (operation : ∀ sizes, (∀ name, (inputs name).Carrier sizes) → ∀ name, (outputs name).Carrier sizes) :
    CallingConvention.Realizes (domains inputs outputs) readOnly sizeTapes outputTapes
      (algorithm inputs outputs operation)
      (entry (fun name => (inputs name).width Empty.elim) (fun name => (outputs name).width Empty.elim)) none
      (fun _ _ => True)
      (fun sizes input output => output = operation sizes (fun name => input ⟨.inl name, rfl⟩)) := by
  classical
  let inputWidths := fun name => (inputs name).width Empty.elim
  let outputWidths := fun name => (outputs name).width Empty.elim
  refine ⟨(by intro parameter; cases parameter), (by intro name; rfl), (by intro symbols; apply halt),
    MvPolynomial.C (cost inputWidths + cost outputWidths), ?_⟩
  intro sizes input initial valid represented headers
  have sameSizes : sizes = (Empty.elim : Empty → ℕ) := Subsingleton.elim _ _
  subst sizes
  let values : ∀ name : Fin inputCount, (inputs name).Carrier Empty.elim :=
    fun name => input ⟨Sum.inl name, rfl⟩
  let bits := fun name => List.ofFn (fun index : Fin (inputWidths name) =>
    ((inputs name).encode Empty.elim (values name)).getLsbD index.val)
  choose old oldLength oldEq using fun name => represented.2 (Sum.inr name) rfl
  obtain ⟨final, trace, canonical, outside⟩ := runsWithContext inputWidths outputWidths
    Function.Embedding.inl Function.Embedding.inr (encodedTable inputs outputs operation)
    bits (fun _ => List.length_ofFn) old oldLength
    (fun name => (domains inputs outputs name).width Empty.elim) readOnly
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => [0]) (fun _ => [0]) initial
    (by
      intro name
      change initial (.inl name) = _
      have canonicalInput := represented.1 (Sum.inl name) rfl
      change initial (.inl name) = encoded (inputs name) Empty.elim (values name) at canonicalInput
      simpa only [block, buffer_padding, bits, inputWidths, encoded, tape, buffer, EncodedDomain.ArrayEncoding.bits] using canonicalInput)
    (by intro name; change initial (.inr name) = _; simpa only [block, buffer_padding] using oldEq name)
  have registers : (fun (name : Fin inputCount) (index : Fin (inputWidths name)) => ((bits name)[index.val]?).getD false) =
      fun (name : Fin inputCount) (index : Fin (inputWidths name)) => ((inputs name).encode Empty.elim (values name)).getLsbD index.val := by
    funext name index; simp [bits]
  rw [registers, encodedTable_encode] at canonical
  refine ⟨cost inputWidths + cost outputWidths, operation Empty.elim values, final, by simp, trace, rfl, ?_⟩
  intro name
  change final (.inr name) = encoded (outputs name) Empty.elim _
  have result := canonical name
  change final (.inr name) = block _ [0] [0] at result
  rw [block, buffer_padding] at result
  exact result

end Polytime2.FiniteTable
