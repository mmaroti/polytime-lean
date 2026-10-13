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

import Polytime2.StandardTerminatedCopy
import Polytime2.StandardConstant
import Polytime2.StandardBinaryScan
import Polytime2.CallingConventionRegions

/-! # Restoring copy and clear commands in a caller's tape collection

Only the destination is changed. Its fixed region may initially contain any
symbols, including blanks. Source widths come from canonical input words.
-/

namespace Polytime2.StandardTapeCommands

open MultiTape CallingConvention
open Binary (Symbol word)

-- tapeLevel: names of the caller's tapes.
universe tapeLevel
variable {TapeName : Type tapeLevel} [DecidableEq TapeName]

noncomputable def copy (source target : TapeName) (distinct : source ≠ target) :
    Machine (CallingConvention.Alphabet TapeName) (Fin 3) :=
  MultiTape.wire (twoTapes source target distinct) StandardTerminatedCopy.machine

/-- Copying preserves all tapes except its destination, including the source. -/
theorem copy_runs (source target : TapeName) (distinct : source ≠ target)
    (width : TapeName → ℕ) (readOnly : TapeName → Bool)
    (writable : readOnly target = false) (bits : List Bool) (old : List Symbol)
    (sourceWidth : width source = bits.length) (targetWidth : width target = bits.length)
    (oldLength : old.length = bits.length) (initial : Tapes (CallingConvention.Alphabet TapeName))
    (sourceEq : initial source = buffer (word bits)) (targetEq : initial target = buffer old) :
    Runs width readOnly (copy source target distinct) (2 * bits.length + 2)
      0 (fun _ => 0) initial 2 (fun _ => 0)
      (Function.update initial target (buffer (word bits))) := by
  apply (StandardTerminatedCopy.runs bits old oldLength).wire_of_eq
    (twoTapes source target distinct) width readOnly
  · intro name
    cases name <;> simp [sourceWidth, targetWidth]
  · intro name premise
    cases name
    · rfl
    · simp [writable] at premise
  · intro name
    cases name
    · exact sourceEq.trans (buffer_padding (word bits)).symm
    · exact targetEq.trans (buffer_padding old).symm
  · intro name
    cases name
    · simp only [twoTapes_false, Function.update_of_ne distinct]
      exact sourceEq.trans (buffer_padding (word bits)).symm
    · simp only [twoTapes_true, Function.update_self]
      exact (buffer_padding (word bits)).symm
  · intro name outside
    have different : name ≠ target := by
      intro equal
      subst name
      exact outside ⟨true, rfl⟩
    exact Function.update_of_ne different _ _

-- parameterLevel: size names; carrierLevel: mathematical values being copied.
universe parameterLevel carrierLevel

/-- Internal copies need only a valid source and the destination's preserved
region. Previous destination contents need not represent any mathematical value. -/
theorem copy_encoded_runs {Parameter : Type parameterLevel} [Fintype Parameter]
    (domain : EncodedDomain.{parameterLevel, carrierLevel} Parameter)
    (sizes : Parameter → ℕ) (value : domain.Carrier sizes)
    (source target : TapeName) (distinct : source ≠ target)
    (width : TapeName → ℕ) (readOnly : TapeName → Bool)
    (writable : readOnly target = false)
    (sourceWidth : width source = domain.width sizes)
    (targetWidth : width target = domain.width sizes)
    (initial : Tapes (CallingConvention.Alphabet TapeName))
    (sourceEq : initial source = encoded domain sizes value)
    (targetRegion : Region (width target) 0 (initial target)) :
    Runs width readOnly (copy source target distinct) (2 * domain.width sizes + 2)
      0 (fun _ => 0) initial 2 (fun _ => 0)
      (Function.update initial target (encoded domain sizes value)) := by
  let bits := List.ofFn (fun index : Fin (domain.width sizes) =>
    (domain.encode sizes value).getLsbD index.val)
  have length : bits.length = domain.width sizes := List.length_ofFn
  obtain ⟨old, oldLength, targetEq⟩ := targetRegion.exists_buffer
  simpa only [length, bits, encoded, CallingConvention.tape, buffer] using
    copy_runs source target distinct width readOnly writable bits old
    (sourceWidth.trans length.symm) (targetWidth.trans length.symm)
    (oldLength.trans (targetWidth.trans length.symm)) initial sourceEq targetEq

noncomputable def clear (source target : TapeName) (distinct : source ≠ target) :
    Machine (CallingConvention.Alphabet TapeName) (StandardBinaryScan.State Unit) :=
  MultiTape.wire (twoTapes source target distinct) (StandardBinaryScan.machine BinaryScan.clear)

/-- Clearing derives its extent from an immutable canonical source, even if
all destination cells are initially blank. -/
theorem clear_runs (source target : TapeName) (distinct : source ≠ target)
    (width : TapeName → ℕ) (readOnly : TapeName → Bool)
    (writable : readOnly target = false) (bits : List Bool) (old : List Symbol)
    (sourceWidth : width source = bits.length) (targetWidth : width target = bits.length)
    (oldLength : old.length = bits.length) (initial : Tapes (CallingConvention.Alphabet TapeName))
    (sourceEq : initial source = buffer (word bits)) (targetEq : initial target = buffer old) :
    Runs width readOnly (clear source target distinct) (2 * bits.length + 2)
      (.inl ()) (fun _ => 0) initial (.inr ((), true)) (fun _ => 0)
      (Function.update initial target (buffer (word (List.replicate bits.length false)))) := by
  have trace := StandardBinaryScan.runs BinaryScan.clear () bits old oldLength
  simp only [StandardBinaryScan.run, BinaryScan.clear_run] at trace
  apply trace.wire_of_eq (twoTapes source target distinct) width readOnly
  · intro name
    cases name <;> simp [sourceWidth, targetWidth]
  · intro name premise
    cases name
    · rfl
    · simp [writable] at premise
  · intro name
    cases name
    · exact sourceEq.trans (buffer_padding (word bits)).symm
    · exact targetEq.trans (buffer_padding old).symm
  · intro name
    cases name
    · simp only [twoTapes_false, Function.update_of_ne distinct]
      exact sourceEq.trans (buffer_padding (word bits)).symm
    · simp only [twoTapes_true, Function.update_self]
      exact (buffer_padding (word (List.replicate bits.length false))).symm
  · intro name outside
    have different : name ≠ target := by
      intro equal
      subst name
      exact outside ⟨true, rfl⟩
    exact Function.update_of_ne different _ _

/-- Write a specialization-fixed word without a prepared source tape. -/
noncomputable def setConstant (target : TapeName) (bits : List Bool) :
    Machine (CallingConvention.Alphabet TapeName) (Copy.State bits.length) :=
  MultiTape.wire (oneTape target) (StandardConstant.machine bits)

/-- Field constants and fixed tables overwrite arbitrary contents, preserving
all other tapes and restoring the destination head. -/
theorem setConstant_runs (target : TapeName) (bits : List Bool)
    (width : TapeName → ℕ) (readOnly : TapeName → Bool)
    (writable : readOnly target = false) (targetWidth : width target = bits.length)
    (initial : Tapes (CallingConvention.Alphabet TapeName)) (old : List Symbol)
    (oldLength : old.length = bits.length) (targetEq : initial target = buffer old) :
    Runs width readOnly (setConstant target bits) (2 * bits.length + 1)
      (false, Fin.last bits.length) (fun _ => 0) initial (true, 0) (fun _ => 0)
      (Function.update initial target (buffer (word bits))) := by
  apply (StandardConstant.runs bits old oldLength).wire_of_eq (oneTape target) width readOnly
  · intro name
    exact targetWidth
  · intro name premise
    simpa only [oneTape_apply, writable] using premise
  · intro name
    exact targetEq
  · intro name
    exact Function.update_self target _ _
  · intro name outside
    have different : name ≠ target := by
      intro equal
      subst name
      exact outside ⟨(), rfl⟩
    exact Function.update_of_ne different _ _

/-- A constant Boolean writes its only data cell and immediately returns. -/
def booleanMachine (bit : Bool) : Machine (CallingConvention.Alphabet Unit) Bool
  | false, _ => some (true, fun _ => (Binary.data bit, none))
  | true, _ => none

private theorem boolean_runs (bit : Bool) (old : Symbol) :
    Runs (fun _ : Unit => 1) (fun _ => false) (booleanMachine bit) 1
      false (fun _ => 0) (fun _ => buffer [old]) true (fun _ => 0) (fun _ => buffer [Binary.data bit]) := by
  apply Runs.next (nextState := true) (actions := fun _ => (Binary.data bit, none)) rfl
    (by intro name premise; simp at premise)
  have tapes : act (fun _ : Unit => (Binary.data bit, none)) (fun _ => buffer [old]) =
      fun _ : Unit => buffer [Binary.data bit] := by
    funext name
    simp [act, buffer, Turing.Tape.mk₁, Turing.Tape.mk₂, Turing.Tape.write_mk']
  simpa only [displacement, add_zero, tapes] using
    (Runs.zero (machine := booleanMachine bit) true (fun _ => 0) (fun _ : Unit => buffer [Binary.data bit]))

noncomputable def setBoolean (target : TapeName) (bit : Bool) :
    Machine (CallingConvention.Alphabet TapeName) Bool :=
  MultiTape.wire (oneTape target) (booleanMachine bit)

/-- Constant initialization needs no prepared source tape. It writes only its
one-bit destination, preserving all other tapes and surrounding blanks. -/
theorem setBoolean_runs (target : TapeName) (bit : Bool)
    (width : TapeName → ℕ) (readOnly : TapeName → Bool)
    (writable : readOnly target = false) (targetWidth : width target = 1)
    (initial : Tapes (CallingConvention.Alphabet TapeName)) (old : Symbol)
    (targetEq : initial target = buffer [old]) :
    Runs width readOnly (setBoolean target bit) 1 false (fun _ => 0) initial true (fun _ => 0)
      (Function.update initial target (buffer [Binary.data bit])) := by
  apply (boolean_runs bit old).wire_of_eq (oneTape target) width readOnly
  · intro name
    exact targetWidth
  · intro name premise
    simpa only [oneTape_apply, writable] using premise
  · intro name
    exact targetEq
  · intro name
    exact Function.update_self target _ _
  · intro name outside
    have different : name ≠ target := by
      intro equal
      subst name
      exact outside ⟨(), rfl⟩
    exact Function.update_of_ne different _ _

/-- The standalone Boolean command satisfies the complete encoded-domain
calling convention, including arbitrary initial output contents. -/
def booleanDomains : Unit → EncodedDomain Empty := fun _ => EncodedDomain.booleans

def noSizeTapes : Empty ↪ Unit :=
  ⟨Empty.elim, by intro parameter; cases parameter⟩

noncomputable def booleanAlgorithm (bit : Bool) :
    Machine (CallingConvention.Alphabet Unit) Bool := setBoolean () bit

theorem booleanContract (bit : Bool) :
    CallingConvention.Realizes booleanDomains (fun _ => false) noSizeTapes
      (booleanAlgorithm bit) false true
      (fun _ _ => True)
      (fun _ _ output => output ⟨(), rfl⟩ = bit) := by
  refine ⟨(by intro parameter; cases parameter), ?_, MvPolynomial.C 1, ?_⟩
  · intro symbols
    simp [booleanAlgorithm, setBoolean, booleanMachine, MultiTape.wire]
  · intro assignment input initial valid represented sizes
    obtain ⟨old, oldLength, oldEq⟩ := represented.2 () rfl
    have domainWidth : (booleanDomains ()).width assignment = 1 := by
      norm_num [booleanDomains, EncodedDomain.booleans, EncodedDomain.fixed,
        finTwoEquiv]
    have width : old.length = 1 := by
      rw [domainWidth] at oldLength
      exact oldLength
    obtain ⟨oldBit, rfl⟩ := List.length_eq_one_iff.mp width
    have localTrace := boolean_runs bit oldBit
    have trace := localTrace.wire_of_eq (oneTape ()) (fun _ : Unit => 1)
      (fun _ => false) (by intro name; rfl) (by intro name premise; exact premise)
      (fun _ => buffer [oldBit]) (fun _ => buffer [Binary.data bit])
      (by intro name; rfl) (by intro name; rfl)
      (by intro name outside; exact False.elim (outside ⟨(), rfl⟩))
    have initialEq : initial = fun _ : Unit => buffer [oldBit] := by
      funext name
      have equal : name = () := Subsingleton.elim _ _
      subst name
      exact oldEq
    refine ⟨1, (fun _ => bit), (fun _ => buffer [Binary.data bit]),
      ?_, ?_, rfl, ?_⟩
    · norm_num [MvPolynomial.eval]
    · rw [initialEq]
      have widths : (fun name : Unit => (booleanDomains name).width assignment) =
          fun _ => 1 := by
        funext name
        exact domainWidth
      rw [widths]
      simpa [booleanAlgorithm, setBoolean] using trace
    · intro name writable
      have equal : name = () := Subsingleton.elim _ _
      subst name
      simpa [booleanDomains] using
        (CallingConvention.encoded_booleans assignment bit).symm

end Polytime2.StandardTapeCommands
