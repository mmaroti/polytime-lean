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

import Polytime2.Arithmetic.BinaryDivision
import Polytime2.Primitives.Join
import Polytime2.Encoding.Records

/-! # Packing both division results into their canonical pair encoding

The long-division pass runs once. The existing field joiner concatenates its
quotient and remainder words into the public product domain.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.StandardBinaryDivision.Packed

open MultiTape CallingConvention
open Binary (word value)

noncomputable def domains : Unit ⊕ Fin 9 → EncodedDomain Unit
  | .inl parameter => EncodedDomain.unary parameter
  | .inr name => if name = 8 then
      (EncodedDomain.binaryNaturals ()).prod (EncodedDomain.binaryNaturals ())
    else if name = 4 then EncodedDomain.booleans else EncodedDomain.binaryNaturals ()

def readOnly : Unit ⊕ Fin 9 → Bool
  | .inl _ => true
  | .inr name => decide (name = 1 ∨ name = 6)

def dataTapes : Fin 8 ↪ Unit ⊕ Fin 9 :=
  ⟨(fun name => .inr ⟨name.val, by omega⟩), by
    intro first second equal
    exact Fin.ext (congrArg (fun name : Unit ⊕ Fin 9 =>
      match name with | .inl _ => 0 | .inr index => index.val) equal)⟩

@[simp] theorem dataTapes_apply (name : Fin 8) : dataTapes name = .inr ⟨name.val, by omega⟩ := rfl

def joinTapes : Join.TapeName 2 ↪ Unit ⊕ Fin 9 :=
  ⟨(fun name => match name with
      | .inl index => if index = 0 then .inr 7 else .inr 0
      | .inr _ => .inr 8), by
    intro first second equal
    fin_cases first <;> fin_cases second <;> simp_all⟩

@[simp] theorem joinTapes_left (index : Fin 2) :
    joinTapes (.inl index) = if index = 0 then .inr 7 else .inr 0 := rfl
@[simp] theorem joinTapes_right (name : Unit) : joinTapes (.inr name) = .inr 8 := rfl

def sizeTapes : Unit ↪ Unit ⊕ Fin 9 := ⟨Sum.inl, Sum.inl_injective⟩
def outputTapes : Unit ↪ Unit ⊕ Fin 9 := oneTape (.inr 8)

abbrev JoinState :=
  Pipeline.State (fun _ : Fin 2 => Bool ⊕ (Fin 2 ⊕ Fin 3)) ⊕ (Fin 2 ⊕ Fin 3)
abbrev State := Sum StandardBinaryDivision.State JoinState

noncomputable def divide : Machine (CallingConvention.Alphabet (Unit ⊕ Fin 9)) StandardBinaryDivision.State :=
  wire dataTapes StandardBinaryDivision.machine
noncomputable def join : Machine (CallingConvention.Alphabet (Unit ⊕ Fin 9)) JoinState := wire joinTapes Join.machine
noncomputable def algorithm : Machine (CallingConvention.Alphabet (Unit ⊕ Fin 9)) State :=
  MultiTape.sequence divide join Join.entry

def entry : State := .inl StandardBinaryDivision.entry
def exit : State := .inr Join.exit

/-- Both exact-width results are returned together after one long-division pass. -/
theorem contract : CallingConvention.Realizes domains readOnly sizeTapes outputTapes algorithm entry exit
    (fun sizes input =>
      0 < (input ⟨.inr 1, rfl⟩ : Fin (2 ^ sizes ())).val ∧
      2 * (input ⟨.inr 1, rfl⟩ : Fin (2 ^ sizes ())).val ≤ 2 ^ sizes ())
    (fun sizes input output =>
      (output () : Fin (2 ^ sizes ()) × Fin (2 ^ sizes ())).1.val =
          (input ⟨.inr 6, rfl⟩ : Fin (2 ^ sizes ())).val /
            (input ⟨.inr 1, rfl⟩ : Fin (2 ^ sizes ())).val ∧
      (output () : Fin (2 ^ sizes ()) × Fin (2 ^ sizes ())).2.val =
          (input ⟨.inr 6, rfl⟩ : Fin (2 ^ sizes ())).val %
            (input ⟨.inr 1, rfl⟩ : Fin (2 ^ sizes ())).val) := by
  refine ⟨(by intro parameter; rfl), (by intro name; rfl),
    (by intro symbols; simp [algorithm, exit, MultiTape.sequence, join, wire, Join.halt]),
    12 * MvPolynomial.X () ^ 2 + 39 * MvPolynomial.X () + 26, ?_⟩
  intro sizes input initial valid represented headers
  let dividend := List.ofFn (fun index : Fin (sizes ()) =>
    (BitVec.ofFin (input ⟨.inr 6, rfl⟩)).getLsbD index.val)
  let divisor := List.ofFn (fun index : Fin (sizes ()) =>
    (BitVec.ofFin (input ⟨.inr 1, rfl⟩)).getLsbD index.val)
  have dividendLength : dividend.length = sizes () := List.length_ofFn
  have divisorLength : divisor.length = sizes () := List.length_ofFn
  have dividendValue : value dividend = (input ⟨.inr 6, rfl⟩ : Fin (2 ^ sizes ())).val :=
    Binary.value_bits (BitVec.ofFin (input ⟨.inr 6, rfl⟩))
  have divisorValue : value divisor = (input ⟨.inr 1, rfl⟩ : Fin (2 ^ sizes ())).val :=
    Binary.value_bits (BitVec.ofFin (input ⟨.inr 1, rfl⟩))
  have widthsMatch : ∀ name, (domains (dataTapes name)).width sizes =
      StandardBinaryDivision.widths dividend.length divisor.length name := by
    intro name
    fin_cases name <;> norm_num [dataTapes_apply, domains, StandardBinaryDivision.widths,
      dividendLength, divisorLength, EncodedDomain.booleans, EncodedDomain.fixed]
  obtain ⟨localFinal, localTrace, quotientEq, remainderEq⟩ :=
    StandardBinaryDivision.runs dividend divisor (fun name => initial (dataTapes name))
      ((represented.1 (.inr 6) rfl).trans (encoded_binaryNaturals_value () sizes _))
      ((represented.1 (.inr 1) rfl).trans (encoded_binaryNaturals_value () sizes _))
      (by intro name; rw [← widthsMatch]; exact represented.region (dataTapes name))
  obtain ⟨after, first, located, outside, immutable⟩ := localTrace.wire_restoring dataTapes
    (fun name => (domains name).width sizes) readOnly widthsMatch
    (by intro name premise; fin_cases name <;> simp_all [dataTapes_apply, readOnly, StandardBinaryDivision.readOnly])
    initial (fun _ => rfl)
  let answer := finish divisor dividend.reverse
    (List.replicate divisor.length false, List.replicate divisor.length false)
  have lengths := finish_lengths divisor dividend.reverse
    (List.replicate divisor.length false, List.replicate divisor.length false)
    List.length_replicate List.length_replicate
  have quotientLength : answer.1.length = sizes () := lengths.1.trans divisorLength
  have remainderLength : answer.2.length = sizes () := lengths.2.trans divisorLength
  let words : Fin 2 → List Bool := ![answer.1, answer.2]
  have totalLength : (List.ofFn words).flatten.length = 2 * sizes () := by
    simp [words, List.ofFn_succ, quotientLength, remainderLength]
    omega
  obtain ⟨old, oldLength, oldEq⟩ := (first.region (.inr 8) (represented.region (.inr 8))).exists_buffer
  have oldFits : old.length = (List.ofFn words).flatten.length := by
    rw [totalLength]
    simp [domains, EncodedDomain.width, EncodedDomain.binaryNaturals, EncodedDomain.ofCodec] at oldLength
    omega
  obtain ⟨joinTicks, joinCost, joinTrace⟩ := Join.runs words old oldFits
  have joinWidths : ∀ name, (domains (joinTapes name)).width sizes = Join.widths words name := by
    intro name
    fin_cases name <;> simp [domains, joinTapes_left, joinTapes_right, Join.widths, words, quotientLength,
      remainderLength, EncodedDomain.width, EncodedDomain.binaryNaturals, EncodedDomain.ofCodec,
      List.ofFn_succ]
  obtain ⟨final, joined, joinedLocated, joinedOutside, joinedImmutable⟩ := joinTrace.wire_restoring joinTapes
    (fun name => (domains name).width sizes) readOnly joinWidths
    (by intro name premise; fin_cases name <;> simp_all [readOnly, joinTapes_left, joinTapes_right, Join.readOnly]) after
    (by
      intro name
      fin_cases name
      · exact (located 7).trans quotientEq
      · exact (located 0).trans remainderEq
      · simpa [Join.frame, Join.prefixBits, joinTapes_right, buffer, word, Turing.Tape.mk₁, Turing.Tape.mk₂, Binary.mk_append_blank] using oldEq)
  have complete := first.sequence join Join.entry
    (by intro symbols; simp [wire, StandardBinaryDivision.machine,
      StandardBinaryDivision.exit, MultiTape.sequence, StandardBinaryDivision.loopMachine,
      StandardBitFold.machine, StandardBitFold.exit]) joined
  have correct := result_value dividend divisor (by rw [divisorValue]; exact valid.1)
    (by rw [divisorValue, divisorLength]; exact valid.2)
    (by rw [divisorLength, dividendValue]; exact (input ⟨.inr 6, rfl⟩).isLt)
  let quotientValue : Fin (2 ^ sizes ()) := ⟨value answer.1,
    by simpa only [quotientLength] using Binary.value_lt_pow_length answer.1⟩
  let remainderValue : Fin (2 ^ sizes ()) := ⟨value answer.2,
    by simpa only [remainderLength] using Binary.value_lt_pow_length answer.2⟩
  refine ⟨_, (fun _ => (quotientValue, remainderValue)), final, ?_, complete, ?_, ?_⟩
  · simp only [map_add, map_mul, map_pow, map_ofNat, MvPolynomial.eval_X]
    rw [dividendLength, divisorLength]
    rw [totalLength] at joinCost
    nlinarith [joinCost]
  · simpa only [dividendValue, divisorValue] using correct
  · intro name
    cases name
    change final (.inr 8) = encoded ((EncodedDomain.binaryNaturals ()).prod
      (EncodedDomain.binaryNaturals ())) sizes (quotientValue, remainderValue)
    have bitsQuotient : EncodedDomain.ArrayEncoding.bits
        ((EncodedDomain.binaryNaturals ()).encode sizes quotientValue) = answer.1 := by
      simp only [EncodedDomain.binaryNaturals, EncodedDomain.ofCodec,
        EncodedDomain.ArrayEncoding.bits_cast]
      change List.ofFn (fun index : Fin (sizes ()) =>
        (BitVec.ofFin quotientValue).getLsbD index.val) = answer.1
      rw [← BitVec.ofNat_finVal]
      exact Binary.bits_value answer.1 quotientLength
    have bitsRemainder : EncodedDomain.ArrayEncoding.bits
        ((EncodedDomain.binaryNaturals ()).encode sizes remainderValue) = answer.2 := by
      simp only [EncodedDomain.binaryNaturals, EncodedDomain.ofCodec,
        EncodedDomain.ArrayEncoding.bits_cast]
      change List.ofFn (fun index : Fin (sizes ()) =>
        (BitVec.ofFin remainderValue).getLsbD index.val) = answer.2
      rw [← BitVec.ofNat_finVal]
      exact Binary.bits_value answer.2 remainderLength
    change final (.inr 8) = buffer (word (EncodedDomain.ArrayEncoding.bits
      (((EncodedDomain.binaryNaturals ()).prod (EncodedDomain.binaryNaturals ())).encode
        sizes (quotientValue, remainderValue))))
    rw [EncodedDomain.bits_prod_encode, bitsQuotient, bitsRemainder]
    have outputEq := joinedLocated (.inr ())
    change final (.inr 8) = buffer (word (List.ofFn words).flatten) at outputEq
    simpa [words, List.ofFn_succ] using outputEq

end Polytime2.StandardBinaryDivision.Packed
