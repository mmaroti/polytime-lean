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

import Polytime2.TableTraversal
import Polytime2.Binary
import Mathlib.Data.BitVec
import Mathlib.Data.Nat.Log

/-! # Fixed-width binary conversion for scalar streams

The binary tape is named `false` and the scalar tape `true`. A fixed-width
binary word is collected in finite controller memory and decoded by a fixed
table. Heads advance past one word and one scalar, preserving surrounding data.
Width and tables are specialization constants, not runtime registers.
-/

namespace Polytime2.ScalarCodec

open MultiTape

variable {Scalar : Type} {width : ℕ}

abbrev Alphabet (Scalar : Type) : Bool → Type
  | false => Binary.Symbol
  | true => TableTraversal.Symbol Scalar

instance (name : Bool) : Inhabited (Alphabet Scalar name) :=
  match name with
  | false => inferInstanceAs (Inhabited Binary.Symbol)
  | true => inferInstanceAs (Inhabited (TableTraversal.Symbol Scalar))

instance [Fintype Scalar] (name : Bool) : Fintype (Alphabet Scalar name) :=
  match name with
  | false => inferInstanceAs (Fintype Binary.Symbol)
  | true => inferInstanceAs (Fintype (TableTraversal.Symbol Scalar))

def frame (binaryLeft binaryRight : List Binary.Symbol)
    (scalarLeft scalarRight : List (TableTraversal.Symbol Scalar)) : Tapes (Alphabet Scalar)
  | false => Turing.Tape.mk' (Turing.ListBlank.mk binaryLeft) (Turing.ListBlank.mk binaryRight)
  | true => Turing.Tape.mk' (Turing.ListBlank.mk scalarLeft) (Turing.ListBlank.mk scalarRight)

/-- Reuse Lean's bit vectors; the controller stores their individual bits. -/
def bufferBits (buffer : Fin width → Bool) : BitVec width :=
  (BitVec.ofBoolListLE (List.ofFn buffer)).cast (by simp)

@[simp] theorem bufferBits_get (buffer : Fin width → Bool) (index : Fin width) :
    (bufferBits buffer).getLsbD index.val = buffer index := by
  simp only [bufferBits, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn, index.isLt, ↓reduceDIte, Option.getD_some]


/-- Canonical little-endian bits of one fixed-width scalar word. -/
def word (bits : BitVec width) : List Binary.Symbol :=
  Binary.word (List.ofFn (fun index : Fin width => bits.getLsbD index.val))

@[simp] theorem word_length (bits : BitVec width) : (word bits).length = width := by
  simp [word, Binary.word]

/-- Binary labels from a chosen fixed enumeration. -/
def represent {cardinality : ℕ} (enumeration : Scalar ≃ Fin cardinality) (value : Scalar) :
    BitVec (Nat.clog 2 cardinality) :=
  BitVec.ofNatLT (enumeration value).val
    (lt_of_lt_of_le (enumeration value).isLt (Nat.le_pow_clog (by decide) cardinality))

/-- Invalid binary labels are irrelevant under the input hypothesis. -/
def interpret {cardinality : ℕ} (enumeration : Scalar ≃ Fin cardinality) (fallback : Scalar)
    (bits : BitVec (Nat.clog 2 cardinality)) : Scalar :=
  if valid : bits.toNat < cardinality then enumeration.symm ⟨bits.toNat, valid⟩ else fallback

@[simp] theorem interpret_represent {cardinality : ℕ} (enumeration : Scalar ≃ Fin cardinality)
    (fallback value : Scalar) : interpret enumeration fallback (represent enumeration value) = value := by
  simp [interpret, represent, (enumeration value).isLt]

abbrev DecodeState (width : ℕ) := Sum (Fin (width + 1) × (Fin width → Bool)) Unit

def decodeMachine (decode : BitVec width → Scalar) : Machine (Alphabet Scalar) (DecodeState width)
  | .inl (position, buffer), symbols =>
    if valid : position.val < width then
      some (.inl (⟨position.val + 1, by omega⟩,
        Function.update buffer ⟨position.val, valid⟩ (decide (symbols false = 2))),
        fun name => match name with
        | false => (symbols false, some .right)
        | true => (symbols true, none))
    else some (.inr (), fun name => match name with
      | false => (symbols false, none)
      | true => (some (some (decode (bufferBits buffer))), some .right))
  | .inr (), _ => none

def decodeEntry (width : ℕ) : DecodeState width := .inl (0, fun _ => false)
def decodeExit (width : ℕ) : DecodeState width := .inr ()

private theorem suffix_steps (decode : BitVec width → Scalar) (bits : Fin width → Bool)
    (position : Fin (width + 1)) (buffer : Fin width → Bool)
    (known : ∀ index, index.val < position.val → buffer index = bits index)
    (binaryLeft binaryRight : List Binary.Symbol)
    (scalarLeft scalarRight : List (TableTraversal.Symbol Scalar)) (previous : TableTraversal.Symbol Scalar) :
    Steps (decodeMachine decode) (width - position.val + 1)
      (.inl (position, buffer), frame binaryLeft
        (Binary.word ((List.ofFn bits).drop position.val) ++ binaryRight) scalarLeft (previous :: scalarRight))
      (decodeExit width, frame
        ((Binary.word ((List.ofFn bits).drop position.val)).reverse ++ binaryLeft) binaryRight
        (some (some (decode (bufferBits bits))) :: scalarLeft) scalarRight) := by
  generalize ranking : width - position.val = remaining
  induction remaining using Nat.strong_induction_on generalizing position buffer binaryLeft with
  | h remaining hypothesis =>
    by_cases valid : position.val < width
    · let index : Fin width := ⟨position.val, valid⟩
      let nextPosition : Fin (width + 1) := ⟨position.val + 1, by omega⟩
      let nextBuffer := Function.update buffer index (bits index)
      have dropped : (List.ofFn bits).drop position.val =
          bits index :: (List.ofFn bits).drop (position.val + 1) := by
        have equation := List.drop_eq_getElem_cons (l := List.ofFn bits) (by simpa using valid)
        rw [List.getElem_ofFn] at equation
        exact equation
      have nextKnown : ∀ other, other.val < nextPosition.val → nextBuffer other = bits other := by
        intro other earlier
        by_cases equal : other = index
        · subst other; simp [nextBuffer]
        · have different : other.val ≠ position.val := by
            intro equalValue; exact equal (Fin.ext equalValue)
          have smaller : other.val < position.val := by dsimp [nextPosition] at earlier; omega
          simp [nextBuffer, equal, known other smaller]
      have first : step (decodeMachine decode)
          (.inl (position, buffer), frame binaryLeft
            (Binary.word ((List.ofFn bits).drop position.val) ++ binaryRight) scalarLeft (previous :: scalarRight)) =
          some (.inl (nextPosition, nextBuffer), frame (Binary.data (bits index) :: binaryLeft)
            (Binary.word ((List.ofFn bits).drop (position.val + 1)) ++ binaryRight) scalarLeft (previous :: scalarRight)) := by
        simp only [step, decodeMachine, valid, ↓reduceDIte, dropped, Binary.word, List.map_cons,
          List.cons_append, MultiTape.read, frame, Turing.Tape.mk'_head, Turing.ListBlank.head_mk, List.headI_cons,
          Option.map_some]
        have bitRead : decide (Binary.data (bits index) = 2) = bits index := by cases bits index <;> decide
        rw [bitRead]
        congr 2
        funext name
        cases name with
        | false => simp [act, frame, Turing.Tape.write_mk', Turing.Tape.move_right_mk', Turing.ListBlank.cons_mk]
        | true => simp [act, frame, Turing.Tape.write_mk', Turing.ListBlank.cons_mk]
      have rest := hypothesis (width - nextPosition.val) (by dsimp [nextPosition]; omega)
        nextPosition nextBuffer nextKnown (Binary.data (bits index) :: binaryLeft) rfl
      have trace := Steps.next first rest
      simpa [dropped, Binary.word, List.reverse_cons, List.append_assoc, nextPosition,
        show width - position.val = width - (position.val + 1) + 1 by omega, ← ranking] using trace
    · have last : position.val = width := by have bound := position.isLt; omega
      have complete : buffer = bits := by
        funext index
        exact known index (by rw [last]; exact index.isLt)
      have empty : (List.ofFn bits).drop position.val = [] := by
        rw [last]; exact List.drop_eq_nil_of_le (by simp)
      rw [← ranking, empty, last, Nat.sub_self, Nat.zero_add, Binary.word, List.map_nil,
        List.nil_append, List.reverse_nil, List.nil_append]
      refine .next ?_ (.zero _)
      simp only [step, decodeMachine, valid, ↓reduceDIte, complete, Option.map_some, decodeExit]
      congr 2
      funext name
      cases name with
      | false => exact Turing.Tape.write_self _
      | true => simp [act, frame, Turing.Tape.write_mk', Turing.Tape.move_right_mk', Turing.ListBlank.cons_mk]

/-- Decode one word with exact cost, without receiving a prepared scalar buffer. -/
theorem decode_steps (decode : BitVec width → Scalar) (bits : BitVec width)
    (binaryLeft binaryRight : List Binary.Symbol)
    (scalarLeft scalarRight : List (TableTraversal.Symbol Scalar)) (previous : TableTraversal.Symbol Scalar) :
    Steps (decodeMachine decode) (width + 1)
      (decodeEntry width, frame binaryLeft
        (Binary.word (List.ofFn (fun index : Fin width => bits.getLsbD index.val)) ++ binaryRight)
        scalarLeft (previous :: scalarRight))
      (decodeExit width, frame
        ((Binary.word (List.ofFn (fun index : Fin width => bits.getLsbD index.val))).reverse ++ binaryLeft)
        binaryRight (some (some (decode bits)) :: scalarLeft) scalarRight) := by
  have recovered : bufferBits (fun index : Fin width => bits.getLsbD index.val) = bits := by
    apply BitVec.eq_of_getLsbD_eq
    intro index valid
    exact bufferBits_get _ ⟨index, valid⟩
  simpa only [decodeEntry, Fin.val_zero, Nat.sub_zero, List.drop_zero, recovered] using
    suffix_steps decode (fun index : Fin width => bits.getLsbD index.val) 0 (fun _ => false)
      (by intro index earlier; change index.val < 0 at earlier; omega) binaryLeft binaryRight scalarLeft scalarRight previous

theorem decode_halt (decode : BitVec width → Scalar) (symbols : Symbols (Alphabet Scalar)) :
    decodeMachine decode (decodeExit width) symbols = none := rfl


abbrev EncodeState (width : ℕ) := Sum (Option (Fin (width + 1) × BitVec width)) Unit

instance encodeStatesFinite (width : ℕ) : Fintype (EncodeState width) := by
  let bitVectorsFinite : Fintype (BitVec width) :=
    Fintype.ofEquiv (Fin (2 ^ width)) BitVec.equivFin.toEquiv.symm
  infer_instance

def encodeMachine [Inhabited Scalar] (encode : Scalar → BitVec width) :
    Machine (Alphabet Scalar) (EncodeState width)
  | .inl none, symbols =>
    some (.inl (some (0, encode ((symbols true).join.getD default))), stationary symbols)
  | .inl (some (position, bits)), symbols =>
    if valid : position.val < width then
      some (.inl (some (⟨position.val + 1, by omega⟩, bits)), fun name => match name with
        | false => (Binary.data (bits.getLsbD position.val), some .right)
        | true => (symbols true, none))
    else some (.inr (), fun name => (symbols name, if name then some .right else none))
  | .inr (), _ => none

def encodeEntry (width : ℕ) : EncodeState width := .inl none
def encodeExit (width : ℕ) : EncodeState width := .inr ()

private theorem encode_suffix_steps [Inhabited Scalar] (encode : Scalar → BitVec width)
    (bits : BitVec width) (position : Fin (width + 1))
    (old : List Binary.Symbol) (oldLength : old.length = width - position.val)
    (binaryLeft binaryRight : List Binary.Symbol)
    (scalarLeft scalarRight : List (TableTraversal.Symbol Scalar)) (value : Scalar) :
    Steps (encodeMachine encode) (width - position.val + 1)
      (.inl (some (position, bits)), frame binaryLeft (old ++ binaryRight) scalarLeft (some (some value) :: scalarRight))
      (encodeExit width, frame
        ((Binary.word ((List.ofFn (fun index : Fin width => bits.getLsbD index.val)).drop position.val)).reverse ++ binaryLeft)
        binaryRight (some (some value) :: scalarLeft) scalarRight) := by
  generalize ranking : width - position.val = remaining
  induction remaining using Nat.strong_induction_on generalizing position old binaryLeft with
  | h remaining hypothesis =>
    by_cases valid : position.val < width
    · let nextPosition : Fin (width + 1) := ⟨position.val + 1, by omega⟩
      have dropped : (List.ofFn (fun index : Fin width => bits.getLsbD index.val)).drop position.val =
          bits.getLsbD position.val :: (List.ofFn (fun index : Fin width => bits.getLsbD index.val)).drop (position.val + 1) := by
        have equation := List.drop_eq_getElem_cons
          (l := List.ofFn (fun index : Fin width => bits.getLsbD index.val)) (by simpa using valid)
        rw [List.getElem_ofFn] at equation
        exact equation
      cases old with
      | nil => simp only [List.length_nil] at oldLength; omega
      | cons previous old =>
        have first : step (encodeMachine encode)
            (.inl (some (position, bits)), frame binaryLeft ((previous :: old) ++ binaryRight)
              scalarLeft (some (some value) :: scalarRight)) =
            some (.inl (some (nextPosition, bits)), frame (Binary.data (bits.getLsbD position.val) :: binaryLeft)
              (old ++ binaryRight) scalarLeft (some (some value) :: scalarRight)) := by
          simp only [step, encodeMachine, valid, ↓reduceDIte, Option.map_some]
          congr 2
          funext name
          cases name <;> simp [act, frame, MultiTape.read, Turing.Tape.write_mk',
            Turing.Tape.move_right_mk', Turing.ListBlank.cons_mk]
        have smaller : old.length = width - nextPosition.val := by
          dsimp [nextPosition]; simp only [List.length_cons] at oldLength; omega
        have rest := hypothesis (width - nextPosition.val) (by dsimp [nextPosition]; omega)
          nextPosition old smaller (Binary.data (bits.getLsbD position.val) :: binaryLeft) rfl
        have trace := Steps.next first rest
        simpa only [dropped, Binary.word, List.map_cons, List.reverse_cons, List.append_assoc,
          List.cons_append, List.nil_append, nextPosition,
          show width - position.val = width - (position.val + 1) + 1 by omega, ← ranking] using trace
    · have last : position.val = width := by have bound := position.isLt; omega
      have emptyOld : old = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst old
      have empty : (List.ofFn (fun index : Fin width => bits.getLsbD index.val)).drop position.val = [] := by
        rw [last]; exact List.drop_eq_nil_of_le (by simp)
      rw [← ranking, empty, last, Nat.sub_self, Nat.zero_add, Binary.word, List.map_nil,
        List.nil_append, List.reverse_nil, List.nil_append]
      refine .next ?_ (.zero _)
      simp only [step, encodeMachine, valid, ↓reduceDIte, Option.map_some, encodeExit]
      congr 2
      funext name
      cases name with
      | false => exact Turing.Tape.write_self (Turing.Tape.mk' (Turing.ListBlank.mk binaryLeft) (Turing.ListBlank.mk binaryRight))
      | true => simp [act, frame, MultiTape.read, Turing.Tape.write_mk', Turing.Tape.move_right_mk', Turing.ListBlank.cons_mk]

/-- Encode one scalar with exact cost, preserving the scalar and binary suffixes. -/
theorem encode_steps [Inhabited Scalar] (encode : Scalar → BitVec width) (value : Scalar)
    (old : List Binary.Symbol) (oldLength : old.length = width)
    (binaryLeft binaryRight : List Binary.Symbol)
    (scalarLeft scalarRight : List (TableTraversal.Symbol Scalar)) :
    Steps (encodeMachine encode) (width + 2)
      (encodeEntry width, frame binaryLeft (old ++ binaryRight) scalarLeft (some (some value) :: scalarRight))
      (encodeExit width, frame
        ((Binary.word (List.ofFn (fun index : Fin width => (encode value).getLsbD index.val))).reverse ++ binaryLeft)
        binaryRight (some (some value) :: scalarLeft) scalarRight) := by
  have first : step (encodeMachine encode)
      (encodeEntry width, frame binaryLeft (old ++ binaryRight) scalarLeft (some (some value) :: scalarRight)) =
      some (.inl (some (0, encode value)), frame binaryLeft (old ++ binaryRight) scalarLeft (some (some value) :: scalarRight)) := by
    simp [step, encodeMachine, encodeEntry, MultiTape.read, frame, act_stationary]
  have rest := encode_suffix_steps encode (encode value) 0 old (by simpa using oldLength)
    binaryLeft binaryRight scalarLeft scalarRight value
  simpa only [Fin.val_zero, Nat.sub_zero, List.drop_zero, Nat.add_assoc] using Steps.next first rest

theorem encode_halt [Inhabited Scalar] (encode : Scalar → BitVec width) (symbols : Symbols (Alphabet Scalar)) :
    encodeMachine encode (encodeExit width) symbols = none := rfl

end Polytime2.ScalarCodec
