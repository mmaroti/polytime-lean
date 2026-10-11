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

import Polytime2.ScalarCodec
import Polytime2.While
import Polytime2.UnaryAppend
import Polytime2.ReturnToMarker

/-! # Streaming binary-to-scalar conversion

Repeated fixed-width decoding prepares a densely stored scalar array from its
canonical binary payload. The binary input ends at blank, and the scalar output
is initially blank. Every iteration and controller handover is counted.
-/

namespace Polytime2.ScalarStreams

open MultiTape
open ScalarCodec (Alphabet frame)

variable {Scalar : Type} {width : ℕ}

def word (encode : Scalar → BitVec width) (values : List Scalar) : List Binary.Symbol :=
  values.flatMap (ScalarCodec.word ∘ encode)

/-- Canonical scalar payload before mapping bits to tape symbols. -/
def bits (encode : Scalar → BitVec width) (values : List Scalar) : List Bool :=
  values.flatMap (fun value => List.ofFn (fun index : Fin width => (encode value).getLsbD index.val))

theorem word_eq (encode : Scalar → BitVec width) (values : List Scalar) :
    word encode values = Binary.word (bits encode values) := by
  simp [word, bits, ScalarCodec.word, Binary.word, List.map_flatMap, Function.comp_def]

@[simp] theorem word_length (encode : Scalar → BitVec width) (values : List Scalar) :
    (word encode values).length = values.length * width := by
  induction values with
  | nil => simp [word]
  | cons value values hypothesis => simp [word, Nat.add_mul, Nat.add_comm]

private theorem head_nonblank (bits : BitVec width) (positive : 0 < width) (right : List Binary.Symbol) :
    ((ScalarCodec.word bits) ++ right).headI ≠ 0 := by
  have nonempty : ScalarCodec.word bits ≠ [] := by
    intro empty
    have length := ScalarCodec.word_length bits
    rw [empty] at length
    simp only [List.length_nil] at length
    omega
  cases equation : ScalarCodec.word bits with
  | nil => exact False.elim (nonempty equation)
  | cons symbol rest =>
    have member : symbol ∈ ScalarCodec.word bits := by rw [equation]; simp
    obtain ⟨bit, _, equal⟩ := List.mem_map.mp member
    subst symbol
    cases bit <;> simp [Binary.data]

private theorem blank_scalar :
    Turing.ListBlank.mk [(none : TableTraversal.Symbol Scalar)] = Turing.ListBlank.mk [] :=
  Turing.ListBlank.cons_head_tail (Turing.ListBlank.mk [])

@[simp] private theorem frame_scalar_blank (binaryLeft binaryRight : List Binary.Symbol)
    (scalarLeft : List (TableTraversal.Symbol Scalar)) :
    frame binaryLeft binaryRight scalarLeft [(none : TableTraversal.Symbol Scalar)] =
      frame binaryLeft binaryRight scalarLeft [] := by
  funext name
  cases name <;> simp [frame, blank_scalar]

def guard : Machine (Alphabet Scalar) Unit := fun _ _ => none

def hasBinary (symbols : Symbols (Alphabet Scalar)) : Bool := decide (symbols false ≠ 0)

abbrev DecodeState (width : ℕ) := Sum (Sum Unit (ScalarCodec.DecodeState width)) Unit

def decodeMachine (decode : BitVec width → Scalar) : Machine (Alphabet Scalar) (DecodeState width) :=
  withExit (whileMachine guard (ScalarCodec.decodeMachine decode) () (ScalarCodec.decodeEntry width) hasBinary)

def decodeEntry (width : ℕ) : DecodeState width := .inl (.inl ())
def decodeExit (width : ℕ) : DecodeState width := .inr ()

private theorem decode_loop_steps (encode : Scalar → BitVec width) (decode : BitVec width → Scalar)
    (roundtrip : ∀ value, decode (encode value) = value) (positive : 0 < width)
    (values : List Scalar) (binaryLeft : List Binary.Symbol) (scalarLeft : List (TableTraversal.Symbol Scalar)) :
    Steps (whileMachine guard (ScalarCodec.decodeMachine decode) () (ScalarCodec.decodeEntry width) hasBinary)
      (values.length * (width + 3))
      (.inl (), frame binaryLeft (word encode values ++ [0]) scalarLeft [none])
      (.inl (), frame ((word encode values).reverse ++ binaryLeft) [0]
        ((TableTraversal.word values).reverse ++ scalarLeft) [none]) := by
  induction values generalizing binaryLeft scalarLeft with
  | nil =>
    simpa [word, TableTraversal.word] using (Steps.zero
      (machine := whileMachine guard (ScalarCodec.decodeMachine decode) () (ScalarCodec.decodeEntry width) hasBinary)
      (.inl (), frame binaryLeft [0] scalarLeft [none]))
  | cons value values hypothesis =>
    have nonblank := head_nonblank (encode value) positive (word encode values ++ [0])
    have selected : hasBinary (MultiTape.read (frame binaryLeft
        (ScalarCodec.word (encode value) ++ (word encode values ++ [0])) scalarLeft [none])) = true := by
      simp [hasBinary, MultiTape.read, frame, nonblank]
    have entered : step (whileMachine guard (ScalarCodec.decodeMachine decode) () (ScalarCodec.decodeEntry width) hasBinary)
        (.inl (), frame binaryLeft (ScalarCodec.word (encode value) ++ (word encode values ++ [0])) scalarLeft [none]) =
        some (.inr (ScalarCodec.decodeEntry width),
          frame binaryLeft (ScalarCodec.word (encode value) ++ (word encode values ++ [0])) scalarLeft [none]) := by
      simp only [frame_scalar_blank] at selected
      simp [step, whileMachine, guard, selected]
    have decoded := ScalarCodec.decode_steps decode (encode value) binaryLeft (word encode values ++ [0]) scalarLeft [] none
    change Steps _ _ _ (ScalarCodec.decodeExit width,
      frame ((ScalarCodec.word (encode value)).reverse ++ binaryLeft) (word encode values ++ [0])
        (some (some (decode (encode value))) :: scalarLeft) []) at decoded
    rw [roundtrip value] at decoded
    have lifted := decoded.rename Sum.inr
      (target := whileMachine guard (ScalarCodec.decodeMachine decode) () (ScalarCodec.decodeEntry width) hasBinary)
      (by intro state symbols next actions transition; simp [whileMachine, transition])
    have restarted : step (whileMachine guard (ScalarCodec.decodeMachine decode) () (ScalarCodec.decodeEntry width) hasBinary)
        (.inr (ScalarCodec.decodeExit width),
          frame ((ScalarCodec.word (encode value)).reverse ++ binaryLeft) (word encode values ++ [0])
            (some (some value) :: scalarLeft) []) =
        some (.inl (), frame ((ScalarCodec.word (encode value)).reverse ++ binaryLeft) (word encode values ++ [0])
            (some (some value) :: scalarLeft) []) := by
      simp [step, whileMachine, ScalarCodec.decode_halt]
    have rest := hypothesis ((ScalarCodec.word (encode value)).reverse ++ binaryLeft) (some (some value) :: scalarLeft)
    simp only [frame_scalar_blank] at entered rest
    have trace := Steps.next entered (lifted.trans (Steps.next restarted rest))
    convert trace using 1 <;>
      simp [word, List.flatMap_cons, TableTraversal.word, List.reverse_append, List.reverse_cons,
        List.append_assoc, Nat.add_mul, Nat.add_assoc, ScalarCodec.word]
    omega

/-- Preparing an arbitrary scalar array requires time linear in its bit length
and number of entries, including handovers and the final exit transition. -/
theorem decode_steps (encode : Scalar → BitVec width) (decode : BitVec width → Scalar)
    (roundtrip : ∀ value, decode (encode value) = value) (positive : 0 < width)
    (values : List Scalar) (binaryLeft : List Binary.Symbol) (scalarLeft : List (TableTraversal.Symbol Scalar)) :
    Steps (decodeMachine decode) (values.length * (width + 3) + 1)
      (decodeEntry width, frame binaryLeft (word encode values ++ [0]) scalarLeft [none])
      (decodeExit width, frame ((word encode values).reverse ++ binaryLeft) [0]
        ((TableTraversal.word values).reverse ++ scalarLeft) [none]) := by
  have trace := decode_loop_steps encode decode roundtrip positive values binaryLeft scalarLeft
  exact withExit_steps _ trace (by simp [step, whileMachine, guard, hasBinary, MultiTape.read, frame])

theorem decode_halt (decode : BitVec width → Scalar) (symbols : Symbols (Alphabet Scalar)) :
    decodeMachine decode (decodeExit width) symbols = none := rfl


@[simp] private theorem frame_binary_zeros (count : ℕ) (binaryLeft : List Binary.Symbol)
    (scalarLeft scalarRight : List (TableTraversal.Symbol Scalar)) :
    frame binaryLeft (List.replicate count 0 ++ [0]) scalarLeft scalarRight =
      frame binaryLeft [0] scalarLeft scalarRight := by
  funext name
  cases name with
  | false =>
    change Turing.Tape.mk' _ (Turing.ListBlank.mk (List.replicate count (0 : Binary.Symbol) ++ [0])) =
      Turing.Tape.mk' _ (Turing.ListBlank.mk [0])
    rw [← List.replicate_succ', UnaryAppend.mk_replicate_zero, UnaryAppend.mk_zero]
  | true => rfl

def hasScalar (symbols : Symbols (Alphabet Scalar)) : Bool := (symbols true).join.isSome

abbrev EncodeState (width : ℕ) := Sum (Sum Unit (ScalarCodec.EncodeState width)) Unit

def encodeMachine [Inhabited Scalar] (encode : Scalar → BitVec width) : Machine (Alphabet Scalar) (EncodeState width) :=
  withExit (whileMachine guard (ScalarCodec.encodeMachine encode) () (ScalarCodec.encodeEntry width) hasScalar)

def encodeEntry (width : ℕ) : EncodeState width := .inl (.inl ())
def encodeExit (width : ℕ) : EncodeState width := .inr ()

private theorem encode_loop_steps [Inhabited Scalar] (encode : Scalar → BitVec width)
    (values : List Scalar) (binaryLeft : List Binary.Symbol) (scalarLeft : List (TableTraversal.Symbol Scalar)) :
    Steps (whileMachine guard (ScalarCodec.encodeMachine encode) () (ScalarCodec.encodeEntry width) hasScalar)
      (values.length * (width + 4))
      (.inl (), frame binaryLeft [0] scalarLeft (TableTraversal.word values ++ [none]))
      (.inl (), frame ((word encode values).reverse ++ binaryLeft) [0]
        ((TableTraversal.word values).reverse ++ scalarLeft) [none]) := by
  induction values generalizing binaryLeft scalarLeft with
  | nil =>
    simpa [word, TableTraversal.word] using (Steps.zero
      (machine := whileMachine guard (ScalarCodec.encodeMachine encode) () (ScalarCodec.encodeEntry width) hasScalar)
      (.inl (), frame binaryLeft [0] scalarLeft [none]))
  | cons value values hypothesis =>
    have entered : step (whileMachine guard (ScalarCodec.encodeMachine encode) () (ScalarCodec.encodeEntry width) hasScalar)
        (.inl (), frame binaryLeft [0] scalarLeft (some (some value) :: (TableTraversal.word values ++ [none]))) =
        some (.inr (ScalarCodec.encodeEntry width),
          frame binaryLeft [0] scalarLeft (some (some value) :: (TableTraversal.word values ++ [none]))) := by
      simp [step, whileMachine, guard, hasScalar, MultiTape.read, frame]
    have encoded := ScalarCodec.encode_steps encode value (List.replicate width 0) (by simp)
      binaryLeft [0] scalarLeft (TableTraversal.word values ++ [none])
    simp only [frame_binary_zeros] at encoded
    have lifted := encoded.rename Sum.inr
      (target := whileMachine guard (ScalarCodec.encodeMachine encode) () (ScalarCodec.encodeEntry width) hasScalar)
      (by intro state symbols next actions transition; simp [whileMachine, transition])
    have restarted : step (whileMachine guard (ScalarCodec.encodeMachine encode) () (ScalarCodec.encodeEntry width) hasScalar)
        (.inr (ScalarCodec.encodeExit width), frame ((ScalarCodec.word (encode value)).reverse ++ binaryLeft) [0]
          (some (some value) :: scalarLeft) (TableTraversal.word values ++ [none])) =
        some (.inl (), frame ((ScalarCodec.word (encode value)).reverse ++ binaryLeft) [0]
          (some (some value) :: scalarLeft) (TableTraversal.word values ++ [none])) := by
      simp [step, whileMachine, ScalarCodec.encode_halt]
    have rest := hypothesis ((ScalarCodec.word (encode value)).reverse ++ binaryLeft) (some (some value) :: scalarLeft)
    have trace := Steps.next entered (lifted.trans (Steps.next restarted rest))
    convert trace using 1 <;>
      simp [word, List.flatMap_cons, TableTraversal.word, List.reverse_append, List.reverse_cons,
        List.append_assoc, Nat.add_mul, Nat.add_assoc, ScalarCodec.word]
    omega

/-- Serialize a scalar array onto initially blank tape, including all loop costs. -/
theorem encode_steps [Inhabited Scalar] (encode : Scalar → BitVec width)
    (values : List Scalar) (binaryLeft : List Binary.Symbol) (scalarLeft : List (TableTraversal.Symbol Scalar)) :
    Steps (encodeMachine encode) (values.length * (width + 4) + 1)
      (encodeEntry width, frame binaryLeft [0] scalarLeft (TableTraversal.word values ++ [none]))
      (encodeExit width, frame ((word encode values).reverse ++ binaryLeft) [0]
        ((TableTraversal.word values).reverse ++ scalarLeft) [none]) := by
  have trace := encode_loop_steps encode values binaryLeft scalarLeft
  exact withExit_steps _ trace (by simp [step, whileMachine, guard, hasScalar, MultiTape.read, frame])

theorem encode_halt [Inhabited Scalar] (encode : Scalar → BitVec width) (symbols : Symbols (Alphabet Scalar)) :
    encodeMachine encode (encodeExit width) symbols = none := rfl


noncomputable def returnScalar [DecidableEq Scalar] : Machine (Alphabet Scalar) (Fin 2) :=
  wire (oneTape true) (ReturnToMarker.machine (some none : TableTraversal.Symbol Scalar))

/-- Restore a streamed array head without changing either tape. -/
theorem returnScalar_steps [DecidableEq Scalar] (values : List Scalar)
    (binaryLeft binaryRight : List Binary.Symbol) (scalarLeft : List (TableTraversal.Symbol Scalar)) :
    Steps returnScalar (values.length + 2)
      (0, frame binaryLeft binaryRight ((TableTraversal.word values).reverse ++ some none :: scalarLeft) [none])
      (1, frame binaryLeft binaryRight (some none :: scalarLeft) (TableTraversal.word values ++ [none])) := by
  have noMarker : ∀ symbol ∈ (TableTraversal.word values).reverse,
      symbol ≠ (some none : TableTraversal.Symbol Scalar) := by
    intro symbol member
    obtain ⟨value, _, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp member)
    simp
  have restored := ReturnToMarker.steps (some none : TableTraversal.Symbol Scalar)
    (TableTraversal.word values).reverse noMarker none (by simp) scalarLeft []
  simp only [List.length_reverse, TableTraversal.word, List.length_map, List.reverse_reverse] at restored
  apply wire_steps_of_eq (oneTape true) _ restored
  · intro name; cases name; rfl
  · intro name; cases name; rfl
  · intro name outside
    cases name with
    | false => rfl
    | true => exact False.elim (outside ⟨(), rfl⟩)

abbrev PrepareState (width : ℕ) := Sum (DecodeState width) (Fin 2)

noncomputable def prepareMachine [DecidableEq Scalar] (decode : BitVec width → Scalar) :
    Machine (Alphabet Scalar) (PrepareState width) := sequence (decodeMachine decode) returnScalar 0

def prepareEntry (width : ℕ) : PrepareState width := .inl (decodeEntry width)
def prepareExit (width : ℕ) : PrepareState width := .inr 1

/-- Convert the binary payload to the dense scalar array expected by matrix
routines, including restoring its head and charging all preparation work. -/
theorem prepare_steps [DecidableEq Scalar] (encode : Scalar → BitVec width) (decode : BitVec width → Scalar)
    (roundtrip : ∀ value, decode (encode value) = value) (positive : 0 < width)
    (values : List Scalar) (binaryLeft : List Binary.Symbol) (scalarLeft : List (TableTraversal.Symbol Scalar)) :
    Steps (prepareMachine decode) (values.length * (width + 4) + 4)
      (prepareEntry width, frame binaryLeft (word encode values ++ [0]) (some none :: scalarLeft) [none])
      (prepareExit width, frame ((word encode values).reverse ++ binaryLeft) [0]
        (some none :: scalarLeft) (TableTraversal.word values ++ [none])) := by
  have decoded := decode_steps encode decode roundtrip positive values binaryLeft (some none :: scalarLeft)
  have restored := returnScalar_steps values ((word encode values).reverse ++ binaryLeft) [0] scalarLeft
  have complete := sequence_steps _ _ 0 decoded (decode_halt decode) restored
  convert complete using 1 <;> first | rfl | ring

theorem prepare_halt [DecidableEq Scalar] (decode : BitVec width → Scalar) (symbols : Symbols (Alphabet Scalar)) :
    prepareMachine decode (prepareExit width) symbols = none := by
  simp [prepareMachine, prepareExit, MultiTape.sequence, returnScalar, wire, ReturnToMarker.halt]


noncomputable def returnBinary : Machine (Alphabet Scalar) (Fin 2) :=
  wire (oneTape false) (ReturnToMarker.machine (3 : Binary.Symbol))

/-- Restore the binary output head while preserving the scalar tape. -/
theorem returnBinary_steps (encode : Scalar → BitVec width) (values : List Scalar)
    (binaryLeft : List Binary.Symbol) (scalarLeft scalarRight : List (TableTraversal.Symbol Scalar)) :
    Steps returnBinary (values.length * width + 2)
      (0, frame ((word encode values).reverse ++ 3 :: binaryLeft) [0] scalarLeft scalarRight)
      (1, frame (3 :: binaryLeft) (word encode values ++ [0]) scalarLeft scalarRight) := by
  have noMarker : ∀ symbol ∈ (word encode values).reverse, symbol ≠ (3 : Binary.Symbol) := by
    intro symbol member
    have inWord := List.mem_reverse.mp member
    obtain ⟨value, _, inBlock⟩ := List.mem_flatMap.mp inWord
    obtain ⟨bit, _, rfl⟩ := List.mem_map.mp inBlock
    cases bit <;> decide
  have restored := ReturnToMarker.steps (3 : Binary.Symbol) (word encode values).reverse
    noMarker 0 (by decide) binaryLeft []
  simp only [List.length_reverse, word_length, List.reverse_reverse] at restored
  apply wire_steps_of_eq (oneTape false) _ restored
  · intro name; cases name; rfl
  · intro name; cases name; rfl
  · intro name outside
    cases name with
    | false => exact False.elim (outside ⟨(), rfl⟩)
    | true => rfl

abbrev SerializeState (width : ℕ) := Sum (Sum (EncodeState width) (Fin 2)) (Fin 2)

noncomputable def serializeMachine [Inhabited Scalar] [DecidableEq Scalar] (encode : Scalar → BitVec width) :
    Machine (Alphabet Scalar) (SerializeState width) :=
  sequence (sequence (encodeMachine encode) returnBinary 0) returnScalar 0

def serializeEntry (width : ℕ) : SerializeState width := .inl (.inl (encodeEntry width))
def serializeExit (width : ℕ) : SerializeState width := .inr 1

/-- Extract a dense binary output and restore both heads, preserving the full
scalar array. Neither routine receives preallocated output cells. -/
theorem serialize_steps [Inhabited Scalar] [DecidableEq Scalar] (encode : Scalar → BitVec width)
    (values : List Scalar) (binaryLeft : List Binary.Symbol) (scalarLeft : List (TableTraversal.Symbol Scalar)) :
    Steps (serializeMachine encode) (values.length * (2 * width + 5) + 7)
      (serializeEntry width, frame (3 :: binaryLeft) [0] (some none :: scalarLeft) (TableTraversal.word values ++ [none]))
      (serializeExit width, frame (3 :: binaryLeft) (word encode values ++ [0])
        (some none :: scalarLeft) (TableTraversal.word values ++ [none])) := by
  have encoded := encode_steps encode values (3 :: binaryLeft) (some none :: scalarLeft)
  have binaryRestored := returnBinary_steps encode values binaryLeft
    ((TableTraversal.word values).reverse ++ some none :: scalarLeft) [none]
  have scalarRestored := returnScalar_steps values (3 :: binaryLeft) (word encode values ++ [0]) scalarLeft
  have first := sequence_steps _ _ 0 encoded (encode_halt encode) binaryRestored
  have complete := sequence_steps _ _ 0 first
    (by intro symbols; simp [MultiTape.sequence, returnBinary, wire, ReturnToMarker.halt]) scalarRestored
  convert complete using 1 <;> first | rfl | ring

theorem serialize_halt [Inhabited Scalar] [DecidableEq Scalar]
    (encode : Scalar → BitVec width) (symbols : Symbols (Alphabet Scalar)) :
    serializeMachine encode (serializeExit width) symbols = none := by
  simp [serializeMachine, serializeExit, MultiTape.sequence, returnScalar, wire, ReturnToMarker.halt]

end Polytime2.ScalarStreams
