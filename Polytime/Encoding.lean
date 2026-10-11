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

import Mathlib.Data.Nat.Log
import Mathlib.Data.BitVec
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic

/-! # Canonical fixed-width codecs

Each codec uses `BitVec` directly. Product fields and power entries occupy
consecutive blocks from least to most significant; sum payloads have zero padding.
-/

namespace Polytime

-- u: encoded carriers; v: target carriers when transporting a codec along an equivalence.
universe u v

private def join (a : BitVec m) (b : BitVec n) : BitVec (m + n) :=
  (b ++ a).cast (Nat.add_comm n m)

private def first (b : BitVec (m + n)) : BitVec m := b.extractLsb' 0 m
private def last (b : BitVec (m + n)) : BitVec n := b.extractLsb' m n

@[simp] private theorem first_join (a : BitVec m) (b : BitVec n) : first (join a b) = a := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  simp [first, join, BitVec.getLsbD_append, hi]

@[simp] private theorem last_join (a : BitVec m) (b : BitVec n) : last (join a b) = b := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  simp only [last, join, BitVec.getLsbD_extractLsb', BitVec.getLsbD_cast,
    BitVec.getLsbD_append]
  simp [hi, show ¬ m + i < m by omega]

@[simp] private theorem join_parts (b : BitVec (m + n)) : join (first b) (last b) = b := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  simp only [join, first, last, BitVec.getLsbD_cast, BitVec.getLsbD_append,
    BitVec.getLsbD_extractLsb']
  by_cases h : i < m
  · simp [h]
  · simp [h, show i - m < n by omega, Nat.add_sub_of_le (by omega : m ≤ i)]

structure BitCodec (A : Type u) (width : ℕ) where
  encode : A → BitVec width
  decode : BitVec width → Option A
  decode_encode : ∀ x, decode (encode x) = some x
  encode_decode : ∀ b x, decode b = some x → encode x = b

namespace BitCodec

/-- Pointwise agreement with a stored block gives its complete encoded slice. -/
theorem slice_of_bits {width blockWidth : ℕ} (payload : BitVec width)
    (block : BitVec blockWidth) (start : ℕ) (fits : start + blockWidth ≤ width)
    (agrees : ∀ offset : Fin blockWidth,
      payload.getLsbD (start + offset.val) = block.getLsbD offset.val) :
    ((List.ofFn (fun index : Fin width => payload.getLsbD index.val)).drop start).take blockWidth =
      List.ofFn (fun offset : Fin blockWidth => block.getLsbD offset.val) := by
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, List.length_ofFn]
    omega
  · intro index firstValid secondValid
    simp only [List.length_ofFn] at secondValid
    simp only [List.getElem_take, List.getElem_drop, List.getElem_ofFn]
    exact agrees ⟨index, secondValid⟩

/-- Updating a reserved block preserves precisely the prefix and suffix.
Clients supply bit-level encoding compatibility, not list-index arithmetic. -/
theorem replace_of_bits {width blockWidth : ℕ} (payload updated : BitVec width)
    (block : BitVec blockWidth) (start : ℕ) (fits : start + blockWidth ≤ width)
    (inside : ∀ offset : Fin blockWidth,
      updated.getLsbD (start + offset.val) = block.getLsbD offset.val)
    (outside : ∀ index : Fin width, index.val < start ∨ start + blockWidth ≤ index.val →
      updated.getLsbD index.val = payload.getLsbD index.val) :
    List.ofFn (fun index : Fin width => updated.getLsbD index.val) =
      (List.ofFn (fun index : Fin width => payload.getLsbD index.val)).take start ++
        (List.ofFn (fun offset : Fin blockWidth => block.getLsbD offset.val) ++
          (List.ofFn (fun index : Fin width => payload.getLsbD index.val)).drop (start + blockWidth)) := by
  have startFits : start ≤ width := by omega
  have prefixLength : ((List.ofFn (fun index : Fin width => payload.getLsbD index.val)).take start).length = start := by
    simp only [List.length_take, List.length_ofFn]
    omega
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_append, prefixLength, List.length_drop]
    omega
  · intro index firstValid secondValid
    simp only [List.length_ofFn] at firstValid
    by_cases before : index < start
    · simpa [List.getElem_append, prefixLength, Nat.min_eq_left startFits, ← BitVec.getLsbD_eq_getElem, before, List.getElem_take] using
        outside ⟨index, firstValid⟩ (Or.inl before)
    · by_cases within : index - start < blockWidth
      · have address : start + (index - start) = index := by omega
        have bit := inside ⟨index - start, within⟩
        rw [address] at bit
        simpa [List.getElem_append, prefixLength, Nat.min_eq_left startFits, ← BitVec.getLsbD_eq_getElem, before, within] using bit
      · have after : start + blockWidth ≤ index := by omega
        have address : start + blockWidth + (index - start - blockWidth) = index := by omega
        simpa [List.getElem_append, prefixLength, Nat.min_eq_left startFits, ← BitVec.getLsbD_eq_getElem, before, within, List.getElem_drop, address] using
          outside ⟨index, firstValid⟩ (Or.inr after)

variable {A B : Type u} {w m n : ℕ}

theorem injective (c : BitCodec A w) : Function.Injective c.encode := by
  intro x y h
  have := congrArg c.decode h
  simpa [c.decode_encode] using this

def transport {B : Type v} (c : BitCodec A w) (e : A ≃ B) : BitCodec B w where
  encode b := c.encode (e.symm b)
  decode b := (c.decode b).map e
  decode_encode b := by simp [c.decode_encode]
  encode_decode b x h := by
    cases hd : c.decode b with
    | none => simp [hd] at h
    | some a =>
      simp only [hd, Option.map_some, Option.some.injEq] at h
      subst x
      simpa using c.encode_decode b a hd

def cast (c : BitCodec A w) (h : w = v) : BitCodec A v := h ▸ c

@[simp] theorem cast_encode (c : BitCodec A w) {targetWidth : ℕ}
    (equality : w = targetWidth) (value : A) :
    (c.cast equality).encode value = (c.encode value).cast equality := by
  cases equality
  rfl

def unit : BitCodec PUnit.{u + 1} 0 where
  encode _ := BitVec.ofNat 0 0
  decode _ := some PUnit.unit
  decode_encode x := by cases x; rfl
  encode_decode b x _ := by exact (BitVec.eq_nil b).symm

def product (a : BitCodec A m) (b : BitCodec B n) : BitCodec (A × B) (m + n) where
  encode x := join (a.encode x.1) (b.encode x.2)
  decode bits := do
    let x ← a.decode (first bits)
    let y ← b.decode (last bits)
    pure (x, y)
  decode_encode x := by
    change ((a.decode (first (join (a.encode x.1) (b.encode x.2)))).bind
      fun y => (b.decode (last (join (a.encode x.1) (b.encode x.2)))).bind
        fun z => some (y, z)) = some x
    simp only [first_join, last_join]
    rw [a.decode_encode, b.decode_encode]
    rfl
  encode_decode bits x h := by
    cases ha : a.decode (first bits) with
    | none => simp [ha] at h
    | some y =>
      cases hb : b.decode (last bits) with
      | none => simp [ha, hb] at h
      | some z =>
        change ((a.decode (first bits)).bind fun y =>
          (b.decode (last bits)).bind fun z => some (y, z)) = some x at h
        simp only [ha, hb, Option.bind_some, Option.some.injEq] at h
        subst x
        rw [a.encode_decode _ _ ha, b.encode_decode _ _ hb, join_parts]

/-- Retain only canonical encodings after a compositional candidate decoder. -/
def checked (enc : A → BitVec w) (candidate : BitVec w → Option A)
    (roundtrip : ∀ x, candidate (enc x) = some x) : BitCodec A w where
  encode := enc
  decode bits := (candidate bits).bind fun x => if enc x = bits then some x else none
  decode_encode x := by simp [roundtrip]
  encode_decode bits x h := by
    cases hc : candidate bits with
    | none => simp [hc] at h
    | some y =>
      simp only [hc, Option.bind_some] at h
      split at h
      · have hy : y = x := Option.some.inj h
        subst x
        assumption
      · contradiction

/-- Binary labels, including empty and singleton carriers. -/
def fin (k : ℕ) : BitCodec (Fin k) (Nat.clog 2 k) where
  encode i := BitVec.ofNatLT i.val
    (lt_of_lt_of_le i.isLt (Nat.le_pow_clog (by decide) k))
  decode bits :=
    let v := bits.toNat
    if h : v < k then some ⟨v, h⟩ else none
  decode_encode i := by simp [i.isLt]
  encode_decode bits i h := by
    dsimp at h
    split at h
    · have hi := congrArg (fun x : Option (Fin k) => x.map Fin.val) h
      simp only [Option.map_some, Option.some.injEq] at hi
      apply BitVec.toNat_injective
      simpa using hi.symm
    · contradiction

def headTailEquiv (A : Type u) (n : ℕ) : (Fin (n + 1) → A) ≃ A × (Fin n → A) where
  toFun f := (f 0, fun i => f i.succ)
  invFun p := Fin.cases p.1 p.2
  left_inv f := by funext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  right_inv p := rfl

def power (c : BitCodec A w) : (n : ℕ) → BitCodec (Fin n → A) (n * w)
  | 0 => (unit.{u}.transport
      { toFun := fun _ => Fin.elim0
        invFun := fun _ => PUnit.unit
        left_inv := fun x => by cases x; rfl
        right_inv := fun f => by funext i; exact Fin.elim0 i }).cast (Nat.zero_mul w).symm
  | n + 1 => ((c.product (power c n)).transport (headTailEquiv A n).symm).cast
      (by simp [Nat.add_mul, Nat.add_comm])

/-- An entry occupies its fixed-width block in tuple order. -/
theorem power_encode_entry_bit (c : BitCodec A w) (length : ℕ)
    (tuple : Fin length → A) (index : Fin length) (offset : Fin w) :
    ((c.power length).encode tuple).getLsbD (index.val * w + offset.val) =
      (c.encode (tuple index)).getLsbD offset.val := by
  induction length with
  | zero => exact Fin.elim0 index
  | succ length hypothesis =>
    rw [power]
    simp only [cast_encode, BitVec.getLsbD_cast]
    change (join (c.encode (tuple 0))
      ((c.power length).encode (fun position => tuple position.succ))).getLsbD
        (index.val * w + offset.val) = _
    simp only [join, BitVec.getLsbD_cast, BitVec.getLsbD_append]
    refine Fin.cases ?_ (fun position => ?_) index
    · simp [offset.isLt]
    · have outside : ¬ (position.val + 1) * w + offset.val < w := by
        rw [Nat.add_mul, Nat.one_mul]
        omega
      have address : (position.val + 1) * w + offset.val - w =
          position.val * w + offset.val := by
        rw [Nat.add_mul, Nat.one_mul]
        omega
      simpa only [Fin.val_succ, outside, ite_false, address] using
        hypothesis (fun position => tuple position.succ) position

/-- Single-bit entries occur in tuple order from least to most significant. -/
theorem power_encode_bit (c : BitCodec A 1) (length : ℕ)
    (tuple : Fin length → A) (index : Fin length) :
    ((c.power length).encode tuple).getLsbD index.val = (c.encode (tuple index)).getLsbD 0 := by
  simpa using c.power_encode_entry_bit length tuple index (0 : Fin 1)

def tagged {r : ℕ} (A : Fin r → Type u) (width : Fin r → ℕ)
    (c : ∀ i, BitCodec (A i) (width i)) (W : ℕ) (hw : ∀ i, width i ≤ W) :
    BitCodec (Sigma A) (Nat.clog 2 r + W) :=
  checked
    (fun x => join ((fin r).encode x.1) (((c x.1).encode x.2).setWidth W))
    (fun bits => ((fin r).decode (first bits)).bind fun i =>
      ((c i).decode ((last bits).setWidth (width i))).map (Sigma.mk i))
    (by
      intro ⟨i, x⟩
      simp only [first_join, last_join]
      rw [(fin r).decode_encode]
      simp only [Option.bind_some, BitVec.setWidth_setWidth_of_le _ (hw i), BitVec.setWidth_eq]
      rw [(c i).decode_encode]
      rfl)

end BitCodec

end Polytime
