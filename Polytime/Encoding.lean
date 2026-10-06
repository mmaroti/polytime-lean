import Mathlib.Data.Nat.Log
import Mathlib.Data.BitVec
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.GetD
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic

/-! # Canonical fixed-width codecs

Internally bits are indexed from least to most significant. Public codecs use
`BitVec`; the internal function representation makes block layouts explicit.
-/

namespace Polytime

abbrev Bits (n : ℕ) := Fin n → Bool

namespace Bits

def toBitVec (b : Bits n) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn b)).cast (List.length_ofFn ..)

def ofBitVec (b : BitVec n) : Bits n := fun i => b.getLsbD i

@[simp] theorem of_to (b : Bits n) : ofBitVec (toBitVec b) = b := by
  funext i
  simp only [ofBitVec, toBitVec, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

@[simp] theorem to_of (b : BitVec n) : toBitVec (ofBitVec b) = b := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  have h := congrFun (of_to (ofBitVec b)) ⟨i, hi⟩
  exact h

def join (a : Bits m) (b : Bits n) : Bits (m + n) := Fin.addCases a b
def first (b : Bits (m + n)) : Bits m := fun i => b (Fin.castAdd n i)
def last (b : Bits (m + n)) : Bits n := fun i => b (Fin.natAdd m i)

@[simp] theorem first_join (a : Bits m) (b : Bits n) : first (join a b) = a := by
  funext i; simp [first, join]

@[simp] theorem last_join (a : Bits m) (b : Bits n) : last (join a b) = b := by
  funext i; simp [last, join]

@[simp] theorem join_parts (b : Bits (m + n)) : join (first b) (last b) = b := by
  funext i
  refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [join, first, last]

end Bits

structure RawCodec (A : Type u) (width : ℕ) where
  encode : A → Bits width
  decode : Bits width → Option A
  decode_encode : ∀ x, decode (encode x) = some x
  encode_decode : ∀ b x, decode b = some x → encode x = b

namespace RawCodec

variable {A B : Type u} {w m n : ℕ}

theorem injective (c : RawCodec A w) : Function.Injective c.encode := by
  intro x y h
  have := congrArg c.decode h
  simpa [c.decode_encode] using this

def transport {B : Type v} (c : RawCodec A w) (e : A ≃ B) : RawCodec B w where
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

def cast (c : RawCodec A w) (h : w = v) : RawCodec A v := h ▸ c

def unit : RawCodec PUnit.{u + 1} 0 where
  encode _ := Fin.elim0
  decode _ := some PUnit.unit
  decode_encode x := by cases x; rfl
  encode_decode b x _ := by funext i; exact Fin.elim0 i

def product (a : RawCodec A m) (b : RawCodec B n) : RawCodec (A × B) (m + n) where
  encode x := Bits.join (a.encode x.1) (b.encode x.2)
  decode bits := do
    let x ← a.decode (Bits.first bits)
    let y ← b.decode (Bits.last bits)
    pure (x, y)
  decode_encode x := by
    change ((a.decode (Bits.first (Bits.join (a.encode x.1) (b.encode x.2)))).bind
      fun y => (b.decode (Bits.last (Bits.join (a.encode x.1) (b.encode x.2)))).bind
        fun z => some (y, z)) = some x
    simp only [Bits.first_join, Bits.last_join]
    rw [a.decode_encode, b.decode_encode]
    rfl
  encode_decode bits x h := by
    cases ha : a.decode (Bits.first bits) with
    | none => simp [ha] at h
    | some y =>
      cases hb : b.decode (Bits.last bits) with
      | none => simp [ha, hb] at h
      | some z =>
        change ((a.decode (Bits.first bits)).bind fun y =>
          (b.decode (Bits.last bits)).bind fun z => some (y, z)) = some x at h
        simp only [ha, hb, Option.bind_some, Option.some.injEq] at h
        subst x
        rw [a.encode_decode _ _ ha, b.encode_decode _ _ hb, Bits.join_parts]

/-- Retain only canonical encodings after a compositional candidate decoder. -/
def checked (enc : A → Bits w) (candidate : Bits w → Option A)
    (roundtrip : ∀ x, candidate (enc x) = some x) : RawCodec A w where
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
def fin (k : ℕ) : RawCodec (Fin k) (Nat.clog 2 k) where
  encode i := Bits.ofBitVec (BitVec.ofNatLT i.val
    (lt_of_lt_of_le i.isLt (Nat.le_pow_clog (by decide) k)))
  decode bits :=
    let v := (Bits.toBitVec bits).toNat
    if h : v < k then some ⟨v, h⟩ else none
  decode_encode i := by simp [Bits.to_of, i.isLt]
  encode_decode bits i h := by
    dsimp at h
    split at h
    · have hi := congrArg (fun x : Option (Fin k) => x.map Fin.val) h
      simp only [Option.map_some, Option.some.injEq] at hi
      apply_fun Bits.toBitVec
      · apply BitVec.toNat_injective
        simpa using hi.symm
      · exact Function.LeftInverse.injective Bits.of_to
    · contradiction

def headTailEquiv (A : Type u) (n : ℕ) : (Fin (n + 1) → A) ≃ A × (Fin n → A) where
  toFun f := (f 0, fun i => f i.succ)
  invFun p := Fin.cases p.1 p.2
  left_inv f := by funext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  right_inv p := rfl

def power (c : RawCodec A w) : (n : ℕ) → RawCodec (Fin n → A) (n * w)
  | 0 => (unit.{u}.transport
      { toFun := fun _ => Fin.elim0
        invFun := fun _ => PUnit.unit
        left_inv := fun x => by cases x; rfl
        right_inv := fun f => by funext i; exact Fin.elim0 i }).cast (Nat.zero_mul w).symm
  | n + 1 => ((c.product (power c n)).transport (headTailEquiv A n).symm).cast
      (by simp [Nat.add_mul, Nat.add_comm])

/-- Pad the high end of a payload; no inhabitant of its carrier is needed. -/
def pad (bits : Bits w) (W : ℕ) : Bits W :=
  fun i => if h : i.val < w then bits ⟨i.val, h⟩ else false

def take (bits : Bits W) (h : w ≤ W) : Bits w := fun i => bits ⟨i.val, lt_of_lt_of_le i.isLt h⟩

@[simp] theorem take_pad (bits : Bits w) (h : w ≤ W) : take (pad bits W) h = bits := by
  funext i
  simp [take, pad, i.isLt]

def tagged {r : ℕ} (A : Fin r → Type u) (width : Fin r → ℕ)
    (c : ∀ i, RawCodec (A i) (width i)) (W : ℕ) (hw : ∀ i, width i ≤ W) :
    RawCodec (Sigma A) (Nat.clog 2 r + W) :=
  checked
    (fun x => Bits.join ((fin r).encode x.1) (pad ((c x.1).encode x.2) W))
    (fun bits => ((fin r).decode (Bits.first bits)).bind fun i =>
      ((c i).decode (take (Bits.last bits) (hw i))).map (Sigma.mk i))
    (by
      intro ⟨i, x⟩
      simp only [Bits.first_join, Bits.last_join]
      rw [(fin r).decode_encode]
      simp only [Option.bind_some, take_pad]
      rw [(c i).decode_encode]
      rfl)

end RawCodec

structure BitCodec (A : Type u) (width : ℕ) where
  encode : A → BitVec width
  decode : BitVec width → Option A
  decode_encode : ∀ x, decode (encode x) = some x
  encode_decode : ∀ b x, decode b = some x → encode x = b

def RawCodec.toBitCodec (c : RawCodec A w) : BitCodec A w where
  encode x := Bits.toBitVec (c.encode x)
  decode b := c.decode (Bits.ofBitVec b)
  decode_encode x := by simp [c.decode_encode]
  encode_decode b x h := by rw [c.encode_decode _ _ h, Bits.to_of]

end Polytime
