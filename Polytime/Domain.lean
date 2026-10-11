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

import Polytime.Size
import Polytime.Encoding
import Mathlib.Data.List.MinMax

/-! # Recursive parametric domains

Parameter assignments index values and exact widths. Polynomial-size bounds
hold for every assignment, with all parameters on equal footing. No size
headers are included in these codecs.
-/

namespace Polytime

-- u: fixed carriers and the mathematical values of domain expressions.
universe u

structure FixedPresentation where
  Carrier : Type u
  cardinality : ℕ
  enumeration : Carrier ≃ Fin cardinality

namespace FixedPresentation

def bitWidth (p : FixedPresentation.{u}) : ℕ := Nat.clog 2 p.cardinality

def codec (p : FixedPresentation.{u}) : BitCodec p.Carrier p.bitWidth :=
  (BitCodec.fin p.cardinality).transport p.enumeration.symm

def fin (k : ℕ) : FixedPresentation where
  Carrier := Fin k
  cardinality := k
  enumeration := Equiv.refl _

end FixedPresentation

inductive DomainExpression (ctx : SizeContext) : Type (u + 1)
  | fixed (presentation : FixedPresentation.{u})
  | product (children : List (DomainExpression ctx))
  | sum (alternatives : List (DomainExpression ctx))
  | power (base : DomainExpression ctx) (exponent : SizeExpression ctx)

namespace DomainExpression

variable {ctx : SizeContext}

/-- The mathematical values described by an expression at a size assignment. -/
def Value (d : DomainExpression.{u} ctx) (a : SizeAssignment ctx) : Type u :=
  match d with
  | .fixed p => p.Carrier
  | .product [] => PUnit
  | .product (d :: ds) => d.Value a × (product ds).Value a
  | .sum ds => (i : Fin ds.length) × (ds.get i).Value a
  | .power d e => Fin (e.eval a) → d.Value a
termination_by sizeOf d
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | have h := List.sizeOf_get ds i
      simp only [List.get_eq_getElem] at h
      omega

@[simp] theorem value_fixed (p : FixedPresentation.{u}) (a : SizeAssignment ctx) :
    (fixed p).Value a = p.Carrier := by simp [Value]

@[simp] theorem value_power (d : DomainExpression ctx) (e : SizeExpression ctx)
    (a : SizeAssignment ctx) :
    (power d e).Value a = (Fin (e.eval a) → d.Value a) := by simp [Value]

@[simp] theorem value_product_nil (a : SizeAssignment ctx) :
    (product []).Value a = PUnit.{u + 1} := by simp [Value]

@[simp] theorem value_product_cons (d : DomainExpression ctx) (ds : List (DomainExpression ctx))
    (a : SizeAssignment ctx) :
    (product (d :: ds)).Value a = (d.Value a × (product ds).Value a) := by simp [Value]

@[simp] theorem value_sum (ds : List (DomainExpression ctx)) (a : SizeAssignment ctx) :
    (sum ds).Value a = ((i : Fin ds.length) × (ds.get i).Value a) := by simp [Value]

section DomainDefinitions

/-- Exact encoded width; no polynomial witness needs to be constructed first. -/
def bitWidth (d : DomainExpression ctx) (a : SizeAssignment ctx) : ℕ :=
  match d with
  | .fixed p => p.bitWidth
  | .product [] => 0
  | .product (d :: ds) => d.bitWidth a + (product ds).bitWidth a
  | .sum ds => Nat.clog 2 ds.length + (ds.map fun d => d.bitWidth a).foldr max 0
  | .power d e => e.eval a * d.bitWidth a
termination_by sizeOf d

@[simp] theorem bitWidth_fixed (p : FixedPresentation) (a : SizeAssignment ctx) :
    (fixed p).bitWidth a = p.bitWidth := by simp [bitWidth]

@[simp] theorem bitWidth_power (d : DomainExpression ctx) (e : SizeExpression ctx)
    (a : SizeAssignment ctx) :
    (power d e).bitWidth a = e.eval a * d.bitWidth a := by simp [bitWidth]

@[simp] theorem bitWidth_product_nil (a : SizeAssignment ctx) :
    (product []).bitWidth a = 0 := by simp [bitWidth]

@[simp] theorem bitWidth_product_cons (d : DomainExpression ctx) (ds : List (DomainExpression ctx))
    (a : SizeAssignment ctx) :
    (product (d :: ds)).bitWidth a = d.bitWidth a + (product ds).bitWidth a := by
  simp [bitWidth]

@[simp] theorem bitWidth_sum (ds : List (DomainExpression ctx)) (a : SizeAssignment ctx) :
    (sum ds).bitWidth a =
      Nat.clog 2 ds.length + (ds.map fun d => d.bitWidth a).foldr max 0 := by simp [bitWidth]

private theorem width_le_maximum (ds : List (DomainExpression ctx)) (a : SizeAssignment ctx)
    (i : Fin ds.length) :
    (ds.get i).bitWidth a ≤ (ds.map fun d => d.bitWidth a).foldr max 0 := by
  apply List.le_max_of_le
  · exact List.mem_map.mpr ⟨ds.get i, List.get_mem _ _, rfl⟩
  · exact le_rfl

noncomputable section DomainCodecs

/-- Codecs are assembled directly by recursion over the domain expression. -/
def codec (d : DomainExpression.{u} ctx) (a : SizeAssignment ctx) :
    BitCodec (d.Value a) (d.bitWidth a) :=
  match d with
  | .fixed p => by simpa only [value_fixed, bitWidth_fixed] using p.codec
  | .product [] => by simpa only [value_product_nil, bitWidth_product_nil] using BitCodec.unit
  | .product (d :: ds) => by
      simpa only [value_product_cons, bitWidth_product_cons] using
        (d.codec a).product ((product ds).codec a)
  | .sum ds => by
      simpa only [value_sum, bitWidth_sum] using
        BitCodec.tagged (fun i => (ds.get i).Value a) (fun i => (ds.get i).bitWidth a)
          (fun i => (ds.get i).codec a)
          ((ds.map fun d => d.bitWidth a).foldr max 0) (width_le_maximum ds a)
  | .power d e => by
      simpa only [value_power, bitWidth_power] using (d.codec a).power (e.eval a)
termination_by sizeOf d
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | have h := List.sizeOf_get ds i
      simp only [List.get_eq_getElem] at h
      omega

def encode (d : DomainExpression ctx) (a : SizeAssignment ctx) :
    d.Value a → BitVec (d.bitWidth a) := (d.codec a).encode

/-- View a fixed constructor through its mathematical carrier. -/
def fixedEquiv (presentation : FixedPresentation.{u}) (assignment : SizeAssignment ctx) :
    (fixed presentation).Value assignment ≃ presentation.Carrier :=
  Equiv.cast (value_fixed presentation assignment)

/-- View a power constructor as an ordinary fixed-size tuple. -/
def powerEquiv (base : DomainExpression.{u} ctx) (length : SizeExpression ctx) (assignment : SizeAssignment ctx) :
    (power base length).Value assignment ≃ (Fin (length.eval assignment) → base.Value assignment) :=
  Equiv.cast (value_power base length assignment)

/-- Mathematical indexing hides recursive-carrier casts. -/
def powerLookup (base : DomainExpression.{u} ctx) (length : SizeExpression ctx) (assignment : SizeAssignment ctx)
    (value : (power base length).Value assignment) (index : Fin (length.eval assignment)) : base.Value assignment :=
  powerEquiv base length assignment value index

/-- Constructor values hide the equalities induced by recursive carrier types. -/
def fixedValue (p : FixedPresentation.{u}) (a : SizeAssignment ctx) (value : p.Carrier) :
    (fixed p).Value a := cast (value_fixed p a).symm value

def powerValue (d : DomainExpression.{u} ctx) (e : SizeExpression ctx) (a : SizeAssignment ctx)
    (tuple : Fin (e.eval a) → d.Value a) : (power d e).Value a :=
  cast (value_power d e a).symm tuple

def productValue (d : DomainExpression.{u} ctx) (ds : List (DomainExpression ctx))
    (a : SizeAssignment ctx) (value : d.Value a × (product ds).Value a) :
    (product (d :: ds)).Value a := cast (value_product_cons d ds a).symm value

def sumValue (ds : List (DomainExpression.{u} ctx)) (a : SizeAssignment ctx)
    (value : (i : Fin ds.length) × (ds.get i).Value a) : (sum ds).Value a :=
  cast (value_sum ds a).symm value

private theorem encode_bit_transport {Source Target : Type u} {sourceWidth targetWidth : ℕ}
    (carrier : Source = Target) (width : sourceWidth = targetWidth)
    {source : BitCodec Source sourceWidth} {target : BitCodec Target targetWidth}
    (same : HEq source target) {sourceValue : Source} {targetValue : Target}
    (values : HEq sourceValue targetValue) (offset : ℕ) :
    (source.encode sourceValue).getLsbD offset = (target.encode targetValue).getLsbD offset := by
  cases carrier
  cases width
  cases same
  cases values
  rfl

@[simp] theorem encode_fixed_bit (p : FixedPresentation.{u}) (a : SizeAssignment ctx)
    (value : p.Carrier) (offset : ℕ) :
    ((fixed p).encode a (fixedValue p a value)).getLsbD offset =
      (p.codec.encode value).getLsbD offset := by
  apply encode_bit_transport (value_fixed p a) (bitWidth_fixed p a)
  · simp only [codec]; exact cast_heq _ _
  · exact cast_heq _ _

@[simp] theorem encode_power_bit (d : DomainExpression.{u} ctx) (e : SizeExpression ctx)
    (a : SizeAssignment ctx) (tuple : Fin (e.eval a) → d.Value a) (offset : ℕ) :
    ((power d e).encode a (powerValue d e a tuple)).getLsbD offset =
      (((d.codec a).power (e.eval a)).encode tuple).getLsbD offset := by
  apply encode_bit_transport (value_power d e a) (bitWidth_power d e a)
  · simp only [codec]; exact cast_heq _ _
  · exact cast_heq _ _

/-- Read a component's bits directly from an arbitrary power value. -/
theorem encode_power_lookup_bit (base : DomainExpression.{u} ctx) (length : SizeExpression ctx)
    (assignment : SizeAssignment ctx) (value : (power base length).Value assignment)
    (index : Fin (length.eval assignment)) (offset : Fin (base.bitWidth assignment)) :
    ((power base length).encode assignment value).getLsbD (index.val * base.bitWidth assignment + offset.val) =
      (base.encode assignment (powerLookup base length assignment value index)).getLsbD offset.val := by
  let tuple := powerEquiv base length assignment value
  have represented : value = powerValue base length assignment tuple := by
    change value = (powerEquiv base length assignment).symm tuple
    exact ((powerEquiv base length assignment).symm_apply_apply value).symm
  rw [represented, encode_power_bit]
  simpa only [powerLookup, encode, tuple, ← represented] using
    BitCodec.power_encode_entry_bit (base.codec assignment) (length.eval assignment) tuple index offset

/-- Read a fixed constructor without constructing or exposing carrier casts. -/
theorem encode_fixed_view_bit (presentation : FixedPresentation.{u}) (assignment : SizeAssignment ctx)
    (value : (fixed presentation).Value assignment) (offset : ℕ) :
    ((fixed presentation).encode assignment value).getLsbD offset =
      (presentation.codec.encode (fixedEquiv presentation assignment value)).getLsbD offset := by
  have represented : value = fixedValue presentation assignment (fixedEquiv presentation assignment value) := by
    change value = (fixedEquiv presentation assignment).symm (fixedEquiv presentation assignment value)
    exact ((fixedEquiv presentation assignment).symm_apply_apply value).symm
  rw [represented, encode_fixed_bit]
  simp only [← represented]

/-- Fixed-entry lookup exposes the scalar width directly. -/
theorem encode_power_fixed_lookup_bit (presentation : FixedPresentation.{u}) (length : SizeExpression ctx)
    (assignment : SizeAssignment ctx) (value : (power (fixed presentation) length).Value assignment)
    (index : Fin (length.eval assignment)) (offset : Fin presentation.bitWidth) :
    ((power (fixed presentation) length).encode assignment value).getLsbD
        (index.val * presentation.bitWidth + offset.val) =
      (presentation.codec.encode (fixedEquiv presentation assignment
        (powerLookup (fixed presentation) length assignment value index))).getLsbD offset.val := by
  have component := encode_power_lookup_bit (fixed presentation) length assignment value index
    ⟨offset.val, by simp⟩
  simpa only [bitWidth_fixed] using component.trans (encode_fixed_view_bit presentation assignment _ offset.val)

@[simp] theorem encode_product_bit (d : DomainExpression.{u} ctx) (ds : List (DomainExpression ctx))
    (a : SizeAssignment ctx) (value : d.Value a × (product ds).Value a) (offset : ℕ) :
    ((product (d :: ds)).encode a (productValue d ds a value)).getLsbD offset =
      (((d.codec a).product ((product ds).codec a)).encode value).getLsbD offset := by
  apply encode_bit_transport (value_product_cons d ds a) (bitWidth_product_cons d ds a)
  · simp only [codec]; exact cast_heq _ _
  · exact cast_heq _ _

@[simp] theorem encode_sum_bit (ds : List (DomainExpression.{u} ctx)) (a : SizeAssignment ctx)
    (value : (i : Fin ds.length) × (ds.get i).Value a) (offset : ℕ) :
    ((sum ds).encode a (sumValue ds a value)).getLsbD offset =
      ((BitCodec.tagged (fun i => (ds.get i).Value a) (fun i => (ds.get i).bitWidth a)
        (fun i => (ds.get i).codec a)
        ((ds.map fun d => d.bitWidth a).foldr max 0) (width_le_maximum ds a)).encode value).getLsbD offset := by
  apply encode_bit_transport (value_sum ds a) (bitWidth_sum ds a)
  · simp only [codec]; exact cast_heq _ _
  · exact cast_heq _ _

/-- Constructor equations expose bit vectors at their ordinary component widths. -/
@[simp] theorem encode_fixed (p : FixedPresentation.{u}) (a : SizeAssignment ctx) (value : p.Carrier) :
    ((fixed p).encode a (fixedValue p a value)).cast (bitWidth_fixed p a) = p.codec.encode value := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro offset valid
  simp only [BitVec.getLsbD_cast]
  exact encode_fixed_bit p a value offset

@[simp] theorem encode_power (d : DomainExpression.{u} ctx) (e : SizeExpression ctx)
    (a : SizeAssignment ctx) (tuple : Fin (e.eval a) → d.Value a) :
    ((power d e).encode a (powerValue d e a tuple)).cast (bitWidth_power d e a) =
      ((d.codec a).power (e.eval a)).encode tuple := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro offset valid
  simp only [BitVec.getLsbD_cast]
  exact encode_power_bit d e a tuple offset

@[simp] theorem encode_product (d : DomainExpression.{u} ctx) (ds : List (DomainExpression ctx))
    (a : SizeAssignment ctx) (value : d.Value a × (product ds).Value a) :
    ((product (d :: ds)).encode a (productValue d ds a value)).cast (bitWidth_product_cons d ds a) =
      ((d.codec a).product ((product ds).codec a)).encode value := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro offset valid
  simp only [BitVec.getLsbD_cast]
  exact encode_product_bit d ds a value offset

@[simp] theorem encode_sum (ds : List (DomainExpression.{u} ctx)) (a : SizeAssignment ctx)
    (value : (i : Fin ds.length) × (ds.get i).Value a) :
    ((sum ds).encode a (sumValue ds a value)).cast (bitWidth_sum ds a) =
      (BitCodec.tagged (fun i => (ds.get i).Value a) (fun i => (ds.get i).bitWidth a)
        (fun i => (ds.get i).codec a)
        ((ds.map fun d => d.bitWidth a).foldr max 0) (width_le_maximum ds a)).encode value := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro offset valid
  simp only [BitVec.getLsbD_cast]
  exact encode_sum_bit ds a value offset

/-- Fixed-carrier powers expose ordinary mathematical tuples directly. -/
def powerFixedValue (p : FixedPresentation.{u}) (e : SizeExpression ctx)
    (a : SizeAssignment ctx) (tuple : Fin (e.eval a) → p.Carrier) :
    (power (fixed p) e).Value a :=
  powerValue (fixed p) e a (fun index => fixedValue p a (tuple index))

private theorem power_codec_transport {Source Target : Type u} {sourceWidth targetWidth length : ℕ}
    (carrier : Source = Target) (width : sourceWidth = targetWidth)
    {source : BitCodec Source sourceWidth} {target : BitCodec Target targetWidth}
    (same : HEq source target) : HEq (source.power length) (target.power length) := by
  cases carrier
  cases width
  cases same
  rfl

private theorem tuple_cast_heq {Source Target : Type u} {length : ℕ}
    (carrier : Source = Target) (tuple : Fin length → Source) :
    HEq (fun index => cast carrier (tuple index)) tuple := by
  cases carrier
  rfl

/-- The constructor agrees with the direct mathematical carrier identification. -/
theorem powerFixedValue_eq_cast (p : FixedPresentation.{u}) (e : SizeExpression ctx)
    (a : SizeAssignment ctx) (tuple : Fin (e.eval a) → p.Carrier) :
    powerFixedValue p e a tuple =
      cast (by simp only [value_power, value_fixed] :
        (power (fixed p) e).Value a = (Fin (e.eval a) → p.Carrier)).symm tuple := by
  apply eq_of_heq
  exact ((cast_heq _ _).trans (tuple_cast_heq (value_fixed p a).symm tuple)).trans
    (cast_heq _ _).symm

@[simp] theorem encode_power_fixed_bit (p : FixedPresentation.{u}) (e : SizeExpression ctx)
    (a : SizeAssignment ctx) (tuple : Fin (e.eval a) → p.Carrier) (offset : ℕ) :
    ((power (fixed p) e).encode a (powerFixedValue p e a tuple)).getLsbD offset =
      ((p.codec.power (e.eval a)).encode tuple).getLsbD offset := by
  rw [powerFixedValue, encode_power_bit]
  have same : HEq ((fixed p : DomainExpression ctx).codec a) p.codec := by
    simp only [codec]; exact cast_heq _ _
  have powers := power_codec_transport (length := e.eval a) (value_fixed p a) (bitWidth_fixed p a) same
  exact encode_bit_transport (by rw [value_fixed]) (by rw [bitWidth_fixed]) powers
    (tuple_cast_heq (value_fixed p a).symm tuple) offset

def decode (d : DomainExpression ctx) (a : SizeAssignment ctx) :
    BitVec (d.bitWidth a) → Option (d.Value a) := (d.codec a).decode

@[simp] theorem decode_encode (d : DomainExpression ctx) (a : SizeAssignment ctx) (x : d.Value a) :
    d.decode a (d.encode a x) = some x := (d.codec a).decode_encode x

theorem encode_decode (d : DomainExpression ctx) (a : SizeAssignment ctx)
    (bits : BitVec (d.bitWidth a)) (x : d.Value a) (h : d.decode a bits = some x) :
    d.encode a x = bits := (d.codec a).encode_decode bits x h

theorem encode_injective (d : DomainExpression ctx) (a : SizeAssignment ctx) :
    Function.Injective (d.encode a) := by
  intro x y h
  have := congrArg (d.decode a) h
  simpa using this

end DomainCodecs

noncomputable section DomainBounds

/-- An automatically composed polynomial upper bound on encoded width. -/
def sizeBound (d : DomainExpression ctx) : SizePolynomial ctx :=
  match d with
  | .fixed p => SizePolynomial.constant p.bitWidth
  | .product ds => (ds.map sizeBound).sum
  | .sum ds => SizePolynomial.constant (Nat.clog 2 ds.length) + (ds.map sizeBound).sum
  | .power d e => e.polynomial * d.sizeBound
termination_by sizeOf d

private theorem maximum_le_bound (ds : List (DomainExpression ctx)) (a : SizeAssignment ctx)
    (h : ∀ d ∈ ds, d.bitWidth a ≤ d.sizeBound.eval a) :
    (ds.map fun d => d.bitWidth a).foldr max 0 ≤ ((ds.map sizeBound).sum).eval a := by
  induction ds with
  | nil => simp
  | cons d ds ih =>
      simp only [List.map_cons, List.foldr_cons, List.sum_cons, SizePolynomial.eval_add]
      exact max_le
        ((h d (List.mem_cons_self ..)).trans (Nat.le_add_right _ _))
        ((ih (fun d hd => h d (List.mem_cons_of_mem _ hd))).trans (Nat.le_add_left _ _))

theorem bitWidth_le (d : DomainExpression ctx) (a : SizeAssignment ctx) :
    d.bitWidth a ≤ d.sizeBound.eval a := by
  cases d with
  | fixed p => simp [sizeBound]
  | product ds =>
      cases ds with
      | nil => simp [sizeBound]
      | cons d ds =>
          simpa [sizeBound] using
            Nat.add_le_add (bitWidth_le d a) (bitWidth_le (product ds) a)
  | sum ds =>
      simp only [bitWidth_sum, sizeBound, SizePolynomial.eval_add, SizePolynomial.eval_constant]
      exact Nat.add_le_add_left (maximum_le_bound ds a (fun d hd => bitWidth_le d a)) _
  | power d e =>
      simpa [sizeBound, ← SizeExpression.eval_eq] using Nat.mul_le_mul_left (e.polynomial.eval a) (bitWidth_le d a)
termination_by sizeOf d

theorem polynomially_bounded (d : DomainExpression ctx) :
    ∃ p : SizePolynomial ctx, ∀ a, d.bitWidth a ≤ p.eval a :=
  ⟨d.sizeBound, d.bitWidth_le⟩

end DomainBounds
end DomainDefinitions
end DomainExpression
end Polytime
