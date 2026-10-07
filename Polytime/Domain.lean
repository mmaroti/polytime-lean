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

noncomputable section DomainDefinitions

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

/-- An automatically composed polynomial upper bound on encoded width. -/
def sizeBound (d : DomainExpression ctx) : SizeExpression ctx :=
  match d with
  | .fixed p => SizeExpression.constant p.bitWidth
  | .product ds => (ds.map sizeBound).sum
  | .sum ds => SizeExpression.constant (Nat.clog 2 ds.length) + (ds.map sizeBound).sum
  | .power d e => e * d.sizeBound
termination_by sizeOf d

private theorem maximum_le_bound (ds : List (DomainExpression ctx)) (a : SizeAssignment ctx)
    (h : ∀ d ∈ ds, d.bitWidth a ≤ d.sizeBound.eval a) :
    (ds.map fun d => d.bitWidth a).foldr max 0 ≤ ((ds.map sizeBound).sum).eval a := by
  induction ds with
  | nil => simp
  | cons d ds ih =>
      simp only [List.map_cons, List.foldr_cons, List.sum_cons, SizeExpression.eval_add]
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
      simp only [bitWidth_sum, sizeBound, SizeExpression.eval_add, SizeExpression.eval_constant]
      exact Nat.add_le_add_left (maximum_le_bound ds a (fun d hd => bitWidth_le d a)) _
  | power d e =>
      simpa [sizeBound] using Nat.mul_le_mul_left (e.eval a) (bitWidth_le d a)
termination_by sizeOf d

theorem polynomially_bounded (d : DomainExpression ctx) :
    ∃ p : SizeExpression ctx, ∀ a, d.bitWidth a ≤ p.eval a :=
  ⟨d.sizeBound, d.bitWidth_le⟩

end DomainDefinitions
end DomainExpression
end Polytime
