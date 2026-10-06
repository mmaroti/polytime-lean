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

structure FinitePresentation where
  Carrier : Type u
  cardinality : ℕ
  enumeration : Carrier ≃ Fin cardinality

namespace FinitePresentation

def bitWidth (p : FinitePresentation.{u}) : ℕ := Nat.clog 2 p.cardinality

def codec (p : FinitePresentation.{u}) : RawCodec p.Carrier p.bitWidth :=
  (RawCodec.fin p.cardinality).transport p.enumeration.symm

def fin (k : ℕ) : FinitePresentation where
  Carrier := Fin k
  cardinality := k
  enumeration := Equiv.refl _

end FinitePresentation

inductive DomainExpr (ctx : SizeContext) : Type (u + 1)
  | fixed (presentation : FinitePresentation.{u})
  | product (children : List (DomainExpr ctx))
  | sum (alternatives : List (DomainExpr ctx))
  | power (base : DomainExpr ctx) (exponent : SizeExpr ctx)

/-- A semantic interpretation, with an internal, automatically composed bound. -/
structure DomainFamily (ctx : SizeContext) where
  Value : SizeAssignment ctx → Type u
  width : SizeAssignment ctx → ℕ
  rawCodec : ∀ a, RawCodec (Value a) (width a)
  bound : SizeExpr ctx
  width_le : ∀ a, width a ≤ bound.eval a

namespace DomainFamily

variable {ctx : SizeContext}

noncomputable section

def fixed (p : FinitePresentation.{u}) : DomainFamily ctx where
  Value _ := p.Carrier
  width _ := p.bitWidth
  rawCodec _ := p.codec
  bound := SizeExpr.constant p.bitWidth
  width_le _ := by simp

def product : List (DomainFamily.{u} ctx) → DomainFamily ctx
  | [] =>
      { Value := fun _ => PUnit
        width := fun _ => 0
        rawCodec := fun _ => RawCodec.unit
        bound := 0
        width_le := fun _ => by simp }
  | d :: ds =>
      { Value := fun a => d.Value a × (product ds).Value a
        width := fun a => d.width a + (product ds).width a
        rawCodec := fun a => (d.rawCodec a).product ((product ds).rawCodec a)
        bound := d.bound + (product ds).bound
        width_le := fun a => by
          simpa using Nat.add_le_add (d.width_le a) ((product ds).width_le a) }

def maximumWidth (ds : List (DomainFamily ctx)) (a : SizeAssignment ctx) : ℕ :=
  (ds.map fun d => d.width a).foldr max 0

theorem width_le_maximum (ds : List (DomainFamily ctx)) (a : SizeAssignment ctx)
    (i : Fin ds.length) : (ds.get i).width a ≤ maximumWidth ds a := by
  apply List.le_max_of_le
  · exact List.mem_map.mpr ⟨ds.get i, List.get_mem _ _, rfl⟩
  · exact le_rfl

theorem maximum_le_bound (ds : List (DomainFamily ctx)) (a : SizeAssignment ctx) :
    maximumWidth ds a ≤ (product ds).bound.eval a := by
  induction ds with
  | nil => simp [maximumWidth, product]
  | cons d ds ih =>
      simp only [maximumWidth, List.map_cons, List.foldr_cons, product, SizeExpr.eval_add]
      exact max_le
        ((d.width_le a).trans (Nat.le_add_right _ _))
        (ih.trans (Nat.le_add_left _ _))

def sum (ds : List (DomainFamily.{u} ctx)) : DomainFamily ctx where
  Value a := (i : Fin ds.length) × (ds.get i).Value a
  width a := Nat.clog 2 ds.length + maximumWidth ds a
  rawCodec a := RawCodec.tagged _ _ (fun i => (ds.get i).rawCodec a)
    (maximumWidth ds a) (width_le_maximum ds a)
  bound := SizeExpr.constant (Nat.clog 2 ds.length) + (product ds).bound
  width_le a := by
    simpa using Nat.add_le_add_left (maximum_le_bound ds a) (Nat.clog 2 ds.length)

def power (d : DomainFamily.{u} ctx) (e : SizeExpr ctx) : DomainFamily ctx where
  Value a := Fin (e.eval a) → d.Value a
  width a := e.eval a * d.width a
  rawCodec a := (d.rawCodec a).power (e.eval a)
  bound := e * d.bound
  width_le a := by
    simpa using Nat.mul_le_mul (le_refl (e.eval a)) (d.width_le a)

end
end DomainFamily

namespace DomainExpr

variable {ctx : SizeContext}

noncomputable def interpret : DomainExpr.{u} ctx → DomainFamily ctx
  | .fixed p => DomainFamily.fixed p
  | .product ds => DomainFamily.product (ds.map interpret)
  | .sum ds => DomainFamily.sum (ds.map interpret)
  | .power d e => DomainFamily.power (interpret d) e

def Value (d : DomainExpr ctx) (a : SizeAssignment ctx) : Type u :=
  d.interpret.Value a

@[simp] theorem value_fixed (p : FinitePresentation.{u})
    (a : SizeAssignment ctx) : (fixed p).Value a = p.Carrier := by
  simp [Value, interpret, DomainFamily.fixed]

@[simp] theorem value_power (d : DomainExpr ctx) (e : SizeExpr ctx)
    (a : SizeAssignment ctx) :
    (power d e).Value a = (Fin (e.eval a) → d.Value a) := by
  simp [Value, interpret, DomainFamily.power]

@[simp] theorem value_product_nil (a : SizeAssignment ctx) :
    (product []).Value a = PUnit.{u + 1} := by simp [Value, interpret, DomainFamily.product]

@[simp] theorem value_product_cons (d : DomainExpr ctx) (ds : List (DomainExpr ctx))
    (a : SizeAssignment ctx) :
    (product (d :: ds)).Value a = (d.Value a × (product ds).Value a) := by
  simp [Value, interpret, DomainFamily.product]

noncomputable def bitWidth (d : DomainExpr ctx)
    (a : SizeAssignment ctx) : ℕ := d.interpret.width a

noncomputable def codec (d : DomainExpr ctx)
    (a : SizeAssignment ctx) : BitCodec (d.Value a) (d.bitWidth a) :=
  (d.interpret.rawCodec a).toBitCodec

noncomputable def encode (d : DomainExpr ctx)
    (a : SizeAssignment ctx) : d.Value a → BitVec (d.bitWidth a) :=
  (d.codec a).encode

noncomputable def decode (d : DomainExpr ctx)
    (a : SizeAssignment ctx) : BitVec (d.bitWidth a) → Option (d.Value a) :=
  (d.codec a).decode

@[simp] theorem decode_encode (d : DomainExpr ctx)
    (a : SizeAssignment ctx) (x : d.Value a) :
    d.decode a (d.encode a x) = some x := (d.codec a).decode_encode x

theorem encode_decode (d : DomainExpr ctx)
    (a : SizeAssignment ctx) (bits : BitVec (d.bitWidth a)) (x : d.Value a)
    (h : d.decode a bits = some x) : d.encode a x = bits :=
  (d.codec a).encode_decode bits x h

theorem encode_injective (d : DomainExpr ctx)
    (a : SizeAssignment ctx) : Function.Injective (d.encode a) := by
  intro x y h
  have := congrArg (d.decode a) h
  simpa using this

noncomputable def sizeBound (d : DomainExpr ctx) : SizeExpr ctx :=
  d.interpret.bound

@[simp] theorem bitWidth_fixed (p : FinitePresentation)
    (a : SizeAssignment ctx) : (fixed p).bitWidth a = p.bitWidth := by
  simp [bitWidth, interpret, DomainFamily.fixed]

@[simp] theorem bitWidth_power (d : DomainExpr ctx) (e : SizeExpr ctx)
    (a : SizeAssignment ctx) :
    (power d e).bitWidth a = e.eval a * d.bitWidth a := by
  simp [bitWidth, interpret, DomainFamily.power]

@[simp] theorem bitWidth_product_nil (a : SizeAssignment ctx) :
    (product []).bitWidth a = 0 := by simp [bitWidth, interpret, DomainFamily.product]

@[simp] theorem bitWidth_product_cons (d : DomainExpr ctx) (ds : List (DomainExpr ctx))
    (a : SizeAssignment ctx) :
    (product (d :: ds)).bitWidth a = d.bitWidth a + (product ds).bitWidth a := by
  simp [bitWidth, interpret, DomainFamily.product]

@[simp] theorem bitWidth_sum (ds : List (DomainExpr ctx))
    (a : SizeAssignment ctx) : (sum ds).bitWidth a =
      Nat.clog 2 ds.length + (ds.map fun d => d.bitWidth a).foldr max 0 := by
  simp [bitWidth, interpret, DomainFamily.sum, DomainFamily.maximumWidth, List.map_map,
    Function.comp_def]

theorem bitWidth_le (d : DomainExpr ctx)
    (a : SizeAssignment ctx) :
    d.bitWidth a ≤ d.sizeBound.eval a := d.interpret.width_le a

theorem polynomially_bounded (d : DomainExpr ctx) :
    ∃ p : SizeExpr ctx, ∀ a, d.bitWidth a ≤ p.eval a :=
  ⟨d.sizeBound, d.bitWidth_le⟩

end DomainExpr
end Polytime
