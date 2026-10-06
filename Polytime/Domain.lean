import Polytime.Size
import Polytime.Encoding
import Mathlib.Data.List.MinMax

/-! # Recursive parametric domains

Parameter assignments index values and exact widths. Only the polynomial-size
theorems require admissibility. No size headers are included in these codecs.
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

inductive DomainExpr (Param : Type) : Type (u + 1)
  | fixed (presentation : FinitePresentation.{u})
  | product (children : List (DomainExpr Param))
  | sum (alternatives : List (DomainExpr Param))
  | power (base : DomainExpr Param) (exponent : SizeExpr Param)

/-- A semantic interpretation, with an internal, automatically composed bound. -/
structure DomainFamily {Param : Type} [Fintype Param] (ctx : SizeContext Param) where
  Value : SizeAssignment Param → Type u
  width : SizeAssignment Param → ℕ
  rawCodec : ∀ a, RawCodec (Value a) (width a)
  bound : Polynomial ℕ
  width_le : ∀ a, ctx.Admissible a → width a ≤ bound.eval a.N

namespace DomainFamily

variable {Param : Type} [Fintype Param] {ctx : SizeContext Param}

noncomputable section

def fixed (p : FinitePresentation.{u}) : DomainFamily ctx where
  Value _ := p.Carrier
  width _ := p.bitWidth
  rawCodec _ := p.codec
  bound := Polynomial.C p.bitWidth
  width_le _ _ := by simp

def product : List (DomainFamily.{u} ctx) → DomainFamily ctx
  | [] =>
      { Value := fun _ => PUnit
        width := fun _ => 0
        rawCodec := fun _ => RawCodec.unit
        bound := 0
        width_le := fun _ _ => by simp }
  | d :: ds =>
      { Value := fun a => d.Value a × (product ds).Value a
        width := fun a => d.width a + (product ds).width a
        rawCodec := fun a => (d.rawCodec a).product ((product ds).rawCodec a)
        bound := d.bound + (product ds).bound
        width_le := fun a ha => by
          simpa using Nat.add_le_add (d.width_le a ha) ((product ds).width_le a ha) }

def maximumWidth (ds : List (DomainFamily ctx)) (a : SizeAssignment Param) : ℕ :=
  (ds.map fun d => d.width a).foldr max 0

theorem width_le_maximum (ds : List (DomainFamily ctx)) (a : SizeAssignment Param)
    (i : Fin ds.length) : (ds.get i).width a ≤ maximumWidth ds a := by
  apply List.le_max_of_le
  · exact List.mem_map.mpr ⟨ds.get i, List.get_mem _ _, rfl⟩
  · exact le_rfl

theorem maximum_le_bound (ds : List (DomainFamily ctx)) (a : SizeAssignment Param)
    (ha : ctx.Admissible a) : maximumWidth ds a ≤ (product ds).bound.eval a.N := by
  induction ds with
  | nil => simp [maximumWidth, product]
  | cons d ds ih =>
      simp only [maximumWidth, List.map_cons, List.foldr_cons, product, Polynomial.eval_add]
      exact max_le
        ((d.width_le a ha).trans (Nat.le_add_right _ _))
        (ih.trans (Nat.le_add_left _ _))

def sum (ds : List (DomainFamily.{u} ctx)) : DomainFamily ctx where
  Value a := (i : Fin ds.length) × (ds.get i).Value a
  width a := Nat.clog 2 ds.length + maximumWidth ds a
  rawCodec a := RawCodec.tagged _ _ (fun i => (ds.get i).rawCodec a)
    (maximumWidth ds a) (width_le_maximum ds a)
  bound := Polynomial.C (Nat.clog 2 ds.length) + (product ds).bound
  width_le a ha := by
    simpa using Nat.add_le_add_left (maximum_le_bound ds a ha) (Nat.clog 2 ds.length)

def power (d : DomainFamily.{u} ctx) (e : SizeExpr Param) : DomainFamily ctx where
  Value a := Fin (e.eval a) → d.Value a
  width a := e.eval a * d.width a
  rawCodec a := (d.rawCodec a).power (e.eval a)
  bound := e.envelope ctx * d.bound
  width_le a ha := by
    simpa using Nat.mul_le_mul (e.eval_le_envelope ctx a ha) (d.width_le a ha)

end
end DomainFamily

namespace DomainExpr

variable {Param : Type} [Fintype Param]

noncomputable def interpret (ctx : SizeContext Param) : DomainExpr.{u} Param → DomainFamily ctx
  | .fixed p => DomainFamily.fixed p
  | .product ds => DomainFamily.product (ds.map (interpret ctx))
  | .sum ds => DomainFamily.sum (ds.map (interpret ctx))
  | .power d e => DomainFamily.power (interpret ctx d) e

def Value (d : DomainExpr Param) (ctx : SizeContext Param) (a : SizeAssignment Param) : Type u :=
  (d.interpret ctx).Value a

@[simp] theorem value_fixed (p : FinitePresentation.{u}) (ctx : SizeContext Param)
    (a : SizeAssignment Param) : (fixed p).Value ctx a = p.Carrier := by
  simp [Value, interpret, DomainFamily.fixed]

@[simp] theorem value_power (d : DomainExpr Param) (e : SizeExpr Param)
    (ctx : SizeContext Param) (a : SizeAssignment Param) :
    (power d e).Value ctx a = (Fin (e.eval a) → d.Value ctx a) := by
  simp [Value, interpret, DomainFamily.power]

@[simp] theorem value_product_nil (ctx : SizeContext Param) (a : SizeAssignment Param) :
    (product []).Value ctx a = PUnit.{u + 1} := by simp [Value, interpret, DomainFamily.product]

@[simp] theorem value_product_cons (d : DomainExpr Param) (ds : List (DomainExpr Param))
    (ctx : SizeContext Param) (a : SizeAssignment Param) :
    (product (d :: ds)).Value ctx a = (d.Value ctx a × (product ds).Value ctx a) := by
  simp [Value, interpret, DomainFamily.product]

noncomputable def bitWidth (d : DomainExpr Param) (ctx : SizeContext Param)
    (a : SizeAssignment Param) : ℕ := (d.interpret ctx).width a

noncomputable def codec (d : DomainExpr Param) (ctx : SizeContext Param)
    (a : SizeAssignment Param) : BitCodec (d.Value ctx a) (d.bitWidth ctx a) :=
  ((d.interpret ctx).rawCodec a).toBitCodec

noncomputable def encode (d : DomainExpr Param) (ctx : SizeContext Param)
    (a : SizeAssignment Param) : d.Value ctx a → BitVec (d.bitWidth ctx a) :=
  (d.codec ctx a).encode

noncomputable def decode (d : DomainExpr Param) (ctx : SizeContext Param)
    (a : SizeAssignment Param) : BitVec (d.bitWidth ctx a) → Option (d.Value ctx a) :=
  (d.codec ctx a).decode

@[simp] theorem decode_encode (d : DomainExpr Param) (ctx : SizeContext Param)
    (a : SizeAssignment Param) (x : d.Value ctx a) :
    d.decode ctx a (d.encode ctx a x) = some x := (d.codec ctx a).decode_encode x

theorem encode_decode (d : DomainExpr Param) (ctx : SizeContext Param)
    (a : SizeAssignment Param) (bits : BitVec (d.bitWidth ctx a)) (x : d.Value ctx a)
    (h : d.decode ctx a bits = some x) : d.encode ctx a x = bits :=
  (d.codec ctx a).encode_decode bits x h

theorem encode_injective (d : DomainExpr Param) (ctx : SizeContext Param)
    (a : SizeAssignment Param) : Function.Injective (d.encode ctx a) := by
  intro x y h
  have := congrArg (d.decode ctx a) h
  simpa using this

noncomputable def sizeBound (d : DomainExpr Param) (ctx : SizeContext Param) : Polynomial ℕ :=
  (d.interpret ctx).bound

@[simp] theorem bitWidth_fixed (p : FinitePresentation) (ctx : SizeContext Param)
    (a : SizeAssignment Param) : (fixed p).bitWidth ctx a = p.bitWidth := by
  simp [bitWidth, interpret, DomainFamily.fixed]

@[simp] theorem bitWidth_power (d : DomainExpr Param) (e : SizeExpr Param)
    (ctx : SizeContext Param) (a : SizeAssignment Param) :
    (power d e).bitWidth ctx a = e.eval a * d.bitWidth ctx a := by
  simp [bitWidth, interpret, DomainFamily.power]

@[simp] theorem bitWidth_product_nil (ctx : SizeContext Param) (a : SizeAssignment Param) :
    (product []).bitWidth ctx a = 0 := by simp [bitWidth, interpret, DomainFamily.product]

@[simp] theorem bitWidth_product_cons (d : DomainExpr Param) (ds : List (DomainExpr Param))
    (ctx : SizeContext Param) (a : SizeAssignment Param) :
    (product (d :: ds)).bitWidth ctx a = d.bitWidth ctx a + (product ds).bitWidth ctx a := by
  simp [bitWidth, interpret, DomainFamily.product]

@[simp] theorem bitWidth_sum (ds : List (DomainExpr Param)) (ctx : SizeContext Param)
    (a : SizeAssignment Param) : (sum ds).bitWidth ctx a =
      Nat.clog 2 ds.length + (ds.map fun d => d.bitWidth ctx a).foldr max 0 := by
  simp [bitWidth, interpret, DomainFamily.sum, DomainFamily.maximumWidth, List.map_map,
    Function.comp_def]

theorem bitWidth_le (d : DomainExpr Param) (ctx : SizeContext Param)
    (a : SizeAssignment Param) (ha : ctx.Admissible a) :
    d.bitWidth ctx a ≤ (d.sizeBound ctx).eval a.N := (d.interpret ctx).width_le a ha

theorem polynomially_bounded (d : DomainExpr Param) (ctx : SizeContext Param) :
    ∃ p : Polynomial ℕ, ∀ a, ctx.Admissible a → d.bitWidth ctx a ≤ p.eval a.N :=
  ⟨d.sizeBound ctx, d.bitWidth_le ctx⟩

end DomainExpr
end Polytime
