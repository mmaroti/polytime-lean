import Polytime.Examples.Matrices

/-! # Encoding and boundary examples

These kernel-checked examples exercise layout and rejection, in addition to
the generic round-trip and canonical-decoding proofs.
-/

namespace Polytime.Examples.Domains

noncomputable section

def context : SizeContext Empty := ⟨Empty.elim⟩
def assignment (N : ℕ) : SizeAssignment Empty := ⟨N, Empty.elim⟩

example (N : ℕ) : context.Admissible (assignment N) := by intro k; exact Empty.elim k

def emptyFixed : DomainExpr Empty := .fixed (FinitePresentation.fin 0)
def singletonFixed : DomainExpr Empty := .fixed (FinitePresentation.fin 1)

example (N : ℕ) : emptyFixed.bitWidth context (assignment N) = 0 := by
  simp [emptyFixed, FinitePresentation.bitWidth, FinitePresentation.fin]

example (N : ℕ) : IsEmpty (emptyFixed.Value context (assignment N)) := by
  simp only [emptyFixed, DomainExpr.value_fixed, FinitePresentation.fin]
  infer_instance

example (N : ℕ) : singletonFixed.bitWidth context (assignment N) = 0 := by
  simp [singletonFixed, FinitePresentation.bitWidth, FinitePresentation.fin]

example : (RawCodec.fin 0).decode (fun i => Fin.elim0 i) = none := by decide
example : (RawCodec.fin 1).toBitCodec.decode (BitVec.ofNat 0 0) = some ⟨0, by decide⟩ := by
  decide

example (N : ℕ) : (DomainExpr.product []).bitWidth context (assignment N) = 0 := by simp
example (N : ℕ) : (DomainExpr.sum []).bitWidth context (assignment N) = 0 := by simp

example : RawCodec.unit.toBitCodec.decode (BitVec.ofNat 0 0) = some PUnit.unit := by decide

def zeroPower : DomainExpr Empty := .power emptyFixed (SizeExpr.constant 0)

example (N : ℕ) : zeroPower.bitWidth context (assignment N) = 0 := by simp [zeroPower]

example (N : ℕ) : Unique (zeroPower.Value context (assignment N)) := by
  simp only [zeroPower, DomainExpr.value_power, SizeExpr.eval_constant]
  infer_instance

example (N : ℕ) : IsEmpty ((DomainExpr.power emptyFixed (SizeExpr.constant 1)).Value
    context (assignment N)) := by
  simp only [DomainExpr.value_power, SizeExpr.eval_constant, emptyFixed, DomainExpr.value_fixed,
    FinitePresentation.fin]
  infer_instance

def alternatives : DomainExpr Empty :=
  .sum [.fixed (FinitePresentation.fin 2), .fixed (FinitePresentation.fin 3)]

example (N : ℕ) : alternatives.bitWidth context (assignment N) = 3 := by
  simp [alternatives, FinitePresentation.bitWidth, FinitePresentation.fin]
  decide

/-- First alternative has a one-bit payload, second a two-bit payload. -/
def widths : Fin 2 → ℕ := ![1, 2]
def carriers : Fin 2 → Type := fun i => if i.val = 0 then Fin 2 else Fin 3

instance (i : Fin 2) : DecidableEq (carriers i) := by
  unfold carriers
  split <;> infer_instance

def alternativeCodecs : (i : Fin 2) → RawCodec (carriers i) (widths i) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact RawCodec.fin 2
  · refine Fin.cases ?_ (fun k => Fin.elim0 k) j
    exact RawCodec.fin 3

def sumCodec : RawCodec (Sigma carriers) 3 :=
  RawCodec.tagged carriers widths alternativeCodecs 2
    (by intro i; fin_cases i <;> decide)

/-- Tag 0, payload 1, zero high padding: bits [0,1,0]. -/
example : sumCodec.toBitCodec.encode ⟨0, (1 : Fin 2)⟩ = BitVec.ofNat 3 2 := by decide
example : sumCodec.toBitCodec.decode (BitVec.ofNat 3 2) = some ⟨0, (1 : Fin 2)⟩ := by decide

/-- The same payload with nonzero padding must be rejected. -/
example : sumCodec.toBitCodec.decode (BitVec.ofNat 3 6) = none := by decide

/-- Tag 1 with unused payload label 3 must be rejected. -/
example : sumCodec.toBitCodec.decode (BitVec.ofNat 3 7) = none := by decide

/-- A three-alternative union leaves binary tag 3 unused. -/
def threeAlternatives : RawCodec ((_i : Fin 3) × Fin 1) 2 :=
  RawCodec.tagged (fun _ => Fin 1) (fun _ => 0) (fun _ => RawCodec.fin 1) 0
    (by intro i; exact le_rfl)

example : threeAlternatives.toBitCodec.decode (BitVec.ofNat 2 3) = none := by decide

example : (RawCodec.fin 3).toBitCodec.decode (BitVec.ofNat 2 3) = none := by decide

/-- Product fields occupy low bits first: label 1 then the two-bit label 2. -/
example : ((RawCodec.fin 2).product (RawCodec.fin 3)).toBitCodec.encode (1, 2) =
    BitVec.ofNat 3 5 := by
  apply BitVec.toNat_injective
  decide

/-- Power entries likewise occupy consecutive low-to-high blocks. -/
example : ((RawCodec.fin 3).power 3).toBitCodec.encode ![0, 1, 2] =
    BitVec.ofNat 6 36 := by
  apply BitVec.toNat_injective
  decide

/-- Arbitrary carrier universes are supported, including by encodings. -/
def lifted : FinitePresentation.{1} where
  Carrier := ULift.{1} (Fin 2)
  cardinality := 2
  enumeration := Equiv.ulift

example (x : lifted.Carrier) : lifted.codec.decode (lifted.codec.encode x) = some x :=
  lifted.codec.decode_encode x

def nested : DomainExpr Empty :=
  .product [alternatives, .power (.power singletonFixed SizeExpr.main) (SizeExpr.main ^ 2)]

example : ∃ p : Polynomial ℕ, ∀ a, context.Admissible a → nested.bitWidth context a ≤ p.eval a.N :=
  nested.polynomially_bounded context

end
end Polytime.Examples.Domains
