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

import Polytime.Examples.Matrices

/-! # Encoding and boundary examples

These kernel-checked examples exercise layout and rejection, in addition to
the generic round-trip and canonical-decoding proofs.
-/

namespace Polytime.Examples.Domains

noncomputable section DomainExamples

abbrev context : SizeContext := ⟨Empty, inferInstance⟩
def assignment : SizeAssignment context := Empty.elim

def emptyFixed : DomainExpr context := .fixed (FinitePresentation.fin 0)
def singletonFixed : DomainExpr context := .fixed (FinitePresentation.fin 1)

example : emptyFixed.bitWidth assignment = 0 := by
  simp [emptyFixed, FinitePresentation.bitWidth, FinitePresentation.fin]

example : IsEmpty (emptyFixed.Value assignment) := by
  simp only [emptyFixed, DomainExpr.value_fixed, FinitePresentation.fin]
  infer_instance

example : singletonFixed.bitWidth assignment = 0 := by
  simp [singletonFixed, FinitePresentation.bitWidth, FinitePresentation.fin]

example : (RawCodec.fin 0).decode (fun i => Fin.elim0 i) = none := by decide
example : (RawCodec.fin 1).toBitCodec.decode (BitVec.ofNat 0 0) = some ⟨0, by decide⟩ := by
  decide

example : (DomainExpr.product []).bitWidth assignment = 0 := by simp
example : (DomainExpr.sum []).bitWidth assignment = 0 := by simp

example : RawCodec.unit.toBitCodec.decode (BitVec.ofNat 0 0) = some PUnit.unit := by decide

def zeroPower : DomainExpr context := .power emptyFixed (SizeExpression.constant 0)

example : zeroPower.bitWidth assignment = 0 := by simp [zeroPower]

example : Unique (zeroPower.Value assignment) := by
  simp only [zeroPower, DomainExpr.value_power, SizeExpression.eval_constant]
  infer_instance

example : IsEmpty ((DomainExpr.power emptyFixed (SizeExpression.constant 1)).Value
    assignment) := by
  simp only [DomainExpr.value_power, SizeExpression.eval_constant, emptyFixed, DomainExpr.value_fixed,
    FinitePresentation.fin]
  infer_instance

def alternatives : DomainExpr context :=
  .sum [.fixed (FinitePresentation.fin 2), .fixed (FinitePresentation.fin 3)]

example : alternatives.bitWidth assignment = 3 := by
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

def nested : DomainExpr Matrices.context :=
  .product [Matrices.domain Matrices.field5,
    .power (.power (.fixed (FinitePresentation.fin 2))
      (SizeExpression.parameter (ctx := Matrices.context) .K))
      (SizeExpression.parameter (ctx := Matrices.context) .L ^ 2)]

example : ∃ p : SizeExpression Matrices.context, ∀ a, nested.bitWidth a ≤ p.eval a :=
  nested.polynomially_bounded

/-- Even a parameter named N is an ordinary name, without special bounds. -/
inductive PeerParameter | N | K | L
  deriving DecidableEq

instance : Fintype PeerParameter :=
  ⟨{.N, .K, .L}, by intro k; cases k <;> simp⟩

abbrev peerContext : SizeContext := ⟨PeerParameter, inferInstance⟩
def peerAssignment : SizeAssignment peerContext
  | .N => 0
  | .K => 7
  | .L => 11

def peerExponent : SizeExpression peerContext :=
  SizeExpression.parameter (ctx := peerContext) .N ^ 2 +
    SizeExpression.parameter (ctx := peerContext) .K * SizeExpression.parameter (ctx := peerContext) .L

example : peerExponent.eval peerAssignment = 77 := by
  simp [peerExponent, SizeExpression.eval_parameter (ctx := peerContext), peerAssignment]

example : ∃ p : SizeExpression peerContext, ∀ a,
    (DomainExpr.power (.fixed (FinitePresentation.fin 2)) peerExponent).bitWidth a ≤ p.eval a :=
  DomainExpr.polynomially_bounded _

end DomainExamples
end Polytime.Examples.Domains
