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

import Polytime1.Examples.Matrices

/-! # Encoding and boundary examples

These kernel-checked examples exercise layout and rejection, in addition to
the generic round-trip and canonical-decoding proofs.
-/

namespace Polytime1.Examples.Domains

noncomputable section DomainExamples

abbrev context : SizeContext := ⟨Empty, inferInstance⟩
def assignment : SizeAssignment context := Empty.elim

def emptyFixed : DomainExpression context := .fixed (FixedPresentation.fin 0)
def singletonFixed : DomainExpression context := .fixed (FixedPresentation.fin 1)

example : emptyFixed.bitWidth assignment = 0 := by
  simp [emptyFixed, FixedPresentation.bitWidth, FixedPresentation.fin]

example : IsEmpty (emptyFixed.Value assignment) := by
  simp only [emptyFixed, DomainExpression.value_fixed, FixedPresentation.fin]
  infer_instance

example : singletonFixed.bitWidth assignment = 0 := by
  simp [singletonFixed, FixedPresentation.bitWidth, FixedPresentation.fin]

example : (BitCodec.fin 0).decode (BitVec.ofNat 0 0) = none := by decide
example : (BitCodec.fin 1).decode (BitVec.ofNat 0 0) = some ⟨0, by decide⟩ := by
  decide

example : (DomainExpression.product []).bitWidth assignment = 0 := by simp
example : (DomainExpression.sum []).bitWidth assignment = 0 := by simp

example : BitCodec.unit.decode (BitVec.ofNat 0 0) = some PUnit.unit := by decide

def zeroPower : DomainExpression context := .power emptyFixed (SizeExpression.constant 0)

example : zeroPower.bitWidth assignment = 0 := by simp [zeroPower]

example : Unique (zeroPower.Value assignment) := by
  simp only [zeroPower, DomainExpression.value_power, SizeExpression.eval_constant]
  infer_instance

example : IsEmpty ((DomainExpression.power emptyFixed (SizeExpression.constant 1)).Value
    assignment) := by
  simp only [DomainExpression.value_power, SizeExpression.eval_constant, emptyFixed, DomainExpression.value_fixed,
    FixedPresentation.fin]
  infer_instance

def alternatives : DomainExpression context :=
  .sum [.fixed (FixedPresentation.fin 2), .fixed (FixedPresentation.fin 3)]

example : alternatives.bitWidth assignment = 3 := by
  simp [alternatives, FixedPresentation.bitWidth, FixedPresentation.fin]
  decide

/-- First alternative has a one-bit payload, second a two-bit payload. -/
def widths : Fin 2 → ℕ := ![1, 2]
def carriers : Fin 2 → Type := fun i => if i.val = 0 then Fin 2 else Fin 3

instance (i : Fin 2) : DecidableEq (carriers i) := by
  unfold carriers
  split <;> infer_instance

def alternativeCodecs : (i : Fin 2) → BitCodec (carriers i) (widths i) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact BitCodec.fin 2
  · refine Fin.cases ?_ (fun k => Fin.elim0 k) j
    exact BitCodec.fin 3

def sumCodec : BitCodec (Sigma carriers) 3 :=
  BitCodec.tagged carriers widths alternativeCodecs 2
    (by intro i; fin_cases i <;> decide)

/-- Tag 0, payload 1, zero high padding: bits [0,1,0]. -/
example : sumCodec.encode ⟨0, (1 : Fin 2)⟩ = BitVec.ofNat 3 2 := by decide
example : sumCodec.decode (BitVec.ofNat 3 2) = some ⟨0, (1 : Fin 2)⟩ := by decide

/-- The same payload with nonzero padding must be rejected. -/
example : sumCodec.decode (BitVec.ofNat 3 6) = none := by decide

/-- Tag 1 with unused payload label 3 must be rejected. -/
example : sumCodec.decode (BitVec.ofNat 3 7) = none := by decide

/-- A three-alternative union leaves binary tag 3 unused. -/
def threeAlternatives : BitCodec ((_i : Fin 3) × Fin 1) 2 :=
  BitCodec.tagged (fun _ => Fin 1) (fun _ => 0) (fun _ => BitCodec.fin 1) 0
    (by intro i; exact le_rfl)

example : threeAlternatives.decode (BitVec.ofNat 2 3) = none := by decide

example : (BitCodec.fin 3).decode (BitVec.ofNat 2 3) = none := by decide

/-- Product fields occupy low bits first: label 1 then the two-bit label 2. -/
example : ((BitCodec.fin 2).product (BitCodec.fin 3)).encode (1, 2) =
    BitVec.ofNat 3 5 := by
  apply BitVec.toNat_injective
  decide

/-- Power entries likewise occupy consecutive low-to-high blocks. -/
example : ((BitCodec.fin 3).power 3).encode ![0, 1, 2] =
    BitVec.ofNat 6 36 := by
  apply BitVec.toNat_injective
  decide

/-- Arbitrary carrier universes are supported, including by encodings. -/
def lifted : FixedPresentation.{1} where
  Carrier := ULift.{1} (Fin 2)
  cardinality := 2
  enumeration := Equiv.ulift

example (x : lifted.Carrier) : lifted.codec.decode (lifted.codec.encode x) = some x :=
  lifted.codec.decode_encode x

def nested : DomainExpression Matrices.context :=
  .product [Matrices.domain Matrices.field5,
    .power (.power (.fixed (FixedPresentation.fin 2))
      (SizeExpression.parameter (ctx := Matrices.context) .K))
      (SizeExpression.parameter (ctx := Matrices.context) .L ^ 2)]

example : ∃ p : SizePolynomial Matrices.context, ∀ a, nested.bitWidth a ≤ p.eval a :=
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

example : ∃ p : SizePolynomial peerContext, ∀ a,
    (DomainExpression.power (.fixed (FixedPresentation.fin 2)) peerExponent).bitWidth a ≤ p.eval a :=
  DomainExpression.polynomially_bounded _

end DomainExamples
end Polytime1.Examples.Domains
